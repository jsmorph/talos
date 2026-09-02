import Interpreter.Wasm.Examples.Harness

/-!
# Binary64 division example

The hand-written WAT function exposes `f64.div` directly.  The symbolic trace
uses the pure modeled IEEE operation and is independent of interpreter fuel.
-/

namespace Wasm
open SmallStep
namespace Float64Division

def divWat : String := "
(module
  (func (export \"div64\")
    (param f64 f64) (result f64)
    local.get 0
    local.get 1
    f64.div))
"

def divModule : Module := Wasm.Examples.decodeOrDefault divWat
def divBody : Program := [.localGet 0, .localGet 1, .f64Div]

def hasDivBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f64Div] => true
  | _ => false

theorem hasDivBody_eq :
    ∀ body : Program, hasDivBody (some body) = true → body = divBody := by
  intro body h
  simp only [hasDivBody] at h
  split at h
  · simp_all [divBody]
  · contradiction

theorem div_signature :
    divModule.funcs.length = 1 ∧
    divModule.funcs.head?.map (·.params) = some [.f64, .f64] ∧
    divModule.funcs.head?.map (·.results) = some [.f64] := by
  native_decide

theorem div_export :
    divModule.exports = [{ name := "div64", funcIdx := 0 }] := by
  native_decide

theorem div_body_eq : divModule.funcs[0]!.body = divBody := by
  apply hasDivBody_eq
  native_decide

theorem div_funcAt : divModule.funcs[0]? = some divModule.funcs[0]! := by
  have h : 0 < divModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runDiv (a b : UInt64) : List Value :=
  Wasm.Examples.runValues 2 divModule 0 divModule.initialStore [.f64 b, .f64 a]

theorem exact_six_div_four :
    runDiv 0x4018000000000000 0x4010000000000000 =
      [.f64 0x3FF8000000000000] := by
  native_decide

def divConfig (a b : UInt64) : Config Unit :=
  { expr := .running
      { locals := { params := [.f64 a, .f64 b] }
        code := divBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := divModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := divModule.initialStore } }

theorem div_initConfig (a b : UInt64) :
    initConfig { module := divModule, host := {} } 0
        divModule.initialStore [.f64 b, .f64 a] = .ok (divConfig a b) := by
  have himports : divModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    div_funcAt]
  simp [Function.numParams, Function.toLocals, divConfig]
  constructor
  · constructor
    · have hparamsLength :
          (divModule.funcs[0]?.getD default).params.length = 2 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasDivBody_eq
      native_decide
    · constructor <;> native_decide

theorem div_steps (a b : UInt64) :
    Steps (divConfig a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f64Div), (.administrative .finish)]
      ⟨.done [.f64 (IEEE64.div a b)], (divConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [divConfig, f64Div] using
    (Steps.refl
      (⟨.done [.f64 (IEEE64.div a b)], (divConfig a b).store⟩ : Config Unit))

theorem div_terminates (a b : UInt64) :
    TerminatesWith (divConfig a b)
      (fun values _ => values = [.f64 (IEEE64.div a b)]) :=
  TerminatesWith.of_steps (div_steps a b) rfl

end Float64Division
end Wasm
