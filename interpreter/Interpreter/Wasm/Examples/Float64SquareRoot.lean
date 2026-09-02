import Interpreter.Wasm.Examples.Harness

/-!
# Binary64 square-root example
-/

namespace Wasm
open SmallStep
namespace Float64SquareRoot

def sqrtWat : String := "
(module
  (func (export \"sqrt64\")
    (param f64) (result f64)
    local.get 0
    f64.sqrt))
"

def sqrtModule : Module := Wasm.Examples.decodeOrDefault sqrtWat
def sqrtBody : Program := [.localGet 0, .f64Sqrt]

theorem sqrt_signature :
    sqrtModule.funcs.length = 1 ∧
    sqrtModule.funcs.head?.map (·.params) = some [.f64] ∧
    sqrtModule.funcs.head?.map (·.results) = some [.f64] := by
  native_decide

def hasSqrtBody : Option Program → Bool
  | some [.localGet 0, .f64Sqrt] => true
  | _ => false

theorem hasSqrtBody_eq :
    ∀ body : Program, hasSqrtBody (some body) = true → body = sqrtBody := by
  intro body h
  simp only [hasSqrtBody] at h
  split at h
  · simp_all [sqrtBody]
  · contradiction

theorem sqrt_funcAt : sqrtModule.funcs[0]? = some sqrtModule.funcs[0]! := by
  have h : 0 < sqrtModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runSqrt (a : UInt64) : List Value :=
  Wasm.Examples.runValues 2 sqrtModule 0 sqrtModule.initialStore [.f64 a]

theorem sqrt_four_is_two :
    runSqrt 0x4010000000000000 = [.f64 0x4000000000000000] := by
  native_decide

def sqrtConfig (a : UInt64) : Config Unit :=
  { expr := .running
      { locals := { params := [.f64 a] }
        code := sqrtBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := sqrtModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := sqrtModule.initialStore } }

theorem sqrt_initConfig (a : UInt64) :
    initConfig { module := sqrtModule, host := {} } 0
        sqrtModule.initialStore [.f64 a] = .ok (sqrtConfig a) := by
  have himports : sqrtModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    sqrt_funcAt]
  simp [Function.numParams, Function.toLocals, sqrtConfig]
  constructor
  · constructor
    · have hparamsLength :
          (sqrtModule.funcs[0]?.getD default).params.length = 1 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasSqrtBody_eq
      native_decide
    · constructor <;> native_decide

theorem sqrt_steps (a : UInt64) :
    Steps (sqrtConfig a)
      [(.instruction (.localGet 0)), (.instruction .f64Sqrt),
       (.administrative .finish)]
      ⟨.done [.f64 (IEEE64.sqrt a)], (sqrtConfig a).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat1 rfl rfl)
  apply Steps.cons .finish
  simpa [sqrtConfig, f64Sqrt] using
    (Steps.refl
      (⟨.done [.f64 (IEEE64.sqrt a)], (sqrtConfig a).store⟩ : Config Unit))

theorem sqrt_terminates (a : UInt64) :
    TerminatesWith (sqrtConfig a)
      (fun values _ => values = [.f64 (IEEE64.sqrt a)]) :=
  TerminatesWith.of_steps (sqrt_steps a) rfl

end Float64SquareRoot
end Wasm
