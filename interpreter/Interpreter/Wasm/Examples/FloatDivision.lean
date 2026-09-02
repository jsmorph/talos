import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 division example

The hand-written WAT function exposes `f32.div` directly.  Its symbolic theorem
covers all bit patterns; concrete theorems exercise exact division, gradual
underflow, division by zero, and the invalid zero-over-zero case.
-/

namespace Wasm
open SmallStep
namespace FloatDivision

def divWat : String := "
(module
  (func (export \"div\")
    (param f32 f32) (result f32)
    local.get 0
    local.get 1
    f32.div))
"

def divModule : Module := Wasm.Examples.decodeOrDefault divWat

def divBody : Program := [.localGet 0, .localGet 1, .f32Div]

theorem div_signature :
    divModule.funcs.length = 1 ∧
    divModule.funcs.head?.map (·.params) = some [.f32, .f32] ∧
    divModule.funcs.head?.map (·.results) = some [.f32] := by
  native_decide

theorem div_export :
    divModule.exports = [{ name := "div", funcIdx := 0 }] := by
  native_decide

def hasDivBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f32Div] => true
  | _ => false

theorem hasDivBody_eq :
    ∀ body : Program, hasDivBody (some body) = true → body = divBody := by
  intro body h
  simp only [hasDivBody] at h
  split at h
  · simp_all [divBody]
  · contradiction

theorem div_body_eq : divModule.funcs[0]!.body = divBody := by
  apply hasDivBody_eq
  native_decide

theorem div_funcAt :
    divModule.funcs[0]? = some divModule.funcs[0]! := by
  have h : 0 < divModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runDiv (a b : UInt32) : List Value :=
  Wasm.Examples.runValues 2 divModule 0 divModule.initialStore
    [.f32 b, .f32 a]

theorem exact_six_div_four :
    runDiv 0x40C00000 0x40800000 = [.f32 0x3FC00000] := by
  native_decide

theorem min_normal_div_two_is_subnormal :
    runDiv 0x00800000 0x40000000 = [.f32 0x00400000] := by
  native_decide

theorem one_div_zero_is_infinity :
    runDiv 0x3F800000 0x00000000 = [.f32 0x7F800000] := by
  native_decide

theorem zero_div_zero_is_nan :
    runDiv 0x00000000 0x00000000 = [.f32 IEEE32.canonicalNaN] := by
  native_decide

def divResult (a b : UInt32) : UInt32 := f32Div a b

def divConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 a, .f32 b] }
        code := divBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := divModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := divModule.initialStore } }

theorem div_initConfig (a b : UInt32) :
    initConfig { module := divModule, host := {} } 0
        divModule.initialStore [.f32 b, .f32 a] =
      .ok (divConfig a b) := by
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

theorem div_steps (a b : UInt32) :
    Steps (divConfig a b)
      [ (.instruction (.localGet 0))
      , (.instruction (.localGet 1))
      , (.instruction .f32Div)
      , (.administrative .finish) ]
      ⟨.done [.f32 (divResult a b)], (divConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [divConfig, divResult] using
    (Steps.refl
      (⟨.done [.f32 (divResult a b)],
        (divConfig a b).store⟩ : Config Unit))

theorem div_terminates (a b : UInt32) :
    TerminatesWith (divConfig a b)
      (fun values _ => values = [.f32 (Wasm.IEEE32.div a b)]) := by
  simpa [divResult, f32Div] using
    (TerminatesWith.of_steps (div_steps a b) rfl)

theorem div_partiallyMeets (a b : UInt32) :
    PartiallyMeets (divConfig a b)
      (fun values _ => values = [.f32 (Wasm.IEEE32.div a b)]) :=
  (div_terminates a b).toPartiallyMeets

end FloatDivision
end Wasm