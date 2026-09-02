import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 multiplication example

This file decodes a hand-written WAT function and proves its symbolic
small-step behavior for arbitrary binary32 inputs.  Concrete checks cover an
exact normal product and gradual underflow at the least-subnormal tie.
-/

namespace Wasm
open SmallStep
namespace FloatMultiplication

def mulWat : String := "
(module
  (func (export \"mul\")
    (param f32 f32) (result f32)
    local.get 0
    local.get 1
    f32.mul))
"

def mulModule : Module := Wasm.Examples.decodeOrDefault mulWat

def mulBody : Program :=
  [ .localGet 0
  , .localGet 1
  , .f32Mul ]

theorem mul_signature :
    mulModule.funcs.length = 1 ∧
    mulModule.funcs.head?.map (·.params) = some [.f32, .f32] ∧
    mulModule.funcs.head?.map (·.results) = some [.f32] := by
  native_decide

theorem mul_export :
    mulModule.exports = [{ name := "mul", funcIdx := 0 }] := by
  native_decide

def hasMulBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f32Mul] => true
  | _ => false

theorem mul_body :
    hasMulBody (mulModule.funcs.head?.map (·.body)) = true := by
  native_decide

theorem hasMulBody_eq :
    ∀ body : Program, hasMulBody (some body) = true → body = mulBody := by
  intro body h
  simp only [hasMulBody] at h
  split at h
  · simp_all [mulBody]
  · contradiction

theorem mul_body_eq : mulModule.funcs[0]!.body = mulBody := by
  apply hasMulBody_eq
  native_decide

theorem mul_funcAt :
    mulModule.funcs[0]? = some mulModule.funcs[0]! := by
  have h : 0 < mulModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runMul (a b : UInt32) : List Value :=
  Wasm.Examples.runValues 2 mulModule 0 mulModule.initialStore
    [.f32 a, .f32 b]

/-- `1.5 * -2 = -3` is exactly representable. -/
theorem exact_normal_product :
    runMul 0x3FC00000 0xC0000000 = [.f32 0xC0400000] := by
  native_decide

/-- Half of the least positive subnormal is exactly between positive zero and
the least subnormal; ties-to-even selects positive zero. -/
theorem least_subnormal_underflow_tie :
    runMul 0x00000001 0x3F000000 = [.f32 0x00000000] := by
  native_decide

def mulResult (a b : UInt32) : UInt32 := f32Mul a b

def mulConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 a, .f32 b] }
        code := mulBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := mulModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := mulModule.initialStore } }

theorem mul_initConfig (a b : UInt32) :
    initConfig { module := mulModule, host := {} } 0
        mulModule.initialStore [.f32 b, .f32 a] =
      .ok (mulConfig a b) := by
  have himports : mulModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    mul_funcAt]
  simp [Function.numParams, Function.toLocals, mulConfig]
  constructor
  · constructor
    · have hparamsLength :
          (mulModule.funcs[0]?.getD default).params.length = 2 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasMulBody_eq
      native_decide
    · constructor <;> native_decide

theorem mul_steps (a b : UInt32) :
    Steps (mulConfig a b)
      [ (.instruction (.localGet 0))
      , (.instruction (.localGet 1))
      , (.instruction .f32Mul)
      , (.administrative .finish) ]
      ⟨.done [.f32 (mulResult a b)], (mulConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [mulConfig, mulResult] using
    (Steps.refl
      (⟨.done [.f32 (mulResult a b)],
        (mulConfig a b).store⟩ : Config Unit))

/-- Fuel-independent total correctness for the decoded WAT multiplication
program on arbitrary input bit patterns. -/
theorem mul_terminates (a b : UInt32) :
    TerminatesWith (mulConfig a b)
      (fun values _ => values = [.f32 (Wasm.IEEE32.mul a b)]) := by
  simpa [mulResult, f32Mul] using
    (TerminatesWith.of_steps (mul_steps a b) rfl)

theorem mul_partiallyMeets (a b : UInt32) :
    PartiallyMeets (mulConfig a b)
      (fun values _ => values = [.f32 (Wasm.IEEE32.mul a b)]) :=
  (mul_terminates a b).toPartiallyMeets

end FloatMultiplication
end Wasm