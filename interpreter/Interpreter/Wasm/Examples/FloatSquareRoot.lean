import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 square-root example
-/

namespace Wasm
open SmallStep
namespace FloatSquareRoot

def sqrtWat : String := "
(module
  (func (export \"sqrt\")
    (param f32) (result f32)
    local.get 0
    f32.sqrt))
"

def sqrtModule : Module := Wasm.Examples.decodeOrDefault sqrtWat
def sqrtBody : Program := [.localGet 0, .f32Sqrt]

theorem sqrt_signature :
    sqrtModule.funcs.length = 1 ∧
    sqrtModule.funcs.head?.map (·.params) = some [.f32] ∧
    sqrtModule.funcs.head?.map (·.results) = some [.f32] := by
  native_decide

def hasSqrtBody : Option Program → Bool
  | some [.localGet 0, .f32Sqrt] => true
  | _ => false

theorem hasSqrtBody_eq :
    ∀ body : Program, hasSqrtBody (some body) = true → body = sqrtBody := by
  intro body h
  simp only [hasSqrtBody] at h
  split at h
  · simp_all [sqrtBody]
  · contradiction

theorem sqrt_funcAt :
    sqrtModule.funcs[0]? = some sqrtModule.funcs[0]! := by
  have h : 0 < sqrtModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runSqrt (a : UInt32) : List Value :=
  Wasm.Examples.runValues 2 sqrtModule 0 sqrtModule.initialStore [.f32 a]

theorem sqrt_four_is_two :
    runSqrt 0x40800000 = [.f32 0x40000000] := by
  native_decide

theorem sqrt_negative_one_is_nan :
    runSqrt 0xBF800000 = [.f32 IEEE32.canonicalNaN] := by
  native_decide

theorem sqrt_preserves_negative_zero :
    runSqrt 0x80000000 = [.f32 0x80000000] := by
  native_decide

def sqrtResult (a : UInt32) : UInt32 := f32Sqrt a

def sqrtConfig (a : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 a] }
        code := sqrtBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := sqrtModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := sqrtModule.initialStore } }

theorem sqrt_initConfig (a : UInt32) :
    initConfig { module := sqrtModule, host := {} } 0
        sqrtModule.initialStore [.f32 a] = .ok (sqrtConfig a) := by
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

theorem sqrt_steps (a : UInt32) :
    Steps (sqrtConfig a)
      [ (.instruction (.localGet 0))
      , (.instruction .f32Sqrt)
      , (.administrative .finish) ]
      ⟨.done [.f32 (sqrtResult a)], (sqrtConfig a).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat1 rfl rfl)
  apply Steps.cons .finish
  simpa [sqrtConfig, sqrtResult] using
    (Steps.refl
      (⟨.done [.f32 (sqrtResult a)],
        (sqrtConfig a).store⟩ : Config Unit))

theorem sqrt_terminates (a : UInt32) :
    TerminatesWith (sqrtConfig a)
      (fun values _ => values = [.f32 (Wasm.IEEE32.sqrt a)]) := by
  simpa [sqrtResult, f32Sqrt] using
    (TerminatesWith.of_steps (sqrt_steps a) rfl)

theorem sqrt_partiallyMeets (a : UInt32) :
    PartiallyMeets (sqrtConfig a)
      (fun values _ => values = [.f32 (Wasm.IEEE32.sqrt a)]) :=
  (sqrt_terminates a).toPartiallyMeets

end FloatSquareRoot
end Wasm