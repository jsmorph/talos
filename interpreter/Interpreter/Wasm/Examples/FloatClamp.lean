import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 comparison and selection example

`clamp(x, low, high)` is encoded as `min(max(x, low), high)`.
-/

namespace Wasm
open SmallStep
namespace FloatClamp

def clampWat : String := "
(module
  (func (export \"clamp\")
    (param f32 f32 f32) (result f32)
    local.get 0
    local.get 1
    f32.max
    local.get 2
    f32.min))
"

def clampModule : Module := Wasm.Examples.decodeOrDefault clampWat
def clampBody : Program :=
  [.localGet 0, .localGet 1, .f32Max, .localGet 2, .f32Min]

def hasClampBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f32Max, .localGet 2, .f32Min] => true
  | _ => false

theorem hasClampBody_eq :
    ∀ body : Program,
      hasClampBody (some body) = true → body = clampBody := by
  intro body h
  simp only [hasClampBody] at h
  split at h
  · simp_all [clampBody]
  · contradiction

theorem clamp_funcAt :
    clampModule.funcs[0]? = some clampModule.funcs[0]! := by
  have h : 0 < clampModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runClamp (x low high : UInt32) : List Value :=
  Wasm.Examples.runValues 2 clampModule 0 clampModule.initialStore
    [.f32 high, .f32 low, .f32 x]

theorem clamp_inside_range :
    runClamp 0x40000000 0x3F800000 0x40400000 = [.f32 0x40000000] := by
  native_decide

theorem clamp_below_range :
    runClamp 0x00000000 0x3F800000 0x40400000 = [.f32 0x3F800000] := by
  native_decide

theorem clamp_above_range :
    runClamp 0x40800000 0x3F800000 0x40400000 = [.f32 0x40400000] := by
  native_decide

theorem clamp_nan_is_canonical_nan :
    runClamp 0x7FA00001 0x3F800000 0x40400000 =
      [.f32 IEEE32.canonicalNaN] := by
  native_decide

def clampResult (x low high : UInt32) : UInt32 :=
  IEEE32.min (IEEE32.max x low) high

def clampConfig (x low high : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 x, .f32 low, .f32 high] }
        code := clampBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := clampModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := clampModule.initialStore } }

theorem clamp_initConfig (x low high : UInt32) :
    initConfig { module := clampModule, host := {} } 0
        clampModule.initialStore [.f32 high, .f32 low, .f32 x] =
      .ok (clampConfig x low high) := by
  have himports : clampModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    clamp_funcAt]
  simp [Function.numParams, Function.toLocals, clampConfig]
  constructor
  · constructor
    · have hparamsLength :
          (clampModule.funcs[0]?.getD default).params.length = 3 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasClampBody_eq
      native_decide
    · constructor <;> native_decide

theorem clamp_steps (x low high : UInt32) :
    Steps (clampConfig x low high)
      [ (.instruction (.localGet 0))
      , (.instruction (.localGet 1))
      , (.instruction .f32Max)
      , (.instruction (.localGet 2))
      , (.instruction .f32Min)
      , (.administrative .finish) ]
      ⟨.done [.f32 (clampResult x low high)],
        (clampConfig x low high).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [clampConfig, clampResult, f32Min, f32Max] using
    (Steps.refl
      (⟨.done [.f32 (clampResult x low high)],
        (clampConfig x low high).store⟩ : Config Unit))

theorem clamp_terminates (x low high : UInt32) :
    TerminatesWith (clampConfig x low high)
      (fun values _ => values = [.f32 (clampResult x low high)]) :=
  TerminatesWith.of_steps (clamp_steps x low high) rfl

theorem clamp_partiallyMeets (x low high : UInt32) :
    PartiallyMeets (clampConfig x low high)
      (fun values _ => values = [.f32 (clampResult x low high)]) :=
  (clamp_terminates x low high).toPartiallyMeets

end FloatClamp
end Wasm
