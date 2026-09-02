import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 integral-rounding example
-/

namespace Wasm
open SmallStep
namespace FloatNearest

def nearestWat : String := "
(module
  (func (export \"nearest\")
    (param f32) (result f32)
    local.get 0
    f32.nearest))
"

def nearestModule : Module := Wasm.Examples.decodeOrDefault nearestWat
def nearestBody : Program := [.localGet 0, .f32Nearest]

def hasNearestBody : Option Program → Bool
  | some [.localGet 0, .f32Nearest] => true
  | _ => false

theorem hasNearestBody_eq :
    ∀ body : Program,
      hasNearestBody (some body) = true → body = nearestBody := by
  intro body h
  simp only [hasNearestBody] at h
  split at h
  · simp_all [nearestBody]
  · contradiction

theorem nearest_funcAt :
    nearestModule.funcs[0]? = some nearestModule.funcs[0]! := by
  have h : 0 < nearestModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runNearest (a : UInt32) : List Value :=
  Wasm.Examples.runValues 2 nearestModule 0 nearestModule.initialStore [.f32 a]

theorem nearest_one_and_half_is_two :
    runNearest 0x3FC00000 = [.f32 0x40000000] := by
  native_decide

theorem nearest_two_and_half_ties_to_even :
    runNearest 0x40200000 = [.f32 0x40000000] := by
  native_decide

theorem nearest_negative_half_is_negative_zero :
    runNearest 0xBF000000 = [.f32 0x80000000] := by
  native_decide

def nearestConfig (a : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 a] }
        code := nearestBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := nearestModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := nearestModule.initialStore } }

theorem nearest_initConfig (a : UInt32) :
    initConfig { module := nearestModule, host := {} } 0
        nearestModule.initialStore [.f32 a] = .ok (nearestConfig a) := by
  have himports : nearestModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    nearest_funcAt]
  simp [Function.numParams, Function.toLocals, nearestConfig]
  constructor
  · constructor
    · have hparamsLength :
          (nearestModule.funcs[0]?.getD default).params.length = 1 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasNearestBody_eq
      native_decide
    · constructor <;> native_decide

theorem nearest_steps (a : UInt32) :
    Steps (nearestConfig a)
      [ (.instruction (.localGet 0))
      , (.instruction .f32Nearest)
      , (.administrative .finish) ]
      ⟨.done [.f32 (IEEE32.nearest a)], (nearestConfig a).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat1 rfl rfl)
  apply Steps.cons .finish
  simpa [nearestConfig, f32Nearest] using
    (Steps.refl
      (⟨.done [.f32 (IEEE32.nearest a)],
        (nearestConfig a).store⟩ : Config Unit))

theorem nearest_terminates (a : UInt32) :
    TerminatesWith (nearestConfig a)
      (fun values _ => values = [.f32 (IEEE32.nearest a)]) :=
  TerminatesWith.of_steps (nearest_steps a) rfl

end FloatNearest
end Wasm