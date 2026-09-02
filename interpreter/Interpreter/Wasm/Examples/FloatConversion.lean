import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 conversion round-trip example

One WAT program converts a signed `i32` to `f32` and truncates it back;
concrete theorems show the exact range boundary and the first inexact value.
A second one-instruction WAT program has a fuel-independent arbitrary-input
theorem for the proof-visible signed conversion itself.
-/

namespace Wasm
open SmallStep
namespace FloatConversion

def roundTripWat : String := "
(module
  (func (export \"round_trip\")
    (param i32) (result i32)
    local.get 0
    f32.convert_i32_s
    i32.trunc_f32_s))
"

def roundTripModule : Module := Wasm.Examples.decodeOrDefault roundTripWat
def roundTripBody : Program :=
  [.localGet 0, .f32ConvertI32S, .i32TruncF32S]

def hasRoundTripBody : Option Program → Bool
  | some [.localGet 0, .f32ConvertI32S, .i32TruncF32S] => true
  | _ => false

theorem hasRoundTripBody_eq :
    ∀ body : Program,
      hasRoundTripBody (some body) = true → body = roundTripBody := by
  intro body h
  simp only [hasRoundTripBody] at h
  split at h
  · simp_all [roundTripBody]
  · contradiction

theorem roundTrip_funcAt :
    roundTripModule.funcs[0]? = some roundTripModule.funcs[0]! := by
  have h : 0 < roundTripModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runRoundTrip (a : UInt32) : List Value :=
  Wasm.Examples.runValues 2 roundTripModule 0 roundTripModule.initialStore [.i32 a]

theorem largest_odd_exact_i32_round_trips :
    runRoundTrip 0x00FFFFFF = [.i32 0x00FFFFFF] := by
  native_decide

theorem first_inexact_i32_rounds_to_even :
    runRoundTrip 0x01000001 = [.i32 0x01000000] := by
  native_decide

def convertWat : String := "
(module
  (func (export \"convert_i32_s\")
    (param i32) (result f32)
    local.get 0
    f32.convert_i32_s))
"

def convertModule : Module := Wasm.Examples.decodeOrDefault convertWat
def convertBody : Program := [.localGet 0, .f32ConvertI32S]

def hasConvertBody : Option Program → Bool
  | some [.localGet 0, .f32ConvertI32S] => true
  | _ => false

theorem hasConvertBody_eq :
    ∀ body : Program, hasConvertBody (some body) = true → body = convertBody := by
  intro body h
  simp only [hasConvertBody] at h
  split at h
  · simp_all [convertBody]
  · contradiction

theorem convert_funcAt :
    convertModule.funcs[0]? = some convertModule.funcs[0]! := by
  have h : 0 < convertModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def convertResult (a : UInt32) : UInt32 := f32ConvertI32S a

def convertConfig (a : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 a] }
        code := convertBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := convertModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := convertModule.initialStore } }

theorem convert_steps (a : UInt32) :
    Steps (convertConfig a)
      [ (.instruction (.localGet 0))
      , (.instruction .f32ConvertI32S)
      , (.administrative .finish) ]
      ⟨.done [.f32 (convertResult a)], (convertConfig a).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat1 rfl rfl)
  apply Steps.cons .finish
  simpa [convertConfig, convertResult] using
    (Steps.refl
      (⟨.done [.f32 (convertResult a)],
        (convertConfig a).store⟩ : Config Unit))

theorem convert_terminates (a : UInt32) :
    TerminatesWith (convertConfig a)
      (fun values _ => values = [.f32 (IEEE32.convertI32S a)]) := by
  simpa [convertResult, f32ConvertI32S] using
    (TerminatesWith.of_steps (convert_steps a) rfl)

end FloatConversion
end Wasm