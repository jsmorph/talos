import Interpreter.Wasm.Examples.Harness

/-!
# Algorithm-level sine approximation example

WebAssembly core has no transcendental opcodes.  This module therefore
implements the cubic small-angle polynomial `x - x^3 / 6` from ordinary f32
instructions and proves its exact floating-point execution for every input.
-/

namespace Wasm
open SmallStep
namespace FloatSinPolynomial

def sinWat : String := "
(module
  (func (export \"sin_small\")
    (param f32) (result f32)
    local.get 0
    local.get 0
    local.get 0
    f32.mul
    local.get 0
    f32.mul
    f32.const 6
    f32.div
    f32.sub))
"

def sinModule : Module := Wasm.Examples.decodeOrDefault sinWat
def six : UInt32 := 0x40C00000
def sinBody : Program :=
  [.localGet 0, .localGet 0, .localGet 0, .f32Mul, .localGet 0,
   .f32Mul, .f32Const six, .f32Div, .f32Sub]

def hasSinBody : Option Program → Bool
  | some [.localGet 0, .localGet 0, .localGet 0, .f32Mul, .localGet 0,
      .f32Mul, .f32Const 0x40C00000, .f32Div, .f32Sub] => true
  | _ => false

theorem hasSinBody_eq :
    ∀ body : Program, hasSinBody (some body) = true → body = sinBody := by
  intro body h
  simp only [hasSinBody] at h
  split at h
  · simp_all [sinBody, six]
  · contradiction

theorem sin_funcAt : sinModule.funcs[0]? = some sinModule.funcs[0]! := by
  have h : 0 < sinModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def sinResult (x : UInt32) : UInt32 :=
  IEEE32.sub x (IEEE32.div (IEEE32.mul (IEEE32.mul x x) x) six)

def runSin (x : UInt32) : List Value :=
  Wasm.Examples.runValues 2 sinModule 0 sinModule.initialStore [.f32 x]

theorem sin_zero : runSin 0 = [.f32 0] := by
  native_decide

/-- At `x = 1/2`, the program returns the correctly rounded cubic value
`23/48`, approximately `0.4791667`. -/
theorem sin_half_cubic_value : runSin 0x3F000000 = [.f32 0x3EF55555] := by
  native_decide

def sinConfig (x : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 x] }
        code := sinBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := sinModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := sinModule.initialStore } }

theorem sin_initConfig (x : UInt32) :
    initConfig { module := sinModule, host := {} } 0
        sinModule.initialStore [.f32 x] = .ok (sinConfig x) := by
  have himports : sinModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    sin_funcAt]
  simp [Function.numParams, Function.toLocals, sinConfig]
  constructor
  · constructor
    · have hparamsLength :
          (sinModule.funcs[0]?.getD default).params.length = 1 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasSinBody_eq
      native_decide
    · constructor <;> native_decide

theorem sin_steps (x : UInt32) :
    Steps (sinConfig x)
      [(.instruction (.localGet 0)), (.instruction (.localGet 0)),
       (.instruction (.localGet 0)), (.instruction .f32Mul),
       (.instruction (.localGet 0)), (.instruction .f32Mul),
       (.instruction (.f32Const six)), (.instruction .f32Div),
       (.instruction .f32Sub), (.administrative .finish)]
      ⟨.done [.f32 (sinResult x)], (sinConfig x).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat0 rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [sinConfig, sinResult, six, f32Mul, f32Div, f32Sub] using
    (Steps.refl
      (⟨.done [.f32 (sinResult x)], (sinConfig x).store⟩ : Config Unit))

theorem sin_terminates (x : UInt32) :
    TerminatesWith (sinConfig x)
      (fun values _ => values = [.f32 (sinResult x)]) :=
  TerminatesWith.of_steps (sin_steps x) rfl

end FloatSinPolynomial
end Wasm