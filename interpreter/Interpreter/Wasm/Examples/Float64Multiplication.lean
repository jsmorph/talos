import Interpreter.Wasm.Examples.Harness

/-!
# Binary64 multiplication example
-/

namespace Wasm
open SmallStep
namespace Float64Multiplication

def mulWat : String := "
(module
  (func (export \"mul64\")
    (param f64 f64) (result f64)
    local.get 0
    local.get 1
    f64.mul))
"

def mulModule : Module := Wasm.Examples.decodeOrDefault mulWat
def mulBody : Program := [.localGet 0, .localGet 1, .f64Mul]

def hasMulBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f64Mul] => true
  | _ => false

theorem hasMulBody_eq :
    ∀ body : Program, hasMulBody (some body) = true → body = mulBody := by
  intro body h
  simp only [hasMulBody] at h
  split at h
  · simp_all [mulBody]
  · contradiction

theorem mul_funcAt : mulModule.funcs[0]? = some mulModule.funcs[0]! := by
  have h : 0 < mulModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runMul (a b : UInt64) : List Value :=
  Wasm.Examples.runValues 2 mulModule 0 mulModule.initialStore [.f64 a, .f64 b]

theorem exact_product :
    runMul 0x3FF8000000000000 0xC000000000000000 =
      [.f64 0xC008000000000000] := by
  native_decide

def mulConfig (a b : UInt64) : Config Unit :=
  { expr := .running
      { locals := { params := [.f64 a, .f64 b] }
        code := mulBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := mulModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := mulModule.initialStore } }

theorem mul_initConfig (a b : UInt64) :
    initConfig { module := mulModule, host := {} } 0
        mulModule.initialStore [.f64 b, .f64 a] = .ok (mulConfig a b) := by
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

theorem mul_steps (a b : UInt64) :
    Steps (mulConfig a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f64Mul), (.administrative .finish)]
      ⟨.done [.f64 (IEEE64.mul a b)], (mulConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [mulConfig, f64Mul] using
    (Steps.refl
      (⟨.done [.f64 (IEEE64.mul a b)], (mulConfig a b).store⟩ : Config Unit))

theorem mul_terminates (a b : UInt64) :
    TerminatesWith (mulConfig a b)
      (fun values _ => values = [.f64 (IEEE64.mul a b)]) :=
  TerminatesWith.of_steps (mul_steps a b) rfl

end Float64Multiplication
end Wasm
