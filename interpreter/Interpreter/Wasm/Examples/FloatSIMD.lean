import Interpreter.Wasm.Examples.Harness

/-!
# Lane-wise binary32 SIMD multiplication example
-/

namespace Wasm
open SmallStep
namespace FloatSIMD

def mulWat : String := "
(module
  (func (export \"mul4\")
    (param v128 v128) (result v128)
    local.get 0
    local.get 1
    f32x4.mul))
"

def mulModule : Module := Wasm.Examples.decodeOrDefault mulWat
def mulOp : Simd.BinOp := .fMul .f32x4
def mulBody : Program := [.localGet 0, .localGet 1, .vBinOp mulOp]

def hasMulBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .vBinOp (.fMul .f32x4)] => true
  | _ => false

theorem hasMulBody_eq :
    ∀ body : Program, hasMulBody (some body) = true → body = mulBody := by
  intro body h
  simp only [hasMulBody] at h
  split at h
  · simp_all [mulBody, mulOp]
  · contradiction

theorem mul_funcAt : mulModule.funcs[0]? = some mulModule.funcs[0]! := by
  have h : 0 < mulModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def runMul (a b : BitVec 128) : List Value :=
  Wasm.Examples.runValues 2 mulModule 0 mulModule.initialStore [.v128 a, .v128 b]

def exampleA : BitVec 128 := Simd.ofLanes 32
  [0x3F800000, 0x80000000, 0x7F800000, 0x7FA00001]

def exampleB : BitVec 128 := Simd.ofLanes 32
  [0x40000000, 0x40400000, 0x00000000, 0x3F800000]

def exampleResult : BitVec 128 := Simd.ofLanes 32
  [0x40000000, 0x80000000, IEEE32.canonicalNaN.toNat,
   IEEE32.canonicalNaN.toNat]

theorem lane_special_values :
    runMul exampleA exampleB = [.v128 exampleResult] := by
  native_decide

def mulConfig (a b : BitVec 128) : Config Unit :=
  { expr := .running
      { locals := { params := [.v128 a, .v128 b] }
        code := mulBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := mulModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := mulModule.initialStore } }

theorem mul_initConfig (a b : BitVec 128) :
    initConfig { module := mulModule, host := {} } 0
        mulModule.initialStore [.v128 b, .v128 a] = .ok (mulConfig a b) := by
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

theorem mul_steps (a b : BitVec 128) :
    Steps (mulConfig a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction (.vBinOp mulOp)), (.administrative .finish)]
      ⟨.done [.v128 (mulOp.eval a b)], (mulConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .vBinOp
  apply Steps.cons .finish
  simpa [mulConfig] using
    (Steps.refl
      (⟨.done [.v128 (mulOp.eval a b)], (mulConfig a b).store⟩ : Config Unit))

theorem mul_terminates (a b : BitVec 128) :
    TerminatesWith (mulConfig a b)
      (fun values _ => values = [.v128 (mulOp.eval a b)]) :=
  TerminatesWith.of_steps (mul_steps a b) rfl

/-! ## Binary64 lanes -/

def mul64Wat : String := "
(module
  (func (export \"mul2\")
    (param v128 v128) (result v128)
    local.get 0
    local.get 1
    f64x2.mul))
"

def mul64Module : Module := Wasm.Examples.decodeOrDefault mul64Wat
def mul64Op : Simd.BinOp := .fMul .f64x2
def mul64Body : Program := [.localGet 0, .localGet 1, .vBinOp mul64Op]

def hasMul64Body : Option Program → Bool
  | some [.localGet 0, .localGet 1, .vBinOp (.fMul .f64x2)] => true
  | _ => false

theorem hasMul64Body_eq :
    ∀ body : Program, hasMul64Body (some body) = true → body = mul64Body := by
  intro body h
  simp only [hasMul64Body] at h
  split at h
  · simp_all [mul64Body, mul64Op]
  · contradiction

theorem mul64_funcAt :
    mul64Module.funcs[0]? = some mul64Module.funcs[0]! := by
  have h : 0 < mul64Module.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def example64A : BitVec 128 := Simd.ofLanes 64
  [0x3FF0000000000000, 0x7FF0000000000000]

def example64B : BitVec 128 := Simd.ofLanes 64
  [0x4000000000000000, 0x0000000000000000]

def example64Result : BitVec 128 := Simd.ofLanes 64
  [0x4000000000000000, IEEE64.canonicalNaN.toNat]

theorem binary64_lane_special_values :
    mul64Op.eval example64A example64B = example64Result := by
  native_decide

def mul64Config (a b : BitVec 128) : Config Unit :=
  { expr := .running
      { locals := { params := [.v128 a, .v128 b] }
        code := mul64Body
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := mul64Module, host := {} }]
            entry := ⟨0⟩ }
        wasm := mul64Module.initialStore } }

theorem mul64_initConfig (a b : BitVec 128) :
    initConfig { module := mul64Module, host := {} } 0
        mul64Module.initialStore [.v128 b, .v128 a] =
      .ok (mul64Config a b) := by
  have himports : mul64Module.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    mul64_funcAt]
  simp [Function.numParams, Function.toLocals, mul64Config]
  constructor
  · constructor
    · have hparamsLength :
          (mul64Module.funcs[0]?.getD default).params.length = 2 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasMul64Body_eq
      native_decide
    · constructor <;> native_decide

theorem mul64_steps (a b : BitVec 128) :
    Steps (mul64Config a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction (.vBinOp mul64Op)), (.administrative .finish)]
      ⟨.done [.v128 (mul64Op.eval a b)], (mul64Config a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .vBinOp
  apply Steps.cons .finish
  simpa [mul64Config] using
    (Steps.refl
      (⟨.done [.v128 (mul64Op.eval a b)],
        (mul64Config a b).store⟩ : Config Unit))

theorem mul64_terminates (a b : BitVec 128) :
    TerminatesWith (mul64Config a b)
      (fun values _ => values = [.v128 (mul64Op.eval a b)]) :=
  TerminatesWith.of_steps (mul64_steps a b) rfl

end FloatSIMD
end Wasm