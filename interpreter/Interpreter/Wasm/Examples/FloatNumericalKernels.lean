import Interpreter.Wasm.Examples.Harness

/-!
# Representative floating-point numerical kernels

The decoded hand-written programs implement an f32 affine evaluation and a
two-term f64 dot product.  Their symbolic traces use only the modeled IEEE
operations and do not mention interpreter fuel.
-/

namespace Wasm
open SmallStep
namespace FloatNumericalKernels

def affineWat : String := "
(module
  (func (export \"affine32\")
    (param f32 f32 f32) (result f32)
    local.get 0
    local.get 1
    f32.mul
    local.get 2
    f32.add))
"

def affineModule : Module := Wasm.Examples.decodeOrDefault affineWat
def affineBody : Program :=
  [.localGet 0, .localGet 1, .f32Mul, .localGet 2, .f32Add]

def hasAffineBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f32Mul, .localGet 2, .f32Add] => true
  | _ => false

theorem hasAffineBody_eq : ∀ body : Program,
    hasAffineBody (some body) = true → body = affineBody := by
  intro body h
  simp only [hasAffineBody] at h
  split at h
  · simp_all [affineBody]
  · contradiction

theorem affine_signature :
    affineModule.funcs.length = 1 ∧
    affineModule.funcs.head?.map (·.params) = some [.f32, .f32, .f32] ∧
    affineModule.funcs.head?.map (·.results) = some [.f32] := by
  native_decide

theorem affine_funcAt :
    affineModule.funcs[0]? = some affineModule.funcs[0]! := by
  have h : 0 < affineModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def affineResult (a x b : UInt32) : UInt32 :=
  IEEE32.add (IEEE32.mul a x) b

def affineConfig (a x b : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 a, .f32 x, .f32 b] }
        code := affineBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := affineModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := affineModule.initialStore } }

theorem affine_initConfig (a x b : UInt32) :
    initConfig { module := affineModule, host := {} } 0
        affineModule.initialStore [.f32 b, .f32 x, .f32 a] =
      .ok (affineConfig a x b) := by
  have himports : affineModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    affine_funcAt]
  simp [Function.numParams, Function.toLocals, affineConfig]
  constructor
  · constructor
    · have hparamsLength :
          (affineModule.funcs[0]?.getD default).params.length = 3 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasAffineBody_eq
      native_decide
    · constructor <;> native_decide

theorem affine_steps (a x b : UInt32) :
    Steps (affineConfig a x b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f32Mul), (.instruction (.localGet 2)),
       (.instruction .f32Add), (.administrative .finish)]
      ⟨.done [.f32 (affineResult a x b)], (affineConfig a x b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [affineConfig, affineResult, f32Mul, f32Add] using
    (Steps.refl
      (⟨.done [.f32 (affineResult a x b)],
        (affineConfig a x b).store⟩ : Config Unit))

theorem affine_terminates (a x b : UInt32) :
    TerminatesWith (affineConfig a x b)
      (fun values _ => values = [.f32 (affineResult a x b)]) :=
  TerminatesWith.of_steps (affine_steps a x b) rfl

def dotWat : String := "
(module
  (func (export \"dot2_f64\")
    (param f64 f64 f64 f64) (result f64)
    local.get 0
    local.get 1
    f64.mul
    local.get 2
    local.get 3
    f64.mul
    f64.add))
"

def dotModule : Module := Wasm.Examples.decodeOrDefault dotWat
def dotBody : Program :=
  [.localGet 0, .localGet 1, .f64Mul, .localGet 2, .localGet 3,
   .f64Mul, .f64Add]

def hasDotBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f64Mul, .localGet 2, .localGet 3,
      .f64Mul, .f64Add] => true
  | _ => false

theorem hasDotBody_eq : ∀ body : Program,
    hasDotBody (some body) = true → body = dotBody := by
  intro body h
  simp only [hasDotBody] at h
  split at h
  · simp_all [dotBody]
  · contradiction

theorem dot_signature :
    dotModule.funcs.length = 1 ∧
    dotModule.funcs.head?.map (·.params) =
      some [.f64, .f64, .f64, .f64] ∧
    dotModule.funcs.head?.map (·.results) = some [.f64] := by
  native_decide

theorem dot_funcAt : dotModule.funcs[0]? = some dotModule.funcs[0]! := by
  have h : 0 < dotModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def dotResult (a₀ b₀ a₁ b₁ : UInt64) : UInt64 :=
  IEEE64.add (IEEE64.mul a₀ b₀) (IEEE64.mul a₁ b₁)

def dotConfig (a₀ b₀ a₁ b₁ : UInt64) : Config Unit :=
  { expr := .running
      { locals := { params := [.f64 a₀, .f64 b₀, .f64 a₁, .f64 b₁] }
        code := dotBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := dotModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := dotModule.initialStore } }

theorem dot_initConfig (a₀ b₀ a₁ b₁ : UInt64) :
    initConfig { module := dotModule, host := {} } 0 dotModule.initialStore
        [.f64 b₁, .f64 a₁, .f64 b₀, .f64 a₀] =
      .ok (dotConfig a₀ b₀ a₁ b₁) := by
  have himports : dotModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    dot_funcAt]
  simp [Function.numParams, Function.toLocals, dotConfig]
  constructor
  · constructor
    · have hparamsLength :
          (dotModule.funcs[0]?.getD default).params.length = 4 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasDotBody_eq
      native_decide
    · constructor <;> native_decide

theorem dot_steps (a₀ b₀ a₁ b₁ : UInt64) :
    Steps (dotConfig a₀ b₀ a₁ b₁)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f64Mul), (.instruction (.localGet 2)),
       (.instruction (.localGet 3)), (.instruction .f64Mul),
       (.instruction .f64Add), (.administrative .finish)]
      ⟨.done [.f64 (dotResult a₀ b₀ a₁ b₁)],
        (dotConfig a₀ b₀ a₁ b₁).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [dotConfig, dotResult, f64Mul, f64Add] using
    (Steps.refl
      (⟨.done [.f64 (dotResult a₀ b₀ a₁ b₁)],
        (dotConfig a₀ b₀ a₁ b₁).store⟩ : Config Unit))

theorem dot_terminates (a₀ b₀ a₁ b₁ : UInt64) :
    TerminatesWith (dotConfig a₀ b₀ a₁ b₁)
      (fun values _ => values = [.f64 (dotResult a₀ b₀ a₁ b₁)]) :=
  TerminatesWith.of_steps (dot_steps a₀ b₀ a₁ b₁) rfl

end FloatNumericalKernels
end Wasm
