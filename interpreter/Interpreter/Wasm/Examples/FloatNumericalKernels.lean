import Interpreter.Wasm.Examples.Harness

/-!
# Representative floating-point numerical kernels

The decoded hand-written programs implement f32 affine and three-stage Horner
evaluation plus two- and four-term f64 dot products.  Their symbolic traces
use only the modeled IEEE operations and do not mention interpreter fuel.
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

def horner3Wat : String := "
(module
  (func (export \"horner3_f32\")
    (param f32 f32 f32 f32 f32) (result f32)
    local.get 1
    local.get 0
    f32.mul
    local.get 2
    f32.add
    local.get 0
    f32.mul
    local.get 3
    f32.add
    local.get 0
    f32.mul
    local.get 4
    f32.add))
"

def horner3Module : Module := Wasm.Examples.decodeOrDefault horner3Wat
def horner3Body : Program :=
  [.localGet 1, .localGet 0, .f32Mul, .localGet 2, .f32Add,
   .localGet 0, .f32Mul, .localGet 3, .f32Add,
   .localGet 0, .f32Mul, .localGet 4, .f32Add]

def hasHorner3Body : Option Program → Bool
  | some [.localGet 1, .localGet 0, .f32Mul, .localGet 2, .f32Add,
      .localGet 0, .f32Mul, .localGet 3, .f32Add,
      .localGet 0, .f32Mul, .localGet 4, .f32Add] => true
  | _ => false

theorem hasHorner3Body_eq : ∀ body : Program,
    hasHorner3Body (some body) = true → body = horner3Body := by
  intro body h
  simp only [hasHorner3Body] at h
  split at h
  · simp_all [horner3Body]
  · contradiction

theorem horner3_signature :
    horner3Module.funcs.length = 1 ∧
    horner3Module.funcs.head?.map (·.params) =
      some [.f32, .f32, .f32, .f32, .f32] ∧
    horner3Module.funcs.head?.map (·.results) = some [.f32] := by
  native_decide

theorem horner3_funcAt :
    horner3Module.funcs[0]? = some horner3Module.funcs[0]! := by
  have h : 0 < horner3Module.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def horner3Result (x c₃ c₂ c₁ c₀ : UInt32) : UInt32 :=
  IEEE32.add
    (IEEE32.mul
      (IEEE32.add
        (IEEE32.mul (IEEE32.add (IEEE32.mul c₃ x) c₂) x) c₁)
      x)
    c₀

def horner3Config (x c₃ c₂ c₁ c₀ : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 x, .f32 c₃, .f32 c₂, .f32 c₁, .f32 c₀] }
        code := horner3Body
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := horner3Module, host := {} }]
            entry := ⟨0⟩ }
        wasm := horner3Module.initialStore } }

theorem horner3_initConfig (x c₃ c₂ c₁ c₀ : UInt32) :
    initConfig { module := horner3Module, host := {} } 0
        horner3Module.initialStore
        [.f32 c₀, .f32 c₁, .f32 c₂, .f32 c₃, .f32 x] =
      .ok (horner3Config x c₃ c₂ c₁ c₀) := by
  have himports : horner3Module.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    horner3_funcAt]
  simp [Function.numParams, Function.toLocals, horner3Config]
  constructor
  · constructor
    · have hparamsLength :
          (horner3Module.funcs[0]?.getD default).params.length = 5 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasHorner3Body_eq
      native_decide
    · constructor <;> native_decide

theorem horner3_steps (x c₃ c₂ c₁ c₀ : UInt32) :
    Steps (horner3Config x c₃ c₂ c₁ c₀)
      [(.instruction (.localGet 1)), (.instruction (.localGet 0)),
       (.instruction .f32Mul), (.instruction (.localGet 2)),
       (.instruction .f32Add), (.instruction (.localGet 0)),
       (.instruction .f32Mul), (.instruction (.localGet 3)),
       (.instruction .f32Add), (.instruction (.localGet 0)),
       (.instruction .f32Mul), (.instruction (.localGet 4)),
       (.instruction .f32Add), (.administrative .finish)]
      ⟨.done [.f32 (horner3Result x c₃ c₂ c₁ c₀)],
        (horner3Config x c₃ c₂ c₁ c₀).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [horner3Config, horner3Result, f32Mul, f32Add] using
    (Steps.refl
      (⟨.done [.f32 (horner3Result x c₃ c₂ c₁ c₀)],
        (horner3Config x c₃ c₂ c₁ c₀).store⟩ : Config Unit))

theorem horner3_terminates (x c₃ c₂ c₁ c₀ : UInt32) :
    TerminatesWith (horner3Config x c₃ c₂ c₁ c₀)
      (fun values _ =>
        values = [.f32 (horner3Result x c₃ c₂ c₁ c₀)]) :=
  TerminatesWith.of_steps (horner3_steps x c₃ c₂ c₁ c₀) rfl

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

def dot4Wat : String := "
(module
  (func (export \"dot4_f64\")
    (param f64 f64 f64 f64 f64 f64 f64 f64) (result f64)
    local.get 0
    local.get 1
    f64.mul
    local.get 2
    local.get 3
    f64.mul
    f64.add
    local.get 4
    local.get 5
    f64.mul
    f64.add
    local.get 6
    local.get 7
    f64.mul
    f64.add))
"

def dot4Module : Module := Wasm.Examples.decodeOrDefault dot4Wat
def dot4Body : Program :=
  [.localGet 0, .localGet 1, .f64Mul,
   .localGet 2, .localGet 3, .f64Mul, .f64Add,
   .localGet 4, .localGet 5, .f64Mul, .f64Add,
   .localGet 6, .localGet 7, .f64Mul, .f64Add]

def hasDot4Body : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f64Mul,
      .localGet 2, .localGet 3, .f64Mul, .f64Add,
      .localGet 4, .localGet 5, .f64Mul, .f64Add,
      .localGet 6, .localGet 7, .f64Mul, .f64Add] => true
  | _ => false

theorem hasDot4Body_eq : ∀ body : Program,
    hasDot4Body (some body) = true → body = dot4Body := by
  intro body h
  simp only [hasDot4Body] at h
  split at h
  · simp_all [dot4Body]
  · contradiction

theorem dot4_signature :
    dot4Module.funcs.length = 1 ∧
    dot4Module.funcs.head?.map (·.params) =
      some [.f64, .f64, .f64, .f64, .f64, .f64, .f64, .f64] ∧
    dot4Module.funcs.head?.map (·.results) = some [.f64] := by
  native_decide

theorem dot4_funcAt :
    dot4Module.funcs[0]? = some dot4Module.funcs[0]! := by
  have h : 0 < dot4Module.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def dot4Result (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64) : UInt64 :=
  IEEE64.add
    (IEEE64.add
      (IEEE64.add (IEEE64.mul a₀ b₀) (IEEE64.mul a₁ b₁))
      (IEEE64.mul a₂ b₂))
    (IEEE64.mul a₃ b₃)

def dot4Config (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64) : Config Unit :=
  { expr := .running
      { locals :=
          { params :=
              [.f64 a₀, .f64 b₀, .f64 a₁, .f64 b₁,
               .f64 a₂, .f64 b₂, .f64 a₃, .f64 b₃] }
        code := dot4Body
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := dot4Module, host := {} }]
            entry := ⟨0⟩ }
        wasm := dot4Module.initialStore } }

theorem dot4_initConfig (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64) :
    initConfig { module := dot4Module, host := {} } 0
        dot4Module.initialStore
        [.f64 b₃, .f64 a₃, .f64 b₂, .f64 a₂,
         .f64 b₁, .f64 a₁, .f64 b₀, .f64 a₀] =
      .ok (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) := by
  have himports : dot4Module.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    dot4_funcAt]
  simp [Function.numParams, Function.toLocals, dot4Config]
  constructor
  · constructor
    · have hparamsLength :
          (dot4Module.funcs[0]?.getD default).params.length = 8 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasDot4Body_eq
      native_decide
    · constructor <;> native_decide

theorem dot4_steps (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64) :
    Steps (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f64Mul), (.instruction (.localGet 2)),
       (.instruction (.localGet 3)), (.instruction .f64Mul),
       (.instruction .f64Add), (.instruction (.localGet 4)),
       (.instruction (.localGet 5)), (.instruction .f64Mul),
       (.instruction .f64Add), (.instruction (.localGet 6)),
       (.instruction (.localGet 7)), (.instruction .f64Mul),
       (.instruction .f64Add), (.administrative .finish)]
      ⟨.done [.f64 (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)],
        (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [dot4Config, dot4Result, f64Mul, f64Add] using
    (Steps.refl
      (⟨.done [.f64 (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)],
        (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃).store⟩ : Config Unit))

theorem dot4_terminates (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64) :
    TerminatesWith (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)
      (fun values _ =>
        values = [.f64 (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)]) :=
  TerminatesWith.of_steps
    (dot4_steps a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) rfl

end FloatNumericalKernels
end Wasm
