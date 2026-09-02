import Interpreter.Wasm.Examples.Harness

/-!
# Binary64 addition and subtraction examples

Each decoded hand-written WAT function has an explicit symbolic trace and a
fuel-independent termination theorem over the pure modeled IEEE64 semantics.
-/

namespace Wasm
open SmallStep

namespace Float64Addition

def addWat : String := "
(module
  (func (export \"add64\")
    (param f64 f64) (result f64)
    local.get 0
    local.get 1
    f64.add))
"

def addModule : Module := Wasm.Examples.decodeOrDefault addWat
def addBody : Program := [.localGet 0, .localGet 1, .f64Add]

def hasAddBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f64Add] => true
  | _ => false

theorem hasAddBody_eq :
    ∀ body : Program, hasAddBody (some body) = true → body = addBody := by
  intro body h
  simp only [hasAddBody] at h
  split at h
  · simp_all [addBody]
  · contradiction

theorem add_funcAt : addModule.funcs[0]? = some addModule.funcs[0]! := by
  have h : 0 < addModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def addConfig (a b : UInt64) : Config Unit :=
  { expr := .running
      { locals := { params := [.f64 a, .f64 b] }
        code := addBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := addModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := addModule.initialStore } }

theorem add_initConfig (a b : UInt64) :
    initConfig { module := addModule, host := {} } 0
        addModule.initialStore [.f64 b, .f64 a] = .ok (addConfig a b) := by
  have himports : addModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    add_funcAt]
  simp [Function.numParams, Function.toLocals, addConfig]
  constructor
  · constructor
    · have hparamsLength :
          (addModule.funcs[0]?.getD default).params.length = 2 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasAddBody_eq
      native_decide
    · constructor <;> native_decide

theorem add_steps (a b : UInt64) :
    Steps (addConfig a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f64Add), (.administrative .finish)]
      ⟨.done [.f64 (IEEE64.add a b)], (addConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [addConfig, f64Add] using
    (Steps.refl
      (⟨.done [.f64 (IEEE64.add a b)], (addConfig a b).store⟩ : Config Unit))

theorem add_terminates (a b : UInt64) :
    TerminatesWith (addConfig a b)
      (fun values _ => values = [.f64 (IEEE64.add a b)]) :=
  TerminatesWith.of_steps (add_steps a b) rfl

end Float64Addition

namespace Float64Subtraction

def subWat : String := "
(module
  (func (export \"sub64\")
    (param f64 f64) (result f64)
    local.get 0
    local.get 1
    f64.sub))
"

def subModule : Module := Wasm.Examples.decodeOrDefault subWat
def subBody : Program := [.localGet 0, .localGet 1, .f64Sub]

def hasSubBody : Option Program → Bool
  | some [.localGet 0, .localGet 1, .f64Sub] => true
  | _ => false

theorem hasSubBody_eq :
    ∀ body : Program, hasSubBody (some body) = true → body = subBody := by
  intro body h
  simp only [hasSubBody] at h
  split at h
  · simp_all [subBody]
  · contradiction

theorem sub_funcAt : subModule.funcs[0]? = some subModule.funcs[0]! := by
  have h : 0 < subModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

def subConfig (a b : UInt64) : Config Unit :=
  { expr := .running
      { locals := { params := [.f64 a, .f64 b] }
        code := subBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := subModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := subModule.initialStore } }

theorem sub_initConfig (a b : UInt64) :
    initConfig { module := subModule, host := {} } 0
        subModule.initialStore [.f64 b, .f64 a] = .ok (subConfig a b) := by
  have himports : subModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    sub_funcAt]
  simp [Function.numParams, Function.toLocals, subConfig]
  constructor
  · constructor
    · have hparamsLength :
          (subModule.funcs[0]?.getD default).params.length = 2 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasSubBody_eq
      native_decide
    · constructor <;> native_decide

theorem sub_steps (a b : UInt64) :
    Steps (subConfig a b)
      [(.instruction (.localGet 0)), (.instruction (.localGet 1)),
       (.instruction .f64Sub), (.administrative .finish)]
      ⟨.done [.f64 (IEEE64.sub a b)], (subConfig a b).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons .finish
  simpa [subConfig, f64Sub] using
    (Steps.refl
      (⟨.done [.f64 (IEEE64.sub a b)], (subConfig a b).store⟩ : Config Unit))

theorem sub_terminates (a b : UInt64) :
    TerminatesWith (subConfig a b)
      (fun values _ => values = [.f64 (IEEE64.sub a b)]) :=
  TerminatesWith.of_steps (sub_steps a b) rfl

end Float64Subtraction
end Wasm
