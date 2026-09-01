import Interpreter.Wasm.Examples.Harness

/-!
# Binary32 associativity-gap example

This file decodes and executes a hand-written WAT function computing
`abs((a + (b + c)) - ((a + b) + c))`.  The executable checks distinguish an
exactly associative input from an input that exposes binary32 rounding.
-/

namespace Wasm
open SmallStep
namespace FloatAssociativity

/-- A hand-written WebAssembly function measuring the binary32 associativity
gap for three inputs. -/
def assocGapWat : String := "
(module
  (func (export \"assoc_gap\")
    (param f32 f32 f32) (result f32)
    local.get 0
    local.get 1
    local.get 2
    f32.add
    f32.add
    local.get 0
    local.get 1
    f32.add
    local.get 2
    f32.add
    f32.sub
    f32.abs))
"

/-- The decoded module used by both execution checks and proofs. -/
def assocGapModule : Module := Wasm.Examples.decodeOrDefault assocGapWat

/-- The instruction sequence expected from the WAT decoder. -/
def assocGapBody : Program :=
  [ .localGet 0
  , .localGet 1
  , .localGet 2
  , .f32Add
  , .f32Add
  , .localGet 0
  , .localGet 1
  , .f32Add
  , .localGet 2
  , .f32Add
  , .f32Sub
  , .f32Abs ]

theorem assocGap_signature :
    assocGapModule.funcs.length = 1 ∧
    assocGapModule.funcs.head?.map (·.params) =
      some [.f32, .f32, .f32] ∧
    assocGapModule.funcs.head?.map (·.results) = some [.f32] := by
  native_decide

theorem assocGap_export :
    assocGapModule.exports = [{ name := "assoc_gap", funcIdx := 0 }] := by
  native_decide

/-- Decidable projection used to check the decoded instruction sequence without
requiring an equality instance for every WebAssembly instruction. -/
def hasAssocGapBody : Option Program → Bool
  | some
      [ .localGet 0
      , .localGet 1
      , .localGet 2
      , .f32Add
      , .f32Add
      , .localGet 0
      , .localGet 1
      , .f32Add
      , .localGet 2
      , .f32Add
      , .f32Sub
      , .f32Abs ] => true
  | _ => false

theorem assocGap_body :
    hasAssocGapBody (assocGapModule.funcs.head?.map (·.body)) = true := by
  native_decide

/-- A successful body-shape check determines the complete instruction list. -/
theorem hasAssocGapBody_eq :
    ∀ body : Program,
      hasAssocGapBody (some body) = true → body = assocGapBody := by
  intro body h
  simp only [hasAssocGapBody] at h
  split at h
  · simp_all [assocGapBody]
  · contradiction

/-- Logical form of the decoder-body check, used to connect the explicit trace
below to the decoded WAT module. -/
theorem assocGap_body_eq :
    assocGapModule.funcs[0]!.body = assocGapBody := by
  apply hasAssocGapBody_eq
  native_decide

theorem assocGap_funcAt :
    assocGapModule.funcs[0]? = some assocGapModule.funcs[0]! := by
  have h : 0 < assocGapModule.funcs.length := by native_decide
  rw [List.getElem?_eq_getElem h]
  congr 1
  simp [getElem!_pos, h]

theorem assocGap_params :
    assocGapModule.funcs[0]!.params = [.f32, .f32, .f32] := by
  native_decide

theorem assocGap_locals : assocGapModule.funcs[0]!.locals = [] := by
  native_decide

theorem assocGap_results : assocGapModule.funcs[0]!.results = [.f32] := by
  native_decide

/-- Execute the decoded function with three raw binary32 bit patterns. -/
def runAssocGap (a b c : UInt32) : List Value :=
  Wasm.Examples.runValues 2 assocGapModule 0 assocGapModule.initialStore
    [.f32 a, .f32 b, .f32 c]

/-- `1/2`, `1/4`, and `1/8` are added exactly in either association. -/
theorem exact_input_returns_zero :
    runAssocGap 0x3f000000 0x3e800000 0x3e000000 = [.f32 0] := by
  native_decide

/-- For `a = 1` and `b = c = 2^-24`, ties-to-even loses each small addend in
the left-associated expression, while adding the small values first preserves
their sum.  The resulting gap is `2^-23`. -/
theorem rounded_input_returns_two_pow_neg_23 :
    runAssocGap 0x3f800000 0x33800000 0x33800000 = [.f32 0x34000000] := by
  native_decide

/-! ## Symbolic small-step execution -/

/-- The raw binary32 result computed by `assoc_gap`. -/
def assocGapResult (a b c : UInt32) : UInt32 :=
  f32Abs
    (f32Sub
      (f32Add a (f32Add b c))
      (f32Add (f32Add a b) c))

/-- Explicit initial configuration for a call whose local parameters are
`a`, `b`, and `c`. -/
def assocGapConfig (a b c : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.f32 a, .f32 b, .f32 c] }
        code := assocGapBody
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := assocGapModule, host := {} }]
            entry := ⟨0⟩ }
        wasm := assocGapModule.initialStore } }

/-- Initializing entry zero of the decoded module yields the explicit
configuration.  Entry arguments use the interpreter's operand-stack order. -/
theorem assocGap_initConfig (a b c : UInt32) :
    initConfig { module := assocGapModule, host := {} } 0
        assocGapModule.initialStore [.f32 c, .f32 b, .f32 a] =
      .ok (assocGapConfig a b c) := by
  have himports : assocGapModule.imports.length = 0 := by native_decide
  simp only [initConfig, himports, Nat.lt_irrefl, if_false, Nat.zero_sub,
    assocGap_funcAt]
  simp [Function.numParams, Function.toLocals, assocGapConfig]
  constructor
  · constructor
    · have hparamsLength :
          (assocGapModule.funcs[0]?.getD default).params.length = 3 := by
        native_decide
      simp [hparamsLength]
    · native_decide
  · constructor
    · apply hasAssocGapBody_eq
      native_decide
    · constructor <;> native_decide

/-- Relational execution of the decoded instruction sequence for arbitrary
binary32 inputs. -/
theorem assocGap_steps (a b c : UInt32) :
    Steps (assocGapConfig a b c)
      [ (.instruction (.localGet 0))
      , (.instruction (.localGet 1))
      , (.instruction (.localGet 2))
      , (.instruction .f32Add)
      , (.instruction .f32Add)
      , (.instruction (.localGet 0))
      , (.instruction (.localGet 1))
      , (.instruction .f32Add)
      , (.instruction (.localGet 2))
      , (.instruction .f32Add)
      , (.instruction .f32Sub)
      , (.instruction .f32Abs)
      , (.administrative .finish) ]
      ⟨.done [.f32 (assocGapResult a b c)], (assocGapConfig a b c).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat1 rfl rfl)
  apply Steps.cons .finish
  simpa [assocGapConfig, assocGapResult] using
    (Steps.refl
      (⟨.done [.f32 (assocGapResult a b c)],
        (assocGapConfig a b c).store⟩ : Config Unit))

/-- Fuel-independent total correctness for the symbolic result. -/
theorem assocGap_terminates (a b c : UInt32) :
    TerminatesWith (assocGapConfig a b c)
      (fun values _ => values = [.f32 (assocGapResult a b c)]) :=
  TerminatesWith.of_steps (assocGap_steps a b c) rfl

theorem assocGap_partiallyMeets (a b c : UInt32) :
    PartiallyMeets (assocGapConfig a b c)
      (fun values _ => values = [.f32 (assocGapResult a b c)]) :=
  (assocGap_terminates a b c).toPartiallyMeets

end FloatAssociativity
end Wasm
