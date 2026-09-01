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

end FloatAssociativity
end Wasm
