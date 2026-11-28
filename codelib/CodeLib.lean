module

public import CodeLib.Attrs
public import CodeLib.Basic
public import CodeLib.Entry
public import CodeLib.Equivalence
public import CodeLib.UInt32
public import CodeLib.UInt64
public import CodeLib.WordCodec
public import CodeLib.RustStd.Frame
public import CodeLib.RustStd.Region
public import CodeLib.RustStd.MemArray
public import CodeLib.RustStd.MemFillLoop
public import CodeLib.RustStd.MemCopyLoop
public import CodeLib.RustStd.UInt
public import CodeLib.RustStd.Option
public import CodeLib.RustStd.U64.Basic
public import CodeLib.RustStd.U64.AbsDiff
public import CodeLib.RustStd.U64.Add
public import CodeLib.RustStd.U64.Sub
public import CodeLib.RustStd.U64.Mul
public import CodeLib.RustStd.U64.Div
public import CodeLib.RustStd.U64.Rem
public import CodeLib.RustStd.U64.BitAnd
public import CodeLib.RustStd.U64.BitOr
public import CodeLib.RustStd.U64.BitXor
public import CodeLib.RustStd.U64.Not
public import CodeLib.RustStd.U64.Shl
public import CodeLib.RustStd.U64.Shr
public import CodeLib.RustStd.Array.Basic
public import CodeLib.RustStd.Array.Len
public import CodeLib.RustStd.Array.IsEmpty
public import CodeLib.RustStd.Array.SmallStep
public import CodeLib.Near.State
public import CodeLib.Near.Env
public import CodeLib.Near.Proof
public import CodeLib.SepLogic.WasmHeap
public import CodeLib.SepLogic.WasmRules
public import CodeLib.SepLogic.SmallStepLanguage
public import CodeLib.SepLogic.SmallStepState
public import CodeLib.SepLogic.SmallStepLifting
public import CodeLib.SepLogic.SmallStepTotalLifting
public import CodeLib.SepLogic.SmallStepOutcomeLanguage
public import CodeLib.SepLogic.SmallStepOutcomeExample
public import CodeLib.SepLogic.SmallStepAdequacy
public import CodeLib.SepLogic.SmallStepAdequacyExamples
public import CodeLib.SepLogic.SmallStepOutcomeAdequacy
public import CodeLib.Examples.MergeSort.TotalProof
public import CodeLib.Examples.Quicksort.TotalProof
public import CodeLib.Examples.SelectionSort.StdIOProof
public import CodeLib.Examples.MergeSort.Adequacy
public import CodeLib.SepLogic.HostCallExample
public import CodeLib.SepLogic.TwoModuleExample
public import CodeLib.SepLogic.CrossInstanceExample
public import CodeLib.SepLogic.CounterHostExample
public import CodeLib.SepLogic.ImportChainExample
public import CodeLib.SepLogic.SharedMemoryExample

@[expose] public section

/-!
# CodeLib — umbrella import for downstream code

Generated `Program.lean` files (emitted by `lake exe verifier check`) and
hand-written `Spec.lean` siblings should `import CodeLib`, never the
interpreter directly. Today this is mostly a thin re-export of Wasm;
domain-specific spec helpers will live here as they accrete.
-/
