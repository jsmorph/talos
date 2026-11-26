module

public import Interpreter.Wasm.Examples.IsEven
public import Interpreter.Wasm.Examples.SimpleLoop
public import Interpreter.Wasm.Examples.Factorial
public import Interpreter.Wasm.Examples.InfiniteLoop
public import Interpreter.Wasm.Examples.EvenOddRec
public import Interpreter.Wasm.Examples.CallIndirect
public import Interpreter.Wasm.Examples.SumI64
public import Interpreter.Wasm.Examples.IfAbs
public import Interpreter.Wasm.Examples.Switch
public import Interpreter.Wasm.Examples.SelectMin
public import Interpreter.Wasm.Examples.RefIsNull
public import Interpreter.Wasm.Examples.TableDispatch
public import Interpreter.Wasm.Examples.EarlyReturn
public import Interpreter.Wasm.Examples.EarlyBr
public import Interpreter.Wasm.Examples.EarlyBrInvalid
public import Interpreter.Wasm.Examples.TrapDivZero
public import Interpreter.Wasm.Examples.TrapUnreachable
public import Interpreter.Wasm.Examples.MemDataSection
public import Interpreter.Wasm.Examples.MemReplace
public import Interpreter.Wasm.Examples.MemNarrowI32
public import Interpreter.Wasm.Examples.MemI64
public import Interpreter.Wasm.Examples.MemGrow
public import Interpreter.Wasm.Examples.MemFill
public import Interpreter.Wasm.Examples.MemCopy
public import Interpreter.Wasm.Examples.GlobalCounter
public import Interpreter.Wasm.Examples.MultiValue
public import Interpreter.Wasm.Examples.ClzPopcnt
public import Interpreter.Wasm.Examples.HostDispatch
public import Interpreter.Wasm.Examples.Counter
public import Interpreter.Wasm.Examples.Random
public import Interpreter.Wasm.Examples.UniversalHost
public import Interpreter.Wasm.Examples.DecoderImport
public import Interpreter.Wasm.Examples.DecoderImportedGlobal
public import Interpreter.Wasm.Examples.FloatOps
public import Interpreter.Wasm.Examples.IEEE32
public import Interpreter.Wasm.Examples.FloatAssociativity
public import Interpreter.Wasm.Examples.Gcd
public import Interpreter.Wasm.Examples.SelectAbs
public import Interpreter.Wasm.Examples.GlobalInitExpr
public import Interpreter.Wasm.Examples.SegmentOffsetExpr
public import Interpreter.Wasm.Examples.CallIndirectSubtype
public import Interpreter.Wasm.Examples.RefCastFuncType
public import Interpreter.Wasm.Examples.SmallStep
public import Interpreter.Wasm.Examples.Validation
public import Interpreter.Wasm.Examples.MeasureLoopDemo

@[expose] public section

/-! # Wasm.Examples.Basic

Umbrella import for the bundled worked examples. Every example file under
`Interpreter/Wasm/Examples/` must be imported here: this module is the only
thing the CI `Interpreter` build reaches, so an example missing from this list
is never compiled and its `native_decide` checks never run. -/
