import Interpreter.Wasm.IEEE32
import Interpreter.Wasm.IEEE64

/-! ## Floating-point values and operations

Wasm `f32`/`f64` values are modelled by their **IEEE-754 bit patterns**
(`UInt32` / `UInt64`), not by Lean's opaque `Float`. The bit pattern is the
faithful representation: it preserves NaN payloads and the sign of zero,
leaves `Value`'s derived `DecidableEq`/`BEq` intact, and matches the
bit-level style the integer instructions already use.

Binary32 arithmetic, square root, comparisons, selection, sign operations,
integral rounding, and integer conversions use the pure integer implementation
in `Interpreter.Wasm.IEEE32`.  Binary64 scalar arithmetic, square root,
comparisons, selection, sign operations, and integral rounding likewise use
`Interpreter.Wasm.IEEE64`.  The remaining f64 conversion operations retain
Lean's native `Float` implementation.  Numeric results funnel through the
`f32Canon` / `f64Canon` seam, whose bit-level classifiers map a NaN result to
the canonical quiet NaN.

`abs`, `neg` and `copysign` are bit operations exactly as the spec defines
them: they act on the sign bit alone and never canonicalize. -/

namespace Wasm

/-! ### Canonical NaN -/

/-- Canonical quiet `f32` NaN: sign 0, exponent all ones, top mantissa bit set. -/
def f32CanonicalNaN : UInt32 := 0x7FC00000
/-- Canonical quiet `f64` NaN. -/
def f64CanonicalNaN : UInt64 := 0x7FF8000000000000

/-- Normalise a numeric result: any NaN becomes the canonical NaN. -/
def f32Canon (b : UInt32) : UInt32 :=
  if IEEE32.isNaN b then f32CanonicalNaN else b
def f64Canon (b : UInt64) : UInt64 :=
  if IEEE64.isNaN b then f64CanonicalNaN else b

/-! ### Sign-bit operations

Defined directly on the bits, matching the spec; NaN payloads survive. -/

def f32Abs (a : UInt32) : UInt32 := IEEE32.abs a
def f64Abs (a : UInt64) : UInt64 := IEEE64.abs a
def f32Neg (a : UInt32) : UInt32 := IEEE32.negate a
def f64Neg (a : UInt64) : UInt64 := IEEE64.negate a
def f32Copysign (a b : UInt32) : UInt32 := IEEE32.copySign a b
def f64Copysign (a b : UInt64) : UInt64 :=
  IEEE64.copySign a b

/-! ### Arithmetic -/

def f32Add (a b : UInt32) : UInt32 := IEEE32.add a b
def f32Sub (a b : UInt32) : UInt32 := IEEE32.sub a b
def f32Mul (a b : UInt32) : UInt32 := IEEE32.mul a b
def f32Div (a b : UInt32) : UInt32 := IEEE32.div a b
def f64Add (a b : UInt64) : UInt64 := IEEE64.add a b
def f64Sub (a b : UInt64) : UInt64 := IEEE64.sub a b
def f64Mul (a b : UInt64) : UInt64 := IEEE64.mul a b
def f64Div (a b : UInt64) : UInt64 := IEEE64.div a b

def f32Sqrt  (a : UInt32) : UInt32 := IEEE32.sqrt a
def f64Sqrt  (a : UInt64) : UInt64 := IEEE64.sqrt a
def f32Ceil  (a : UInt32) : UInt32 := IEEE32.ceil a
def f64Ceil  (a : UInt64) : UInt64 := IEEE64.ceil a
def f32Floor (a : UInt32) : UInt32 := IEEE32.floor a
def f64Floor (a : UInt64) : UInt64 := IEEE64.floor a

/-- Round toward zero: ceiling for negatives, floor otherwise. -/
def f32Trunc (a : UInt32) : UInt32 :=
  IEEE32.trunc a
def f64Trunc (a : UInt64) : UInt64 :=
  IEEE64.trunc a

/-- Round to nearest integer, ties to even. -/
def f32Nearest (a : UInt32) : UInt32 :=
  IEEE32.nearest a
def f64Nearest (a : UInt64) : UInt64 :=
  IEEE64.nearest a

/-! ### min / max

NaN in either operand yields the canonical NaN. When both operands are zero
the sign is resolved per spec: `min` keeps a negative zero, `max` a positive
zero (`|||` / `&&&` on the sign bits). -/

def f32Min (a b : UInt32) : UInt32 :=
  IEEE32.min a b
def f32Max (a b : UInt32) : UInt32 :=
  IEEE32.max a b
def f64Min (a b : UInt64) : UInt64 :=
  IEEE64.min a b
def f64Max (a b : UInt64) : UInt64 :=
  IEEE64.max a b

/-! ### Comparisons

IEEE-754 ordered comparisons (any comparison with NaN is `false`, except
`ne`; `+0` equals `-0`). The `f32` operands are promoted to `f64` first,
which is exact and preserves ordering, equality and NaN-ness. Each yields a
`Bool`; the interpreter lands it as an `i32` `0`/`1`. -/

def f32Eq (a b : UInt32) : Bool := IEEE32.eq a b
def f32Ne (a b : UInt32) : Bool := !(IEEE32.eq a b)
def f32Lt (a b : UInt32) : Bool := IEEE32.lt a b
def f32Gt (a b : UInt32) : Bool := IEEE32.lt b a
def f32Le (a b : UInt32) : Bool := IEEE32.le a b
def f32Ge (a b : UInt32) : Bool := IEEE32.le b a
def f64Eq (a b : UInt64) : Bool := IEEE64.eq a b
def f64Ne (a b : UInt64) : Bool := !(IEEE64.eq a b)
def f64Lt (a b : UInt64) : Bool := IEEE64.lt a b
def f64Gt (a b : UInt64) : Bool := IEEE64.lt b a
def f64Le (a b : UInt64) : Bool := IEEE64.le a b
def f64Ge (a b : UInt64) : Bool := IEEE64.le b a

/-! ### Integer → float conversions

`_s` reads the operand as signed, `_u` as unsigned. These never produce a
NaN, but may round to the nearest representable value. -/

def f32ConvertI32S (a : UInt32) : UInt32 := IEEE32.convertI32S a
def f32ConvertI32U (a : UInt32) : UInt32 := IEEE32.convertI32U a
def f32ConvertI64S (a : UInt64) : UInt32 := IEEE32.convertI64S a
def f32ConvertI64U (a : UInt64) : UInt32 := IEEE32.convertI64U a
def f64ConvertI32S (a : UInt32) : UInt64 := IEEE64.convertI32S a
def f64ConvertI32U (a : UInt32) : UInt64 := IEEE64.convertI32U a
def f64ConvertI64S (a : UInt64) : UInt64 := IEEE64.convertI64S a
def f64ConvertI64U (a : UInt64) : UInt64 := IEEE64.convertI64U a

/-! ### float ↔ float -/

def f64PromoteF32 (a : UInt32) : UInt64 := f64Canon (Float32.ofBits a).toFloat.toBits
def f32DemoteF64  (a : UInt64) : UInt32 := f32Canon (Float.ofBits a).toFloat32.toBits

/-! ### float → integer (trapping)

`none` reports a wasm trap: NaN, infinity, or a value whose truncation falls
outside the target's range.  Both formats use their proof-visible exact scaled
integer representations.  The unsigned-`i64` and signed-`i64` upper bounds
(`2^64`, `2^63`) are exclusive. -/

def i32TruncF32S (a : UInt32) : Option UInt32 := IEEE32.truncI32S a
def i32TruncF32U (a : UInt32) : Option UInt32 := IEEE32.truncI32U a
def i32TruncF64S (a : UInt64) : Option UInt32 := IEEE64.truncI32S a
def i32TruncF64U (a : UInt64) : Option UInt32 := IEEE64.truncI32U a
def i64TruncF32S (a : UInt32) : Option UInt64 := IEEE32.truncI64S a
def i64TruncF32U (a : UInt32) : Option UInt64 := IEEE32.truncI64U a
def i64TruncF64S (a : UInt64) : Option UInt64 := IEEE64.truncI64S a
def i64TruncF64U (a : UInt64) : Option UInt64 := IEEE64.truncI64U a

/-! ### float → integer (saturating)

`trunc_sat` never traps: NaN maps to `0`, out-of-range values saturate to the
target's minimum or maximum. -/

def i32TruncSatF32S (a : UInt32) : UInt32 := IEEE32.truncSatI32S a
def i32TruncSatF32U (a : UInt32) : UInt32 := IEEE32.truncSatI32U a
def i32TruncSatF64S (a : UInt64) : UInt32 := IEEE64.truncSatI32S a
def i32TruncSatF64U (a : UInt64) : UInt32 := IEEE64.truncSatI32U a
def i64TruncSatF32S (a : UInt32) : UInt64 := IEEE32.truncSatI64S a
def i64TruncSatF32U (a : UInt32) : UInt64 := IEEE32.truncSatI64U a
def i64TruncSatF64S (a : UInt64) : UInt64 := IEEE64.truncSatI64S a
def i64TruncSatF64U (a : UInt64) : UInt64 := IEEE64.truncSatI64U a

end Wasm
