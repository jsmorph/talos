import Interpreter.Wasm.Examples.IEEE32

/-!
# Binary32 conversion differential checks

The proof-visible integer/float, trapping, and saturating conversions are
compared with the former native implementation.  These are regression tests,
not logical bridge axioms.
-/

namespace Wasm.Examples.IEEE32Conversions

private def nativeConvertI32S (a : UInt32) : UInt32 :=
  (Float32.ofInt a.toInt32.toInt).toBits

private def nativeConvertI32U (a : UInt32) : UInt32 :=
  (Float32.ofNat a.toNat).toBits

private def nativeConvertI64S (a : UInt64) : UInt32 :=
  (Float32.ofInt a.toInt64.toInt).toBits

private def nativeConvertI64U (a : UInt64) : UInt32 :=
  (Float32.ofNat a.toNat).toBits

private def truncReal (x : Float) : Option Float :=
  if x.isNaN then none else some (if x < 0.0 then x.ceil else x.floor)

private def nativeTruncI32S (a : UInt32) : Option UInt32 :=
  match truncReal (Float32.ofBits a).toFloat with
  | none => none
  | some t => if (-2147483648.0 : Float) ≤ t ∧ t ≤ (2147483647.0 : Float)
      then some t.toInt64.toUInt64.toUInt32 else none

private def nativeTruncI32U (a : UInt32) : Option UInt32 :=
  match truncReal (Float32.ofBits a).toFloat with
  | none => none
  | some t => if (0.0 : Float) ≤ t ∧ t ≤ (4294967295.0 : Float)
      then some t.toUInt64.toUInt32 else none

private def nativeTruncI64S (a : UInt32) : Option UInt64 :=
  match truncReal (Float32.ofBits a).toFloat with
  | none => none
  | some t => if (-9223372036854775808.0 : Float) ≤ t ∧
      t < (9223372036854775808.0 : Float)
      then some t.toInt64.toUInt64 else none

private def nativeTruncI64U (a : UInt32) : Option UInt64 :=
  match truncReal (Float32.ofBits a).toFloat with
  | none => none
  | some t => if (0.0 : Float) ≤ t ∧ t < (18446744073709551616.0 : Float)
      then some t.toUInt64 else none

private def nativeSatI32S (a : UInt32) : UInt32 :=
  let x := (Float32.ofBits a).toFloat
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (-2147483648.0 : Float) then 0x80000000
    else if t ≥ (2147483647.0 : Float) then 0x7FFFFFFF
    else t.toInt64.toUInt64.toUInt32

private def nativeSatI32U (a : UInt32) : UInt32 :=
  let x := (Float32.ofBits a).toFloat
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (0.0 : Float) then 0
    else if t ≥ (4294967295.0 : Float) then 0xFFFFFFFF
    else t.toUInt64.toUInt32

private def nativeSatI64S (a : UInt32) : UInt64 :=
  let x := (Float32.ofBits a).toFloat
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (-9223372036854775808.0 : Float) then 0x8000000000000000
    else if t ≥ (9223372036854775808.0 : Float) then 0x7FFFFFFFFFFFFFFF
    else t.toInt64.toUInt64

private def nativeSatI64U (a : UInt32) : UInt64 :=
  let x := (Float32.ofBits a).toFloat
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (0.0 : Float) then 0
    else if t ≥ (18446744073709551616.0 : Float) then 0xFFFFFFFFFFFFFFFF
    else t.toUInt64

def conversionCases : List (UInt32 × UInt64) :=
  IEEE32.differentialCases.map fun p =>
    (p.1, UInt64.ofNat (p.1.toNat * 2 ^ 32 + p.2.toNat))

theorem differential_conversions_agree_with_native :
    conversionCases.all (fun p =>
      Wasm.IEEE32.convertI32S p.1 == nativeConvertI32S p.1 &&
      Wasm.IEEE32.convertI32U p.1 == nativeConvertI32U p.1 &&
      Wasm.IEEE32.convertI64S p.2 == nativeConvertI64S p.2 &&
      Wasm.IEEE32.convertI64U p.2 == nativeConvertI64U p.2 &&
      Wasm.IEEE32.truncI32S p.1 == nativeTruncI32S p.1 &&
      Wasm.IEEE32.truncI32U p.1 == nativeTruncI32U p.1 &&
      Wasm.IEEE32.truncI64S p.1 == nativeTruncI64S p.1 &&
      Wasm.IEEE32.truncI64U p.1 == nativeTruncI64U p.1 &&
      Wasm.IEEE32.truncSatI32S p.1 == nativeSatI32S p.1 &&
      Wasm.IEEE32.truncSatI32U p.1 == nativeSatI32U p.1 &&
      Wasm.IEEE32.truncSatI64S p.1 == nativeSatI64S p.1 &&
      Wasm.IEEE32.truncSatI64U p.1 == nativeSatI64U p.1) = true := by
  native_decide

theorem conversion_boundaries :
    Wasm.IEEE32.truncI32S 0x4F000000 = none ∧
    Wasm.IEEE32.truncI32S 0xCF000000 = some 0x80000000 ∧
    Wasm.IEEE32.truncSatI32S 0x7FC00000 = 0 ∧
    Wasm.IEEE32.truncSatI32S 0x7F800000 = 0x7FFFFFFF ∧
    Wasm.IEEE32.truncSatI32S 0xFF800000 = 0x80000000 := by
  native_decide

end Wasm.Examples.IEEE32Conversions