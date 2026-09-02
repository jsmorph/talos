import Interpreter.Wasm.Float

/-!
# Pure binary64 differential checks

All proof-visible scalar binary64 arithmetic, selection, comparison, and
integral-rounding operations are compared with the native `Float` oracle.
-/

namespace Wasm.Examples.IEEE64

private def nativeCanon (b : UInt64) : UInt64 :=
  if (Float.ofBits b).isNaN then 0x7FF8000000000000 else b

private def nativeMin (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let y := Float.ofBits b
  if x.isNaN || y.isNaN then 0x7FF8000000000000
  else if x == 0.0 && y == 0.0 then a ||| b
  else if x < y then a else b

private def nativeMax (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let y := Float.ofBits b
  if x.isNaN || y.isNaN then 0x7FF8000000000000
  else if x == 0.0 && y == 0.0 then a &&& b
  else if x < y then b else a

private def nativeNearest (a : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let fl := x.floor
  let cl := x.ceil
  let dlo := x - fl
  let dhi := cl - x
  let r := if dlo < dhi then fl
    else if dhi < dlo then cl
    else if (fl * 0.5).floor * 2.0 == fl then fl else cl
  nativeCanon r.toBits

private def nativeConvertI32S (a : UInt32) : UInt64 :=
  (Float.ofInt a.toInt32.toInt).toBits

private def nativeConvertI32U (a : UInt32) : UInt64 :=
  (Float.ofNat a.toNat).toBits

private def nativeConvertI64S (a : UInt64) : UInt64 :=
  (Float.ofInt a.toInt64.toInt).toBits

private def nativeConvertI64U (a : UInt64) : UInt64 :=
  (Float.ofNat a.toNat).toBits

private def truncReal (x : Float) : Option Float :=
  if x.isNaN then none else some (if x < 0.0 then x.ceil else x.floor)

private def nativeTruncI32S (a : UInt64) : Option UInt32 :=
  match truncReal (Float.ofBits a) with
  | none => none
  | some t => if (-2147483648.0 : Float) ≤ t ∧ t ≤ (2147483647.0 : Float)
      then some t.toInt64.toUInt64.toUInt32 else none

private def nativeTruncI32U (a : UInt64) : Option UInt32 :=
  match truncReal (Float.ofBits a) with
  | none => none
  | some t => if (0.0 : Float) ≤ t ∧ t ≤ (4294967295.0 : Float)
      then some t.toUInt64.toUInt32 else none

private def nativeTruncI64S (a : UInt64) : Option UInt64 :=
  match truncReal (Float.ofBits a) with
  | none => none
  | some t => if (-9223372036854775808.0 : Float) ≤ t ∧
      t < (9223372036854775808.0 : Float)
      then some t.toInt64.toUInt64 else none

private def nativeTruncI64U (a : UInt64) : Option UInt64 :=
  match truncReal (Float.ofBits a) with
  | none => none
  | some t => if (0.0 : Float) ≤ t ∧
      t < (18446744073709551616.0 : Float)
      then some t.toUInt64 else none

private def nativeSatI32S (a : UInt64) : UInt32 :=
  let x := Float.ofBits a
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (-2147483648.0 : Float) then 0x80000000
    else if t ≥ (2147483647.0 : Float) then 0x7FFFFFFF
    else t.toInt64.toUInt64.toUInt32

private def nativeSatI32U (a : UInt64) : UInt32 :=
  let x := Float.ofBits a
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (0.0 : Float) then 0
    else if t ≥ (4294967295.0 : Float) then 0xFFFFFFFF
    else t.toUInt64.toUInt32

private def nativeSatI64S (a : UInt64) : UInt64 :=
  let x := Float.ofBits a
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (-9223372036854775808.0 : Float) then 0x8000000000000000
    else if t ≥ (9223372036854775808.0 : Float) then 0x7FFFFFFFFFFFFFFF
    else t.toInt64.toUInt64

private def nativeSatI64U (a : UInt64) : UInt64 :=
  let x := Float.ofBits a
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
    if t ≤ (0.0 : Float) then 0
    else if t ≥ (18446744073709551616.0 : Float) then 0xFFFFFFFFFFFFFFFF
    else t.toUInt64

def differentialCases : List (UInt64 × UInt64) :=
  (List.range 1024).map fun n =>
    (UInt64.ofNat (6364136223846793005 * n + 1442695040888963407),
     UInt64.ofNat (2862933555777941757 * n + 3037000493))

def edgeCases : List (UInt64 × UInt64) :=
  [(0, 0), (0x8000000000000000, 0),
   (0, 0x7FF0000000000000),
   (1, 0x3FE0000000000000),
   (0x0010000000000000, 0x3FE0000000000000),
   (0x7FEFFFFFFFFFFFFF, 0x4000000000000000),
   (0x7FF8000000000000, 0x3FF0000000000000)]

theorem differential_scalar_operations_agree_with_native :
    (edgeCases ++ differentialCases).all (fun p =>
      IEEE64.add p.1 p.2 == nativeCanon (Float.ofBits p.1 + Float.ofBits p.2).toBits &&
      IEEE64.sub p.1 p.2 == nativeCanon (Float.ofBits p.1 - Float.ofBits p.2).toBits &&
      IEEE64.mul p.1 p.2 == nativeCanon (Float.ofBits p.1 * Float.ofBits p.2).toBits &&
      IEEE64.div p.1 p.2 == nativeCanon (Float.ofBits p.1 / Float.ofBits p.2).toBits &&
      IEEE64.sqrt p.1 == nativeCanon (Float.ofBits p.1).sqrt.toBits &&
      IEEE64.min p.1 p.2 == nativeMin p.1 p.2 &&
      IEEE64.max p.1 p.2 == nativeMax p.1 p.2 &&
      IEEE64.eq p.1 p.2 == (Float.ofBits p.1 == Float.ofBits p.2) &&
      IEEE64.lt p.1 p.2 == decide (Float.ofBits p.1 < Float.ofBits p.2) &&
      IEEE64.le p.1 p.2 == decide (Float.ofBits p.1 ≤ Float.ofBits p.2) &&
      IEEE64.ceil p.1 == nativeCanon (Float.ofBits p.1).ceil.toBits &&
      IEEE64.floor p.1 == nativeCanon (Float.ofBits p.1).floor.toBits &&
      IEEE64.trunc p.1 == nativeCanon (if Float.ofBits p.1 < 0.0 then
        (Float.ofBits p.1).ceil else (Float.ofBits p.1).floor).toBits &&
      IEEE64.nearest p.1 == nativeNearest p.1) = true := by
  native_decide

/-- Full-width deterministic samples compare every proof-visible binary64
integer conversion with the former native implementation. -/
theorem differential_conversions_agree_with_native :
    (edgeCases ++ differentialCases).all (fun p =>
      let i32 := p.1.toUInt32
      IEEE64.convertI32S i32 == nativeConvertI32S i32 &&
      IEEE64.convertI32U i32 == nativeConvertI32U i32 &&
      IEEE64.convertI64S p.2 == nativeConvertI64S p.2 &&
      IEEE64.convertI64U p.2 == nativeConvertI64U p.2 &&
      IEEE64.truncI32S p.1 == nativeTruncI32S p.1 &&
      IEEE64.truncI32U p.1 == nativeTruncI32U p.1 &&
      IEEE64.truncI64S p.1 == nativeTruncI64S p.1 &&
      IEEE64.truncI64U p.1 == nativeTruncI64U p.1 &&
      IEEE64.truncSatI32S p.1 == nativeSatI32S p.1 &&
      IEEE64.truncSatI32U p.1 == nativeSatI32U p.1 &&
      IEEE64.truncSatI64S p.1 == nativeSatI64S p.1 &&
      IEEE64.truncSatI64U p.1 == nativeSatI64U p.1) = true := by
  native_decide

theorem binary64_boundaries :
    IEEE64.mul 0x0010000000000000 0x3FE0000000000000 =
      0x0008000000000000 ∧
    IEEE64.mul 0x0000000000000001 0x3FE0000000000000 = 0 ∧
    IEEE64.div 0x3FF0000000000000 0 = 0x7FF0000000000000 ∧
    IEEE64.sqrt 0x4010000000000000 = 0x4000000000000000 := by
  native_decide

theorem binary64_conversion_boundaries :
    IEEE64.convertI64U 0x0020000000000001 = 0x4340000000000000 ∧
    IEEE64.truncI32S 0x41E0000000000000 = none ∧
    IEEE64.truncI32S 0xC1E0000000000000 = some 0x80000000 ∧
    IEEE64.truncSatI64U IEEE64.canonicalNaN = 0 ∧
    IEEE64.truncSatI64U (IEEE64.infinity false) = 0xFFFFFFFFFFFFFFFF := by
  native_decide

end Wasm.Examples.IEEE64
