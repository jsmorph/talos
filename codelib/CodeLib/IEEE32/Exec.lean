import Interpreter.Wasm
import Std.Tactic.BVDecide

open Wasm

/-!
Pure bitvector IEEE 754 f32 helpers and compatibility bridges for
`float_trunc` proofs.

**These bridge axioms are trusted, not proved.** The five `axiom` declarations
below (`beq_ax`, `isNaN_ax`, `ble_ax`, `blt_ax`, `satI32S_eq`) now relate the
proof-visible integer IEEE32 implementation to the older bitvector helpers;
they are the only axioms in this repository beyond Lean's own. Anything that
imports this module and uses them — including everything proved further down
this file — is therefore *not* axiom-free. Check what a given result rests on
with `#print axioms <name>`.

For that reason the `CodeLib` umbrella does **not** import this module: import
`CodeLib.IEEE32.Exec` explicitly in the (few) files that need the bridge, so the
axioms stay out of the ambient environment of everything else.
-/

namespace IEEE32Exec

/-! ## Pure bitvector f32 helpers -/

-- NaN: exponent all 1s (0x7F800000 mask), mantissa nonzero
def isNaN (x : UInt32) : Bool :=
  (x &&& 0x7F800000 == 0x7F800000) && !(x &&& 0x007FFFFF == 0)

-- IEEE 754 ordered equality: both non-NaN, and same bits or both ±0
def beq (a b : UInt32) : Bool :=
  !isNaN a && !isNaN b &&
  (a == b || (a &&& 0x7FFFFFFF == 0 && b &&& 0x7FFFFFFF == 0))

-- IEEE 754 ordered less-than: false if NaN; positive floats order like unsigned ints
def blt (a b : UInt32) : Bool :=
  !isNaN a && !isNaN b &&
  !(a &&& 0x7FFFFFFF == 0 && b &&& 0x7FFFFFFF == 0) &&
  (if a &&& 0x80000000 == 0 && !(b &&& 0x80000000 == 0) then false  -- pos > neg
   else if !(a &&& 0x80000000 == 0) && b &&& 0x80000000 == 0 then true   -- neg < pos
   else if a &&& 0x80000000 == 0 then a < b   -- both non-neg: unsigned cmp
   else a > b)                                  -- both neg: reversed

-- IEEE 754 ordered ≤
def ble (a b : UInt32) : Bool := blt a b || beq a b

-- Saturating f32 → i32 truncation toward zero, purely in bitvectors.
-- Mirrors `satI32S` from Float.lean without touching Float.
def satI32S (x : UInt32) : UInt32 :=
  if isNaN x then 0
  else
    let s := x >>> 31
    let e := (x >>> 23) &&& 0xFF
    let m := x &&& 0x007FFFFF
    if e == 0xFF then
      -- ±infinity
      if s == 0 then 0x7FFFFFFF else 0x80000000
    else if e < 127 then
      -- |value| < 1; truncation toward zero = 0
      0
    else if e ≥ 158 then
      -- |value| ≥ 2^31; saturate
      if s == 0 then 0x7FFFFFFF else 0x80000000
    else
      -- 127 ≤ e ≤ 157: |value| in [1, 2^31); result fits in i32
      -- magnitude = (1.mantissa) >> (150 - e)  [or << (e - 150) when e > 150]
      let full := 0x800000 ||| m
      let mag : UInt32 :=
        if e ≤ 150 then full >>> (150 - e)
        else full <<< (e - 150)
      if s == 0 then mag else 0 - mag

/-! ## Compatibility axioms: proof-visible model matches legacy bitvector helpers -/

-- Ordered equality agrees with the legacy bitvector equality.
axiom beq_ax (a b : UInt32) :
    Wasm.IEEE32.eq a b = beq a b

-- Classification agrees with the legacy bitvector classifier.
axiom isNaN_ax (a : UInt32) :
    Wasm.IEEE32.isNaN a = isNaN a

-- Ordered less-than-or-equal agrees with the legacy helper.
axiom ble_ax (a b : UInt32) :
    Wasm.IEEE32.le a b = ble a b

-- Ordered less-than agrees with the legacy helper.
axiom blt_ax (a b : UInt32) :
    Wasm.IEEE32.lt a b = blt a b

-- i32TruncSatF32S agrees with ieee32 satI32S
axiom satI32S_eq (a : UInt32) :
    i32TruncSatF32S a = satI32S a

/-! ## Theorems used by `FloatTrunc.Spec` -/

theorem f32Ne_self_iff_isNaN (x : UInt32) :
    f32Ne x x = Wasm.IEEE32.isNaN x := by
  simp only [f32Ne, beq_ax, isNaN_ax, isNaN, beq]
  bv_decide

set_option maxHeartbeats 1600000 in
theorem i32TruncSatF32S_large_pos {x : UInt32}
    (hnan : f32Ne x x = false)
    (hge : f32Ge x 1325400064 = true) :
    i32TruncSatF32S x = 0x7FFFFFFF := by
  simp only [f32Ne, f32Ge, beq_ax, ble_ax, satI32S_eq,
             isNaN, beq, blt, ble, satI32S] at *
  bv_decide

set_option maxHeartbeats 1600000 in
theorem i32TruncSatF32S_large_neg {x : UInt32}
    (hnan : f32Ne x x = false)
    (hlt : f32Lt x 3472883712 = true) :
    i32TruncSatF32S x = 0x80000000 := by
  simp only [f32Ne, f32Lt, beq_ax, blt_ax, satI32S_eq,
             isNaN, beq, blt, satI32S] at *
  bv_decide

end IEEE32Exec
