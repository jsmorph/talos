import CodeLib.IEEE32.Roundoff

/-!
# IEEE-754 binary32 exceptional values

This file proves the NaN, infinity, and round-to-nearest overflow behavior of
the proof-visible WebAssembly binary32 operations.
-/

namespace CodeLib.IEEE32

open Wasm

/-! ## Classification -/

theorem canonicalNaN_exponent :
    Wasm.IEEE32.exponent Wasm.IEEE32.canonicalNaN = 0xFF := by
  norm_num [Wasm.IEEE32.canonicalNaN, Wasm.IEEE32.exponent,
    UInt32.toNat_ofNat]

theorem canonicalNaN_fraction :
    Wasm.IEEE32.fraction Wasm.IEEE32.canonicalNaN = 2 ^ 22 := by
  norm_num [Wasm.IEEE32.canonicalNaN, Wasm.IEEE32.fraction,
    UInt32.toNat_ofNat]

theorem canonicalNaN_isNaN :
    Wasm.IEEE32.isNaN Wasm.IEEE32.canonicalNaN = true := by
  simp [Wasm.IEEE32.isNaN, canonicalNaN_exponent, canonicalNaN_fraction]

theorem infinity_eq_encodeFinite (negative : Bool) :
    Wasm.IEEE32.infinity negative =
      Wasm.IEEE32.encodeFinite negative 0xFF 0 := by
  cases negative <;> decide

theorem infinity_exponent (negative : Bool) :
    Wasm.IEEE32.exponent (Wasm.IEEE32.infinity negative) = 0xFF := by
  rw [infinity_eq_encodeFinite]
  exact exponent_encodeFinite negative 0xFF 0 (by norm_num) (by norm_num)

theorem infinity_fraction (negative : Bool) :
    Wasm.IEEE32.fraction (Wasm.IEEE32.infinity negative) = 0 := by
  rw [infinity_eq_encodeFinite]
  exact fraction_encodeFinite negative 0xFF 0 (by norm_num) (by norm_num)

theorem infinity_sign (negative : Bool) :
    Wasm.IEEE32.sign (Wasm.IEEE32.infinity negative) = negative := by
  rw [infinity_eq_encodeFinite]
  exact sign_encodeFinite negative 0xFF 0 (by norm_num) (by norm_num)

theorem infinity_isInfinite (negative : Bool) :
    Wasm.IEEE32.isInfinite (Wasm.IEEE32.infinity negative) = true := by
  simp [Wasm.IEEE32.isInfinite, infinity_exponent, infinity_fraction]

theorem infinity_not_nan (negative : Bool) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.infinity negative) = false := by
  simp [Wasm.IEEE32.isNaN, infinity_exponent, infinity_fraction]

theorem infinity_not_finite (negative : Bool) :
    ¬Finite (Wasm.IEEE32.infinity negative) := by
  simp [Finite, Wasm.IEEE32.isFinite, infinity_exponent]

theorem negate_isNaN (x : UInt32) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.negate x) = Wasm.IEEE32.isNaN x := by
  have he := exponent_lt x
  have hf := fraction_lt x
  simp [Wasm.IEEE32.negate, Wasm.IEEE32.isNaN,
    exponent_encodeFinite (!Wasm.IEEE32.sign x)
      (Wasm.IEEE32.exponent x) (Wasm.IEEE32.fraction x) he hf,
    fraction_encodeFinite (!Wasm.IEEE32.sign x)
      (Wasm.IEEE32.exponent x) (Wasm.IEEE32.fraction x) he hf]

theorem abs_isNaN (x : UInt32) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.abs x) = Wasm.IEEE32.isNaN x := by
  have he := exponent_lt x
  have hf := fraction_lt x
  simp [Wasm.IEEE32.abs, Wasm.IEEE32.isNaN,
    exponent_encodeFinite false (Wasm.IEEE32.exponent x)
      (Wasm.IEEE32.fraction x) he hf,
    fraction_encodeFinite false (Wasm.IEEE32.exponent x)
      (Wasm.IEEE32.fraction x) he hf]

theorem negate_infinity (negative : Bool) :
    Wasm.IEEE32.negate (Wasm.IEEE32.infinity negative) =
      Wasm.IEEE32.infinity (!negative) := by
  rw [Wasm.IEEE32.negate, infinity_sign, infinity_exponent, infinity_fraction]
  rw [infinity_eq_encodeFinite]

/-! ## NaN propagation -/

theorem add_nan_left {a : UInt32} (b : UInt32)
    (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.add a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.add, ha]

theorem add_nan_right (a : UInt32) {b : UInt32}
    (hb : Wasm.IEEE32.isNaN b = true) :
    Wasm.IEEE32.add a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.add, hb]

theorem sub_nan_left {a : UInt32} (b : UInt32)
    (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.sub a b = Wasm.IEEE32.canonicalNaN := by
  exact add_nan_left (Wasm.IEEE32.negate b) ha

theorem sub_nan_right (a : UInt32) {b : UInt32}
    (hb : Wasm.IEEE32.isNaN b = true) :
    Wasm.IEEE32.sub a b = Wasm.IEEE32.canonicalNaN := by
  apply add_nan_right
  rw [negate_isNaN]
  exact hb

theorem abs_nan {x : UInt32} (hx : Wasm.IEEE32.isNaN x = true) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.abs x) = true := by
  rw [abs_isNaN, hx]

/-! ## Infinity arithmetic -/

theorem add_infinity_finite (negative : Bool) (x : UInt32)
    (hx : Finite x) :
    Wasm.IEEE32.add (Wasm.IEEE32.infinity negative) x =
      Wasm.IEEE32.infinity negative := by
  simp [Wasm.IEEE32.add, infinity_not_nan, infinity_isInfinite,
    not_nan_of_finite hx, not_infinite_of_finite hx]

theorem add_finite_infinity (x : UInt32) (negative : Bool)
    (hx : Finite x) :
    Wasm.IEEE32.add x (Wasm.IEEE32.infinity negative) =
      Wasm.IEEE32.infinity negative := by
  simp [Wasm.IEEE32.add, infinity_not_nan, infinity_isInfinite,
    not_nan_of_finite hx, not_infinite_of_finite hx]

theorem add_infinities_same_sign (negative : Bool) :
    Wasm.IEEE32.add (Wasm.IEEE32.infinity negative)
        (Wasm.IEEE32.infinity negative) =
      Wasm.IEEE32.infinity negative := by
  simp [Wasm.IEEE32.add, infinity_not_nan, infinity_isInfinite,
    infinity_sign]

theorem add_infinities_opposite_sign (negative : Bool) :
    Wasm.IEEE32.add (Wasm.IEEE32.infinity negative)
        (Wasm.IEEE32.infinity (!negative)) =
      Wasm.IEEE32.canonicalNaN := by
  cases negative <;>
    simp [Wasm.IEEE32.add, infinity_not_nan, infinity_isInfinite,
      infinity_sign]

theorem sub_infinities_same_sign (negative : Bool) :
    Wasm.IEEE32.sub (Wasm.IEEE32.infinity negative)
        (Wasm.IEEE32.infinity negative) =
      Wasm.IEEE32.canonicalNaN := by
  rw [Wasm.IEEE32.sub, negate_infinity]
  exact add_infinities_opposite_sign negative

theorem sub_infinities_opposite_sign (negative : Bool) :
    Wasm.IEEE32.sub (Wasm.IEEE32.infinity negative)
        (Wasm.IEEE32.infinity (!negative)) =
      Wasm.IEEE32.infinity negative := by
  rw [Wasm.IEEE32.sub, negate_infinity]
  simpa using add_infinities_same_sign negative

theorem sub_infinity_finite (negative : Bool) (x : UInt32)
    (hx : Finite x) :
    Wasm.IEEE32.sub (Wasm.IEEE32.infinity negative) x =
      Wasm.IEEE32.infinity negative := by
  rw [Wasm.IEEE32.sub]
  exact add_infinity_finite negative (Wasm.IEEE32.negate x)
    (negate_spec x hx).1

theorem sub_finite_infinity (x : UInt32) (negative : Bool)
    (hx : Finite x) :
    Wasm.IEEE32.sub x (Wasm.IEEE32.infinity negative) =
      Wasm.IEEE32.infinity (!negative) := by
  rw [Wasm.IEEE32.sub, negate_infinity]
  exact add_finite_infinity x (!negative) hx

end CodeLib.IEEE32
