import CodeLib.IEEE32.Roundoff

/-!
# IEEE-754 binary32 exceptional values

This file proves the NaN, infinity, and round-to-nearest overflow behavior of
the proof-visible WebAssembly binary32 operations.
-/

namespace CodeLib.IEEE32

open Wasm

set_option exponentiation.threshold 300

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

/-! ## Round-to-nearest overflow -/

/-- The exact midpoint threshold for rounding to binary32 infinity under
round-to-nearest, ties-to-even.  Dividing by `2^149` gives
`2^128 - 2^103`, immediately above the largest finite binary32 value. -/
def overflowThreshold : Nat := (2 ^ 25 - 1) * 2 ^ 252

theorem overflowThreshold_eq :
    overflowThreshold = 2 ^ 277 - 2 ^ 252 := by
  norm_num [overflowThreshold]

theorem roundShift_overflow_window {n : Nat}
    (hlower : overflowThreshold ≤ n) (hupper : n < 2 ^ 277) :
    Wasm.IEEE32.roundShift n 253 = 2 ^ 24 := by
  have hunit : 0 < 2 ^ 253 := by positivity
  have hbase : (2 ^ 24 - 1) * 2 ^ 253 ≤ overflowThreshold := by
    norm_num [overflowThreshold]
  have hquotLower : 2 ^ 24 - 1 ≤ n / 2 ^ 253 :=
    (Nat.le_div_iff_mul_le hunit).2 (hbase.trans hlower)
  have hquotUpper : n / 2 ^ 253 < 2 ^ 24 :=
    (Nat.div_lt_iff_lt_mul hunit).2 (by
      convert hupper using 1
      all_goals norm_num)
  have hquot : n / 2 ^ 253 = 2 ^ 24 - 1 := by omega
  have hdecomp :
      n % 2 ^ 253 + 2 ^ 253 * (n / 2 ^ 253) = n :=
    Nat.mod_add_div n (2 ^ 253)
  have hthresholdDecomp :
      overflowThreshold =
        (2 ^ 24 - 1) * 2 ^ 253 + 2 ^ 253 / 2 := by
    norm_num [overflowThreshold]
  have hremainder : 2 ^ 253 / 2 ≤ n % 2 ^ 253 := by omega
  by_cases htie : n % 2 ^ 253 = 2 ^ 253 / 2
  · norm_num at hquot htie
    simp [Wasm.IEEE32.roundShift, hquot, htie]
  · have habove : 2 ^ 253 / 2 < n % 2 ^ 253 := by omega
    norm_num at hquot habove
    simp [Wasm.IEEE32.roundShift, hquot, habove]
    omega

theorem roundScaledMagnitude_overflows_below_two_pow_277
    (negative : Bool) (n : Nat) (hlower : overflowThreshold ≤ n)
    (hupper : n < 2 ^ 277) :
    Wasm.IEEE32.roundScaledMagnitude negative n =
      Wasm.IEEE32.infinity negative := by
  have hn : n ≠ 0 := by
    have hpositive : 0 < overflowThreshold := by norm_num [overflowThreshold]
    omega
  have hthresholdLower : 2 ^ 276 ≤ overflowThreshold := by
    norm_num [overflowThreshold]
  have hlogLower : 276 ≤ Nat.log2 n :=
    (Nat.le_log2 hn).2 (hthresholdLower.trans hlower)
  have hlogUpper : Nat.log2 n < 277 := (Nat.log2_lt hn).2 hupper
  have hlog : Nat.log2 n = 276 := by omega
  have hround : Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
    rw [hlog]
    norm_num
    exact roundShift_overflow_window hlower hupper
  have hroundNum : Wasm.IEEE32.roundShift n 253 = 16777216 := by
    simpa [hlog] using hround
  have hsmall23 : ¬n < 8388608 := by
    have hpositive : 8388608 ≤ overflowThreshold := by
      norm_num [overflowThreshold]
    omega
  have hsmall24 : ¬n < 16777216 := by
    have hpositive : 16777216 ≤ overflowThreshold := by
      norm_num [overflowThreshold]
    omega
  simp [Wasm.IEEE32.roundScaledMagnitude, hsmall23, hsmall24, hlog,
    hroundNum]

theorem roundScaledMagnitude_overflows_above_two_pow_277
    (negative : Bool) (n : Nat) (hlower : 2 ^ 277 ≤ n) :
    Wasm.IEEE32.roundScaledMagnitude negative n =
      Wasm.IEEE32.infinity negative := by
  have hn : n ≠ 0 := by
    have hpositive : 0 < 2 ^ 277 := by positivity
    omega
  have hlogLower : 277 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hlower
  let shift := Nat.log2 n - 23
  let rounded := Wasm.IEEE32.roundShift n shift
  have hshift : 254 ≤ shift := by simp only [shift]; omega
  have hsmall23 : ¬n < 8388608 := by
    have : 8388608 ≤ 2 ^ 277 := by norm_num
    omega
  have hsmall24 : ¬n < 16777216 := by
    have : 16777216 ≤ 2 ^ 277 := by norm_num
    omega
  by_cases hcarry : rounded = 2 ^ 24
  · have hcarry' :
        Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
      simpa [rounded, shift] using hcarry
    simp [Wasm.IEEE32.roundScaledMagnitude, hsmall23, hsmall24, hcarry',
      show 255 ≤ (Nat.log2 n - 23) + 2 by omega]
  · have hcarry' :
        ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
      simpa [rounded, shift] using hcarry
    have hcarryNum :
        ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
      norm_num at hcarry' ⊢
      exact hcarry'
    simp [Wasm.IEEE32.roundScaledMagnitude, hsmall23, hsmall24, hcarryNum,
      show 255 ≤ (Nat.log2 n - 23) + 1 by omega]

/-- Every exact magnitude at or above the IEEE-754 midpoint threshold rounds
to the correctly signed infinity. -/
theorem roundScaledMagnitude_overflows (negative : Bool) (n : Nat)
    (h : overflowThreshold ≤ n) :
    Wasm.IEEE32.roundScaledMagnitude negative n =
      Wasm.IEEE32.infinity negative := by
  by_cases hpower : n < 2 ^ 277
  · exact roundScaledMagnitude_overflows_below_two_pow_277
      negative n h hpower
  · exact roundScaledMagnitude_overflows_above_two_pow_277
      negative n (by omega)

theorem add_overflow (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (h : overflowThreshold ≤
      (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs) :
    Wasm.IEEE32.add a b =
      Wasm.IEEE32.infinity
        (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b < 0) := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  let sum := Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b
  have hthresholdPositive : 0 < overflowThreshold := by
    norm_num [overflowThreshold]
  have h' : overflowThreshold ≤ sum.natAbs := by
    simpa only [sum] using h
  have hsum : sum ≠ 0 := by
    intro hzero
    rw [hzero] at h'
    simp at h'
    omega
  have hround := roundScaledMagnitude_overflows (sum < 0) sum.natAbs h'
  simpa [Wasm.IEEE32.add, hna, hnb, hia, hib, sum, hsum] using hround

theorem sub_overflow (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (h : overflowThreshold ≤
      (Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b).natAbs) :
    Wasm.IEEE32.sub a b =
      Wasm.IEEE32.infinity
        (Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b < 0) := by
  have hneg := negate_spec b hb
  have hadd := add_overflow a (Wasm.IEEE32.negate b) ha hneg.1
    (by simpa only [hneg.2, sub_eq_add_neg] using h)
  simpa only [Wasm.IEEE32.sub, hneg.2, sub_eq_add_neg] using hadd

#print axioms add_nan_left
#print axioms add_infinities_opposite_sign
#print axioms roundScaledMagnitude_overflows
#print axioms add_overflow
#print axioms sub_overflow

end CodeLib.IEEE32
