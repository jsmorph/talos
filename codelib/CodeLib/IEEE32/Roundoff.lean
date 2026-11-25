import Interpreter.Wasm.Examples.FloatAssociativity
import Mathlib.Tactic

/-!
# Axiom-free binary32 roundoff bounds

This file gives the pure interpreter operations a mathematical value and
proves the numerical bound used by the associativity-gap example.
-/

namespace CodeLib.IEEE32

open Wasm

/-- The real value represented by the integer binary32 model.  The value is
used only with a finite-bit hypothesis. -/
noncomputable def value (x : UInt32) : ℝ :=
  (Wasm.IEEE32.scaledValue x : ℝ) / (2 : ℝ) ^ 149

def Finite (x : UInt32) : Prop := Wasm.IEEE32.isFinite x = true

theorem natAbs_scaledValue (x : UInt32) :
    (Wasm.IEEE32.scaledValue x).natAbs =
      Wasm.IEEE32.scaledMagnitude x := by
  simp [Wasm.IEEE32.scaledValue]
  split <;> simp

theorem exponent_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.exponent (Wasm.IEEE32.encodeFinite negative e f) = e := by
  cases negative <;>
    simp [Wasm.IEEE32.exponent, Wasm.IEEE32.encodeFinite,
      UInt32.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem fraction_encodeFinite (negative : Bool) (e f : Nat)
    (_he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.fraction (Wasm.IEEE32.encodeFinite negative e f) = f := by
  cases negative <;>
    simp [Wasm.IEEE32.fraction, Wasm.IEEE32.encodeFinite,
      UInt32.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem sign_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.sign (Wasm.IEEE32.encodeFinite negative e f) = negative := by
  cases negative <;>
    simp [Wasm.IEEE32.sign, Wasm.IEEE32.encodeFinite,
      UInt32.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem finite_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 0xFF) (hf : f < 2 ^ 23) :
    Finite (Wasm.IEEE32.encodeFinite negative e f) := by
  simp [Finite, Wasm.IEEE32.isFinite,
    exponent_encodeFinite negative e f (by omega) hf]
  omega

theorem scaledMagnitude_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.encodeFinite negative e f) =
      if e = 0 then f else (2 ^ 23 + f) * 2 ^ (e - 1) := by
  simp [Wasm.IEEE32.scaledMagnitude,
    exponent_encodeFinite negative e f he hf,
    fraction_encodeFinite negative e f he hf]

theorem scaledValue_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.scaledValue (Wasm.IEEE32.encodeFinite negative e f) =
      let magnitude := if e = 0 then f else (2 ^ 23 + f) * 2 ^ (e - 1)
      if negative then -(magnitude : Int) else magnitude := by
  simp [Wasm.IEEE32.scaledValue,
    scaledMagnitude_encodeFinite negative e f he hf,
    sign_encodeFinite negative e f he hf]

theorem roundShift_bounds (n shift : Nat) :
    n / 2 ^ shift ≤ Wasm.IEEE32.roundShift n shift ∧
      Wasm.IEEE32.roundShift n shift ≤ n / 2 ^ shift + 1 := by
  simp only [Wasm.IEEE32.roundShift]
  split_ifs <;> omega

theorem roundShift_error_cases (n shift : Nat) (hshift : 0 < shift) :
    let rounded := Wasm.IEEE32.roundShift n shift * 2 ^ shift
    let half := 2 ^ shift / 2
    (rounded ≤ n ∧ n - rounded ≤ half) ∨
      (n ≤ rounded ∧ rounded - n ≤ half) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
  have hdecomp :
      n % 2 ^ (k + 1) + n / 2 ^ (k + 1) * 2 ^ (k + 1) = n := by
    simpa [Nat.mul_comm] using Nat.mod_add_div n (2 ^ (k + 1))
  have hunit : 2 ^ (k + 1) / 2 + 2 ^ (k + 1) / 2 = 2 ^ (k + 1) := by
    simp [pow_succ]
    omega
  simp only [Wasm.IEEE32.roundShift]
  split_ifs <;> simp only [Nat.succ_eq_add_one] at *
  · left
    have hle : n / 2 ^ (k + 1) * 2 ^ (k + 1) ≤ n := by omega
    have hsub : n - n / 2 ^ (k + 1) * 2 ^ (k + 1) =
        n % 2 ^ (k + 1) := by omega
    constructor
    · exact hle
    · rw [hsub]
      omega
  · right
    have hle : n ≤ (n / 2 ^ (k + 1) + 1) * 2 ^ (k + 1) := by
      simp only [Nat.add_mul]
      omega
    have hsub : (n / 2 ^ (k + 1) + 1) * 2 ^ (k + 1) - n =
        2 ^ (k + 1) - n % 2 ^ (k + 1) := by
      simp only [Nat.add_mul]
      omega
    constructor
    · exact hle
    · rw [hsub]
      omega
  · left
    have hle : n / 2 ^ (k + 1) * 2 ^ (k + 1) ≤ n := by omega
    have hsub : n - n / 2 ^ (k + 1) * 2 ^ (k + 1) =
        n % 2 ^ (k + 1) := by omega
    constructor
    · exact hle
    · rw [hsub]
      omega
  · right
    have hle : n ≤ (n / 2 ^ (k + 1) + 1) * 2 ^ (k + 1) := by
      simp only [Nat.add_mul]
      omega
    have hsub : (n / 2 ^ (k + 1) + 1) * 2 ^ (k + 1) - n =
        2 ^ (k + 1) - n % 2 ^ (k + 1) := by
      simp only [Nat.add_mul]
      omega
    constructor
    · exact hle
    · rw [hsub]
      omega

theorem abs_int_sub_le_of_error_cases (x y error : Nat)
    (h : (x ≤ y ∧ y - x ≤ error) ∨ (y ≤ x ∧ x - y ≤ error)) :
    |(x : Int) - y| ≤ error := by
  rcases h with h | h
  · have hxy : (x : Int) ≤ y := by exact_mod_cast h.1
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub,
      ← Int.ofNat_sub h.1]
    exact_mod_cast h.2
  · have hyx : (y : Int) ≤ x := by exact_mod_cast h.1
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      ← Int.ofNat_sub h.1]
    exact_mod_cast h.2

/-- The scaled magnitude selected by the pure rounder, before it is packed
into sign, exponent, and fraction fields. -/
def roundedMagnitude (n : Nat) : Nat :=
  if n < 2 ^ 24 then n
  else
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    if rounded == 2 ^ 24 then 2 ^ 23 * 2 ^ (shift + 1)
    else rounded * 2 ^ shift

theorem rounding_parameters {n : Nat} (hmin : 2 ^ 24 ≤ n)
    (hmax : n < 2 ^ 151) :
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    0 < shift ∧ shift ≤ 127 ∧
      2 ^ 23 ≤ rounded ∧ rounded ≤ 2 ^ 24 := by
  have hn : n ≠ 0 := by omega
  have hlogLower : 24 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
  have hlogUpper : Nat.log2 n < 151 := (Nat.log2_lt hn).2 hmax
  let shift := Nat.log2 n - 23
  have hshift : 0 < shift := by simp only [shift]; omega
  have hshiftMax : shift ≤ 127 := by simp only [shift]; omega
  have hpowLower : 2 ^ 23 * 2 ^ shift ≤ n := by
    rw [← pow_add]
    have heq : 23 + shift = Nat.log2 n := by simp only [shift]; omega
    rw [heq]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2 ^ 24 * 2 ^ shift := by
    rw [← pow_add]
    have heq : 24 + shift = Nat.log2 n + 1 := by simp only [shift]; omega
    rw [heq]
    exact Nat.lt_log2_self
  have hquotLower : 2 ^ 23 ≤ n / 2 ^ shift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2 ^ shift < 2 ^ 24 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hround := roundShift_bounds n shift
  change 0 < shift ∧ shift ≤ 127 ∧
    2 ^ 23 ≤ Wasm.IEEE32.roundShift n shift ∧
      Wasm.IEEE32.roundShift n shift ≤ 2 ^ 24
  exact ⟨hshift, hshiftMax, by omega, by omega⟩

theorem roundScaledMagnitude_spec (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 151) :
    Finite (Wasm.IEEE32.roundScaledMagnitude negative n) ∧
      Wasm.IEEE32.scaledMagnitude
          (Wasm.IEEE32.roundScaledMagnitude negative n) = roundedMagnitude n ∧
      |(roundedMagnitude n : Int) - n| ≤ (2 ^ 126 : Nat) := by
  by_cases hsubnormal : n < 2 ^ 23
  · have hsubnormalNum : n < 8388608 := by norm_num at hsubnormal ⊢; exact hsubnormal
    have hexactNum : n < 16777216 := by omega
    have hfinite := finite_encodeFinite negative 0 n (by norm_num) hsubnormal
    have hmagnitude :=
      scaledMagnitude_encodeFinite negative 0 n (by norm_num) hsubnormal
    simp [Wasm.IEEE32.roundScaledMagnitude, roundedMagnitude, hsubnormalNum,
      hexactNum] at hfinite hmagnitude ⊢
    exact ⟨hfinite, hmagnitude⟩
  by_cases hexact : n < 2 ^ 24
  · have hsubnormalNum : ¬n < 8388608 := by norm_num at hsubnormal ⊢; exact hsubnormal
    have hexactNum : n < 16777216 := by norm_num at hexact ⊢; exact hexact
    have hlower : 2 ^ 23 ≤ n := by omega
    have hfraction : n - 2 ^ 23 < 2 ^ 23 := by omega
    have hfinite := finite_encodeFinite negative 1 (n - 2 ^ 23)
      (by norm_num) hfraction
    have hmagnitude :=
      scaledMagnitude_encodeFinite negative 1 (n - 2 ^ 23)
        (by norm_num) hfraction
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative 1 (n - 2 ^ 23) := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum]
    have hrounded : roundedMagnitude n = n := by
      simp [roundedMagnitude, hexactNum]
    have hmagnitude' :
        Wasm.IEEE32.scaledMagnitude
            (Wasm.IEEE32.encodeFinite negative 1 (n - 2 ^ 23)) = n := by
      rw [hmagnitude]
      norm_num
      omega
    rw [hactual, hrounded]
    exact ⟨hfinite, hmagnitude', by simp⟩
  · have hmin : 2 ^ 24 ≤ n := by omega
    have hsubnormalNum : ¬n < 8388608 := by norm_num at hsubnormal ⊢; exact hsubnormal
    have hexactNum : ¬n < 16777216 := by norm_num at hexact ⊢; exact hexact
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    obtain ⟨hshift, hshiftMax, hroundedMin, hroundedMax⟩ :=
      rounding_parameters hmin hmax
    change 0 < shift at hshift
    change shift ≤ 127 at hshiftMax
    change 2 ^ 23 ≤ rounded at hroundedMin
    change rounded ≤ 2 ^ 24 at hroundedMax
    have herrorCases := roundShift_error_cases n shift hshift
    have herrorHalf :
        |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ shift / 2 : Nat) :=
      abs_int_sub_le_of_error_cases _ _ _ herrorCases
    have hhalf : 2 ^ shift / 2 ≤ 2 ^ 126 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
      rw [hk] at hshiftMax
      have hdiv : 2 ^ shift / 2 = 2 ^ k := by
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
      rw [hdiv]
      exact Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    have herror :
        |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ 126 : Nat) :=
      herrorHalf.trans (by exact_mod_cast hhalf)
    by_cases hcarry : rounded = 2 ^ 24
    · have hcarry' :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
        simpa [rounded, shift] using hcarry
      have hcarryNum :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry' ⊢
        exact hcarry'
      have hexponent : shift + 2 < 0xFF := by omega
      have hfinite := finite_encodeFinite negative (shift + 2) 0
        hexponent (by norm_num)
      have hmagnitude :=
        scaledMagnitude_encodeFinite negative (shift + 2) 0 (by omega)
          (by norm_num)
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 2) 0 := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, hcarryNum, show ¬253 ≤ shift by omega,
          Nat.add_assoc]
      have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
        simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum, pow_succ,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        ring
      rw [hactual, hrounded]
      constructor
      · exact hfinite
      constructor
      · rw [hmagnitude]
        simp only [if_neg (by omega : ¬shift + 2 = 0), Nat.add_zero]
        rw [show shift + 2 - 1 = shift + 1 by omega, pow_succ]
        rw [hcarry]
        ring_nf
      · exact herror
    · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
      have hcarry' :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 2 ^ 24 := by
        simpa [rounded, shift] using hcarry
      have hcarryNum :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry' ⊢
        exact hcarry'
      have hexponent : shift + 1 < 0xFF := by omega
      have hfinite := finite_encodeFinite negative (shift + 1)
        (rounded - 2 ^ 23) hexponent hfraction
      have hmagnitude :=
        scaledMagnitude_encodeFinite negative (shift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 1)
            (rounded - 2 ^ 23) := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, rounded, hcarryNum, show ¬254 ≤ shift by omega]
      have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
        simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum]
      rw [hactual, hrounded]
      constructor
      · exact hfinite
      constructor
      · rw [hmagnitude]
        rw [show shift + 1 - 1 = shift by omega]
        have hsum : 2 ^ 23 + (rounded - 2 ^ 23) = rounded := by omega
        rw [hsum]
        simp [show shift + 1 ≠ 0 by omega]
      · exact herror

theorem sign_roundScaledMagnitude (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 151) :
    Wasm.IEEE32.sign (Wasm.IEEE32.roundScaledMagnitude negative n) = negative := by
  by_cases hsubnormal : n < 2 ^ 23
  · have hsubnormalNum : n < 8388608 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative 0 n := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum]
    rw [hactual]
    exact sign_encodeFinite negative 0 n (by norm_num) hsubnormal
  by_cases hexact : n < 2 ^ 24
  · have hsubnormalNum : ¬n < 8388608 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : n < 16777216 := by
      norm_num at hexact ⊢
      exact hexact
    have hfraction : n - 2 ^ 23 < 2 ^ 23 := by omega
    have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
        Wasm.IEEE32.encodeFinite negative 1 (n - 2 ^ 23) := by
      simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum]
    rw [hactual]
    exact sign_encodeFinite negative 1 (n - 2 ^ 23) (by norm_num) hfraction
  · have hmin : 2 ^ 24 ≤ n := by omega
    have hsubnormalNum : ¬n < 8388608 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : ¬n < 16777216 := by
      norm_num at hexact ⊢
      exact hexact
    let shift := Nat.log2 n - 23
    let rounded := Wasm.IEEE32.roundShift n shift
    obtain ⟨_hshift, hshiftMax, hroundedMin, hroundedMax⟩ :=
      rounding_parameters hmin hmax
    change shift ≤ 127 at hshiftMax
    change 2 ^ 23 ≤ rounded at hroundedMin
    change rounded ≤ 2 ^ 24 at hroundedMax
    by_cases hcarry : rounded = 2 ^ 24
    · have hcarryNum :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 2) 0 := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum, shift,
          hcarryNum, show ¬253 ≤ shift by omega, Nat.add_assoc]
      rw [hactual]
      exact sign_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
      have hcarryNum :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 23) = 16777216 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hactual : Wasm.IEEE32.roundScaledMagnitude negative n =
          Wasm.IEEE32.encodeFinite negative (shift + 1)
            (rounded - 2 ^ 23) := by
        simp [Wasm.IEEE32.roundScaledMagnitude, hsubnormalNum, hexactNum, shift,
          rounded, hcarryNum, show ¬254 ≤ shift by omega]
      rw [hactual]
      exact sign_encodeFinite negative (shift + 1) (rounded - 2 ^ 23)
        (by omega) hfraction

theorem scaledValue_roundScaledMagnitude (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 151) :
    Wasm.IEEE32.scaledValue (Wasm.IEEE32.roundScaledMagnitude negative n) =
      if negative then -(roundedMagnitude n : Int) else roundedMagnitude n := by
  have hspec := roundScaledMagnitude_spec negative n hmax
  have hsign := sign_roundScaledMagnitude negative n hmax
  simp [Wasm.IEEE32.scaledValue, hspec.2.1, hsign]

theorem roundScaledValue_spec (z : Int) (hmax : z.natAbs < 2 ^ 151) :
    Finite (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) ∧
      |Wasm.IEEE32.scaledValue
          (Wasm.IEEE32.roundScaledMagnitude (z < 0) z.natAbs) - z| ≤
        (2 ^ 126 : Nat) := by
  have hspec := roundScaledMagnitude_spec (z < 0) z.natAbs hmax
  have hvalue := scaledValue_roundScaledMagnitude (z < 0) z.natAbs hmax
  constructor
  · exact hspec.1
  · by_cases hz : z < 0
    · have hz' : z = -(z.natAbs : Int) :=
        Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hz)
      have hdec : decide (z < 0) = true := by simp [hz]
      rw [hvalue, if_pos hdec]
      have heq : -(roundedMagnitude z.natAbs : Int) - z =
          -((roundedMagnitude z.natAbs : Int) - z.natAbs) := by omega
      rw [heq, abs_neg]
      exact hspec.2.2
    · have hz' : z = (z.natAbs : Int) :=
        Int.eq_natAbs_of_nonneg (Int.le_of_not_gt hz)
      have hdec : decide (z < 0) ≠ true := by simp [hz]
      rw [hvalue, if_neg hdec]
      have heq : (roundedMagnitude z.natAbs : Int) - z =
          (roundedMagnitude z.natAbs : Int) - z.natAbs := by omega
      rw [heq]
      exact hspec.2.2

theorem not_nan_of_finite {x : UInt32} (h : Finite x) :
    Wasm.IEEE32.isNaN x = false := by
  simp [Finite, Wasm.IEEE32.isFinite, Wasm.IEEE32.isNaN] at h ⊢
  omega

theorem not_infinite_of_finite {x : UInt32} (h : Finite x) :
    Wasm.IEEE32.isInfinite x = false := by
  simp [Finite, Wasm.IEEE32.isFinite, Wasm.IEEE32.isInfinite] at h ⊢
  omega

theorem add_spec (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE32.scaledValue a +
      Wasm.IEEE32.scaledValue b).natAbs < 2 ^ 151) :
    Finite (Wasm.IEEE32.add a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) -
        (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b)| ≤
          (2 ^ 126 : Nat) := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  let z := Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b
  by_cases hz : z = 0
  · have hzero : Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) = 0 := by
      simp [Wasm.IEEE32.add, hna, hnb, hia, hib, z, hz]
      split <;> norm_num [Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
        UInt32.toNat_ofNat]
    have hfinite : Finite (Wasm.IEEE32.add a b) := by
      simp [Wasm.IEEE32.add, hna, hnb, hia, hib, z, hz]
      split <;> norm_num [Finite, Wasm.IEEE32.isFinite,
        Wasm.IEEE32.exponent, UInt32.toNat_ofNat]
    rw [hzero, show Wasm.IEEE32.scaledValue a +
      Wasm.IEEE32.scaledValue b = 0 from hz]
    exact ⟨hfinite, by norm_num⟩
  · have hround := roundScaledValue_spec z hbound
    simpa [Wasm.IEEE32.add, hna, hnb, hia, hib, z, hz] using hround

theorem exponent_lt (x : UInt32) : Wasm.IEEE32.exponent x < 2 ^ 8 := by
  exact Nat.mod_lt _ (by norm_num)

theorem fraction_lt (x : UInt32) : Wasm.IEEE32.fraction x < 2 ^ 23 := by
  exact Nat.mod_lt _ (by norm_num)

theorem finite_exponent_lt {x : UInt32} (h : Finite x) :
    Wasm.IEEE32.exponent x < 0xFF := by
  have he := exponent_lt x
  simp [Finite, Wasm.IEEE32.isFinite] at h
  omega

theorem negate_spec (x : UInt32) (h : Finite x) :
    Finite (Wasm.IEEE32.negate x) ∧
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.negate x) =
        -Wasm.IEEE32.scaledValue x := by
  have he := finite_exponent_lt h
  have he' : Wasm.IEEE32.exponent x < 2 ^ 8 := exponent_lt x
  have hf := fraction_lt x
  constructor
  · exact finite_encodeFinite (!Wasm.IEEE32.sign x)
      (Wasm.IEEE32.exponent x) (Wasm.IEEE32.fraction x) he hf
  · rw [Wasm.IEEE32.negate,
      scaledValue_encodeFinite (!Wasm.IEEE32.sign x)
        (Wasm.IEEE32.exponent x) (Wasm.IEEE32.fraction x) he' hf]
    cases hsign : Wasm.IEEE32.sign x <;>
      simp [Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude, hsign]

theorem abs_spec (x : UInt32) (h : Finite x) :
    Finite (Wasm.IEEE32.abs x) ∧
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.abs x) =
        |Wasm.IEEE32.scaledValue x| := by
  have he := finite_exponent_lt h
  have he' : Wasm.IEEE32.exponent x < 2 ^ 8 := exponent_lt x
  have hf := fraction_lt x
  constructor
  · exact finite_encodeFinite false (Wasm.IEEE32.exponent x)
      (Wasm.IEEE32.fraction x) he hf
  · rw [Wasm.IEEE32.abs,
      scaledValue_encodeFinite false (Wasm.IEEE32.exponent x)
        (Wasm.IEEE32.fraction x) he' hf]
    simp only [Bool.false_eq_true, if_false]
    have hmag :
        (if Wasm.IEEE32.exponent x = 0 then Wasm.IEEE32.fraction x
          else (2 ^ 23 + Wasm.IEEE32.fraction x) *
            2 ^ (Wasm.IEEE32.exponent x - 1)) =
          Wasm.IEEE32.scaledMagnitude x := by
      simp [Wasm.IEEE32.scaledMagnitude]
    rw [hmag]
    change (Wasm.IEEE32.scaledMagnitude x : Int) =
      |Wasm.IEEE32.scaledValue x|
    cases hsign : Wasm.IEEE32.sign x <;>
      simp [Wasm.IEEE32.scaledValue, hsign, abs_of_nonneg]

theorem sub_spec (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE32.scaledValue a -
      Wasm.IEEE32.scaledValue b).natAbs < 2 ^ 151) :
    Finite (Wasm.IEEE32.sub a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.sub a b) -
        (Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b)| ≤
          (2 ^ 126 : Nat) := by
  have hneg := negate_spec b hb
  have hadd := add_spec a (Wasm.IEEE32.negate b) ha hneg.1
    (by simpa only [hneg.2, sub_eq_add_neg] using hbound)
  simpa only [Wasm.IEEE32.sub, hneg.2, sub_eq_add_neg] using hadd

theorem natAbs_lt_nat {z : Int} {n : Nat} (h : |z| < (n : Int)) :
    z.natAbs < n := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- In integer units of `2^-149`, the complete associativity-gap result is
nonnegative and strictly below `2^129`. -/
theorem assocGap_scaled_spec (a b c : UInt32)
    (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (haBound : |Wasm.IEEE32.scaledValue a| ≤ (2 ^ 149 : Int))
    (hbBound : |Wasm.IEEE32.scaledValue b| ≤ (2 ^ 149 : Int))
    (hcBound : |Wasm.IEEE32.scaledValue c| ≤ (2 ^ 149 : Int)) :
    Finite (Wasm.FloatAssociativity.assocGapResult a b c) ∧
      0 ≤ Wasm.IEEE32.scaledValue
        (Wasm.FloatAssociativity.assocGapResult a b c) ∧
      Wasm.IEEE32.scaledValue
        (Wasm.FloatAssociativity.assocGapResult a b c) < (2 ^ 129 : Int) := by
  have haBounds := (abs_le.mp haBound)
  have hbBounds := (abs_le.mp hbBound)
  have hcBounds := (abs_le.mp hcBound)

  let bc := Wasm.IEEE32.add b c
  have hbcExactAbs :
      |Wasm.IEEE32.scaledValue b + Wasm.IEEE32.scaledValue c| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 2 * (2 ^ 149 : Int) < 2 ^ 151 := by norm_num
    constructor <;> omega
  have hbc := add_spec b c hb hc (natAbs_lt_nat hbcExactAbs)
  change Finite bc ∧
    |Wasm.IEEE32.scaledValue bc -
      (Wasm.IEEE32.scaledValue b + Wasm.IEEE32.scaledValue c)| ≤
        (2 ^ 126 : Nat) at hbc
  have hbcError := (abs_le.mp hbc.2)

  let left := Wasm.IEEE32.add a bc
  have hleftExactAbs :
      |Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue bc| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 3 * (2 ^ 149 : Int) + 2 ^ 126 < 2 ^ 151 := by
      norm_num
    constructor <;> omega
  have hleft := add_spec a bc ha hbc.1 (natAbs_lt_nat hleftExactAbs)
  change Finite left ∧
    |Wasm.IEEE32.scaledValue left -
      (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue bc)| ≤
        (2 ^ 126 : Nat) at hleft
  have hleftError := (abs_le.mp hleft.2)

  let ab := Wasm.IEEE32.add a b
  have habExactAbs :
      |Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 2 * (2 ^ 149 : Int) < 2 ^ 151 := by norm_num
    constructor <;> omega
  have hab := add_spec a b ha hb (natAbs_lt_nat habExactAbs)
  change Finite ab ∧
    |Wasm.IEEE32.scaledValue ab -
      (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b)| ≤
        (2 ^ 126 : Nat) at hab
  have habError := (abs_le.mp hab.2)

  let right := Wasm.IEEE32.add ab c
  have hrightExactAbs :
      |Wasm.IEEE32.scaledValue ab + Wasm.IEEE32.scaledValue c| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 3 * (2 ^ 149 : Int) + 2 ^ 126 < 2 ^ 151 := by
      norm_num
    constructor <;> omega
  have hright := add_spec ab c hab.1 hc (natAbs_lt_nat hrightExactAbs)
  change Finite right ∧
    |Wasm.IEEE32.scaledValue right -
      (Wasm.IEEE32.scaledValue ab + Wasm.IEEE32.scaledValue c)| ≤
        (2 ^ 126 : Nat) at hright
  have hrightError := (abs_le.mp hright.2)

  have hleftTotal :
      -(2 * (2 ^ 126 : Int)) ≤
          Wasm.IEEE32.scaledValue left -
            (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b +
              Wasm.IEEE32.scaledValue c) ∧
        Wasm.IEEE32.scaledValue left -
            (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b +
              Wasm.IEEE32.scaledValue c) ≤ 2 * (2 ^ 126 : Int) := by
    omega
  have hrightTotal :
      -(2 * (2 ^ 126 : Int)) ≤
          Wasm.IEEE32.scaledValue right -
            (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b +
              Wasm.IEEE32.scaledValue c) ∧
        Wasm.IEEE32.scaledValue right -
            (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b +
              Wasm.IEEE32.scaledValue c) ≤ 2 * (2 ^ 126 : Int) := by
    omega

  let difference := Wasm.IEEE32.sub left right
  have hdifferenceExactAbs :
      |Wasm.IEEE32.scaledValue left - Wasm.IEEE32.scaledValue right| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 4 * (2 ^ 126 : Int) < 2 ^ 151 := by norm_num
    constructor <;> omega
  have hdifference := sub_spec left right hleft.1 hright.1
    (natAbs_lt_nat hdifferenceExactAbs)
  change Finite difference ∧
    |Wasm.IEEE32.scaledValue difference -
      (Wasm.IEEE32.scaledValue left - Wasm.IEEE32.scaledValue right)| ≤
        (2 ^ 126 : Nat) at hdifference
  have hdifferenceError := (abs_le.mp hdifference.2)
  have hdifferenceBound :
      |Wasm.IEEE32.scaledValue difference| ≤ 5 * (2 ^ 126 : Int) := by
    apply abs_le.mpr
    constructor <;> omega

  have hout := abs_spec difference hdifference.1
  have houtNonnegative :
      0 ≤ Wasm.IEEE32.scaledValue (Wasm.IEEE32.abs difference) := by
    rw [hout.2]
    exact abs_nonneg _
  have houtBound :
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.abs difference) <
        (2 ^ 129 : Int) := by
    rw [hout.2]
    have hbudget : 5 * (2 ^ 126 : Int) < 2 ^ 129 := by norm_num
    exact lt_of_le_of_lt hdifferenceBound hbudget
  change Finite (Wasm.IEEE32.abs difference) ∧
    0 ≤ Wasm.IEEE32.scaledValue (Wasm.IEEE32.abs difference) ∧
    Wasm.IEEE32.scaledValue (Wasm.IEEE32.abs difference) < (2 ^ 129 : Int)
  exact And.intro hout.1 (And.intro houtNonnegative houtBound)

/-- The fixed real-valued tolerance used by the end-to-end theorem. -/
noncomputable def epsilon : ℝ := 1 / (2 : ℝ) ^ 20

theorem scaled_abs_le_of_value_abs_le (x : UInt32)
    (h : |value x| ≤ 1) :
    |Wasm.IEEE32.scaledValue x| ≤ (2 ^ 149 : Int) := by
  have hpow : 0 < (2 : ℝ) ^ 149 := by positivity
  have hreal : |(Wasm.IEEE32.scaledValue x : ℝ)| ≤ (2 : ℝ) ^ 149 := by
    rw [value, abs_div, abs_of_pos hpow] at h
    exact (div_le_one hpow).mp h
  exact_mod_cast hreal

/-- Uniform absolute roundoff budget used by bounded binary32 addition and
subtraction. -/
noncomputable def arithmeticEpsilon : ℝ := 1 / (2 : ℝ) ^ 23

/-- Bounded finite binary32 addition differs from exact real addition by at
most one binary32 unit roundoff. -/
theorem add_real_error (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    Finite (Wasm.IEEE32.add a b) ∧
      |value (Wasm.IEEE32.add a b) - (value a + value b)| ≤
        arithmeticEpsilon := by
  have haScaled := scaled_abs_le_of_value_abs_le a haBound
  have hbScaled := scaled_abs_le_of_value_abs_le b hbBound
  have hsum :
      |Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 2 * (2 ^ 149 : Int) < 2 ^ 151 := by norm_num
    have haBounds := abs_le.mp haScaled
    have hbBounds := abs_le.mp hbScaled
    constructor <;> omega
  have hs := add_spec a b ha hb (natAbs_lt_nat hsum)
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) -
        (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b)
    have hz : |z| ≤ (2 ^ 126 : Nat) := hs.2
    have heq :
        value (Wasm.IEEE32.add a b) - (value a + value b) =
          (z : ℝ) / (2 : ℝ) ^ 149 := by
      simp [value, z]
      ring
    rw [heq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 149)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 149)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ 126 := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ 126 := hzReal
      _ = arithmeticEpsilon * (2 : ℝ) ^ 149 := by
        norm_num [arithmeticEpsilon]

/-- Bounded finite binary32 subtraction differs from exact real subtraction
by at most one binary32 unit roundoff. -/
theorem sub_real_error (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    Finite (Wasm.IEEE32.sub a b) ∧
      |value (Wasm.IEEE32.sub a b) - (value a - value b)| ≤
        arithmeticEpsilon := by
  have haScaled := scaled_abs_le_of_value_abs_le a haBound
  have hbScaled := scaled_abs_le_of_value_abs_le b hbBound
  have hdifference :
      |Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b| <
        (2 ^ 151 : Int) := by
    apply abs_lt.mpr
    have hbudget : 2 * (2 ^ 149 : Int) < 2 ^ 151 := by norm_num
    have haBounds := abs_le.mp haScaled
    have hbBounds := abs_le.mp hbScaled
    constructor <;> omega
  have hs := sub_spec a b ha hb (natAbs_lt_nat hdifference)
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.sub a b) -
        (Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b)
    have hz : |z| ≤ (2 ^ 126 : Nat) := hs.2
    have heq :
        value (Wasm.IEEE32.sub a b) - (value a - value b) =
          (z : ℝ) / (2 : ℝ) ^ 149 := by
      simp [value, z]
      ring
    rw [heq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 149)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 149)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ 126 := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ 126 := hzReal
      _ = arithmeticEpsilon * (2 : ℝ) ^ 149 := by
        norm_num [arithmeticEpsilon]

/-- The exact result computed by the WAT body is finite and below `2^-20` for
finite inputs whose real magnitudes are at most one. -/
theorem assocGap_output_lt_epsilon (a b c : UInt32)
    (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1)
    (hcBound : |value c| ≤ 1) :
    Finite (Wasm.FloatAssociativity.assocGapResult a b c) ∧
      value (Wasm.FloatAssociativity.assocGapResult a b c) < epsilon := by
  have hscaled := assocGap_scaled_spec a b c ha hb hc
    (scaled_abs_le_of_value_abs_le a haBound)
    (scaled_abs_le_of_value_abs_le b hbBound)
    (scaled_abs_le_of_value_abs_le c hcBound)
  constructor
  · exact hscaled.1
  · rw [value, epsilon]
    have hcast :
        (Wasm.IEEE32.scaledValue
          (Wasm.FloatAssociativity.assocGapResult a b c) : ℝ) <
            (2 : ℝ) ^ 129 := by
      exact_mod_cast hscaled.2.2
    have hden : 0 < (2 : ℝ) ^ 149 := by positivity
    apply (div_lt_iff₀ hden).2
    have hscale : (1 / (2 : ℝ) ^ 20) * (2 : ℝ) ^ 149 =
        (2 : ℝ) ^ 129 := by norm_num
    rw [hscale]
    exact hcast

/-- Fuel-independent total correctness for the decoded instruction trace,
strengthened with the numerical error bound. -/
theorem assocGap_terminates_lt_epsilon (a b c : UInt32)
    (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1)
    (hcBound : |value c| ≤ 1) :
    Wasm.SmallStep.TerminatesWith
      (Wasm.FloatAssociativity.assocGapConfig a b c)
      (fun values _ =>
        values = [.f32 (Wasm.FloatAssociativity.assocGapResult a b c)] ∧
          Finite (Wasm.FloatAssociativity.assocGapResult a b c) ∧
          value (Wasm.FloatAssociativity.assocGapResult a b c) < epsilon) := by
  have hresult := assocGap_output_lt_epsilon a b c ha hb hc
    haBound hbBound hcBound
  exact (Wasm.FloatAssociativity.assocGap_terminates a b c).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

#print axioms assocGap_output_lt_epsilon
#print axioms assocGap_terminates_lt_epsilon
#print axioms add_real_error
#print axioms sub_real_error

end CodeLib.IEEE32
