import CodeLib.IEEE32.Roundoff
import Interpreter.Wasm.IEEE64
import Mathlib.Tactic

/-!
# Axiom-free binary64 roundoff bounds

Binary64 finite values are represented in integer units of `2^-1074`.  This
file proves the bounded scaled-integer packing result used by the quantitative
operation specifications.
-/

namespace CodeLib.IEEE64

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

open Wasm

noncomputable def value (x : UInt64) : ℝ :=
  (Wasm.IEEE64.scaledValue x : ℝ) / (2 : ℝ) ^ 1074

def Finite (x : UInt64) : Prop := Wasm.IEEE64.isFinite x = true

theorem natAbs_scaledValue (x : UInt64) :
    (Wasm.IEEE64.scaledValue x).natAbs =
      Wasm.IEEE64.scaledMagnitude x := by
  simp [Wasm.IEEE64.scaledValue]
  split <;> simp

theorem exponent_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.exponent (Wasm.IEEE64.encodeFinite negative e f) = e := by
  cases negative <;>
    simp [Wasm.IEEE64.exponent, Wasm.IEEE64.encodeFinite,
      UInt64.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem fraction_encodeFinite (negative : Bool) (e f : Nat)
    (_he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.fraction (Wasm.IEEE64.encodeFinite negative e f) = f := by
  cases negative <;>
    simp [Wasm.IEEE64.fraction, Wasm.IEEE64.encodeFinite,
      UInt64.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem sign_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite negative e f) = negative := by
  cases negative <;>
    simp [Wasm.IEEE64.sign, Wasm.IEEE64.encodeFinite,
      UInt64.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem finite_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 0x7FF) (hf : f < 2 ^ 52) :
    Finite (Wasm.IEEE64.encodeFinite negative e f) := by
  simp [Finite, Wasm.IEEE64.isFinite,
    exponent_encodeFinite negative e f (by omega) hf]
  omega

theorem scaledMagnitude_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite negative e f) =
      if e = 0 then f else (2 ^ 52 + f) * 2 ^ (e - 1) := by
  simp [Wasm.IEEE64.scaledMagnitude,
    exponent_encodeFinite negative e f he hf,
    fraction_encodeFinite negative e f he hf]

theorem scaledValue_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.encodeFinite negative e f) =
      let magnitude := if e = 0 then f else (2 ^ 52 + f) * 2 ^ (e - 1)
      if negative then -(magnitude : Int) else magnitude := by
  simp [Wasm.IEEE64.scaledValue,
    scaledMagnitude_encodeFinite negative e f he hf,
    sign_encodeFinite negative e f he hf]

/-- The scaled magnitude selected before sign, exponent, and fraction packing. -/
def roundedMagnitude (n : Nat) : Nat :=
  if n < 2 ^ 53 then n
  else
    let shift := Nat.log2 n - 52
    let rounded := Wasm.IEEE32.roundShift n shift
    if rounded == 2 ^ 53 then 2 ^ 52 * 2 ^ (shift + 1)
    else rounded * 2 ^ shift

theorem rounding_parameters {n : Nat} (hmin : 2 ^ 53 ≤ n)
    (hmax : n < 2 ^ 1076) :
    let shift := Nat.log2 n - 52
    let rounded := Wasm.IEEE32.roundShift n shift
    0 < shift ∧ shift ≤ 1023 ∧
      2 ^ 52 ≤ rounded ∧ rounded ≤ 2 ^ 53 := by
  have hn : n ≠ 0 := by omega
  have hlogLower : 53 ≤ Nat.log2 n := (Nat.le_log2 hn).2 hmin
  have hlogUpper : Nat.log2 n < 1076 := (Nat.log2_lt hn).2 hmax
  let shift := Nat.log2 n - 52
  have hshift : 0 < shift := by simp only [shift]; omega
  have hshiftMax : shift ≤ 1023 := by simp only [shift]; omega
  have hpowLower : 2 ^ 52 * 2 ^ shift ≤ n := by
    rw [← pow_add]
    have heq : 52 + shift = Nat.log2 n := by simp only [shift]; omega
    rw [heq]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2 ^ 53 * 2 ^ shift := by
    rw [← pow_add]
    have heq : 53 + shift = Nat.log2 n + 1 := by simp only [shift]; omega
    rw [heq]
    exact Nat.lt_log2_self
  have hquotLower : 2 ^ 52 ≤ n / 2 ^ shift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2 ^ shift < 2 ^ 53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hround := CodeLib.IEEE32.roundShift_bounds n shift
  change 0 < shift ∧ shift ≤ 1023 ∧
    2 ^ 52 ≤ Wasm.IEEE32.roundShift n shift ∧
      Wasm.IEEE32.roundShift n shift ≤ 2 ^ 53
  exact ⟨hshift, hshiftMax, by omega, by omega⟩

/-- On scaled magnitudes below four, binary64 packing is finite and incurs at
most `2^1022` scaled units of error, i.e. `2^-52` in real units. -/
theorem roundScaledMagnitude_spec (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 1076) :
    Finite (Wasm.IEEE64.roundScaledMagnitude negative n) ∧
      Wasm.IEEE64.scaledMagnitude
          (Wasm.IEEE64.roundScaledMagnitude negative n) = roundedMagnitude n ∧
      |(roundedMagnitude n : Int) - n| ≤ (2 ^ 1022 : Nat) := by
  by_cases hsubnormal : n < 2 ^ 52
  · have hsubnormalNum : n < 4503599627370496 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : n < 9007199254740992 := by omega
    have hfinite := finite_encodeFinite negative 0 n (by norm_num) hsubnormal
    have hmagnitude :=
      scaledMagnitude_encodeFinite negative 0 n (by norm_num) hsubnormal
    simp [Wasm.IEEE64.roundScaledMagnitude, roundedMagnitude, hsubnormalNum,
      hexactNum] at hfinite hmagnitude ⊢
    exact ⟨hfinite, hmagnitude⟩
  by_cases hexact : n < 2 ^ 53
  · have hsubnormalNum : ¬n < 4503599627370496 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : n < 9007199254740992 := by
      norm_num at hexact ⊢
      exact hexact
    have hlower : 2 ^ 52 ≤ n := by omega
    have hfraction : n - 2 ^ 52 < 2 ^ 52 := by omega
    have hfinite := finite_encodeFinite negative 1 (n - 2 ^ 52)
      (by norm_num) hfraction
    have hmagnitude := scaledMagnitude_encodeFinite negative 1 (n - 2 ^ 52)
      (by norm_num) hfraction
    have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
        Wasm.IEEE64.encodeFinite negative 1 (n - 2 ^ 52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum]
    have hrounded : roundedMagnitude n = n := by
      simp [roundedMagnitude, hexactNum]
    have hmagnitude' :
        Wasm.IEEE64.scaledMagnitude
            (Wasm.IEEE64.encodeFinite negative 1 (n - 2 ^ 52)) = n := by
      rw [hmagnitude]
      norm_num
      omega
    rw [hactual, hrounded]
    exact ⟨hfinite, hmagnitude', by simp⟩
  · have hmin : 2 ^ 53 ≤ n := by omega
    have hsubnormalNum : ¬n < 4503599627370496 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : ¬n < 9007199254740992 := by
      norm_num at hexact ⊢
      exact hexact
    let shift := Nat.log2 n - 52
    let rounded := Wasm.IEEE32.roundShift n shift
    obtain ⟨hshift, hshiftMax, hroundedMin, hroundedMax⟩ :=
      rounding_parameters hmin hmax
    change 0 < shift at hshift
    change shift ≤ 1023 at hshiftMax
    change 2 ^ 52 ≤ rounded at hroundedMin
    change rounded ≤ 2 ^ 53 at hroundedMax
    have herrorCases := CodeLib.IEEE32.roundShift_error_cases n shift hshift
    have herrorHalf :
        |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ shift / 2 : Nat) :=
      CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _ herrorCases
    have hhalf : 2 ^ shift / 2 ≤ 2 ^ 1022 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
      rw [hk] at hshiftMax
      have hdiv : 2 ^ shift / 2 = 2 ^ k := by
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
      rw [hdiv]
      exact Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    have herror :
        |((rounded * 2 ^ shift : Nat) : Int) - n| ≤ (2 ^ 1022 : Nat) :=
      herrorHalf.trans (by exact_mod_cast hhalf)
    by_cases hcarry : rounded = 2 ^ 53
    · have hcarryNum :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 52) =
            9007199254740992 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hfinite := finite_encodeFinite negative (shift + 2) 0
        (by omega) (by norm_num)
      have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 2) 0
        (by omega) (by norm_num)
      have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
          Wasm.IEEE64.encodeFinite negative (shift + 2) 0 := by
        simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, hcarryNum, show ¬2047 ≤ shift + 2 by omega,
          Nat.add_assoc]
      have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
        simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum,
          pow_succ, Nat.mul_assoc, Nat.mul_comm]
        ring
      rw [hactual, hrounded]
      constructor
      · exact hfinite
      constructor
      · rw [hmagnitude]
        simp only [if_neg (by omega : ¬shift + 2 = 0), Nat.add_zero]
        rw [show shift + 2 - 1 = shift + 1 by omega, pow_succ, hcarry]
        ring
      · exact herror
    · have hfraction : rounded - 2 ^ 52 < 2 ^ 52 := by omega
      have hcarryNum :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 52) =
            9007199254740992 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hfinite := finite_encodeFinite negative (shift + 1)
        (rounded - 2 ^ 52) (by omega) hfraction
      have hmagnitude := scaledMagnitude_encodeFinite negative (shift + 1)
        (rounded - 2 ^ 52) (by omega) hfraction
      have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
          Wasm.IEEE64.encodeFinite negative (shift + 1)
            (rounded - 2 ^ 52) := by
        simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, rounded, hcarryNum, show ¬2047 ≤ shift + 1 by omega]
      have hrounded : roundedMagnitude n = rounded * 2 ^ shift := by
        simp [roundedMagnitude, hexactNum, shift, rounded, hcarryNum]
      rw [hactual, hrounded]
      constructor
      · exact hfinite
      constructor
      · rw [hmagnitude]
        rw [show shift + 1 - 1 = shift by omega]
        have hsum : 2 ^ 52 + (rounded - 2 ^ 52) = rounded := by omega
        rw [hsum]
        simp [show shift + 1 ≠ 0 by omega]
      · exact herror

theorem sign_roundScaledMagnitude (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 1076) :
    Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude negative n) = negative := by
  by_cases hsubnormal : n < 2 ^ 52
  · have hnum : n < 4503599627370496 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    simp [Wasm.IEEE64.roundScaledMagnitude, hnum,
      sign_encodeFinite negative 0 n (by norm_num) hsubnormal]
  by_cases hexact : n < 2 ^ 53
  · have hsubnormalNum : ¬n < 4503599627370496 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : n < 9007199254740992 := by
      norm_num at hexact ⊢
      exact hexact
    have hfraction : n - 2 ^ 52 < 2 ^ 52 := by omega
    have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
        Wasm.IEEE64.encodeFinite negative 1 (n - 2 ^ 52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum]
    rw [hactual]
    exact sign_encodeFinite negative 1 (n - 2 ^ 52) (by norm_num) hfraction
  · have hmin : 2 ^ 53 ≤ n := by omega
    have hsubnormalNum : ¬n < 4503599627370496 := by
      norm_num at hsubnormal ⊢
      exact hsubnormal
    have hexactNum : ¬n < 9007199254740992 := by
      norm_num at hexact ⊢
      exact hexact
    let shift := Nat.log2 n - 52
    let rounded := Wasm.IEEE32.roundShift n shift
    obtain ⟨_hshift, hshiftMax, hroundedMin, hroundedMax⟩ :=
      rounding_parameters hmin hmax
    change shift ≤ 1023 at hshiftMax
    change 2 ^ 52 ≤ rounded at hroundedMin
    change rounded ≤ 2 ^ 53 at hroundedMax
    by_cases hcarry : rounded = 2 ^ 53
    · have hcarryNum :
          Wasm.IEEE32.roundShift n (Nat.log2 n - 52) =
            9007199254740992 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
          Wasm.IEEE64.encodeFinite negative (shift + 2) 0 := by
        simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, hcarryNum, show ¬2047 ≤ shift + 2 by omega,
          Nat.add_assoc]
      rw [hactual]
      exact sign_encodeFinite negative (shift + 2) 0 (by omega) (by norm_num)
    · have hfraction : rounded - 2 ^ 52 < 2 ^ 52 := by omega
      have hcarryNum :
          ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 52) =
            9007199254740992 := by
        norm_num at hcarry ⊢
        simpa [rounded, shift] using hcarry
      have hactual : Wasm.IEEE64.roundScaledMagnitude negative n =
          Wasm.IEEE64.encodeFinite negative (shift + 1)
            (rounded - 2 ^ 52) := by
        simp [Wasm.IEEE64.roundScaledMagnitude, hsubnormalNum, hexactNum,
          shift, rounded, hcarryNum, show ¬2047 ≤ shift + 1 by omega]
      rw [hactual]
      exact sign_encodeFinite negative (shift + 1) (rounded - 2 ^ 52)
        (by omega) hfraction

theorem scaledValue_roundScaledMagnitude (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 1076) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude negative n) =
      if negative then -(roundedMagnitude n : Int) else roundedMagnitude n := by
  have hspec := roundScaledMagnitude_spec negative n hmax
  have hsign := sign_roundScaledMagnitude negative n hmax
  simp [Wasm.IEEE64.scaledValue, hspec.2.1, hsign]

theorem roundScaledValue_spec (z : Int) (hmax : z.natAbs < 2 ^ 1076) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) ∧
      |Wasm.IEEE64.scaledValue
          (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) - z| ≤
        (2 ^ 1022 : Nat) := by
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

theorem not_nan_of_finite {x : UInt64} (h : Finite x) :
    Wasm.IEEE64.isNaN x = false := by
  simp [Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.isNaN] at h ⊢
  omega

theorem not_infinite_of_finite {x : UInt64} (h : Finite x) :
    Wasm.IEEE64.isInfinite x = false := by
  simp [Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.isInfinite] at h ⊢
  omega

theorem add_spec (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE64.scaledValue a +
      Wasm.IEEE64.scaledValue b).natAbs < 2 ^ 1076) :
    Finite (Wasm.IEEE64.add a b) ∧
      |Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) -
        (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b)| ≤
          (2 ^ 1022 : Nat) := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  by_cases hz : z = 0
  · have hzero : Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = 0 := by
      simp [Wasm.IEEE64.add, hna, hnb, hia, hib, z, hz]
      split <;> decide
    have hfinite : Finite (Wasm.IEEE64.add a b) := by
      simp [Wasm.IEEE64.add, hna, hnb, hia, hib, z, hz]
      split
      · change Wasm.IEEE64.isFinite (Wasm.IEEE64.signMask true) = true
        decide
      · change Wasm.IEEE64.isFinite 0 = true
        decide
    rw [hzero, show Wasm.IEEE64.scaledValue a +
      Wasm.IEEE64.scaledValue b = 0 from hz]
    exact ⟨hfinite, by norm_num⟩
  · have hround := roundScaledValue_spec z hbound
    simpa [Wasm.IEEE64.add, hna, hnb, hia, hib, z, hz] using hround

theorem negate_spec (x : UInt64) (h : Finite x) :
    Finite (Wasm.IEEE64.negate x) ∧
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate x) =
        -Wasm.IEEE64.scaledValue x := by
  have he : Wasm.IEEE64.exponent x < 0x7FF := by
    have he' : Wasm.IEEE64.exponent x < 2 ^ 11 :=
      Nat.mod_lt _ (by norm_num)
    simp [Finite, Wasm.IEEE64.isFinite] at h
    omega
  have he' : Wasm.IEEE64.exponent x < 2 ^ 11 :=
    Nat.mod_lt _ (by norm_num)
  have hf : Wasm.IEEE64.fraction x < 2 ^ 52 :=
    Nat.mod_lt _ (by norm_num)
  constructor
  · exact finite_encodeFinite (!Wasm.IEEE64.sign x)
      (Wasm.IEEE64.exponent x) (Wasm.IEEE64.fraction x) he hf
  · rw [Wasm.IEEE64.negate,
      scaledValue_encodeFinite (!Wasm.IEEE64.sign x)
        (Wasm.IEEE64.exponent x) (Wasm.IEEE64.fraction x) he' hf]
    cases hsign : Wasm.IEEE64.sign x <;>
      simp [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hsign]

theorem sub_spec (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE64.scaledValue a -
      Wasm.IEEE64.scaledValue b).natAbs < 2 ^ 1076) :
    Finite (Wasm.IEEE64.sub a b) ∧
      |Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) -
        (Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b)| ≤
          (2 ^ 1022 : Nat) := by
  have hneg := negate_spec b hb
  have hadd := add_spec a (Wasm.IEEE64.negate b) ha hneg.1
    (by simpa only [hneg.2, sub_eq_add_neg] using hbound)
  simpa only [Wasm.IEEE64.sub, hneg.2, sub_eq_add_neg] using hadd

theorem natAbs_lt_nat {z : Int} {n : Nat} (h : |z| < (n : Int)) :
    z.natAbs < n := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem scaled_abs_le_of_value_abs_le (x : UInt64)
    (h : |value x| ≤ 1) :
    |Wasm.IEEE64.scaledValue x| ≤ (2 ^ 1074 : Int) := by
  have hpow : 0 < (2 : ℝ) ^ 1074 := by positivity
  have hreal :
      |(Wasm.IEEE64.scaledValue x : ℝ)| ≤ (2 : ℝ) ^ 1074 := by
    rw [value, abs_div, abs_of_pos hpow] at h
    exact (div_le_one hpow).mp h
  exact_mod_cast hreal

noncomputable def arithmeticEpsilon : ℝ := 1 / (2 : ℝ) ^ 52

theorem add_real_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
        arithmeticEpsilon := by
  have haScaled := scaled_abs_le_of_value_abs_le a haBound
  have hbScaled := scaled_abs_le_of_value_abs_le b hbBound
  have hsum :
      |Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b| <
        (2 ^ 1076 : Int) := by
    apply abs_lt.mpr
    have hbudget : 2 * (2 ^ 1074 : Int) < 2 ^ 1076 := by norm_num
    have haBounds := abs_le.mp haScaled
    have hbBounds := abs_le.mp hbScaled
    constructor <;> omega
  have hs := add_spec a b ha hb (natAbs_lt_nat hsum)
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) -
        (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b)
    have hz : |z| ≤ (2 ^ 1022 : Nat) := hs.2
    have heq :
        value (Wasm.IEEE64.add a b) - (value a + value b) =
          (z : ℝ) / (2 : ℝ) ^ 1074 := by
      simp [value, z]
      ring
    rw [heq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 1074)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 1074)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ 1022 := by exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ 1022 := hzReal
      _ = arithmeticEpsilon * (2 : ℝ) ^ 1074 := by
        norm_num [arithmeticEpsilon]

theorem sub_real_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    Finite (Wasm.IEEE64.sub a b) ∧
      |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤
        arithmeticEpsilon := by
  have haScaled := scaled_abs_le_of_value_abs_le a haBound
  have hbScaled := scaled_abs_le_of_value_abs_le b hbBound
  have hdifference :
      |Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b| <
        (2 ^ 1076 : Int) := by
    apply abs_lt.mpr
    have hbudget : 2 * (2 ^ 1074 : Int) < 2 ^ 1076 := by norm_num
    have haBounds := abs_le.mp haScaled
    have hbBounds := abs_le.mp hbScaled
    constructor <;> omega
  have hs := sub_spec a b ha hb (natAbs_lt_nat hdifference)
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) -
        (Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b)
    have hz : |z| ≤ (2 ^ 1022 : Nat) := hs.2
    have heq :
        value (Wasm.IEEE64.sub a b) - (value a - value b) =
          (z : ℝ) / (2 : ℝ) ^ 1074 := by
      simp [value, z]
      ring
    rw [heq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 1074)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 1074)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ 1022 := by exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ 1022 := hzReal
      _ = arithmeticEpsilon * (2 : ℝ) ^ 1074 := by
        norm_num [arithmeticEpsilon]

#print axioms roundScaledMagnitude_spec
#print axioms add_real_error
#print axioms sub_real_error

end CodeLib.IEEE64
