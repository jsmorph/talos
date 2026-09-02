import CodeLib.IEEE32.Roundoff

/-!
# Quantitative specifications for the non-integral binary32 rounders

The arithmetic model has separate one-rounding algorithms for dyadic
products, rational quotients, and square roots.  This file proves their
integer error contracts before operation-specific files translate those
contracts to real values.
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 8192

open Wasm

theorem roundedMagnitude_eq_self {n : Nat} (h : n ≤ 2 ^ 24) :
    roundedMagnitude n = n := by
  by_cases hlt : n < 2 ^ 24
  · norm_num at hlt
    simp [roundedMagnitude, hlt]
  · have hn : n = 2 ^ 24 := by omega
    subst n
    simp only [roundedMagnitude, Nat.lt_irrefl, if_false,
      Nat.log2_two_pow]
    norm_num [Wasm.IEEE32.roundShift]

theorem roundScaledMagnitude_exact (negative : Bool) (n : Nat)
    (h : n ≤ 2 ^ 24) :
    Finite (Wasm.IEEE32.roundScaledMagnitude negative n) ∧
      Wasm.IEEE32.scaledMagnitude
          (Wasm.IEEE32.roundScaledMagnitude negative n) = n ∧
      Wasm.IEEE32.sign
          (Wasm.IEEE32.roundScaledMagnitude negative n) = negative := by
  have hmax : n < 2 ^ 151 := by omega
  have hspec := roundScaledMagnitude_spec negative n hmax
  have hsign := sign_roundScaledMagnitude negative n hmax
  rw [roundedMagnitude_eq_self h] at hspec
  exact ⟨hspec.1, hspec.2.1, hsign⟩

private theorem pow_mul_pow (a b : Nat) :
    2 ^ a * 2 ^ b = (2 : Nat) ^ (a + b) := by
  rw [pow_add]

/-- A dyadic product whose exact scaled magnitude is below `2^151` is finite.
After clearing the 149 input fractional bits, its rounded magnitude differs
from the exact numerator by at most `2^275`, i.e. `2^-23` in real units.
The bound is deliberately uniform over subnormal and normal results. -/
theorem roundDyadicMagnitude149_spec (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 300) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n 149) ∧
      Wasm.IEEE32.sign
          (Wasm.IEEE32.roundDyadicMagnitude negative n 149) = negative ∧
      |((Wasm.IEEE32.scaledMagnitude
              (Wasm.IEEE32.roundDyadicMagnitude negative n 149) *
            2 ^ 149 : Nat) : Int) - n| ≤ (2 ^ 275 : Nat) := by
  by_cases hn : n = 0
  · subst n
    cases negative <;>
      norm_num [Wasm.IEEE32.roundDyadicMagnitude, Finite,
        Wasm.IEEE32.isFinite, Wasm.IEEE32.signMask,
        Wasm.IEEE32.sign, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
        UInt32.toNat_ofNat]
  · let outputShift := Nat.log2 n - 172
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 n ≤ 172 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hnlt : n < 2 ^ 173 := by
        have hself : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
        have hp : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ 173 := by
          exact Nat.pow_le_pow_right (by omega) (by omega)
        exact hself.trans_le hp
      let rounded := Wasm.IEEE32.roundShift n 149
      have hroundBounds := roundShift_bounds n 149
      have hquot : n / 2 ^ 149 < 2 ^ 24 := by
        apply (Nat.div_lt_iff_lt_mul (by positivity)).2
        rw [pow_mul_pow]
        norm_num at hnlt ⊢
        exact hnlt
      have hrounded : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundShift n 149 ≤ 2 ^ 24
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
            Wasm.IEEE32.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE32.roundDyadicMagnitude, hn, outputShift, hzero,
          rounded]
      have hroundError := roundShift_error_cases n 149 (by omega)
      have herr :
          |((rounded * 2 ^ 149 : Nat) : Int) - n| ≤ (2 ^ 148 : Nat) := by
        have h := abs_int_sub_le_of_error_cases _ _ _ hroundError
        norm_num at h ⊢
        exact h
      rw [hactual]
      refine ⟨hpack.1, hpack.2.2, ?_⟩
      rw [hpack.2.1]
      exact herr.trans (by norm_num)
    · have hshift : 0 < outputShift := by omega
      have hnpos : 0 < n := by omega
      have hlogLower : 173 ≤ Nat.log2 n := by
        simp [outputShift] at hzero
        omega
      have hlogUpper : Nat.log2 n < 300 :=
        (Nat.log2_lt hn).2 hmax
      have hshiftMax : outputShift ≤ 127 := by
        simp [outputShift]
        omega
      have hshiftEq : 172 + outputShift = Nat.log2 n := by
        simp [outputShift]
        omega
      let totalShift := 149 + outputShift
      let rounded := Wasm.IEEE32.roundShift n totalShift
      have hpowLower : 2 ^ 23 * 2 ^ totalShift ≤ n := by
        rw [pow_mul_pow]
        have heq : 23 + totalShift = Nat.log2 n := by
          simp [totalShift, hshiftEq]
          omega
        rw [heq]
        exact Nat.log2_self_le hn
      have hpowUpper : n < 2 ^ 24 * 2 ^ totalShift := by
        rw [pow_mul_pow]
        have heq : 24 + totalShift = Nat.log2 n + 1 := by
          simp [totalShift, hshiftEq]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotLower : 2 ^ 23 ≤ n / 2 ^ totalShift :=
        (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotUpper : n / 2 ^ totalShift < 2 ^ 24 :=
        (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds := roundShift_bounds n totalShift
      have hroundedLower : 2 ^ 23 ≤ rounded := by
        change 2 ^ 23 ≤ Wasm.IEEE32.roundShift n totalShift
        omega
      have hroundedUpper : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundShift n totalShift ≤ 2 ^ 24
        omega
      have hroundError := roundShift_error_cases n totalShift (by
        simp [totalShift])
      have herrHalf :
          |((rounded * 2 ^ totalShift : Nat) : Int) - n| ≤
            (2 ^ totalShift / 2 : Nat) :=
        abs_int_sub_le_of_error_cases _ _ _ hroundError
      have hhalf : 2 ^ totalShift / 2 ≤ 2 ^ 275 := by
        have htotal : totalShift ≤ 276 := by
          simp [totalShift]
          omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
          (show totalShift ≠ 0 by simp [totalShift])
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have herr :
          |((rounded * 2 ^ totalShift : Nat) : Int) - n| ≤
            (2 ^ 275 : Nat) :=
        herrHalf.trans (by exact_mod_cast hhalf)
      by_cases hcarry : rounded = 2 ^ 24
      · have hcarryNum :
            Wasm.IEEE32.roundShift n (149 + outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, totalShift] using hcarry
        have hfinite := finite_encodeFinite negative (outputShift + 2) 0
          (by omega) (by norm_num)
        have hsign := sign_encodeFinite negative (outputShift + 2) 0
          (by omega) (by norm_num)
        have hmagnitude := scaledMagnitude_encodeFinite negative
          (outputShift + 2) 0 (by omega) (by norm_num)
        have hmagnitude' :
            Wasm.IEEE32.scaledMagnitude
                (Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0) =
              rounded * 2 ^ outputShift := by
          rw [hmagnitude]
          simp only [if_neg (by omega : ¬outputShift + 2 = 0), Nat.add_zero]
          rw [show outputShift + 2 - 1 = outputShift + 1 by omega, hcarry]
          rw [pow_succ]
          norm_num
          ring
        have hactual :
            Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
              Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0 := by
          simp [Wasm.IEEE32.roundDyadicMagnitude, hn, outputShift, hzero,
            hcarryNum, show ¬253 ≤ outputShift by omega, Nat.add_assoc]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * 2 ^ 149 =
            rounded * 2 ^ totalShift := by
          simp [totalShift, pow_add]
          ring
        rw [hmagEq]
        exact herr
      · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
        have hcarryNum :
            ¬Wasm.IEEE32.roundShift n (149 + outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, totalShift] using hcarry
        have hfinite := finite_encodeFinite negative (outputShift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
        have hsign := sign_encodeFinite negative (outputShift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
        have hmagnitude := scaledMagnitude_encodeFinite negative
          (outputShift + 1) (rounded - 2 ^ 23) (by omega) hfraction
        have hmagnitude' :
            Wasm.IEEE32.scaledMagnitude
                (Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                  (rounded - 2 ^ 23)) = rounded * 2 ^ outputShift := by
          rw [hmagnitude]
          simp only [if_neg (by omega : ¬outputShift + 1 = 0)]
          rw [show outputShift + 1 - 1 = outputShift by omega]
          have hsum : 2 ^ 23 + (rounded - 2 ^ 23) = rounded := by omega
          rw [hsum]
        have hactual :
            Wasm.IEEE32.roundDyadicMagnitude negative n 149 =
              Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                (rounded - 2 ^ 23) := by
          simp [Wasm.IEEE32.roundDyadicMagnitude, hn, outputShift, hzero,
            rounded, totalShift, hcarryNum, show ¬254 ≤ outputShift by omega]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * 2 ^ 149 =
            rounded * 2 ^ totalShift := by
          simp [totalShift, pow_add]
          ring
        rw [hmagEq]
        exact herr

theorem roundQuotient_bounds (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    numerator / denominator ≤
        Wasm.IEEE32.roundQuotient numerator denominator ∧
      Wasm.IEEE32.roundQuotient numerator denominator ≤
        numerator / denominator + 1 := by
  simp [Wasm.IEEE32.roundQuotient, hdenominator]
  split_ifs <;> omega

theorem roundQuotient_error_cases (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    let rounded :=
      Wasm.IEEE32.roundQuotient numerator denominator * denominator
    (rounded ≤ numerator ∧ numerator - rounded ≤ denominator / 2) ∨
      (numerator ≤ rounded ∧ rounded - numerator ≤ denominator / 2) := by
  have hmod : numerator % denominator < denominator :=
    Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
  have hdecomp :
      numerator % denominator + numerator / denominator * denominator =
        numerator := by
    simpa [Nat.mul_comm] using Nat.mod_add_div numerator denominator
  simp [Wasm.IEEE32.roundQuotient, hdenominator, Nat.add_mul]
  split_ifs <;> omega

theorem roundQuotient_int_error (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    |((Wasm.IEEE32.roundQuotient numerator denominator * denominator : Nat) :
        Int) - numerator| ≤ denominator / 2 := by
  exact abs_int_sub_le_of_error_cases _ _ _
    (roundQuotient_error_cases numerator denominator hdenominator)

/-- A nonnegative rational no larger than `2^149` scaled units rounds to a
finite binary32 number.  Clearing the denominator, the packed magnitude has
absolute error at most `denominator * 2^126`, which is `2^-23` in real units
after division by the common binary32 scale. -/
theorem roundRationalMagnitude_spec (negative : Bool)
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0)
    (hbound : numerator ≤ denominator * 2 ^ 149) :
    Finite
        (Wasm.IEEE32.roundRationalMagnitude negative numerator denominator) ∧
      Wasm.IEEE32.sign
          (Wasm.IEEE32.roundRationalMagnitude negative numerator denominator) =
        negative ∧
      |((Wasm.IEEE32.scaledMagnitude
              (Wasm.IEEE32.roundRationalMagnitude negative numerator denominator) *
            denominator : Nat) : Int) - numerator| ≤
        denominator * 2 ^ 126 := by
  by_cases hnumerator : numerator = 0
  · subst numerator
    cases negative <;>
      norm_num [Wasm.IEEE32.roundRationalMagnitude, Finite,
        Wasm.IEEE32.isFinite, Wasm.IEEE32.signMask,
        Wasm.IEEE32.sign, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
        UInt32.toNat_ofNat]
  · let integerPart := numerator / denominator
    have hdenominatorPos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
    have hintegerBound : integerPart ≤ 2 ^ 149 := by
      apply Nat.div_le_of_le_mul
      simpa [integerPart, Nat.mul_comm] using hbound
    let outputShift := Nat.log2 integerPart - 23
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 integerPart ≤ 23 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hintegerLt : integerPart < 2 ^ 24 := by
        by_cases hintegerZero : integerPart = 0
        · simp [hintegerZero]
        · have hself :
              integerPart < 2 ^ (Nat.log2 integerPart + 1) :=
              Nat.lt_log2_self
          have hp : 2 ^ (Nat.log2 integerPart + 1) ≤ 2 ^ 24 :=
            Nat.pow_le_pow_right (by omega) (by omega)
          exact hself.trans_le hp
      let rounded :=
        Wasm.IEEE32.roundQuotient numerator denominator
      have hroundBounds :=
        roundQuotient_bounds numerator denominator hdenominator
      have hrounded : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundQuotient numerator denominator ≤ 2 ^ 24
        change numerator / denominator < 2 ^ 24 at hintegerLt
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE32.roundRationalMagnitude negative numerator denominator =
            Wasm.IEEE32.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE32.roundRationalMagnitude, hnumerator, hdenominator,
          integerPart, outputShift, hzero, rounded]
      have herr :=
        roundQuotient_int_error numerator denominator hdenominator
      rw [hactual]
      refine ⟨hpack.1, hpack.2.2, ?_⟩
      rw [hpack.2.1]
      have herrorBound : denominator / 2 ≤ denominator * 2 ^ 126 :=
        (Nat.div_le_self denominator 2).trans
          (Nat.le_mul_of_pos_right denominator (by positivity))
      exact herr.trans (by exact_mod_cast herrorBound)
    · have hshift : 0 < outputShift := by omega
      have hintegerNe : integerPart ≠ 0 := by
        intro h
        apply hzero
        simp [outputShift, h]
      have hintegerPos : 0 < integerPart := Nat.pos_of_ne_zero hintegerNe
      have hlogLower : 24 ≤ Nat.log2 integerPart := by
        simp [outputShift] at hzero
        omega
      have hintegerLt : integerPart < 2 ^ 150 :=
        hintegerBound.trans_lt (by norm_num)
      have hlogUpper : Nat.log2 integerPart < 150 :=
        (Nat.log2_lt (by omega)).2 hintegerLt
      have hshiftMax : outputShift ≤ 126 := by
        simp [outputShift]
        omega
      have hshiftEq : 23 + outputShift = Nat.log2 integerPart := by
        simp [outputShift]
        omega
      let unitDenominator := denominator * 2 ^ outputShift
      have hunitDenominator : unitDenominator ≠ 0 := by
        simp [unitDenominator, hdenominator]
      let rounded :=
        Wasm.IEEE32.roundQuotient numerator unitDenominator
      have hpowLower : 2 ^ 23 * 2 ^ outputShift ≤ integerPart := by
        rw [pow_mul_pow, hshiftEq]
        exact Nat.log2_self_le (by omega)
      have hpowUpper : integerPart < 2 ^ 24 * 2 ^ outputShift := by
        rw [pow_mul_pow]
        have heq : 24 + outputShift = Nat.log2 integerPart + 1 := by
          rw [← hshiftEq]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotientEq :
          numerator / unitDenominator = integerPart / 2 ^ outputShift := by
        simp [unitDenominator, integerPart, Nat.div_div_eq_div_mul]
      have hquotientLower :
          2 ^ 23 ≤ numerator / unitDenominator := by
        rw [hquotientEq]
        exact (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotientUpper :
          numerator / unitDenominator < 2 ^ 24 := by
        rw [hquotientEq]
        exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds :=
        roundQuotient_bounds numerator unitDenominator hunitDenominator
      have hroundedLower : 2 ^ 23 ≤ rounded := by
        change 2 ^ 23 ≤
          Wasm.IEEE32.roundQuotient numerator unitDenominator
        omega
      have hroundedUpper : rounded ≤ 2 ^ 24 := by
        change Wasm.IEEE32.roundQuotient numerator unitDenominator ≤ 2 ^ 24
        omega
      have herrHalf :=
        roundQuotient_int_error numerator unitDenominator hunitDenominator
      have hhalf : unitDenominator / 2 ≤ denominator * 2 ^ 126 := by
        calc
          unitDenominator / 2 ≤ unitDenominator := Nat.div_le_self _ _
          _ ≤ denominator * 2 ^ 126 := by
            apply Nat.mul_le_mul_left denominator
            exact Nat.pow_le_pow_right (by omega) hshiftMax
      have herr :
          |((rounded * unitDenominator : Nat) : Int) - numerator| ≤
            denominator * 2 ^ 126 :=
        herrHalf.trans (by exact_mod_cast hhalf)
      by_cases hcarry : rounded = 2 ^ 24
      · have hcarryNum :
            Wasm.IEEE32.roundQuotient numerator
                (denominator * 2 ^ outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, unitDenominator] using hcarry
        have hfinite := finite_encodeFinite negative (outputShift + 2) 0
          (by omega) (by norm_num)
        have hsign := sign_encodeFinite negative (outputShift + 2) 0
          (by omega) (by norm_num)
        have hmagnitude := scaledMagnitude_encodeFinite negative
          (outputShift + 2) 0 (by omega) (by norm_num)
        have hmagnitude' :
            Wasm.IEEE32.scaledMagnitude
                (Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0) =
              rounded * 2 ^ outputShift := by
          rw [hmagnitude]
          simp only [if_neg (by omega : ¬outputShift + 2 = 0), Nat.add_zero]
          rw [show outputShift + 2 - 1 = outputShift + 1 by omega, hcarry]
          rw [pow_succ]
          norm_num
          ring
        have hactual :
            Wasm.IEEE32.roundRationalMagnitude negative numerator denominator =
              Wasm.IEEE32.encodeFinite negative (outputShift + 2) 0 := by
          simp [Wasm.IEEE32.roundRationalMagnitude, hnumerator, hdenominator,
            integerPart, outputShift, hzero, hcarryNum,
            show ¬253 ≤ outputShift by omega, Nat.add_assoc]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * denominator =
            rounded * unitDenominator := by
          simp [unitDenominator]
          ring
        rw [hmagEq]
        exact herr
      · have hfraction : rounded - 2 ^ 23 < 2 ^ 23 := by omega
        have hcarryNum :
            ¬Wasm.IEEE32.roundQuotient numerator
                (denominator * 2 ^ outputShift) = 16777216 := by
          norm_num at hcarry ⊢
          simpa [rounded, unitDenominator] using hcarry
        have hfinite := finite_encodeFinite negative (outputShift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
        have hsign := sign_encodeFinite negative (outputShift + 1)
          (rounded - 2 ^ 23) (by omega) hfraction
        have hmagnitude := scaledMagnitude_encodeFinite negative
          (outputShift + 1) (rounded - 2 ^ 23) (by omega) hfraction
        have hmagnitude' :
            Wasm.IEEE32.scaledMagnitude
                (Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                  (rounded - 2 ^ 23)) = rounded * 2 ^ outputShift := by
          rw [hmagnitude]
          simp only [if_neg (by omega : ¬outputShift + 1 = 0)]
          rw [show outputShift + 1 - 1 = outputShift by omega]
          have hsum : 2 ^ 23 + (rounded - 2 ^ 23) = rounded := by omega
          rw [hsum]
        have hactual :
            Wasm.IEEE32.roundRationalMagnitude negative numerator denominator =
              Wasm.IEEE32.encodeFinite negative (outputShift + 1)
                (rounded - 2 ^ 23) := by
          simp [Wasm.IEEE32.roundRationalMagnitude, hnumerator, hdenominator,
            integerPart, outputShift, hzero, rounded, unitDenominator,
            hcarryNum, show ¬254 ≤ outputShift by omega]
        rw [hactual]
        refine ⟨hfinite, hsign, ?_⟩
        rw [hmagnitude']
        have hmagEq : rounded * 2 ^ outputShift * denominator =
            rounded * unitDenominator := by
          simp [unitDenominator]
          ring
        rw [hmagEq]
        exact herr

#print axioms roundDyadicMagnitude149_spec
#print axioms roundQuotient_int_error
#print axioms roundRationalMagnitude_spec

end CodeLib.IEEE32
