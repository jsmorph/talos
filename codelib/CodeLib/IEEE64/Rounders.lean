import CodeLib.IEEE64.Roundoff
import CodeLib.IEEE32.Rounders

/-!
# Quantitative specifications for binary64 nonintegral rounders
-/

namespace CodeLib.IEEE64

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

open Wasm

theorem roundedMagnitude_eq_self {n : Nat} (h : n ≤ 2 ^ 53) :
    roundedMagnitude n = n := by
  by_cases hlt : n < 2 ^ 53
  · have hltNum : n < 9007199254740992 := by
      norm_num at hlt ⊢
      exact hlt
    simp [roundedMagnitude, hltNum]
  · have hn : n = 2 ^ 53 := by omega
    subst n
    simp only [roundedMagnitude, Nat.lt_irrefl, if_false,
      Nat.log2_two_pow]
    norm_num [Wasm.IEEE32.roundShift]

theorem roundScaledMagnitude_exact (negative : Bool) (n : Nat)
    (h : n ≤ 2 ^ 53) :
    Finite (Wasm.IEEE64.roundScaledMagnitude negative n) ∧
      Wasm.IEEE64.scaledMagnitude
          (Wasm.IEEE64.roundScaledMagnitude negative n) = n ∧
      Wasm.IEEE64.sign
          (Wasm.IEEE64.roundScaledMagnitude negative n) = negative := by
  have hmax : n < 2 ^ 1076 := by omega
  have hspec := roundScaledMagnitude_spec negative n hmax
  have hsign := sign_roundScaledMagnitude negative n hmax
  rw [roundedMagnitude_eq_self h] at hspec
  exact ⟨hspec.1, hspec.2.1, hsign⟩

private theorem pow_mul_pow (a b : Nat) :
    2 ^ a * 2 ^ b = (2 : Nat) ^ (a + b) := by
  rw [pow_add]

private theorem log2_mul_two_pow (n shift : Nat) (hn : n ≠ 0) :
    Nat.log2 (n * 2 ^ shift) = Nat.log2 n + shift := by
  induction shift with
  | zero => simp
  | succ shift ih =>
      rw [pow_succ]
      rw [show n * (2 ^ shift * 2) = 2 * (n * 2 ^ shift) by ring]
      rw [Nat.log2_two_mul (Nat.mul_ne_zero hn (by positivity)), ih]
      omega

private theorem roundShift_mul_two_pow (n shift : Nat) (hshift : 0 < shift) :
    Wasm.IEEE32.roundShift (n * 2 ^ shift) shift = n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
  simp [Wasm.IEEE32.roundShift, pow_succ, Nat.mul_assoc]

private theorem roundedMagnitude_shifted (rounded shift : Nat)
    (hlower : 2 ^ 52 ≤ rounded) (hupper : rounded ≤ 2 ^ 53) :
    roundedMagnitude (rounded * 2 ^ shift) = rounded * 2 ^ shift := by
  by_cases hshift : shift = 0
  · subst shift
    simpa using roundedMagnitude_eq_self hupper
  · have hshiftPos : 0 < shift := Nat.pos_of_ne_zero hshift
    have hroundedNe : rounded ≠ 0 := by omega
    have hlarge : ¬rounded * 2 ^ shift < 2 ^ 53 := by
      have hp : 2 ^ 52 * 2 ^ 1 ≤ rounded * 2 ^ shift :=
        Nat.mul_le_mul hlower
          (Nat.pow_le_pow_right (by omega) (by omega))
      norm_num [← pow_add] at hp ⊢
      exact hp
    by_cases hcarry : rounded = 2 ^ 53
    · subst rounded
      have hlog := log2_mul_two_pow (2 ^ 53) shift (by positivity)
      have hcandidate :
          2 ^ 53 * 2 ^ shift = 2 ^ 52 * 2 ^ (shift + 1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have hactualShift : Nat.log2 (2 ^ 53 * 2 ^ shift) - 52 =
          shift + 1 := by
        rw [hlog, Nat.log2_two_pow]
        omega
      simp only [roundedMagnitude, if_neg hlarge]
      rw [hactualShift, hcandidate,
        roundShift_mul_two_pow _ _ (by omega)]
      norm_num
    · have hroundedLt : rounded < 2 ^ 53 := by omega
      have hlogRounded : Nat.log2 rounded = 52 := by
        exact (Nat.log2_eq_iff hroundedNe).2
          ⟨hlower, by simpa using hroundedLt⟩
      have hlog := log2_mul_two_pow rounded shift hroundedNe
      have hactualShift :
          Nat.log2 (rounded * 2 ^ shift) - 52 = shift := by
        rw [hlog, hlogRounded]
        omega
      simp only [roundedMagnitude, if_neg hlarge]
      rw [hactualShift, roundShift_mul_two_pow _ _ hshiftPos]
      simp only [beq_iff_eq, if_neg hcarry]

/-- A nonnegative rational no larger than `2^1074` scaled units rounds to a
finite binary64 number.  Clearing the denominator, the packed magnitude has
absolute error at most `denominator * 2^1022`, which is `2^-52` in real units
after division by the common binary64 scale. -/
theorem roundRationalMagnitude_spec (negative : Bool)
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0)
    (hbound : numerator ≤ denominator * 2 ^ 1074) :
    Finite
        (Wasm.IEEE64.roundRationalMagnitude negative numerator denominator) ∧
      Wasm.IEEE64.sign
          (Wasm.IEEE64.roundRationalMagnitude negative numerator denominator) =
        negative ∧
      |((Wasm.IEEE64.scaledMagnitude
              (Wasm.IEEE64.roundRationalMagnitude negative numerator denominator) *
            denominator : Nat) : Int) - numerator| ≤
        denominator * 2 ^ 1022 := by
  by_cases hnumerator : numerator = 0
  · subst numerator
    cases negative <;>
      norm_num [Wasm.IEEE64.roundRationalMagnitude, Finite,
        Wasm.IEEE64.isFinite, Wasm.IEEE64.signMask,
        Wasm.IEEE64.sign, Wasm.IEEE64.scaledMagnitude,
        Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
        UInt64.toNat_ofNat]
  · let integerPart := numerator / denominator
    have hdenominatorPos : 0 < denominator :=
      Nat.pos_of_ne_zero hdenominator
    have hintegerBound : integerPart ≤ 2 ^ 1074 := by
      apply Nat.div_le_of_le_mul
      simpa [integerPart, Nat.mul_comm] using hbound
    let outputShift := Nat.log2 integerPart - 52
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 integerPart ≤ 52 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hintegerLt : integerPart < 2 ^ 53 := by
        by_cases hintegerZero : integerPart = 0
        · simp [hintegerZero]
        · have hself :
              integerPart < 2 ^ (Nat.log2 integerPart + 1) :=
              Nat.lt_log2_self
          have hp : 2 ^ (Nat.log2 integerPart + 1) ≤ 2 ^ 53 :=
            Nat.pow_le_pow_right (by omega) (by omega)
          exact hself.trans_le hp
      let rounded :=
        Wasm.IEEE32.roundQuotient numerator denominator
      have hroundBounds :=
        CodeLib.IEEE32.roundQuotient_bounds numerator denominator hdenominator
      have hrounded : rounded ≤ 2 ^ 53 := by
        change Wasm.IEEE32.roundQuotient numerator denominator ≤ 2 ^ 53
        change numerator / denominator < 2 ^ 53 at hintegerLt
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE64.roundRationalMagnitude negative numerator denominator =
            Wasm.IEEE64.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE64.roundRationalMagnitude, hnumerator, hdenominator,
          integerPart, outputShift, hzero, rounded]
      have herr :=
        CodeLib.IEEE32.roundQuotient_int_error
          numerator denominator hdenominator
      rw [hactual]
      refine ⟨hpack.1, hpack.2.2, ?_⟩
      rw [hpack.2.1]
      have herrorBound : denominator / 2 ≤ denominator * 2 ^ 1022 :=
        (Nat.div_le_self denominator 2).trans
          (Nat.le_mul_of_pos_right denominator (by positivity))
      exact herr.trans (by exact_mod_cast herrorBound)
    · have hshift : 0 < outputShift := by omega
      have hintegerNe : integerPart ≠ 0 := by
        intro h
        apply hzero
        simp [outputShift, h]
      have hlogLower : 53 ≤ Nat.log2 integerPart := by
        simp [outputShift] at hzero
        omega
      have hintegerLt : integerPart < 2 ^ 1075 :=
        hintegerBound.trans_lt (by norm_num)
      have hlogUpper : Nat.log2 integerPart < 1075 :=
        (Nat.log2_lt hintegerNe).2 hintegerLt
      have hshiftMax : outputShift ≤ 1022 := by
        simp [outputShift]
        omega
      have hshiftEq : 52 + outputShift = Nat.log2 integerPart := by
        simp [outputShift]
        omega
      let unitDenominator := denominator * 2 ^ outputShift
      have hunitDenominator : unitDenominator ≠ 0 := by
        simp [unitDenominator, hdenominator]
      let rounded :=
        Wasm.IEEE32.roundQuotient numerator unitDenominator
      have hpowLower : 2 ^ 52 * 2 ^ outputShift ≤ integerPart := by
        rw [pow_mul_pow, hshiftEq]
        exact Nat.log2_self_le hintegerNe
      have hpowUpper : integerPart < 2 ^ 53 * 2 ^ outputShift := by
        rw [pow_mul_pow]
        have heq : 53 + outputShift = Nat.log2 integerPart + 1 := by
          rw [← hshiftEq]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotientEq :
          numerator / unitDenominator = integerPart / 2 ^ outputShift := by
        simp [unitDenominator, integerPart, Nat.div_div_eq_div_mul]
      have hquotientLower :
          2 ^ 52 ≤ numerator / unitDenominator := by
        rw [hquotientEq]
        exact (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotientUpper :
          numerator / unitDenominator < 2 ^ 53 := by
        rw [hquotientEq]
        exact (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds :=
        CodeLib.IEEE32.roundQuotient_bounds
          numerator unitDenominator hunitDenominator
      have hroundedLower : 2 ^ 52 ≤ rounded := by
        change 2 ^ 52 ≤
          Wasm.IEEE32.roundQuotient numerator unitDenominator
        omega
      have hroundedUpper : rounded ≤ 2 ^ 53 := by
        change Wasm.IEEE32.roundQuotient numerator unitDenominator ≤ 2 ^ 53
        omega
      have herrHalf :=
        CodeLib.IEEE32.roundQuotient_int_error
          numerator unitDenominator hunitDenominator
      have hhalf : unitDenominator / 2 ≤ denominator * 2 ^ 1022 := by
        calc
          unitDenominator / 2 ≤ unitDenominator := Nat.div_le_self _ _
          _ ≤ denominator * 2 ^ 1022 := by
            apply Nat.mul_le_mul_left denominator
            exact Nat.pow_le_pow_right (by omega) hshiftMax
      have herr :
          |((rounded * unitDenominator : Nat) : Int) - numerator| ≤
            denominator * 2 ^ 1022 :=
        herrHalf.trans (by exact_mod_cast hhalf)
      let candidate := rounded * 2 ^ outputShift
      have hrepresentable : roundedMagnitude candidate = candidate :=
        roundedMagnitude_shifted rounded outputShift
          hroundedLower hroundedUpper
      have hcandidateMax : candidate < 2 ^ 1076 := by
        calc
          candidate ≤ 2 ^ 53 * 2 ^ 1022 :=
            Nat.mul_le_mul hroundedUpper
              (Nat.pow_le_pow_right (by omega) hshiftMax)
          _ = 2 ^ 1075 := by rw [← pow_add]
          _ < 2 ^ 1076 := Nat.pow_lt_pow_right (by omega) (by omega)
      have hpack := roundScaledMagnitude_spec negative candidate hcandidateMax
      have hsign := sign_roundScaledMagnitude negative candidate hcandidateMax
      have hactual :
          Wasm.IEEE64.roundRationalMagnitude negative numerator denominator =
            Wasm.IEEE64.roundScaledMagnitude negative candidate := by
        simp [Wasm.IEEE64.roundRationalMagnitude, hnumerator, hdenominator,
          integerPart, outputShift, hzero, rounded, unitDenominator, candidate]
      rw [hactual]
      refine ⟨hpack.1, hsign, ?_⟩
      rw [hpack.2.1, hrepresentable]
      have hmagEq : candidate * denominator = rounded * unitDenominator := by
        simp [candidate, unitDenominator]
        ring
      rw [hmagEq]
      exact herr

/-- A bounded exact dyadic product receives one ties-to-even rounding step.
The cleared-denominator error is at most `2^2096`, equivalent to `2^-52`
after division by the common real denominator `2^2148`. -/
theorem roundDyadicMagnitude1074_spec (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 2149) :
    Finite (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) ∧
      Wasm.IEEE64.sign
          (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) = negative ∧
      |((Wasm.IEEE64.scaledMagnitude
              (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) *
            2 ^ 1074 : Nat) : Int) - n| ≤ (2 ^ 2096 : Nat) := by
  by_cases hn : n = 0
  · subst n
    cases negative <;>
      norm_num [Wasm.IEEE64.roundDyadicMagnitude, Finite,
        Wasm.IEEE64.isFinite, Wasm.IEEE64.signMask,
        Wasm.IEEE64.sign, Wasm.IEEE64.scaledMagnitude,
        Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
        UInt64.toNat_ofNat]
  · let outputShift := Nat.log2 n - 1126
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 n ≤ 1126 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hnlt : n < 2 ^ 1127 := by
        have hself : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
        exact hself.trans_le
          (Nat.pow_le_pow_right (by omega) (by omega))
      let rounded := Wasm.IEEE32.roundShift n 1074
      have hroundBounds := CodeLib.IEEE32.roundShift_bounds n 1074
      have hquot : n / 2 ^ 1074 < 2 ^ 53 := by
        apply (Nat.div_lt_iff_lt_mul (by positivity)).2
        rw [pow_mul_pow]
        norm_num at hnlt ⊢
        exact hnlt
      have hrounded : rounded ≤ 2 ^ 53 := by
        change Wasm.IEEE32.roundShift n 1074 ≤ 2 ^ 53
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
            Wasm.IEEE64.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE64.roundDyadicMagnitude, hn, outputShift, hzero,
          rounded]
      have hroundError :=
        CodeLib.IEEE32.roundShift_error_cases n 1074 (by omega)
      have herr :
          |((rounded * 2 ^ 1074 : Nat) : Int) - n| ≤
            (2 ^ 1073 : Nat) := by
        have h := CodeLib.IEEE32.abs_int_sub_le_of_error_cases
          _ _ _ hroundError
        norm_num at h ⊢
        exact h
      rw [hactual]
      refine ⟨hpack.1, hpack.2.2, ?_⟩
      rw [hpack.2.1]
      exact herr.trans (by norm_num)
    · have hshift : 0 < outputShift := by omega
      have hlogLower : 1127 ≤ Nat.log2 n := by
        simp [outputShift] at hzero
        omega
      have hlogUpper : Nat.log2 n < 2149 :=
        (Nat.log2_lt hn).2 hmax
      have hshiftMax : outputShift ≤ 1022 := by
        simp [outputShift]
        omega
      have hshiftEq : 1126 + outputShift = Nat.log2 n := by
        simp [outputShift]
        omega
      let totalShift := 1074 + outputShift
      let rounded := Wasm.IEEE32.roundShift n totalShift
      let candidate := rounded * 2 ^ outputShift
      have hpowLower : 2 ^ 52 * 2 ^ totalShift ≤ n := by
        rw [pow_mul_pow]
        have heq : 52 + totalShift = Nat.log2 n := by
          simp only [totalShift]
          omega
        rw [heq]
        exact Nat.log2_self_le hn
      have hpowUpper : n < 2 ^ 53 * 2 ^ totalShift := by
        rw [pow_mul_pow]
        have heq : 53 + totalShift = Nat.log2 n + 1 := by
          simp only [totalShift]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotLower : 2 ^ 52 ≤ n / 2 ^ totalShift :=
        (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotUpper : n / 2 ^ totalShift < 2 ^ 53 :=
        (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds := CodeLib.IEEE32.roundShift_bounds n totalShift
      have hroundedLower : 2 ^ 52 ≤ rounded := by
        change 2 ^ 52 ≤ Wasm.IEEE32.roundShift n totalShift
        omega
      have hroundedUpper : rounded ≤ 2 ^ 53 := by
        change Wasm.IEEE32.roundShift n totalShift ≤ 2 ^ 53
        omega
      have hrepresentable : roundedMagnitude candidate = candidate :=
        roundedMagnitude_shifted rounded outputShift
          hroundedLower hroundedUpper
      have hcandidateMax : candidate < 2 ^ 1076 := by
        calc
          candidate ≤ 2 ^ 53 * 2 ^ 1022 :=
            Nat.mul_le_mul hroundedUpper
              (Nat.pow_le_pow_right (by omega) hshiftMax)
          _ = 2 ^ 1075 := by rw [← pow_add]
          _ < 2 ^ 1076 := Nat.pow_lt_pow_right (by omega) (by omega)
      have hpack := roundScaledMagnitude_spec negative candidate hcandidateMax
      have hsign := sign_roundScaledMagnitude negative candidate hcandidateMax
      have hactual :
          Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
            Wasm.IEEE64.roundScaledMagnitude negative candidate := by
        simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, if_neg hn]
        rw [show Nat.log2 n - (1074 + 52) = outputShift by
          simp [outputShift]]
        rw [if_neg hzero]
      have hroundError :=
        CodeLib.IEEE32.roundShift_error_cases n totalShift (by
          simp [totalShift])
      have hhalf : 2 ^ totalShift / 2 ≤ 2 ^ 2096 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
          (by simp [totalShift] : totalShift ≠ 0)
        have hkMax : k ≤ 2095 := by
          simp [totalShift] at hk
          omega
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have herr :
          |((rounded * 2 ^ totalShift : Nat) : Int) - n| ≤
            (2 ^ 2096 : Nat) :=
        (CodeLib.IEEE32.abs_int_sub_le_of_error_cases
          _ _ _ hroundError).trans (by exact_mod_cast hhalf)
      rw [hactual]
      refine ⟨hpack.1, hsign, ?_⟩
      rw [hpack.2.1, hrepresentable]
      simpa [candidate, totalShift, pow_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using herr

/-- The binary64 dyadic-product rounder retains its local scale.  Above the
normal threshold the error is relative (`2^-53 * n`); below it the error is
at most half the least subnormal unit.  The zero input remains exact. -/
theorem roundDyadicMagnitude1074_adaptive_spec (negative : Bool) (n : Nat)
    (hmax : n < 2 ^ 2149) :
    Finite (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) ∧
      Wasm.IEEE64.sign
          (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) = negative ∧
      |((Wasm.IEEE64.scaledMagnitude
              (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) *
            2 ^ 1074 : Nat) : Int) - n| * (2 ^ 53 : Int) ≤
        (if n = 0 then 0 else max n (2 ^ 1126) : Nat) := by
  have hbase := roundDyadicMagnitude1074_spec negative n hmax
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  by_cases hn : n = 0
  · subst n
    cases negative <;>
      norm_num [Wasm.IEEE64.roundDyadicMagnitude,
        Wasm.IEEE64.signMask, Wasm.IEEE64.scaledMagnitude,
        Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
        UInt64.toNat_ofNat]
  · let outputShift := Nat.log2 n - 1126
    by_cases hzero : outputShift = 0
    · have hlog : Nat.log2 n ≤ 1126 := by
        simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
      have hnlt : n < 2 ^ 1127 := by
        have hself : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
        exact hself.trans_le
          (Nat.pow_le_pow_right (by omega) (by omega))
      let rounded := Wasm.IEEE32.roundShift n 1074
      have hroundBounds := CodeLib.IEEE32.roundShift_bounds n 1074
      have hquot : n / 2 ^ 1074 < 2 ^ 53 := by
        apply (Nat.div_lt_iff_lt_mul (by positivity)).2
        rw [pow_mul_pow]
        norm_num at hnlt ⊢
        exact hnlt
      have hrounded : rounded ≤ 2 ^ 53 := by
        change Wasm.IEEE32.roundShift n 1074 ≤ 2 ^ 53
        omega
      have hpack := roundScaledMagnitude_exact negative rounded hrounded
      have hactual :
          Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
            Wasm.IEEE64.roundScaledMagnitude negative rounded := by
        simp [Wasm.IEEE64.roundDyadicMagnitude, hn, outputShift, hzero,
          rounded]
      have hroundError :=
        CodeLib.IEEE32.roundShift_error_cases n 1074 (by omega)
      have herr :
          |((rounded * 2 ^ 1074 : Nat) : Int) - n| ≤
            (2 ^ 1073 : Nat) := by
        have h := CodeLib.IEEE32.abs_int_sub_le_of_error_cases
          _ _ _ hroundError
        norm_num at h ⊢
        exact h
      rw [hactual, hpack.2.1]
      calc
        |((rounded * 2 ^ 1074 : Nat) : Int) - n| * (2 ^ 53 : Int) ≤
            (2 ^ 1073 : Int) * (2 ^ 53 : Int) :=
          mul_le_mul_of_nonneg_right herr (by positivity)
        _ = (2 ^ 1126 : Nat) := by norm_num [← pow_add]
        _ ≤ (if n = 0 then 0 else max n (2 ^ 1126) : Nat) := by
          simp [hn]
    · have hshift : 0 < outputShift := by omega
      have hlogLower : 1127 ≤ Nat.log2 n := by
        simp [outputShift] at hzero
        omega
      have hlogUpper : Nat.log2 n < 2149 :=
        (Nat.log2_lt hn).2 hmax
      have hshiftMax : outputShift ≤ 1022 := by
        simp [outputShift]
        omega
      have hshiftEq : 1126 + outputShift = Nat.log2 n := by
        simp [outputShift]
        omega
      let totalShift := 1074 + outputShift
      let rounded := Wasm.IEEE32.roundShift n totalShift
      let candidate := rounded * 2 ^ outputShift
      have hpowLower : 2 ^ 52 * 2 ^ totalShift ≤ n := by
        rw [pow_mul_pow]
        have heq : 52 + totalShift = Nat.log2 n := by
          simp only [totalShift]
          omega
        rw [heq]
        exact Nat.log2_self_le hn
      have hpowUpper : n < 2 ^ 53 * 2 ^ totalShift := by
        rw [pow_mul_pow]
        have heq : 53 + totalShift = Nat.log2 n + 1 := by
          simp only [totalShift]
          omega
        rw [heq]
        exact Nat.lt_log2_self
      have hquotLower : 2 ^ 52 ≤ n / 2 ^ totalShift :=
        (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
      have hquotUpper : n / 2 ^ totalShift < 2 ^ 53 :=
        (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
      have hroundBounds := CodeLib.IEEE32.roundShift_bounds n totalShift
      have hroundedLower : 2 ^ 52 ≤ rounded := by
        change 2 ^ 52 ≤ Wasm.IEEE32.roundShift n totalShift
        omega
      have hroundedUpper : rounded ≤ 2 ^ 53 := by
        change Wasm.IEEE32.roundShift n totalShift ≤ 2 ^ 53
        omega
      have hrepresentable : roundedMagnitude candidate = candidate :=
        roundedMagnitude_shifted rounded outputShift
          hroundedLower hroundedUpper
      have hcandidateMax : candidate < 2 ^ 1076 := by
        calc
          candidate ≤ 2 ^ 53 * 2 ^ 1022 :=
            Nat.mul_le_mul hroundedUpper
              (Nat.pow_le_pow_right (by omega) hshiftMax)
          _ = 2 ^ 1075 := by rw [← pow_add]
          _ < 2 ^ 1076 := Nat.pow_lt_pow_right (by omega) (by omega)
      have hpack := roundScaledMagnitude_spec negative candidate hcandidateMax
      have hactual :
          Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
            Wasm.IEEE64.roundScaledMagnitude negative candidate := by
        simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, if_neg hn]
        rw [show Nat.log2 n - (1074 + 52) = outputShift by
          simp [outputShift]]
        rw [if_neg hzero]
      have hroundError :=
        CodeLib.IEEE32.roundShift_error_cases n totalShift (by
          simp [totalShift])
      have herrHalf :
          |((rounded * 2 ^ totalShift : Nat) : Int) - n| ≤
            (2 ^ totalShift / 2 : Nat) :=
        CodeLib.IEEE32.abs_int_sub_le_of_error_cases
          _ _ _ hroundError
      have hhalfScaled :
          ((2 ^ totalShift / 2 : Nat) : Int) * (2 ^ 53 : Int) =
            (2 ^ 52 * 2 ^ totalShift : Nat) := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
          (by simp [totalShift] : totalShift ≠ 0)
        rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
        push_cast
        ring
      rw [hactual, hpack.2.1, hrepresentable]
      have hcandidateEq :
          candidate * 2 ^ 1074 = rounded * 2 ^ totalShift := by
        simp [candidate, totalShift, pow_add]
        ring
      rw [hcandidateEq]
      calc
        |((rounded * 2 ^ totalShift : Nat) : Int) - n| *
            (2 ^ 53 : Int) ≤
              ((2 ^ totalShift / 2 : Nat) : Int) * (2 ^ 53 : Int) :=
          mul_le_mul_of_nonneg_right herrHalf (by positivity)
        _ = (2 ^ 52 * 2 ^ totalShift : Nat) := hhalfScaled
        _ ≤ n := by exact_mod_cast hpowLower
        _ ≤ (if n = 0 then 0 else max n (2 ^ 1126) : Nat) := by
          simp [hn]

/-- Binary64 square-root rounding is finite and positive on scaled magnitudes
at most one, with error at most `2^1022` in the common `2^-1074` scale. -/
theorem roundSqrtMagnitude_spec (magnitude : Nat)
    (hbound : magnitude ≤ 2 ^ 1074) :
    Finite (Wasm.IEEE64.roundSqrtMagnitude magnitude) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.roundSqrtMagnitude magnitude) = false ∧
      |(Wasm.IEEE64.scaledMagnitude
            (Wasm.IEEE64.roundSqrtMagnitude magnitude) : ℝ) -
          Real.sqrt (magnitude * 2 ^ 1074)| ≤ (2 : ℝ) ^ 1022 := by
  by_cases hmagnitude : magnitude = 0
  · subst magnitude
    norm_num [Wasm.IEEE64.roundSqrtMagnitude, Finite,
      Wasm.IEEE64.isFinite, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent,
      Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  · let radicand := magnitude * 2 ^ 1074
    let rootFloor := Nat.sqrt radicand
    let outputShift := Nat.log2 rootFloor - 52
    let rounded := Wasm.IEEE32.roundSqrtIntegral radicand outputShift
    let candidate := rounded * 2 ^ outputShift
    have hradicand : radicand ≤ 2 ^ 2148 := by
      calc
        radicand ≤ 2 ^ 1074 * 2 ^ 1074 :=
          Nat.mul_le_mul_right (2 ^ 1074) hbound
        _ = 2 ^ 2148 := by rw [← pow_add]
    have hrootBound : rootFloor ≤ 2 ^ 1074 := by
      calc
        rootFloor ≤ Nat.sqrt (2 ^ 2148) := by
          simpa [rootFloor] using Nat.sqrt_le_sqrt hradicand
        _ = 2 ^ 1074 := by
          rw [show (2 : Nat) ^ 2148 = ((2 : Nat) ^ 1074) ^ 2 by
            rw [pow_two, ← pow_add]]
          exact Nat.sqrt_eq' _
    have hradicandNe : radicand ≠ 0 := by
      simp [radicand, hmagnitude]
    have hrootNe : rootFloor ≠ 0 := by
      intro h
      have hupper := Nat.lt_succ_sqrt' radicand
      simp [rootFloor, h] at hupper
      apply hradicandNe
      omega
    have hrootLt : rootFloor < 2 ^ 1075 :=
      hrootBound.trans_lt (by norm_num)
    have hlogUpper : Nat.log2 rootFloor < 1075 :=
      (Nat.log2_lt hrootNe).2 hrootLt
    have hshiftMax : outputShift ≤ 1022 := by
      simp [outputShift]
      omega
    have hroundBounds :=
      CodeLib.IEEE32.roundSqrtIntegral_bounds radicand outputShift
    change rootFloor / 2 ^ outputShift ≤ rounded ∧
      rounded ≤ rootFloor / 2 ^ outputShift + 1 at hroundBounds
    have hrepresentable : roundedMagnitude candidate = candidate := by
      by_cases hzero : outputShift = 0
      · have hlog : Nat.log2 rootFloor ≤ 52 := by
          simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
        have hrootLt53 : rootFloor < 2 ^ 53 := by
          have hself : rootFloor < 2 ^ (Nat.log2 rootFloor + 1) :=
            Nat.lt_log2_self
          exact hself.trans_le
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hroundedUpper : rounded ≤ 2 ^ 53 := by
          simp [hzero] at hroundBounds
          omega
        simp [candidate, hzero, roundedMagnitude_eq_self hroundedUpper]
      · have hshiftPos : 0 < outputShift := Nat.pos_of_ne_zero hzero
        have hshiftEq : 52 + outputShift = Nat.log2 rootFloor := by
          simp [outputShift]
          omega
        have hpowLower : 2 ^ 52 * 2 ^ outputShift ≤ rootFloor := by
          rw [← pow_add, hshiftEq]
          exact Nat.log2_self_le hrootNe
        have hpowUpper : rootFloor < 2 ^ 53 * 2 ^ outputShift := by
          rw [← pow_add]
          have heq : 53 + outputShift = Nat.log2 rootFloor + 1 := by
            rw [← hshiftEq]
            omega
          rw [heq]
          exact Nat.lt_log2_self
        have hquotientLower :
            2 ^ 52 ≤ rootFloor / 2 ^ outputShift :=
          (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
        have hquotientUpper :
            rootFloor / 2 ^ outputShift < 2 ^ 53 :=
          (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
        exact roundedMagnitude_shifted rounded outputShift
          (by omega) (by omega)
    have hcandidateMax : candidate < 2 ^ 1076 := by
      by_cases hzero : outputShift = 0
      · have hlog : Nat.log2 rootFloor ≤ 52 := by
          simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
        have hrootLt53 : rootFloor < 2 ^ 53 := by
          exact Nat.lt_log2_self.trans_le
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hroundedUpper : rounded ≤ 2 ^ 53 := by
          simp [hzero] at hroundBounds
          omega
        simp [candidate, hzero]
        exact hroundedUpper.trans_lt (by norm_num)
      · have hroundedUpper : rounded ≤ 2 ^ 53 := by
          have hshiftPos : 0 < outputShift := Nat.pos_of_ne_zero hzero
          have hshiftEq : 52 + outputShift = Nat.log2 rootFloor := by
            simp [outputShift]
            omega
          have hpowUpper : rootFloor < 2 ^ 53 * 2 ^ outputShift := by
            rw [← pow_add]
            have heq : 53 + outputShift = Nat.log2 rootFloor + 1 := by
              rw [← hshiftEq]
              omega
            rw [heq]
            exact Nat.lt_log2_self
          have hquotientUpper :
              rootFloor / 2 ^ outputShift < 2 ^ 53 :=
            (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
          omega
        calc
          candidate ≤ 2 ^ 53 * 2 ^ 1022 :=
            Nat.mul_le_mul hroundedUpper
              (Nat.pow_le_pow_right (by omega) hshiftMax)
          _ = 2 ^ 1075 := by rw [← pow_add]
          _ < 2 ^ 1076 := Nat.pow_lt_pow_right (by omega) (by omega)
    have hpack := roundScaledMagnitude_spec false candidate hcandidateMax
    have hsign := sign_roundScaledMagnitude false candidate hcandidateMax
    have hactual : Wasm.IEEE64.roundSqrtMagnitude magnitude =
        Wasm.IEEE64.roundScaledMagnitude false candidate := by
      simp only [Wasm.IEEE64.roundSqrtMagnitude, beq_iff_eq,
        if_neg hmagnitude]
      rfl
    have herrHalf :=
      CodeLib.IEEE32.roundSqrtIntegral_real_error radicand outputShift
    have hhalf : (2 : ℝ) ^ outputShift / 2 ≤ (2 : ℝ) ^ 1022 := by
      calc
        (2 : ℝ) ^ outputShift / 2 ≤ (2 : ℝ) ^ outputShift := by
          have hp : 0 ≤ (2 : ℝ) ^ outputShift := by positivity
          linarith
        _ ≤ (2 : ℝ) ^ 1022 :=
          pow_le_pow_right₀ (by norm_num) hshiftMax
    have herr : |(candidate : ℝ) - Real.sqrt radicand| ≤
        (2 : ℝ) ^ 1022 := by
      have := herrHalf.trans hhalf
      simpa only [candidate, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        using this
    rw [hactual]
    refine ⟨hpack.1, hsign, ?_⟩
    rw [hpack.2.1, hrepresentable]
    simpa only [radicand, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      using herr

#print axioms roundDyadicMagnitude1074_spec
#print axioms roundDyadicMagnitude1074_adaptive_spec
#print axioms roundRationalMagnitude_spec
#print axioms roundSqrtMagnitude_spec

end CodeLib.IEEE64
