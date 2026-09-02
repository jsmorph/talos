import CodeLib.IEEE64.Roundoff

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

#print axioms roundDyadicMagnitude1074_spec

end CodeLib.IEEE64
