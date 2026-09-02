import CodeLib.IEEE32.Conversions

open Wasm

/-!
Compatibility names and range lemmas used by the generated `float_trunc`
proof.  The authoritative implementation is now the proof-visible
`Wasm.IEEE32` model; the old helper names are aliases, and their compatibility
results are ordinary reflexivity theorems rather than trusted bridges.
-/

namespace IEEE32Exec

/-! ## Compatibility aliases -/

def isNaN (x : UInt32) : Bool := Wasm.IEEE32.isNaN x
def beq (a b : UInt32) : Bool := Wasm.IEEE32.eq a b
def blt (a b : UInt32) : Bool := Wasm.IEEE32.lt a b
def ble (a b : UInt32) : Bool := Wasm.IEEE32.le a b
def satI32S (x : UInt32) : UInt32 := Wasm.IEEE32.truncSatI32S x

theorem beq_ax (a b : UInt32) :
    Wasm.IEEE32.eq a b = beq a b
  := rfl

theorem isNaN_ax (a : UInt32) :
    Wasm.IEEE32.isNaN a = isNaN a
  := rfl

theorem ble_ax (a b : UInt32) :
    Wasm.IEEE32.le a b = ble a b
  := rfl

theorem blt_ax (a b : UInt32) :
    Wasm.IEEE32.lt a b = blt a b
  := rfl

theorem satI32S_eq (a : UInt32) :
    i32TruncSatF32S a = satI32S a
  := rfl

/-! ## Theorems used by `FloatTrunc.Spec` -/

theorem f32Ne_self_iff_isNaN (x : UInt32) :
    f32Ne x x = Wasm.IEEE32.isNaN x := by
  simp [f32Ne, Wasm.IEEE32.eq]

theorem i32TruncSatF32S_large_pos {x : UInt32}
    (hnan : f32Ne x x = false)
    (hge : f32Ge x 1325400064 = true) :
    i32TruncSatF32S x = 0x7FFFFFFF := by
  have hnotNaN : Wasm.IEEE32.isNaN x = false := by
    rw [← f32Ne_self_iff_isNaN x]
    exact hnan
  have hthresholdNaN : Wasm.IEEE32.isNaN 1325400064 = false := by decide
  have hthresholdValue :
      Wasm.IEEE32.scaledValue 1325400064 = (2 : Int) ^ 180 := by decide
  have hvalue : (2 : Int) ^ 180 ≤ Wasm.IEEE32.scaledValue x := by
    simpa [f32Ge, Wasm.IEEE32.le, hnotNaN, hthresholdNaN,
      hthresholdValue] using hge
  by_cases hfinite : Wasm.IEEE32.isFinite x = true
  · have hsign : Wasm.IEEE32.sign x = false := by
      cases hs : Wasm.IEEE32.sign x
      · rfl
      · simp [Wasm.IEEE32.scaledValue, hs] at hvalue
        omega
    have hmag : 2 ^ 180 ≤ Wasm.IEEE32.scaledMagnitude x := by
      simp [Wasm.IEEE32.scaledValue, hsign] at hvalue
      exact_mod_cast hvalue
    have hquot :
        2 ^ 31 ≤ Wasm.IEEE32.scaledMagnitude x / 2 ^ 149 := by
      apply (Nat.le_div_iff_mul_le (by positivity)).2
      norm_num [pow_add] at hmag ⊢
      exact hmag
    have hquotInt :
        (2 : Int) ^ 31 ≤
          (Wasm.IEEE32.scaledMagnitude x : Int) / (2 : Int) ^ 149 := by
      exact_mod_cast hquot
    norm_num at hquotInt
    simp only [i32TruncSatF32S, Wasm.IEEE32.truncSatI32S, hnotNaN,
      Bool.false_eq_true, if_false, Wasm.IEEE32.truncatedInt, hfinite,
      if_true, hsign]
    split
    · rename_i hlow
      omega
    · split
      · rfl
      · rename_i hhigh
        omega
  · have hsign : Wasm.IEEE32.sign x = false := by
      cases hs : Wasm.IEEE32.sign x
      · rfl
      · simp [Wasm.IEEE32.scaledValue, hs] at hvalue
        omega
    simp [i32TruncSatF32S, Wasm.IEEE32.truncSatI32S, hnotNaN,
      Wasm.IEEE32.truncatedInt, hfinite, hsign]

theorem i32TruncSatF32S_large_neg {x : UInt32}
    (hnan : f32Ne x x = false)
    (hlt : f32Lt x 3472883712 = true) :
    i32TruncSatF32S x = 0x80000000 := by
  have hnotNaN : Wasm.IEEE32.isNaN x = false := by
    rw [← f32Ne_self_iff_isNaN x]
    exact hnan
  have hthresholdNaN : Wasm.IEEE32.isNaN 3472883712 = false := by decide
  have hthresholdValue :
      Wasm.IEEE32.scaledValue 3472883712 = -((2 : Int) ^ 180) := by decide
  have hvalue : Wasm.IEEE32.scaledValue x < -((2 : Int) ^ 180) := by
    simpa [f32Lt, Wasm.IEEE32.lt, hnotNaN, hthresholdNaN,
      hthresholdValue] using hlt
  by_cases hfinite : Wasm.IEEE32.isFinite x = true
  · have hsign : Wasm.IEEE32.sign x = true := by
      cases hs : Wasm.IEEE32.sign x
      · simp [Wasm.IEEE32.scaledValue, hs] at hvalue
        omega
      · rfl
    have hmag : 2 ^ 180 < Wasm.IEEE32.scaledMagnitude x := by
      simp [Wasm.IEEE32.scaledValue, hsign] at hvalue
      simpa using hvalue
    have hquot :
        2 ^ 31 ≤ Wasm.IEEE32.scaledMagnitude x / 2 ^ 149 := by
      apply (Nat.le_div_iff_mul_le (by positivity)).2
      norm_num [pow_add] at hmag ⊢
      omega
    have hquotInt :
        (2 : Int) ^ 31 ≤
          (Wasm.IEEE32.scaledMagnitude x : Int) / (2 : Int) ^ 149 := by
      exact_mod_cast hquot
    norm_num at hquotInt
    simp only [i32TruncSatF32S, Wasm.IEEE32.truncSatI32S, hnotNaN,
      Bool.false_eq_true, if_false, Wasm.IEEE32.truncatedInt, hfinite,
      if_true, hsign]
    split
    · rfl
    · rename_i hlow
      omega
  · have hsign : Wasm.IEEE32.sign x = true := by
      cases hs : Wasm.IEEE32.sign x
      · simp [Wasm.IEEE32.scaledValue, hs] at hvalue
        omega
      · rfl
    simp [i32TruncSatF32S, Wasm.IEEE32.truncSatI32S, hnotNaN,
      Wasm.IEEE32.truncatedInt, hfinite, hsign]

#print axioms beq_ax
#print axioms isNaN_ax
#print axioms ble_ax
#print axioms blt_ax
#print axioms satI32S_eq
#print axioms i32TruncSatF32S_large_pos
#print axioms i32TruncSatF32S_large_neg

end IEEE32Exec
