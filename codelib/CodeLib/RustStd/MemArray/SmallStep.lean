import CodeLib.RustStd.MemArray
import Interpreter.Wasm.SmallStep

/-!
# Relational small-step rules for memory-resident arrays

This module connects the `Mem.words64` array view to the authoritative Wasm
small-step relation without depending on a program-logic layer.  It packages
the address, readback, and physical-memory obligations needed by an indexed
`f64.load`, so loop proofs can reuse one exact transition theorem.
-/

namespace Wasm

/-- The address and word observed at an in-range `words64` slot.  The array
bound excludes 32-bit address wraparound. -/
theorem Mem.words64_slot_address_and_read
    (m : Mem) (base : UInt32) (n k : Nat)
    (hk : k < n)
    (hfit : base.toNat + 8 * n ≤ UInt32.size) :
    let address := base + 8 * UInt32.ofNat k
    address.toNat = base.toNat + 8 * k ∧
      m.read64 address =
        (m.words64 base n)[k]'(by simpa using hk) := by
  dsimp only
  have haddress :
      (base + 8 * UInt32.ofNat k).toNat = base.toNat + 8 * k :=
    Mem.words64_slotAddr_toNat base k (by
      simp only [UInt32.size] at hfit ⊢
      omega)
  constructor
  · exact haddress
  · rw [Mem.getElem_words64 m base n k hk]

/-- Every in-range slot of an address-safe array is physically loadable when
the complete array lies within the current linear-memory capacity. -/
theorem Mem.words64_slot_inBounds
    (base : UInt32) (n k capacity : Nat)
    (hk : k < n)
    (hfit : base.toNat + 8 * n ≤ UInt32.size)
    (hcapacity : base.toNat + 8 * n ≤ capacity) :
    (base + 8 * UInt32.ofNat k).toNat + 8 ≤ capacity := by
  rw [Mem.words64_slotAddr_toNat base k (by
    simp only [UInt32.size] at hfit ⊢
    omega)]
  omega

namespace SmallStep

/-- Exact authoritative `f64.load` transition for the `k`-th word in a
`Mem.words64` view.  The result is the stored IEEE-754 bit pattern, the machine
store is unchanged, and both address-space and physical-memory safety are
explicit hypotheses. -/
theorem f64Load_words64
    {α : Type} (store : MachineStore α)
    {params localValues values : List Value}
    (base : UInt32) (n k : Nat)
    (hk : k < n)
    (hfit : base.toNat + 8 * n ≤ UInt32.size)
    (hcapacity : base.toNat + 8 * n ≤ store.wasm.mem.pages * 65536)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let address := base + 8 * UInt32.ofNat k
    Step
      ⟨.running
        ⟨⟨params, localValues, .i32 address :: values⟩,
          .f64Load 0 :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f64Load 0))
      ⟨.running
        ⟨⟨params, localValues,
            .f64 ((store.wasm.mem.words64 base n)[k]'(by
              simpa using hk)) :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store⟩ := by
  dsimp only
  let address := base + 8 * UInt32.ofNat k
  have hfacts := Mem.words64_slot_address_and_read
    store.wasm.mem base n k hk hfit
  have hbound : address.toNat + (0 : UInt32).toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    dsimp only [address]
    have := Mem.words64_slot_inBounds base n k
      (store.wasm.mem.pages * 65536) hk hfit hcapacity
    simpa using this
  have hstep := Step.f64Load
    (α := α) (store := store) (address := Value.i32 address)
    (offset := 0) (logicalAddress := address.toNat)
    (physicalAddress := address)
    (params := params) (localValues := localValues) (values := values)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (SmallStep.memoryAddress?_i32_eq address) hbound
  have hread : store.wasm.mem.read64 (address + 0) =
      (store.wasm.mem.words64 base n)[k]'(by simpa using hk) := by
    rw [UInt32.add_zero]
    exact hfacts.2
  simpa only [address, hread] using hstep

#print axioms Mem.words64_slot_address_and_read
#print axioms Mem.words64_slot_inBounds
#print axioms f64Load_words64

end SmallStep
end Wasm
