import Project.F64Dot.Program
import CodeLib.Numerical.Kernels
import CodeLib.RustStd.MemArray.SmallStep
import Interpreter.Wasm.MeasureTermination
import Mathlib.Tactic

/-!
# Total small-step execution of the generated `f64_dot` loop

The proof in this file is entirely relational.  It follows the exact decoded
body in `Project.F64Dot.func0`, uses the pure IEEE64 operations selected by the
authoritative small-step semantics, and proves that every load-only execution
preserves the complete machine store.
-/

namespace Project.F64Dot.Proof

open Wasm Wasm.SmallStep

private def zeroLengthBody : Program :=
  [.localGet 2, .br_if 0, .f64Const 0, .ret]

private def loopBody : Program :=
  [.localGet 3,
   .localGet 0, .f64Load 0,
   .localGet 1, .f64Load 0,
   .f64Mul, .f64Add, .localSet 3,
   .localGet 0, .const 8, .add, .localSet 0,
   .localGet 1, .const 8, .add, .localSet 1,
   .localGet 2, .const 4294967295, .add, .localTee 2,
   .br_if 0]

private def tailBody : Program :=
  [.localGet 2, .const 1, .eq, .br_if 0,
   .localGet 0, .const 8, .add, .localSet 0,
   .localGet 1, .const 8, .add, .localSet 1,
   .localGet 2, .const 4294967295, .add, .localSet 2,
   .loop 0 0 loopBody]

private def afterZeroLength : Program :=
  [.localGet 0, .f64Load 0,
   .localGet 1, .f64Load 0,
   .f64Mul, .localSet 3,
   .block 0 0 tailBody,
   .localGet 3]

private theorem func0_shape :
    Project.F64Dot.func0 =
      [.block 0 0 zeroLengthBody] ++ afterZeroLength := by
  rfl

private def tailFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := tailBody
    continuation := [.localGet 3]
    belowStack := [] }

private def loopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := loopBody
    continuation := []
    belowStack := [] }

private def machineStore (wasm : Store Unit) : MachineStore Unit :=
  { runtime :=
      { instances :=
          #[{ module := Project.F64Dot.«module», host := {} }]
        entry := ⟨0⟩ }
    wasm }

/-- Direct entry to the exact generated function body over an arbitrary Wasm
store.  The argument order here is ABI order; `initConfig`'s operand-stack
order is connected below. -/
def configFromStore (wasm : Store Unit) (left right count : UInt32) :
    Config Unit :=
  { expr := .running
      ⟨⟨[.i32 left, .i32 right, .i32 count], [.f64 0], []⟩,
        Project.F64Dot.func0, 1, [], [], []⟩
    store := machineStore wasm }

/-- `configFromStore` is exactly the standard single-module entry
configuration.  The external value list is in operand-stack order, hence the
reverse ABI order `count`, `right`, `left`. -/
theorem initConfig_eq_configFromStore
    (wasm : Store Unit) (left right count : UInt32) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 count, .i32 right, .i32 left] =
      .ok (configFromStore wasm left right count) := by
  simp [initConfig, Project.F64Dot.«module», Project.F64Dot.func0Def,
    Function.numParams, Function.toLocals, ValueType.zero,
    configFromStore, machineStore]

private theorem nextAddress (base : UInt32) (index : Nat) :
    8 + (base + 8 * UInt32.ofNat index) =
      base + 8 * UInt32.ofNat (index + 1) := by
  rw [UInt32.ofNat_add, UInt32.mul_add]
  simp
  ac_rfl

private theorem decrementCount {remaining : Nat} (hpositive : 0 < remaining) :
    4294967295 + UInt32.ofNat remaining =
      UInt32.ofNat (remaining - 1) := by
  have hremaining : remaining - 1 + 1 = remaining := by omega
  have hofNat :
      UInt32.ofNat remaining = UInt32.ofNat (remaining - 1) + 1 := by
    rw [← hremaining, UInt32.ofNat_add]
    rfl
  have hmax : (4294967295 : UInt32) + 1 = 0 := by decide
  rw [hofNat]
  calc
    (4294967295 : UInt32) + (UInt32.ofNat (remaining - 1) + 1) =
        UInt32.ofNat (remaining - 1) + (4294967295 + 1) := by ac_rfl
    _ = UInt32.ofNat (remaining - 1) := by rw [hmax, UInt32.add_zero]

private theorem ofNat_ne_zero {n : Nat} (hpositive : 0 < n)
    (hsize : n < UInt32.size) : UInt32.ofNat n ≠ 0 := by
  intro hzero
  have := congrArg UInt32.toNat hzero
  rw [UInt32.toNat_ofNat_of_lt' hsize] at this
  simp only [UInt32.toNat_zero] at this
  omega

private theorem ofNat_ne_one {n : Nat} (htwo : 2 ≤ n)
    (hsize : n < UInt32.size) : UInt32.ofNat n ≠ 1 := by
  intro hone
  have := congrArg UInt32.toNat hone
  rw [UInt32.toNat_ofNat_of_lt' hsize] at this
  simp at this
  omega

private theorem dot64Acc_append (accumulator : UInt64)
    (initial suffix : List (UInt64 × UInt64)) :
    CodeLib.Numerical.Kernels.dot64Acc accumulator (initial ++ suffix) =
      CodeLib.Numerical.Kernels.dot64Acc
        (CodeLib.Numerical.Kernels.dot64Acc accumulator initial) suffix := by
  induction initial generalizing accumulator with
  | nil => rfl
  | cons term tail ih =>
      rcases term with ⟨a, b⟩
      simpa [CodeLib.Numerical.Kernels.dot64Acc] using
        ih (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b))

private theorem dot64Acc_take_succ (accumulator : UInt64)
    (terms : List (UInt64 × UInt64)) (k : Nat) (hk : k < terms.length) :
    CodeLib.Numerical.Kernels.dot64Acc accumulator (terms.take (k + 1)) =
      Wasm.IEEE64.add
        (CodeLib.Numerical.Kernels.dot64Acc accumulator (terms.take k))
        (Wasm.IEEE64.mul terms[k].1 terms[k].2) := by
  rw [List.take_succ_eq_append_getElem hk, dot64Acc_append]
  rfl

private theorem f64Load_words64_zero
    (store : MachineStore Unit)
    {params localValues values : List Value}
    (base : UInt32) (n : Nat) (hn : 0 < n)
    (hfit : base.toNat + 8 * n ≤ UInt32.size)
    (hcapacity : base.toNat + 8 * n ≤ store.wasm.mem.pages * 65536)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    Step
      ⟨.running
        ⟨⟨params, localValues, .i32 base :: values⟩,
          .f64Load 0 :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f64Load 0))
      ⟨.running
        ⟨⟨params, localValues,
            .f64 ((store.wasm.mem.words64 base n)[0]!) :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store⟩ := by
  have hindex : 0 < (store.wasm.mem.words64 base n).length := by
    simpa using hn
  rw [getElem!_pos _ 0 hindex]
  simpa using f64Load_words64 store base n 0 (by omega) hfit hcapacity

/-- Variant of `f64Load_words64` whose conclusion names the element through a
caller-supplied array-view equality.  This hides dependent `getElem` proof
terms before a long explicit trace starts simplifying local updates. -/
private theorem f64Load_words64_of_eq
    (store : MachineStore Unit)
    {params localValues values : List Value}
    (base : UInt32) (n k : Nat) (expected : UInt64)
    (hk : k < n)
    (hfit : base.toNat + 8 * n ≤ UInt32.size)
    (hcapacity : base.toNat + 8 * n ≤ store.wasm.mem.pages * 65536)
    (helement :
      (store.wasm.mem.words64 base n)[k]'(by simpa using hk) = expected)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    Step
      ⟨.running
        ⟨⟨params, localValues,
            .i32 (base + 8 * UInt32.ofNat k) :: values⟩,
          .f64Load 0 :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f64Load 0))
      ⟨.running
        ⟨⟨params, localValues, .f64 expected :: values⟩,
          code, arity, remainder, controls, calls⟩,
        store⟩ := by
  have hload := f64Load_words64 store
    (params := params) (localValues := localValues) (values := values)
    base n k hk hfit hcapacity (code := code) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls)
  rw [helement] at hload
  exact hload

private theorem zero_steps (wasm : Store Unit) (left right : UInt32) :
    Steps (configFromStore wasm left right 0)
      [.instruction (.block 0 0 zeroLengthBody),
       .instruction (.localGet 2),
       .instruction (.br_if 0),
       .instruction (.f64Const 0),
       .administrative .returnFromFunction]
      ⟨.done [.f64 0], machineStore wasm⟩ := by
  simp only [configFromStore, func0_shape, List.cons_append,
    List.nil_append, zeroLengthBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .brIfZero
  apply Steps.cons (.scalarFloat0 rfl)
  exact Steps.single .returnFromFunction

private def afterFirstConfig (wasm : Store Unit) (left right count : UInt32)
    (accumulator : UInt64) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 left, .i32 right, .i32 count], [.f64 accumulator], []⟩,
        [.block 0 0 tailBody, .localGet 3], 1, [], [], []⟩
    store := machineStore wasm }

private theorem first_steps (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left (rest.length + 1) =
        first.1 :: rest.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right (rest.length + 1) =
        first.2 :: rest.map Prod.snd)
    (hleftFit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536) :
    Steps
      (configFromStore wasm left right (UInt32.ofNat (rest.length + 1)))
      [.instruction (.block 0 0 zeroLengthBody),
       .instruction (.localGet 2),
       .instruction (.br_if 0),
       .instruction (.localGet 0),
       .instruction (.f64Load 0),
       .instruction (.localGet 1),
       .instruction (.f64Load 0),
       .instruction .f64Mul,
       .instruction (.localSet 3)]
      (afterFirstConfig wasm left right (UInt32.ofNat (rest.length + 1))
        (Wasm.IEEE64.mul first.1 first.2)) := by
  have hlengthSize : rest.length + 1 < UInt32.size := by
    simp only [UInt32.size] at hleftFit ⊢
    omega
  have hcountNonzero : UInt32.ofNat (rest.length + 1) ≠ 0 :=
    ofNat_ne_zero (by omega) hlengthSize
  simp only [configFromStore, func0_shape, List.cons_append,
    List.nil_append, zeroLengthBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.brIf hcountNonzero (by rfl))
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (f64Load_words64_zero (machineStore wasm)
    left (rest.length + 1) (by omega) hleftFit hleftCapacity)
  simp only [machineStore, hleftView]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (f64Load_words64_zero (machineStore wasm)
    right (rest.length + 1) (by omega) hrightFit hrightCapacity)
  simp only [machineStore, hrightView]
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localSet rfl)
  simpa [afterFirstConfig, machineStore, Wasm.f64Mul] using
    (Steps.refl
      (afterFirstConfig wasm left right (UInt32.ofNat (rest.length + 1))
        (Wasm.IEEE64.mul first.1 first.2)))

private theorem oneTerm_steps (wasm : Store Unit) (left right : UInt32)
    (accumulator : UInt64) :
    Steps (afterFirstConfig wasm left right 1 accumulator)
      [.instruction (.block 0 0 tailBody),
       .instruction (.localGet 2),
       .instruction (.const 1),
       .instruction .eq,
       .instruction (.br_if 0),
       .instruction (.localGet 3),
       .administrative .finish]
      ⟨.done [.f64 accumulator], machineStore wasm⟩ := by
  simp only [afterFirstConfig, tailBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons (.eq (result := 1) rfl)
  apply Steps.cons (.brIf (by decide) (by rfl))
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

/-- The exact machine state at a loop back-edge.  `k` tail terms have already
been accumulated, the pointers address tail term `k`, and the live counter is
the number of tail terms still to execute. -/
private def loopHead (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (k : Nat) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 (left + 8 * UInt32.ofNat (k + 1)),
          .i32 (right + 8 * UInt32.ofNat (k + 1)),
          .i32 (UInt32.ofNat (rest.length - k))],
         [.f64 (CodeLib.Numerical.Kernels.dot64Acc
            (Wasm.IEEE64.mul first.1 first.2) (rest.take k))], []⟩,
        loopBody, 1, [], [loopFrame, tailFrame], []⟩
    store := machineStore wasm }

private theorem enterLoop_steps (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (hrest : rest ≠ [])
    (hfit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size) :
    Steps
      (afterFirstConfig wasm left right (UInt32.ofNat (rest.length + 1))
        (Wasm.IEEE64.mul first.1 first.2))
      [.instruction (.block 0 0 tailBody),
       .instruction (.localGet 2),
       .instruction (.const 1),
       .instruction .eq,
       .instruction (.br_if 0),
       .instruction (.localGet 0),
       .instruction (.const 8),
       .instruction .add,
       .instruction (.localSet 0),
       .instruction (.localGet 1),
       .instruction (.const 8),
       .instruction .add,
       .instruction (.localSet 1),
       .instruction (.localGet 2),
       .instruction (.const 4294967295),
       .instruction .add,
       .instruction (.localSet 2),
       .instruction (.loop 0 0 loopBody)]
      (loopHead wasm left right first rest 0) := by
  have hrestPositive : 0 < rest.length := by
    cases rest with
    | nil => contradiction
    | cons => simp
  have hlengthSize : rest.length + 1 < UInt32.size := by
    simp only [UInt32.size] at hfit ⊢
    omega
  have hrestSize : rest.length < UInt32.size := by omega
  have hrestNonzero : UInt32.ofNat rest.length ≠ 0 :=
    ofNat_ne_zero hrestPositive hrestSize
  have hleftNext :
      8 + left = left + 8 * UInt32.ofNat (0 + 1) := by
    simpa using nextAddress left 0
  have hrightNext :
      8 + right = right + 8 * UInt32.ofNat (0 + 1) := by
    simpa using nextAddress right 0
  have hcountNext :
      4294967295 + UInt32.ofNat (rest.length + 1) =
        UInt32.ofNat rest.length := by
    simpa using decrementCount (remaining := rest.length + 1) (by omega)
  simp only [afterFirstConfig, tailBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons (.eq (result := 0) (by simp [hrestNonzero]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons .loop
  rw [hleftNext, hrightNext, hcountNext]
  exact Steps.refl (loopHead wasm left right first rest 0)

/-- State immediately before the loop's closing `br_if`.  Keeping this state
explicit lets the common load/multiply/add prefix serve both the back-edge and
the final fall-through iteration. -/
private def afterIteration (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (k : Nat) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 (left + 8 * UInt32.ofNat (k + 2)),
          .i32 (right + 8 * UInt32.ofNat (k + 2)),
          .i32 (UInt32.ofNat (rest.length - (k + 1)))],
         [.f64 (CodeLib.Numerical.Kernels.dot64Acc
            (Wasm.IEEE64.mul first.1 first.2) (rest.take (k + 1)))],
         [.i32 (UInt32.ofNat (rest.length - (k + 1)))]⟩,
        [.br_if 0], 1, [], [loopFrame, tailFrame], []⟩
    store := machineStore wasm }

private theorem iteration_prefix_steps
    (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (k : Nat) (hk : k < rest.length)
    (hleftView :
      wasm.mem.words64 left (rest.length + 1) =
        first.1 :: rest.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right (rest.length + 1) =
        first.2 :: rest.map Prod.snd)
    (hleftFit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536) :
    Steps (loopHead wasm left right first rest k)
      [.instruction (.localGet 3),
       .instruction (.localGet 0),
       .instruction (.f64Load 0),
       .instruction (.localGet 1),
       .instruction (.f64Load 0),
       .instruction .f64Mul,
       .instruction .f64Add,
       .instruction (.localSet 3),
       .instruction (.localGet 0),
       .instruction (.const 8),
       .instruction .add,
       .instruction (.localSet 0),
       .instruction (.localGet 1),
       .instruction (.const 8),
       .instruction .add,
       .instruction (.localSet 1),
       .instruction (.localGet 2),
       .instruction (.const 4294967295),
       .instruction .add,
       .instruction (.localTee 2)]
      (afterIteration wasm left right first rest k) := by
  have hslot : k + 1 < rest.length + 1 := by omega
  have hremaining : 0 < rest.length - k := by omega
  have hleftNext :
      8 + (left + 8 * UInt32.ofNat (k + 1)) =
        left + 8 * UInt32.ofNat (k + 2) := by
    exact nextAddress left (k + 1)
  have hrightNext :
      8 + (right + 8 * UInt32.ofNat (k + 1)) =
        right + 8 * UInt32.ofNat (k + 2) := by
    exact nextAddress right (k + 1)
  have hcountNext :
      4294967295 + UInt32.ofNat (rest.length - k) =
        UInt32.ofNat (rest.length - (k + 1)) := by
    rw [decrementCount hremaining]
    congr 1
  have haccumulatorNext :
      Wasm.IEEE64.add
          (CodeLib.Numerical.Kernels.dot64Acc
            (Wasm.IEEE64.mul first.1 first.2) (rest.take k))
          (Wasm.IEEE64.mul rest[k].1 rest[k].2) =
        CodeLib.Numerical.Kernels.dot64Acc
          (Wasm.IEEE64.mul first.1 first.2) (rest.take (k + 1)) := by
    exact (dot64Acc_take_succ _ rest k hk).symm
  simp only [loopHead, loopBody]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (f64Load_words64_of_eq (machineStore wasm)
    left (rest.length + 1) (k + 1) rest[k].1 hslot hleftFit hleftCapacity (by
      simp only [machineStore, hleftView, List.getElem_cons_succ,
        List.getElem_map]))
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (f64Load_words64_of_eq (machineStore wasm)
    right (rest.length + 1) (k + 1) rest[k].2 hslot hrightFit hrightCapacity (by
      simp only [machineStore, hrightView, List.getElem_cons_succ,
        List.getElem_map]))
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localTee rfl)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set, Wasm.f64Add, Wasm.f64Mul]
  rw [hleftNext, hrightNext, hcountNext, haccumulatorNext]
  exact Steps.refl (afterIteration wasm left right first rest k)

private theorem continue_iteration_steps
    (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (k : Nat) (hnext : k + 1 < rest.length)
    (hleftView :
      wasm.mem.words64 left (rest.length + 1) =
        first.1 :: rest.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right (rest.length + 1) =
        first.2 :: rest.map Prod.snd)
    (hleftFit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536) :
    ∃ trace, Steps (loopHead wasm left right first rest k) trace
      (loopHead wasm left right first rest (k + 1)) := by
  have hk : k < rest.length := by omega
  have hremainingPositive : 0 < rest.length - (k + 1) := by omega
  have hremainingSize : rest.length - (k + 1) < UInt32.size := by
    simp only [UInt32.size] at hleftFit ⊢
    omega
  have hremainingNonzero :
      UInt32.ofNat (rest.length - (k + 1)) ≠ 0 :=
    ofNat_ne_zero hremainingPositive hremainingSize
  have hprefix := iteration_prefix_steps wasm left right first rest k hk
    hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
  have backEdge :
      Steps (afterIteration wasm left right first rest k)
        [.instruction (.br_if 0)]
        (loopHead wasm left right first rest (k + 1)) := by
    simp only [afterIteration, loopHead]
    exact Steps.single (.brIf hremainingNonzero (by rfl))
  exact ⟨_, hprefix.trans backEdge⟩

private theorem final_iteration_steps
    (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (k : Nat) (hk : k < rest.length) (hlast : k + 1 = rest.length)
    (hleftView :
      wasm.mem.words64 left (rest.length + 1) =
        first.1 :: rest.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right (rest.length + 1) =
        first.2 :: rest.map Prod.snd)
    (hleftFit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536) :
    ∃ trace, Steps (loopHead wasm left right first rest k) trace
      ⟨.done [.f64 (CodeLib.Numerical.Kernels.dot64
        first rest)], machineStore wasm⟩ := by
  have hprefix := iteration_prefix_steps wasm left right first rest k hk
    hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
  have suffix :
      Steps (afterIteration wasm left right first rest k)
        [.instruction (.br_if 0),
         .administrative .exitControl,
         .administrative .exitControl,
         .instruction (.localGet 3),
         .administrative .finish]
        ⟨.done [.f64 (CodeLib.Numerical.Kernels.dot64
          first rest)], machineStore wasm⟩ := by
    simp only [afterIteration, hlast, Nat.sub_self,
      List.take_length, CodeLib.Numerical.Kernels.dot64]
    apply Steps.cons .brIfZero
    apply Steps.cons (.exitControl rfl)
    apply Steps.cons (.exitControl rfl)
    apply Steps.cons (.localGet rfl)
    exact Steps.single .finish
  exact ⟨_, hprefix.trans suffix⟩

private def loopFamilyConfig (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64)) :
    Option (Fin rest.length) → Config Unit
  | none =>
      ⟨.done [.f64 (CodeLib.Numerical.Kernels.dot64 first rest)],
        machineStore wasm⟩
  | some k => loopHead wasm left right first rest k.val

private def loopFamilyMeasure (rest : List (UInt64 × UInt64)) :
    Option (Fin rest.length) → Nat
  | none => 0
  | some k => rest.length - k.val

private theorem loopHead_terminates
    (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (hrest : rest ≠ [])
    (hleftView :
      wasm.mem.words64 left (rest.length + 1) =
        first.1 :: rest.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right (rest.length + 1) =
        first.2 :: rest.map Prod.snd)
    (hleftFit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536) :
    TerminatesWith (loopHead wasm left right first rest 0)
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64 first rest)] ∧
          store = machineStore wasm) := by
  have hrestPositive : 0 < rest.length := by
    cases rest with
    | nil => contradiction
    | cons => simp
  let post := fun (_ : Option (Fin rest.length))
      (values : List Value) (store : MachineStore Unit) =>
    values = [.f64 (CodeLib.Numerical.Kernels.dot64 first rest)] ∧
      store = machineStore wasm
  have familyTerminates :
      TerminatesWith
        (loopFamilyConfig wasm left right first rest
          (some ⟨0, hrestPositive⟩))
        (post (some ⟨0, hrestPositive⟩)) := by
    refine terminatesWith_of_loop
      (configs := loopFamilyConfig wasm left right first rest)
      (μ := loopFamilyMeasure rest)
      (post := post) ?exit ?iterate (some ⟨0, hrestPositive⟩)
    case exit =>
      intro index hzero
      cases index with
      | none =>
          exact TerminatesWith.done ⟨rfl, rfl⟩
      | some k =>
          simp only [loopFamilyMeasure] at hzero
          have hk := k.isLt
          omega
    case iterate =>
      intro index hnonzero
      cases index with
      | none =>
          simp [loopFamilyMeasure] at hnonzero
      | some k =>
          by_cases hnext : k.val + 1 < rest.length
          · obtain ⟨trace, htrace⟩ := continue_iteration_steps
              wasm left right first rest k.val hnext hleftView hrightView
              hleftFit hrightFit hleftCapacity hrightCapacity
            let next : Option (Fin rest.length) :=
              some ⟨k.val + 1, hnext⟩
            refine ⟨next, trace, ?_, ?_, ?_⟩
            · simp only [next, loopFamilyMeasure]
              omega
            · simpa only [loopFamilyConfig, next] using htrace
            · intro values store hpost
              exact hpost
          · have hlast : k.val + 1 = rest.length := by
              have hk := k.isLt
              omega
            obtain ⟨trace, htrace⟩ := final_iteration_steps
              wasm left right first rest k.val k.isLt hlast hleftView
              hrightView hleftFit hrightFit hleftCapacity hrightCapacity
            refine ⟨none, trace, ?_, ?_, ?_⟩
            · simp only [loopFamilyMeasure]
              have hk := k.isLt
              omega
            · simpa only [loopFamilyConfig] using htrace
            · intro values store hpost
              exact hpost
  simpa only [loopFamilyConfig, post] using familyTerminates

private theorem nonempty_terminates
    (wasm : Store Unit) (left right : UInt32)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left (rest.length + 1) =
        first.1 :: rest.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right (rest.length + 1) =
        first.2 :: rest.map Prod.snd)
    (hleftFit : left.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * (rest.length + 1) ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * (rest.length + 1) ≤ wasm.mem.pages * 65536) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat (rest.length + 1)))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64 first rest)] ∧
          store = machineStore wasm) := by
  refine TerminatesWith.prependSteps
    (first_steps wasm left right first rest hleftView hrightView
      hleftFit hrightFit hleftCapacity hrightCapacity) ?_
  by_cases hrest : rest = []
  · subst hrest
    exact TerminatesWith.of_steps (oneTerm_steps wasm left right
      (Wasm.IEEE64.mul first.1 first.2)) ⟨rfl, rfl⟩
  · refine TerminatesWith.prependSteps
      (enterLoop_steps wasm left right first rest hrest hleftFit) ?_
    exact loopHead_terminates wasm left right first rest hrest
      hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity

/-- The generated zero-length branch returns before either memory load, so it
terminates without any address, capacity, or array-view hypotheses. -/
theorem f64Dot_empty_terminates
    (wasm : Store Unit) (left right : UInt32) :
    TerminatesWith (configFromStore wasm left right 0)
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List [])] ∧
          store = (configFromStore wasm left right 0).store) :=
  TerminatesWith.of_steps (zero_steps wasm left right) ⟨rfl, rfl⟩

/-- The decoded generated function terminates for every runtime length whose
two read-only memory views fit both the 32-bit address space and the physical
linear memory.  It returns the pure modeled binary64 dot product and preserves
the complete machine store, with no finiteness or numerical assumptions. -/
theorem f64Dot_terminates
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store) := by
  cases terms with
  | nil =>
      exact f64Dot_empty_terminates wasm left right
  | cons first rest =>
      exact nonempty_terminates wasm left right first rest
        (by simpa using hleftView) (by simpa using hrightView)
        (by simpa using hleftFit) (by simpa using hrightFit)
        (by simpa using hleftCapacity) (by simpa using hrightCapacity)

/-- Public export-entry form of `f64Dot_terminates`.  It records that the
standard module/function/ABI invocation initializes to the direct proof
configuration, then states the raw fuel-independent execution contract. -/
theorem f64Dot_export_terminates
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (configFromStore wasm left right (UInt32.ofNat terms.length)) ∧
      TerminatesWith
        (configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (configFromStore wasm left right
              (UInt32.ofNat terms.length)).store) := by
  exact ⟨initConfig_eq_configFromStore wasm left right
      (UInt32.ofNat terms.length),
    f64Dot_terminates wasm left right terms hleftView hrightView
      hleftFit hrightFit hleftCapacity hrightCapacity⟩

/-- Fuel-independent execution of the exact generated WAT, strengthened with
the recursive numerical safety interface.  The postcondition retains both the
exact modeled return word and equality of the complete machine store before
adding finiteness and the accumulated absolute-error conclusion. -/
theorem f64Dot_terminates_real_error
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hsafe : CodeLib.Numerical.Kernels.Dot64ListSafe terms) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) -
              CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
            CodeLib.Numerical.Kernels.dot64ListErrorBudget terms) := by
  have hresult := CodeLib.Numerical.Kernels.dot64List_real_error
    terms hinputs hsafe
  exact (f64Dot_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity).mono
      (fun _values _store hexecution =>
        ⟨hexecution.1, hexecution.2, hresult.1, hresult.2⟩)

/-- Exact-real absolute-mass interface for the generated WAT theorem.  The
single aggregate headroom condition constructs the recursive safety evidence
without exposing rounded intermediate accumulators at the public boundary. -/
theorem f64Dot_terminates_real_error_of_abs_mass
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hbudget :
      CodeLib.Numerical.Kernels.dot64AbsMass terms +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) -
              CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
            CodeLib.Numerical.Kernels.dot64ListErrorBudget terms) := by
  have hresult :=
    CodeLib.Numerical.Kernels.dot64List_real_error_of_abs_mass
      terms hinputs hbudget
  exact (f64Dot_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity).mono
      (fun _values _store hexecution =>
        ⟨hexecution.1, hexecution.2, hresult.1, hresult.2⟩)

/-- Public export-entry form of the aggregate numerical theorem.  It pairs
the exact generated-module initialization equation with the strengthened
finite/error execution result. -/
theorem f64Dot_export_terminates_real_error_of_abs_mass
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hbudget :
      CodeLib.Numerical.Kernels.dot64AbsMass terms +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (configFromStore wasm left right (UInt32.ofNat terms.length)) ∧
      TerminatesWith
        (configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (configFromStore wasm left right
              (UInt32.ofNat terms.length)).store ∧
            CodeLib.IEEE64.Finite
              (CodeLib.Numerical.Kernels.dot64List terms) ∧
            |CodeLib.IEEE64.value
                (CodeLib.Numerical.Kernels.dot64List terms) -
                CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
              CodeLib.Numerical.Kernels.dot64ListErrorBudget terms) := by
  exact ⟨initConfig_eq_configFromStore wasm left right
      (UInt32.ofNat terms.length),
    f64Dot_terminates_real_error_of_abs_mass
      wasm left right terms hleftView hrightView hleftFit hrightFit
        hleftCapacity hrightCapacity hinputs hbudget⟩

/-- Uniform left/right envelope interface for the generated WAT theorem.  All
sign, unit-range, exact aggregate headroom, address, and capacity assumptions
remain visible in the statement. -/
theorem f64Dot_terminates_real_error_of_uniform
    (wasm : Store Unit) (left right : UInt32)
    (leftBound rightBound : ℝ)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hleftNonneg : 0 ≤ leftBound) (hrightNonneg : 0 ≤ rightBound)
    (hleftUnit : leftBound ≤ 1) (hrightUnit : rightBound ≤ 1)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UniformInputs
      leftBound rightBound terms)
    (hbudget :
      (terms.length : ℝ) * (leftBound * rightBound) +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) -
              CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
            CodeLib.Numerical.Kernels.dot64ListErrorBudget terms) := by
  have hresult := CodeLib.Numerical.Kernels.dot64List_real_error_of_uniform
    leftBound rightBound terms hleftNonneg hrightNonneg hleftUnit hrightUnit
      hinputs hbudget
  exact (f64Dot_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity).mono
      (fun _values _store hexecution =>
        ⟨hexecution.1, hexecution.2, hresult.1, hresult.2⟩)

/-- Fuel-independent operation-count gamma-times-mass theorem for the exact
generated WAT.
The operational postcondition is unchanged: it retains the exact returned
binary64 word and equality of the complete machine store.  The explicit
recursive safety premise rules out overflow; normal-or-zero products rule out
multiplication underflow. -/
theorem f64Dot_terminates_gamma_error
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hsafe : CodeLib.Numerical.Kernels.Dot64ListSafe terms)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) -
              CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
            CodeLib.Numerical.gamma (2 * terms.length - 1)
              CodeLib.IEEE64.unitRoundoff64 *
                CodeLib.Numerical.Kernels.dot64AbsMass terms) := by
  have hresult := CodeLib.Numerical.Kernels.dot64List_real_gamma_error
    terms hinputs hsafe hnormalOrZero hku
  exact (f64Dot_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity).mono
      (fun _values _store hexecution =>
        ⟨hexecution.1, hexecution.2, hresult.1, hresult.2⟩)

/-- Aggregate-headroom interface for the generated WAT gamma theorem.  Its
exact absolute-mass reserve constructs recursive safety, so no rounded
intermediate accumulator appears at this boundary. -/
theorem f64Dot_terminates_gamma_error_of_abs_mass
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hbudget :
      CodeLib.Numerical.Kernels.dot64AbsMass terms +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) -
              CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
            CodeLib.Numerical.gamma (2 * terms.length - 1)
              CodeLib.IEEE64.unitRoundoff64 *
                CodeLib.Numerical.Kernels.dot64AbsMass terms) := by
  have hresult :=
    CodeLib.Numerical.Kernels.dot64List_real_gamma_error_of_abs_mass
      terms hinputs hbudget hnormalOrZero hku
  exact (f64Dot_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity).mono
      (fun _values _store hexecution =>
        ⟨hexecution.1, hexecution.2, hresult.1, hresult.2⟩)

/-- Export-entry form of the gamma-times-mass theorem, linking the named
generated module invocation to the direct relational proof configuration. -/
theorem f64Dot_export_terminates_gamma_error
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hsafe : CodeLib.Numerical.Kernels.Dot64ListSafe terms)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (configFromStore wasm left right (UInt32.ofNat terms.length)) ∧
      TerminatesWith
        (configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (configFromStore wasm left right
              (UInt32.ofNat terms.length)).store ∧
            CodeLib.IEEE64.Finite
              (CodeLib.Numerical.Kernels.dot64List terms) ∧
            |CodeLib.IEEE64.value
                (CodeLib.Numerical.Kernels.dot64List terms) -
                CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
              CodeLib.Numerical.gamma (2 * terms.length - 1)
                CodeLib.IEEE64.unitRoundoff64 *
                  CodeLib.Numerical.Kernels.dot64AbsMass terms) := by
  exact ⟨initConfig_eq_configFromStore wasm left right
      (UInt32.ofNat terms.length),
    f64Dot_terminates_gamma_error wasm left right terms
      hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
      hinputs hsafe hnormalOrZero hku⟩

/-- Export-entry form of the aggregate-headroom gamma theorem. -/
theorem f64Dot_export_terminates_gamma_error_of_abs_mass
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hbudget :
      CodeLib.Numerical.Kernels.dot64AbsMass terms +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (configFromStore wasm left right (UInt32.ofNat terms.length)) ∧
      TerminatesWith
        (configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (configFromStore wasm left right
              (UInt32.ofNat terms.length)).store ∧
            CodeLib.IEEE64.Finite
              (CodeLib.Numerical.Kernels.dot64List terms) ∧
            |CodeLib.IEEE64.value
                (CodeLib.Numerical.Kernels.dot64List terms) -
                CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
              CodeLib.Numerical.gamma (2 * terms.length - 1)
                CodeLib.IEEE64.unitRoundoff64 *
                  CodeLib.Numerical.Kernels.dot64AbsMass terms) := by
  exact ⟨initConfig_eq_configFromStore wasm left right
      (UInt32.ofNat terms.length),
    f64Dot_terminates_gamma_error_of_abs_mass wasm left right terms
      hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
      hinputs hbudget hnormalOrZero hku⟩

/-- Condition-number corollary for fuel-independent execution of the exact
generated WAT.  The nonzero exact-sum premise is explicit and excludes the
empty branch; exact return-word and complete-store equalities are preserved. -/
theorem f64Dot_terminates_conditioned_relative_error
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hsafe : CodeLib.Numerical.Kernels.Dot64ListSafe terms)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1)
    (hexact : CodeLib.Numerical.Kernels.dot64ExactSum terms ≠ 0) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) /
              CodeLib.Numerical.Kernels.dot64ExactSum terms - 1| ≤
            CodeLib.Numerical.gamma (2 * terms.length - 1)
              CodeLib.IEEE64.unitRoundoff64 *
                CodeLib.Numerical.Kernels.dot64ListConditionNumber terms) := by
  have hcondition :=
    CodeLib.Numerical.Kernels.dot64List_conditioned_relative_error
      terms hinputs hsafe hnormalOrZero hku hexact
  exact (f64Dot_terminates_gamma_error wasm left right terms
    hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
      hinputs hsafe hnormalOrZero hku).mono
    (fun _values _store hexecution =>
      ⟨hexecution.1, hexecution.2.1, hexecution.2.2.1, hcondition⟩)

/-- Aggregate-headroom form of the generated WAT condition-number theorem. -/
theorem f64Dot_terminates_conditioned_relative_error_of_abs_mass
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hbudget :
      CodeLib.Numerical.Kernels.dot64AbsMass terms +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1)
    (hexact : CodeLib.Numerical.Kernels.dot64ExactSum terms ≠ 0) :
    TerminatesWith
      (configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (configFromStore wasm left right
            (UInt32.ofNat terms.length)).store ∧
          CodeLib.IEEE64.Finite
            (CodeLib.Numerical.Kernels.dot64List terms) ∧
          |CodeLib.IEEE64.value
              (CodeLib.Numerical.Kernels.dot64List terms) /
              CodeLib.Numerical.Kernels.dot64ExactSum terms - 1| ≤
            CodeLib.Numerical.gamma (2 * terms.length - 1)
              CodeLib.IEEE64.unitRoundoff64 *
                CodeLib.Numerical.Kernels.dot64ListConditionNumber terms) := by
  have hcondition :=
    CodeLib.Numerical.Kernels.dot64List_conditioned_relative_error_of_abs_mass
      terms hinputs hbudget hnormalOrZero hku hexact
  exact (f64Dot_terminates_gamma_error_of_abs_mass wasm left right terms
    hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
      hinputs hbudget hnormalOrZero hku).mono
    (fun _values _store hexecution =>
      ⟨hexecution.1, hexecution.2.1, hexecution.2.2.1, hcondition⟩)

/-- Export-entry form of the generated WAT condition-number corollary. -/
theorem f64Dot_export_terminates_conditioned_relative_error
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hsafe : CodeLib.Numerical.Kernels.Dot64ListSafe terms)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1)
    (hexact : CodeLib.Numerical.Kernels.dot64ExactSum terms ≠ 0) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (configFromStore wasm left right (UInt32.ofNat terms.length)) ∧
      TerminatesWith
        (configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (configFromStore wasm left right
              (UInt32.ofNat terms.length)).store ∧
            CodeLib.IEEE64.Finite
              (CodeLib.Numerical.Kernels.dot64List terms) ∧
            |CodeLib.IEEE64.value
                (CodeLib.Numerical.Kernels.dot64List terms) /
                CodeLib.Numerical.Kernels.dot64ExactSum terms - 1| ≤
              CodeLib.Numerical.gamma (2 * terms.length - 1)
                CodeLib.IEEE64.unitRoundoff64 *
                  CodeLib.Numerical.Kernels.dot64ListConditionNumber terms) := by
  exact ⟨initConfig_eq_configFromStore wasm left right
      (UInt32.ofNat terms.length),
    f64Dot_terminates_conditioned_relative_error wasm left right terms
      hleftView hrightView hleftFit hrightFit hleftCapacity hrightCapacity
      hinputs hsafe hnormalOrZero hku hexact⟩

/-- Export-entry form of the aggregate-headroom condition-number theorem. -/
theorem f64Dot_export_terminates_conditioned_relative_error_of_abs_mass
    (wasm : Store Unit) (left right : UInt32)
    (terms : List (UInt64 × UInt64))
    (hleftView :
      wasm.mem.words64 left terms.length = terms.map Prod.fst)
    (hrightView :
      wasm.mem.words64 right terms.length = terms.map Prod.snd)
    (hleftFit : left.toNat + 8 * terms.length ≤ UInt32.size)
    (hrightFit : right.toNat + 8 * terms.length ≤ UInt32.size)
    (hleftCapacity :
      left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hrightCapacity :
      right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536)
    (hinputs : CodeLib.Numerical.Kernels.Dot64UnitInputs terms)
    (hbudget :
      CodeLib.Numerical.Kernels.dot64AbsMass terms +
          CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1)
    (hnormalOrZero :
      CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts terms)
    (hku : (((2 * terms.length - 1 : ℕ) : ℝ) *
      CodeLib.IEEE64.unitRoundoff64) < 1)
    (hexact : CodeLib.Numerical.Kernels.dot64ExactSum terms ≠ 0) :
    initConfig { module := Project.F64Dot.«module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (configFromStore wasm left right (UInt32.ofNat terms.length)) ∧
      TerminatesWith
        (configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (configFromStore wasm left right
              (UInt32.ofNat terms.length)).store ∧
            CodeLib.IEEE64.Finite
              (CodeLib.Numerical.Kernels.dot64List terms) ∧
            |CodeLib.IEEE64.value
                (CodeLib.Numerical.Kernels.dot64List terms) /
                CodeLib.Numerical.Kernels.dot64ExactSum terms - 1| ≤
              CodeLib.Numerical.gamma (2 * terms.length - 1)
                CodeLib.IEEE64.unitRoundoff64 *
                  CodeLib.Numerical.Kernels.dot64ListConditionNumber terms) := by
  exact ⟨initConfig_eq_configFromStore wasm left right
      (UInt32.ofNat terms.length),
    f64Dot_terminates_conditioned_relative_error_of_abs_mass
      wasm left right terms hleftView hrightView hleftFit hrightFit
      hleftCapacity hrightCapacity hinputs hbudget hnormalOrZero hku hexact⟩

#print axioms f64Dot_terminates
#print axioms f64Dot_empty_terminates
#print axioms initConfig_eq_configFromStore
#print axioms f64Dot_export_terminates
#print axioms f64Dot_terminates_real_error
#print axioms f64Dot_terminates_real_error_of_abs_mass
#print axioms f64Dot_export_terminates_real_error_of_abs_mass
#print axioms f64Dot_terminates_real_error_of_uniform
#print axioms f64Dot_terminates_gamma_error
#print axioms f64Dot_terminates_gamma_error_of_abs_mass
#print axioms f64Dot_export_terminates_gamma_error
#print axioms f64Dot_export_terminates_gamma_error_of_abs_mass
#print axioms f64Dot_terminates_conditioned_relative_error
#print axioms f64Dot_terminates_conditioned_relative_error_of_abs_mass
#print axioms f64Dot_export_terminates_conditioned_relative_error
#print axioms f64Dot_export_terminates_conditioned_relative_error_of_abs_mass

end Project.F64Dot.Proof
