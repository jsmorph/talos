Warning: truncated output (original token count: 18190)
Total output lines: 1722

import Interpreter.Wasm.Wp.Defs

/-! ### Atomic equations.

    `@[simp]` rewrite rules: when the head of the program matches a constructor,
    `wp` reduces structurally. Stack-consuming instructions reveal a
    `match s.values with ...` that `simp` reduces whenever the stack shape is
    concrete.

    Each lemma is discharged by the `wp_atomic` macro defined below, which
    unfolds `wp`, `exec`, and `execOne` and splits on the relevant `match`/`if`
    structure of the instruction. -/

namespace Wasm

/-- Solve a `wp` atomic-instruction goal whose RHS may contain `match`/`if`
    splits. Repeatedly opens splits and discharges the remaining leaves with
    the `exec`-unfolding helpers from `Defs.lean`. -/
macro "wp_atomic" : tactic => `(tactic|
  (repeat' (first
    | (apply wp_of_exec_eq_succ; intro fuel; simp_all [exec, execOne.eq_def])
    | (apply wp_of_exec_const_succ; intro fuel; simp_all [exec, execOne.eq_def])
    | split)
   all_goals try grind))

@[simp, wp_simp] theorem wp_nil : wp m [] Q st s env ↔ Q (.Fallthrough st s) := by
  wp_atomic

/-! ## Locals / constants -/

@[simp, wp_simp] theorem wp_localGet_cons :
    wp m (.localGet i :: rest) Q st s env ↔
    (match s.get i with
     | some v => wp m rest Q st { s with values := v :: s.values } env
     | none   => Q (.Invalid "localGet index out of bounds")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_localSet_cons :
    wp m (.localSet i :: rest) Q st s env ↔
    (match s.values with
     | v :: vs =>
        (match s.set? i v with
         | some s' => wp m rest Q st { s' with values := vs } env
         | none    => Q (.Invalid "localSet index out of bounds"))
     | _ => Q (.Invalid "localSet with empty stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_localTee_cons :
    wp m (.localTee i :: rest) Q st s env ↔
    (match s.values with
     | v :: _ =>
        (match s.set? i v with
         | some s' => wp m rest Q st s' env
         | none    => Q (.Invalid "localTee index out of bounds"))
     | _ => Q (.Invalid "localTee with empty stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_const_cons :
    wp m (.const v :: rest) Q st s env ↔
    wp m rest Q st { s with values := .i32 v :: s.values } env := by
  wp_atomic

@[simp, wp_simp] theorem wp_constI64_cons :
    wp m (.constI64 v :: rest) Q st s env ↔
    wp m rest Q st { s with values := .i64 v :: s.values } env := by
  wp_atomic

/-! ## i32 arithmetic -/

@[simp, wp_simp] theorem wp_add_cons :
    wp m (.add :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (a + b) :: vs } env
     | _ => Q (.Invalid "add: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_sub_cons :
    wp m (.sub :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (b - a) :: vs } env
     | _ => Q (.Invalid "sub: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_mul_cons :
    wp m (.mul :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (a * b) :: vs } env
     | _ => Q (.Invalid "mul: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_divU_cons :
    wp m (.divU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st { s with values := .i32 (a / b) :: vs } env
     | _ => Q (.Invalid "divU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_divS_cons :
    wp m (.divS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else if a = 0x80000000 ∧ b = 0xFFFFFFFF then Q (.Trap st "integer overflow")
       else wp m rest Q st
         { s with values := .i32 ((Int32.ofInt (Int.tdiv a.toInt32.toInt b.toInt32.toInt)).toUInt32) :: vs } env
     | _ => Q (.Invalid "divS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_remU_cons :
    wp m (.remU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st { s with values := .i32 (a % b) :: vs } env
     | _ => Q (.Invalid "remU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_remS_cons :
    wp m (.remS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st
         { s with values := .i32 ((Int32.ofInt (Int.tmod a.toInt32.toInt b.toInt32.toInt)).toUInt32) :: vs } env
     | _ => Q (.Invalid "remS: ill-shaped operand stack")) := by
  wp_atomic

/-! ## i32 comparison -/

@[simp, wp_simp] theorem wp_eqz_cons :
    wp m (.eqz :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a = 0 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqz: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_eq_cons :
    wp m (.eq :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a = b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eq: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ne_cons :
    wp m (.ne :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ne: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ltU_cons :
    wp m (.ltU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a < b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ltS_cons :
    wp m (.ltS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 < b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_gtU_cons :
    wp m (.gtU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a > b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "gtU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_gtS_cons :
    wp m (.gtS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 > b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "gtS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_leU_cons :
    wp m (.leU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_leS_cons :
    wp m (.leS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 ≤ b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_geU_cons :
    wp m (.geU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_geS_cons :
    wp m (.geS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m re…14190 tokens truncated…me r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if IEEE32.isNaN a then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncF32U_cons :
    wp m (.i32TruncF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i32TruncF32U a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if IEEE32.isNaN a then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncF64S_cons :
    wp m (.i32TruncF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i32TruncF64S a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncF64U_cons :
    wp m (.i32TruncF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i32TruncF64U a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF64U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF32S_cons :
    wp m (.i64TruncF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i64TruncF32S a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if IEEE32.isNaN a then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF32U_cons :
    wp m (.i64TruncF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i64TruncF32U a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if IEEE32.isNaN a then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF64S_cons :
    wp m (.i64TruncF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i64TruncF64S a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF64U_cons :
    wp m (.i64TruncF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i64TruncF64U a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF64U: ill-shaped operand stack")) := by
  wp_atomic

/-! ## float → integer (saturating) -/

@[simp, wp_simp] theorem wp_i32TruncSatF32S_cons :
    wp m (.i32TruncSatF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF32S a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncSatF32U_cons :
    wp m (.i32TruncSatF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF32U a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncSatF64S_cons :
    wp m (.i32TruncSatF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF64S a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncSatF64U_cons :
    wp m (.i32TruncSatF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF64U a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF64U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF32S_cons :
    wp m (.i64TruncSatF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF32S a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF32U_cons :
    wp m (.i64TruncSatF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF32U a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF64S_cons :
    wp m (.i64TruncSatF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF64S a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF64U_cons :
    wp m (.i64TruncSatF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF64U a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF64U: ill-shaped operand stack")) := by
  wp_atomic

/-! ## float ↔ float / reinterpret -/

@[simp, wp_simp] theorem wp_f32DemoteF64_cons :
    wp m (.f32DemoteF64 :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f32 (f32DemoteF64 a) :: vs } env
     | _ => Q (.Invalid "f32DemoteF64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64PromoteF32_cons :
    wp m (.f64PromoteF32 :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f64 (f64PromoteF32 a) :: vs } env
     | _ => Q (.Invalid "f64PromoteF32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32ReinterpretF32_cons :
    wp m (.i32ReinterpretF32 :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: vs => wp m rest Q st { s with values := .i32 b :: vs } env
     | _ => Q (.Invalid "i32ReinterpretF32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64ReinterpretF64_cons :
    wp m (.i64ReinterpretF64 :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: vs => wp m rest Q st { s with values := .i64 b :: vs } env
     | _ => Q (.Invalid "i64ReinterpretF64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32ReinterpretI32_cons :
    wp m (.f32ReinterpretI32 :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: vs => wp m rest Q st { s with values := .f32 b :: vs } env
     | _ => Q (.Invalid "f32ReinterpretI32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64ReinterpretI64_cons :
    wp m (.f64ReinterpretI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: vs => wp m rest Q st { s with values := .f64 b :: vs } env
     | _ => Q (.Invalid "f64ReinterpretI64: ill-shaped operand stack")) := by
  wp_atomic

end Wasm