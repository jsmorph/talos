import Interpreter.Wasm.Examples.FloatSIMD
import CodeLib.IEEE32.Multiplication

/-!
# Lane-wise SIMD floating-point specifications
-/

namespace CodeLib.IEEE32

open Wasm
open Wasm.FloatSIMD

/-- The SIMD operator is exactly the scalar verified multiplication mapped
over four 32-bit lanes. -/
theorem f32x4_mul_is_lane_wise (a b : BitVec 128) :
    mulOp.eval a b =
      Simd.zipLanes 32
        (fun x y =>
          (Wasm.IEEE32.mul (UInt32.ofNat x) (UInt32.ofNat y)).toNat) a b := by
  rfl

theorem f32x4_mul_program_exact (a b : BitVec 128) :
    SmallStep.TerminatesWith (mulConfig a b)
      (fun values _ =>
        values = [.v128
          (Simd.zipLanes 32
            (fun x y =>
              (Wasm.IEEE32.mul (UInt32.ofNat x) (UInt32.ofNat y)).toNat)
            a b)]) := by
  simpa [f32x4_mul_is_lane_wise] using mul_terminates a b

theorem f32x4_special_lane_example :
    mulOp.eval exampleA exampleB = exampleResult := by
  native_decide

/-- Binary64 vector multiplication is the verified scalar binary64 operation
mapped over two 64-bit lanes. -/
theorem f64x2_mul_is_lane_wise (a b : BitVec 128) :
    mul64Op.eval a b =
      Simd.zipLanes 64
        (fun x y =>
          (Wasm.IEEE64.mul (UInt64.ofNat x) (UInt64.ofNat y)).toNat) a b := by
  rfl

theorem f64x2_mul_program_exact (a b : BitVec 128) :
    SmallStep.TerminatesWith (mul64Config a b)
      (fun values _ =>
        values = [.v128
          (Simd.zipLanes 64
            (fun x y =>
              (Wasm.IEEE64.mul (UInt64.ofNat x) (UInt64.ofNat y)).toNat)
            a b)]) := by
  simpa [f64x2_mul_is_lane_wise] using mul64_terminates a b

theorem f64x2_special_lane_example :
    mul64Op.eval example64A example64B = example64Result := by
  native_decide

#print axioms f32x4_mul_is_lane_wise
#print axioms f32x4_mul_program_exact
#print axioms f32x4_special_lane_example
#print axioms f64x2_mul_is_lane_wise
#print axioms f64x2_mul_program_exact
#print axioms f64x2_special_lane_example

end CodeLib.IEEE32
