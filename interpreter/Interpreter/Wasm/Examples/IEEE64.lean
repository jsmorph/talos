import Interpreter.Wasm.Float

/-!
# Pure binary64 differential checks

All proof-visible scalar binary64 arithmetic, selection, comparison, and
integral-rounding operations are compared with the native `Float` oracle.
-/

namespace Wasm.Examples.IEEE64

private def nativeCanon (b : UInt64) : UInt64 :=
  if (Float.ofBits b).isNaN then 0x7FF8000000000000 else b

private def nativeMin (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let y := Float.ofBits b
  if x.isNaN || y.isNaN then 0x7FF8000000000000
  else if x == 0.0 && y == 0.0 then a ||| b
  else if x < y then a else b

private def nativeMax (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let y := Float.ofBits b
  if x.isNaN || y.isNaN then 0x7FF8000000000000
  else if x == 0.0 && y == 0.0 then a &&& b
  else if x < y then b else a

private def nativeNearest (a : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let fl := x.floor
  let cl := x.ceil
  let dlo := x - fl
  let dhi := cl - x
  let r := if dlo < dhi then fl
    else if dhi < dlo then cl
    else if (fl * 0.5).floor * 2.0 == fl then fl else cl
  nativeCanon r.toBits

def differentialCases : List (UInt64 × UInt64) :=
  (List.range 1024).map fun n =>
    (UInt64.ofNat (6364136223846793005 * n + 1442695040888963407),
     UInt64.ofNat (2862933555777941757 * n + 3037000493))

def edgeCases : List (UInt64 × UInt64) :=
  [(0, 0), (0x8000000000000000, 0),
   (0, 0x7FF0000000000000),
   (1, 0x3FE0000000000000),
   (0x0010000000000000, 0x3FE0000000000000),
   (0x7FEFFFFFFFFFFFFF, 0x4000000000000000),
   (0x7FF8000000000000, 0x3FF0000000000000)]

theorem differential_scalar_operations_agree_with_native :
    (edgeCases ++ differentialCases).all (fun p =>
      IEEE64.add p.1 p.2 == nativeCanon (Float.ofBits p.1 + Float.ofBits p.2).toBits &&
      IEEE64.sub p.1 p.2 == nativeCanon (Float.ofBits p.1 - Float.ofBits p.2).toBits &&
      IEEE64.mul p.1 p.2 == nativeCanon (Float.ofBits p.1 * Float.ofBits p.2).toBits &&
      IEEE64.div p.1 p.2 == nativeCanon (Float.ofBits p.1 / Float.ofBits p.2).toBits &&
      IEEE64.sqrt p.1 == nativeCanon (Float.ofBits p.1).sqrt.toBits &&
      IEEE64.min p.1 p.2 == nativeMin p.1 p.2 &&
      IEEE64.max p.1 p.2 == nativeMax p.1 p.2 &&
      IEEE64.eq p.1 p.2 == (Float.ofBits p.1 == Float.ofBits p.2) &&
      IEEE64.lt p.1 p.2 == decide (Float.ofBits p.1 < Float.ofBits p.2) &&
      IEEE64.le p.1 p.2 == decide (Float.ofBits p.1 ≤ Float.ofBits p.2) &&
      IEEE64.ceil p.1 == nativeCanon (Float.ofBits p.1).ceil.toBits &&
      IEEE64.floor p.1 == nativeCanon (Float.ofBits p.1).floor.toBits &&
      IEEE64.trunc p.1 == nativeCanon (if Float.ofBits p.1 < 0.0 then
        (Float.ofBits p.1).ceil else (Float.ofBits p.1).floor).toBits &&
      IEEE64.nearest p.1 == nativeNearest p.1) = true := by
  native_decide

theorem binary64_boundaries :
    IEEE64.mul 0x0010000000000000 0x3FE0000000000000 =
      0x0008000000000000 ∧
    IEEE64.mul 0x0000000000000001 0x3FE0000000000000 = 0 ∧
    IEEE64.div 0x3FF0000000000000 0 = 0x7FF0000000000000 ∧
    IEEE64.sqrt 0x4010000000000000 = 0x4000000000000000 := by
  native_decide

end Wasm.Examples.IEEE64
