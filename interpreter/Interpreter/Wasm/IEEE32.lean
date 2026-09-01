/-!
# Pure binary32 addition

This file implements the IEEE-754 binary32 value decomposition and
round-to-nearest, ties-to-even addition using only integers and bit operations.
Finite values are represented exactly as integer multiples of `2^-149`; this
makes addition exact before the result is rounded back to binary32.

Keeping this operation free of `Float32` externs makes it visible to Lean's
logic and gives downstream proofs a computational definition to reason about.
-/

namespace Wasm.IEEE32

def canonicalNaN : UInt32 := 0x7FC00000

def sign (x : UInt32) : Bool := decide (2 ^ 31 ≤ x.toNat)

def exponent (x : UInt32) : Nat := x.toNat / 2 ^ 23 % 2 ^ 8

def fraction (x : UInt32) : Nat := x.toNat % 2 ^ 23

def isNaN (x : UInt32) : Bool := exponent x == 0xFF && fraction x != 0

def isInfinite (x : UInt32) : Bool :=
  exponent x == 0xFF && fraction x == 0

def isFinite (x : UInt32) : Bool := exponent x != 0xFF

/-- The magnitude of a finite binary32 value in units of `2^-149`. -/
def scaledMagnitude (x : UInt32) : Nat :=
  let e := exponent x
  let f := fraction x
  if e == 0 then f else (2 ^ 23 + f) * 2 ^ (e - 1)

/-- The signed value of a finite binary32 bit pattern in units of `2^-149`. -/
def scaledValue (x : UInt32) : Int :=
  let magnitude : Int := scaledMagnitude x
  if sign x then -magnitude else magnitude

def signMask (negative : Bool) : UInt32 :=
  if negative then 0x80000000 else 0

def infinity (negative : Bool) : UInt32 :=
  signMask negative ||| 0x7F800000

def encodeFinite
    (negative : Bool) (exponentField fractionField : Nat) : UInt32 :=
  UInt32.ofNat
    ((if negative then 2 ^ 31 else 0) + exponentField * 2 ^ 23 + fractionField)

/-- Flip a binary32 sign without inspecting or changing the other fields. -/
def negate (x : UInt32) : UInt32 :=
  encodeFinite (!sign x) (exponent x) (fraction x)

/-- Clear a binary32 sign without inspecting or changing the other fields. -/
def abs (x : UInt32) : UInt32 :=
  encodeFinite false (exponent x) (fraction x)

/-- Round a positive integer quotient to nearest, resolving a tie toward an
even quotient.  `shift` is positive at every call site. -/
def roundShift (n shift : Nat) : Nat :=
  let unit := 2 ^ shift
  let quotient := n / unit
  let remainder := n % unit
  let half := unit / 2
  if remainder < half then quotient
  else if half < remainder then quotient + 1
  else if quotient % 2 == 0 then quotient else quotient + 1

/-- Round an exact, nonzero magnitude expressed in units of `2^-149` to
binary32 using round-to-nearest, ties-to-even. -/
def roundScaledMagnitude (negative : Bool) (n : Nat) : UInt32 :=
  if n < 2 ^ 23 then
    encodeFinite negative 0 n
  else if n < 2 ^ 24 then
    encodeFinite negative 1 (n - 2 ^ 23)
  else
    let shift := Nat.log2 n - 23
    let rounded := roundShift n shift
    let (shift, significand) :=
      if rounded == 2 ^ 24 then (shift + 1, 2 ^ 23)
      else (shift, rounded)
    let exponentField := shift + 1
    if 0xFF ≤ exponentField then infinity negative
    else encodeFinite negative exponentField (significand - 2 ^ 23)

/-- Pure IEEE-754 binary32 addition with round-to-nearest, ties-to-even.
NaN results use WebAssembly's canonical quiet NaN.  Exact cancellation yields
positive zero, except that adding two negative zeroes yields negative zero. -/
def add (a b : UInt32) : UInt32 :=
  if isNaN a || isNaN b then canonicalNaN
  else if isInfinite a then
    if isInfinite b && sign a != sign b then canonicalNaN else a
  else if isInfinite b then b
  else
    let sum := scaledValue a + scaledValue b
    if sum == 0 then
      if sign a && sign b then 0x80000000 else 0
    else roundScaledMagnitude (sum < 0) sum.natAbs

/-- Pure binary32 subtraction, defined by flipping the subtrahend's sign before
the IEEE-754 addition. -/
def sub (a b : UInt32) : UInt32 := add a (negate b)

end Wasm.IEEE32
