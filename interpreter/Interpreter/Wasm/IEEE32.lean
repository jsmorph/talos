/-!
# Pure binary32 arithmetic

This file implements the IEEE-754 binary32 value decomposition and
round-to-nearest, ties-to-even arithmetic using only integers and bit
operations.  Finite values are represented exactly as integer multiples of
`2^-149`; this makes addition exact and makes multiplication an exact dyadic
rational before the result is rounded back to binary32.

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

/-- Copy only the sign of `source` onto the magnitude and payload of `value`. -/
def copySign (value source : UInt32) : UInt32 :=
  encodeFinite (sign source) (exponent value) (fraction value)

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

/-- Round the exact dyadic magnitude `n / 2^fractionalBits`, expressed in
units of `2^-149`, to binary32 with round-to-nearest, ties-to-even.  This
generalizes `roundScaledMagnitude`: the additional fractional bits are kept
until the single final rounding step, avoiding double rounding for products
near a normal or subnormal boundary. -/
def roundDyadicMagnitude
    (negative : Bool) (n fractionalBits : Nat) : UInt32 :=
  if n == 0 then signMask negative
  else
    let outputShift := Nat.log2 n - (fractionalBits + 23)
    if outputShift == 0 then
      let rounded :=
        if fractionalBits == 0 then n else roundShift n fractionalBits
      roundScaledMagnitude negative rounded
    else
      let rounded := roundShift n (fractionalBits + outputShift)
      let (finalShift, significand) :=
        if rounded == 2 ^ 24 then (outputShift + 1, 2 ^ 23)
        else (outputShift, rounded)
      let exponentField := finalShift + 1
      if 0xFF ≤ exponentField then infinity negative
      else encodeFinite negative exponentField (significand - 2 ^ 23)

/-- Round the positive rational `numerator / denominator` to the nearest
integer, resolving an exact half toward the even quotient.  A zero denominator
is outside the arithmetic call sites and is assigned zero to keep this helper
total. -/
def roundQuotient (numerator denominator : Nat) : Nat :=
  if denominator == 0 then 0
  else
    let quotient := numerator / denominator
    let twiceRemainder := 2 * (numerator % denominator)
    if twiceRemainder < denominator then quotient
    else if denominator < twiceRemainder then quotient + 1
    else if quotient % 2 == 0 then quotient else quotient + 1

/-- Round an exact positive rational magnitude in units of `2^-149` to
binary32.  The quotient/remainder comparison performs one ties-to-even
rounding at the output format's effective unit, including gradual underflow. -/
def roundRationalMagnitude
    (negative : Bool) (numerator denominator : Nat) : UInt32 :=
  if numerator == 0 then signMask negative
  else if denominator == 0 then infinity negative
  else
    let integerPart := numerator / denominator
    let outputShift := Nat.log2 integerPart - 23
    if outputShift == 0 then
      roundScaledMagnitude negative (roundQuotient numerator denominator)
    else
      let rounded :=
        roundQuotient numerator (denominator * 2 ^ outputShift)
      let (finalShift, significand) :=
        if rounded == 2 ^ 24 then (outputShift + 1, 2 ^ 23)
        else (outputShift, rounded)
      let exponentField := finalShift + 1
      if 0xFF ≤ exponentField then infinity negative
      else encodeFinite negative exponentField (significand - 2 ^ 23)

/-- Round `sqrt(radicand) / 2^shift` to the nearest integer.  Squaring the
halfway point gives the exact comparison
`4 * radicand` versus `(2 * lower + 1)^2 * 2^(2 * shift)`, so no approximate
square root enters the rounding decision. -/
def roundSqrtIntegral (radicand shift : Nat) : Nat :=
  let lower := Nat.sqrt radicand / 2 ^ shift
  let midpointSquared := (2 * lower + 1) ^ 2 * 2 ^ (2 * shift)
  let fourRadicand := 4 * radicand
  if fourRadicand < midpointSquared then lower
  else if midpointSquared < fourRadicand then lower + 1
  else if lower % 2 == 0 then lower else lower + 1

/-- Correctly round the square root of `magnitude * 2^149` back to a
binary32 magnitude in units of `2^-149`. -/
def roundSqrtMagnitude (magnitude : Nat) : UInt32 :=
  if magnitude == 0 then 0
  else
    let radicand := magnitude * 2 ^ 149
    let rootFloor := Nat.sqrt radicand
    let outputShift := Nat.log2 rootFloor - 23
    let rounded := roundSqrtIntegral radicand outputShift
    -- `rounded * 2^outputShift` is already exactly representable.  Routing it
    -- through the shared scaled-magnitude packer keeps exponent carry and
    -- gradual underflow in one proof-visible implementation.
    roundScaledMagnitude false (rounded * 2 ^ outputShift)

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

/-- Pure IEEE-754 binary32 multiplication with round-to-nearest,
ties-to-even.  A finite product is formed exactly as
`scaledMagnitude a * scaledMagnitude b / 2^149`; `roundDyadicMagnitude`
performs the only rounding step. -/
def mul (a b : UInt32) : UInt32 :=
  if isNaN a || isNaN b then canonicalNaN
  else
    let negative := sign a != sign b
    let aZero := scaledMagnitude a == 0
    let bZero := scaledMagnitude b == 0
    if isInfinite a then
      if bZero then canonicalNaN else infinity negative
    else if isInfinite b then
      if aZero then canonicalNaN else infinity negative
    else if aZero || bZero then signMask negative
    else
      roundDyadicMagnitude negative
        (scaledMagnitude a * scaledMagnitude b) 149

/-- Pure IEEE-754 binary32 division with round-to-nearest, ties-to-even. -/
def div (a b : UInt32) : UInt32 :=
  if isNaN a || isNaN b then canonicalNaN
  else
    let negative := sign a != sign b
    let aZero := scaledMagnitude a == 0
    let bZero := scaledMagnitude b == 0
    if isInfinite a then
      if isInfinite b then canonicalNaN else infinity negative
    else if isInfinite b then signMask negative
    else if bZero then
      if aZero then canonicalNaN else infinity negative
    else if aZero then signMask negative
    else
      roundRationalMagnitude negative
        (scaledMagnitude a * 2 ^ 149) (scaledMagnitude b)

/-- Pure correctly rounded IEEE-754 binary32 square root. -/
def sqrt (a : UInt32) : UInt32 :=
  if isNaN a then canonicalNaN
  else
    let magnitude := scaledMagnitude a
    if magnitude == 0 then a
    else if sign a then canonicalNaN
    else if isInfinite a then a
    else roundSqrtMagnitude magnitude

/-! ## Ordered comparison and selection -/

def eq (a b : UInt32) : Bool :=
  if isNaN a || isNaN b then false else scaledValue a == scaledValue b

def lt (a b : UInt32) : Bool :=
  if isNaN a || isNaN b then false else decide (scaledValue a < scaledValue b)

def le (a b : UInt32) : Bool :=
  if isNaN a || isNaN b then false else decide (scaledValue a ≤ scaledValue b)

def min (a b : UInt32) : UInt32 :=
  if isNaN a || isNaN b then canonicalNaN
  else if scaledMagnitude a == 0 && scaledMagnitude b == 0 then
    signMask (sign a || sign b)
  else if lt a b then a else b

def max (a b : UInt32) : UInt32 :=
  if isNaN a || isNaN b then canonicalNaN
  else if scaledMagnitude a == 0 && scaledMagnitude b == 0 then
    signMask (sign a && sign b)
  else if lt a b then b else a

/-! ## Rounding to integral binary32 values -/

inductive IntegralRounding where
  | ceil
  | floor
  | trunc
  | nearest
  deriving DecidableEq, Repr

def roundIntegralFinite
    (mode : IntegralRounding) (negative : Bool) (magnitude : Nat) : UInt32 :=
  let unit := 2 ^ 149
  let quotient := magnitude / unit
  let remainder := magnitude % unit
  let integerMagnitude :=
    match mode with
    | .ceil =>
        if negative || remainder == 0 then quotient else quotient + 1
    | .floor =>
        if !negative || remainder == 0 then quotient else quotient + 1
    | .trunc => quotient
    | .nearest => roundShift magnitude 149
  roundScaledMagnitude negative (integerMagnitude * unit)

def roundIntegral (mode : IntegralRounding) (a : UInt32) : UInt32 :=
  if isNaN a then canonicalNaN
  else if isInfinite a then a
  else if scaledMagnitude a == 0 then a
  else roundIntegralFinite mode (sign a) (scaledMagnitude a)

def ceil (a : UInt32) : UInt32 := roundIntegral .ceil a
def floor (a : UInt32) : UInt32 := roundIntegral .floor a
def trunc (a : UInt32) : UInt32 := roundIntegral .trunc a
def nearest (a : UInt32) : UInt32 := roundIntegral .nearest a

/-! ## Integer conversions -/

def signedI32Value (a : UInt32) : Int :=
  if sign a then (a.toNat : Int) - (2 : Int) ^ 32 else a.toNat

def signedI64Value (a : UInt64) : Int :=
  if 2 ^ 63 ≤ a.toNat then (a.toNat : Int) - (2 : Int) ^ 64 else a.toNat

def fromInt (a : Int) : UInt32 :=
  roundScaledMagnitude (a < 0) (a.natAbs * 2 ^ 149)

def convertI32S (a : UInt32) : UInt32 := fromInt (signedI32Value a)
def convertI32U (a : UInt32) : UInt32 := fromInt a.toNat
def convertI64S (a : UInt64) : UInt32 := fromInt (signedI64Value a)
def convertI64U (a : UInt64) : UInt32 := fromInt a.toNat

/-- Truncate a finite binary32 value toward zero as an unbounded integer.
Exceptional inputs return `none`; target-width range checks are separate. -/
def truncatedInt (a : UInt32) : Option Int :=
  if isFinite a then
    let magnitude : Nat := scaledMagnitude a / 2 ^ 149
    some (if sign a then -(magnitude : Int) else magnitude)
  else none

def intToUInt32 (a : Int) : UInt32 :=
  UInt32.ofNat (if a < 0 then 2 ^ 32 - a.natAbs else a.natAbs)

def intToUInt64 (a : Int) : UInt64 :=
  UInt64.ofNat (if a < 0 then 2 ^ 64 - a.natAbs else a.natAbs)

def truncI32S (a : UInt32) : Option UInt32 :=
  match truncatedInt a with
  | none => none
  | some value =>
      if -((2 : Int) ^ 31) ≤ value ∧ value < (2 : Int) ^ 31 then
        some (intToUInt32 value)
      else none

def truncI32U (a : UInt32) : Option UInt32 :=
  match truncatedInt a with
  | none => none
  | some value =>
      if 0 ≤ value ∧ value < (2 : Int) ^ 32 then
        some (intToUInt32 value)
      else none

def truncI64S (a : UInt32) : Option UInt64 :=
  match truncatedInt a with
  | none => none
  | some value =>
      if -((2 : Int) ^ 63) ≤ value ∧ value < (2 : Int) ^ 63 then
        some (intToUInt64 value)
      else none

def truncI64U (a : UInt32) : Option UInt64 :=
  match truncatedInt a with
  | none => none
  | some value =>
      if 0 ≤ value ∧ value < (2 : Int) ^ 64 then
        some (intToUInt64 value)
      else none

def truncSatI32S (a : UInt32) : UInt32 :=
  if isNaN a then 0
  else
    match truncatedInt a with
    | none => if sign a then 0x80000000 else 0x7FFFFFFF
    | some value =>
        if value ≤ -((2 : Int) ^ 31) then 0x80000000
        else if (2 : Int) ^ 31 - 1 ≤ value then 0x7FFFFFFF
        else intToUInt32 value

def truncSatI32U (a : UInt32) : UInt32 :=
  if isNaN a then 0
  else
    match truncatedInt a with
    | none => if sign a then 0 else 0xFFFFFFFF
    | some value =>
        if value ≤ 0 then 0
        else if (2 : Int) ^ 32 - 1 ≤ value then 0xFFFFFFFF
        else intToUInt32 value

def truncSatI64S (a : UInt32) : UInt64 :=
  if isNaN a then 0
  else
    match truncatedInt a with
    | none => if sign a then 0x8000000000000000 else 0x7FFFFFFFFFFFFFFF
    | some value =>
        if value ≤ -((2 : Int) ^ 63) then 0x8000000000000000
        else if (2 : Int) ^ 63 - 1 ≤ value then 0x7FFFFFFFFFFFFFFF
        else intToUInt64 value

def truncSatI64U (a : UInt32) : UInt64 :=
  if isNaN a then 0
  else
    match truncatedInt a with
    | none => if sign a then 0 else 0xFFFFFFFFFFFFFFFF
    | some value =>
        if value ≤ 0 then 0
        else if (2 : Int) ^ 64 - 1 ≤ value then 0xFFFFFFFFFFFFFFFF
        else intToUInt64 value

end Wasm.IEEE32
