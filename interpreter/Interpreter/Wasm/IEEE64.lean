import Interpreter.Wasm.IEEE32

/-!
# Pure IEEE-754 binary64 arithmetic

Finite values use integer units of `2^-1074`.  The generic exact rounding
helpers from `IEEE32` operate on arbitrary naturals, so the binary64 layer
changes only the field widths, scale, and special-value constants.
-/

namespace Wasm.IEEE64

def canonicalNaN : UInt64 := 0x7FF8000000000000

def sign (x : UInt64) : Bool := decide (2 ^ 63 ≤ x.toNat)
def exponent (x : UInt64) : Nat := x.toNat / 2 ^ 52 % 2 ^ 11
def fraction (x : UInt64) : Nat := x.toNat % 2 ^ 52

def isNaN (x : UInt64) : Bool := exponent x == 0x7FF && fraction x != 0
def isInfinite (x : UInt64) : Bool :=
  exponent x == 0x7FF && fraction x == 0
def isFinite (x : UInt64) : Bool := exponent x != 0x7FF

def scaledMagnitude (x : UInt64) : Nat :=
  let e := exponent x
  let f := fraction x
  if e == 0 then f else (2 ^ 52 + f) * 2 ^ (e - 1)

def scaledValue (x : UInt64) : Int :=
  let magnitude : Int := scaledMagnitude x
  if sign x then -magnitude else magnitude

def signMask (negative : Bool) : UInt64 :=
  if negative then 0x8000000000000000 else 0

def infinity (negative : Bool) : UInt64 :=
  signMask negative ||| 0x7FF0000000000000

def encodeFinite
    (negative : Bool) (exponentField fractionField : Nat) : UInt64 :=
  UInt64.ofNat
    ((if negative then 2 ^ 63 else 0) + exponentField * 2 ^ 52 + fractionField)

def negate (x : UInt64) : UInt64 :=
  encodeFinite (!sign x) (exponent x) (fraction x)

def abs (x : UInt64) : UInt64 :=
  encodeFinite false (exponent x) (fraction x)

def copySign (value source : UInt64) : UInt64 :=
  encodeFinite (sign source) (exponent value) (fraction value)

def roundScaledMagnitude (negative : Bool) (n : Nat) : UInt64 :=
  if n < 2 ^ 52 then
    encodeFinite negative 0 n
  else if n < 2 ^ 53 then
    encodeFinite negative 1 (n - 2 ^ 52)
  else
    let shift := Nat.log2 n - 52
    let rounded := IEEE32.roundShift n shift
    let (finalShift, significand) :=
      if rounded == 2 ^ 53 then (shift + 1, 2 ^ 52)
      else (shift, rounded)
    let exponentField := finalShift + 1
    if 0x7FF ≤ exponentField then infinity negative
    else encodeFinite negative exponentField (significand - 2 ^ 52)

def roundDyadicMagnitude
    (negative : Bool) (n fractionalBits : Nat) : UInt64 :=
  if n == 0 then signMask negative
  else
    let outputShift := Nat.log2 n - (fractionalBits + 52)
    if outputShift == 0 then
      let rounded :=
        if fractionalBits == 0 then n
        else IEEE32.roundShift n fractionalBits
      roundScaledMagnitude negative rounded
    else
      let rounded := IEEE32.roundShift n (fractionalBits + outputShift)
      let (finalShift, significand) :=
        if rounded == 2 ^ 53 then (outputShift + 1, 2 ^ 52)
        else (outputShift, rounded)
      let exponentField := finalShift + 1
      if 0x7FF ≤ exponentField then infinity negative
      else encodeFinite negative exponentField (significand - 2 ^ 52)

def roundRationalMagnitude
    (negative : Bool) (numerator denominator : Nat) : UInt64 :=
  if numerator == 0 then signMask negative
  else if denominator == 0 then infinity negative
  else
    let integerPart := numerator / denominator
    let outputShift := Nat.log2 integerPart - 52
    if outputShift == 0 then
      roundScaledMagnitude negative
        (IEEE32.roundQuotient numerator denominator)
    else
      let rounded := IEEE32.roundQuotient numerator
        (denominator * 2 ^ outputShift)
      let (finalShift, significand) :=
        if rounded == 2 ^ 53 then (outputShift + 1, 2 ^ 52)
        else (outputShift, rounded)
      let exponentField := finalShift + 1
      if 0x7FF ≤ exponentField then infinity negative
      else encodeFinite negative exponentField (significand - 2 ^ 52)

def roundSqrtMagnitude (magnitude : Nat) : UInt64 :=
  if magnitude == 0 then 0
  else
    let radicand := magnitude * 2 ^ 1074
    let rootFloor := Nat.sqrt radicand
    let outputShift := Nat.log2 rootFloor - 52
    if outputShift == 0 then
      roundScaledMagnitude false (IEEE32.roundSqrtIntegral radicand 0)
    else
      let rounded := IEEE32.roundSqrtIntegral radicand outputShift
      let (finalShift, significand) :=
        if rounded == 2 ^ 53 then (outputShift + 1, 2 ^ 52)
        else (outputShift, rounded)
      let exponentField := finalShift + 1
      if 0x7FF ≤ exponentField then infinity false
      else encodeFinite false exponentField (significand - 2 ^ 52)

def add (a b : UInt64) : UInt64 :=
  if isNaN a || isNaN b then canonicalNaN
  else if isInfinite a then
    if isInfinite b && sign a != sign b then canonicalNaN else a
  else if isInfinite b then b
  else
    let sum := scaledValue a + scaledValue b
    if sum == 0 then
      if sign a && sign b then signMask true else 0
    else roundScaledMagnitude (sum < 0) sum.natAbs

def sub (a b : UInt64) : UInt64 := add a (negate b)

def mul (a b : UInt64) : UInt64 :=
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
    else roundDyadicMagnitude negative
      (scaledMagnitude a * scaledMagnitude b) 1074

def div (a b : UInt64) : UInt64 :=
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
    else roundRationalMagnitude negative
      (scaledMagnitude a * 2 ^ 1074) (scaledMagnitude b)

def sqrt (a : UInt64) : UInt64 :=
  if isNaN a then canonicalNaN
  else
    let magnitude := scaledMagnitude a
    if magnitude == 0 then a
    else if sign a then canonicalNaN
    else if isInfinite a then a
    else roundSqrtMagnitude magnitude

def eq (a b : UInt64) : Bool :=
  if isNaN a || isNaN b then false else scaledValue a == scaledValue b

def lt (a b : UInt64) : Bool :=
  if isNaN a || isNaN b then false else decide (scaledValue a < scaledValue b)

def le (a b : UInt64) : Bool :=
  if isNaN a || isNaN b then false else decide (scaledValue a ≤ scaledValue b)

def min (a b : UInt64) : UInt64 :=
  if isNaN a || isNaN b then canonicalNaN
  else if scaledMagnitude a == 0 && scaledMagnitude b == 0 then
    signMask (sign a || sign b)
  else if lt a b then a else b

def max (a b : UInt64) : UInt64 :=
  if isNaN a || isNaN b then canonicalNaN
  else if scaledMagnitude a == 0 && scaledMagnitude b == 0 then
    signMask (sign a && sign b)
  else if lt a b then b else a

def roundIntegralFinite
    (mode : IEEE32.IntegralRounding) (negative : Bool)
    (magnitude : Nat) : UInt64 :=
  let unit := 2 ^ 1074
  let quotient := magnitude / unit
  let remainder := magnitude % unit
  let integerMagnitude :=
    match mode with
    | .ceil => if negative || remainder == 0 then quotient else quotient + 1
    | .floor => if !negative || remainder == 0 then quotient else quotient + 1
    | .trunc => quotient
    | .nearest => IEEE32.roundShift magnitude 1074
  roundScaledMagnitude negative (integerMagnitude * unit)

def roundIntegral (mode : IEEE32.IntegralRounding) (a : UInt64) : UInt64 :=
  if isNaN a then canonicalNaN
  else if isInfinite a then a
  else if scaledMagnitude a == 0 then a
  else roundIntegralFinite mode (sign a) (scaledMagnitude a)

def ceil (a : UInt64) : UInt64 := roundIntegral .ceil a
def floor (a : UInt64) : UInt64 := roundIntegral .floor a
def trunc (a : UInt64) : UInt64 := roundIntegral .trunc a
def nearest (a : UInt64) : UInt64 := roundIntegral .nearest a

end Wasm.IEEE64
