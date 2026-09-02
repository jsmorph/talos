// Deterministic execution checks for the exact Wasm artifact emitted by:
//   cd programs
//   ../verifier/.lake/build/bin/verifier build f64_dot
//
// These are black-box artifact regressions only, not theorem evidence. Inputs
// and expected results are fixed IEEE-754 binary64 encodings; host JavaScript
// floating-point arithmetic is not used to manufacture an expected result.

import { readFile } from "node:fs/promises";

const artifact = new URL("../build/f64_dot/program.wasm", import.meta.url);
const bytes = await readFile(artifact);
const { instance } = await WebAssembly.instantiate(bytes);
const { dot, memory } = instance.exports;
const view = new DataView(memory.buffer);
const resultBytes = new ArrayBuffer(8);
const resultView = new DataView(resultBytes);

const bits = Object.freeze({
  positiveZero: 0x0000_0000_0000_0000n,
  negativeZero: 0x8000_0000_0000_0000n,
  leastSubnormal: 0x0000_0000_0000_0001n,
  negativeLeastSubnormal: 0x8000_0000_0000_0001n,
  halfMinNormal: 0x0008_0000_0000_0000n,
  minNormal: 0x0010_0000_0000_0000n,
  twoNeg54: 0x3c90_0000_0000_0000n,
  twoNeg53: 0x3ca0_0000_0000_0000n,
  twoNeg8: 0x3f70_0000_0000_0000n,
  twoNeg6: 0x3f90_0000_0000_0000n,
  negativeTwoNeg6: 0xbf90_0000_0000_0000n,
  twoNeg4: 0x3fb0_0000_0000_0000n,
  negativeTwoNeg4: 0xbfb0_0000_0000_0000n,
  headroom256Term: 0x3f6f_ffff_ffff_fc02n,
  headroom256Result: 0x3fef_ffff_ffff_fc01n,
  half: 0x3fe0_0000_0000_0000n,
  negativeHalf: 0xbfe0_0000_0000_0000n,
  belowOne: 0x3fef_ffff_ffff_ffffn,
  one: 0x3ff0_0000_0000_0000n,
  negativeOne: 0xbff0_0000_0000_0000n,
  belowTwo: 0x3fff_ffff_ffff_ffffn,
  two: 0x4000_0000_0000_0000n,
  four: 0x4010_0000_0000_0000n,
  negativeFour: 0xc010_0000_0000_0000n,
  eight: 0x4020_0000_0000_0000n,
  twenty: 0x4034_0000_0000_0000n,
  twoPow6: 0x4050_0000_0000_0000n,
  twoPow10: 0x4090_0000_0000_0000n,
});

const defaultLeft = 4096;
const defaultRight = 8192;
const pageBytes = 65_536;
const memoryBytes = memory.buffer.byteLength;
const lastSlot = memoryBytes - 8;

function write64Bits(base, values) {
  values.forEach((value, index) =>
    view.setBigUint64(base + 8 * index, value, true));
}

function f64Bits(value) {
  resultView.setFloat64(0, value, true);
  return resultView.getBigUint64(0, true);
}

function hex64(value) {
  return `0x${value.toString(16).padStart(16, "0")}`;
}

function assert(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function assertDotBits(
  name,
  left,
  right,
  expected,
  { leftBase = defaultLeft, rightBase = defaultRight } = {},
) {
  assert(left.length === right.length, `${name}: vector length mismatch`);
  write64Bits(leftBase, left);
  write64Bits(rightBase, right);
  const actual = f64Bits(dot(leftBase, rightBase, left.length));
  assert(
    actual === expected,
    `${name}: got ${hex64(actual)}, expected ${hex64(expected)}`,
  );
}

function assertTrap(thunk, message) {
  let trapped = false;
  try {
    thunk();
  } catch (error) {
    if (!(error instanceof WebAssembly.RuntimeError)) {
      throw error;
    }
    trapped = true;
  }
  assert(trapped, message);
}

function repeated(value, length) {
  return Array(length).fill(value);
}

// Length 0: the near-wrap pointers must not be read and the result is +0.
assertDotBits(
  "length 0 returns positive zero without reads",
  [],
  [],
  bits.positiveZero,
  { leftBase: 0xffff_fff8, rightBase: 0xffff_fffc },
);

// Length 1: an exact power-of-two product, signed zero, and a subnormal.
assertDotBits(
  "length 1 exact power-of-two product",
  [bits.twoPow10],
  [bits.twoNeg4],
  bits.twoPow6,
);
assertDotBits(
  "length 1 preserves negative zero",
  [bits.negativeZero],
  [bits.one],
  bits.negativeZero,
);
assertDotBits(
  "length 1 preserves the least subnormal",
  [bits.leastSubnormal],
  [bits.one],
  bits.leastSubnormal,
);
assertDotBits(
  "length 1 produces a subnormal at the normal boundary",
  [bits.minNormal],
  [bits.half],
  bits.halfMinNormal,
);
assertDotBits(
  "length 1 underflow retains the negative-zero sign",
  [bits.negativeLeastSubnormal],
  [bits.half],
  bits.negativeZero,
);

// Length 2: exact mixed-sign cancellation and gradual underflow.
assertDotBits(
  "length 2 mixed signs cancel to positive zero",
  [bits.four, bits.negativeFour],
  [bits.two, bits.two],
  bits.positiveZero,
);
assertDotBits(
  "length 2 accumulates subnormal products",
  [bits.minNormal, bits.leastSubnormal],
  [bits.half, bits.one],
  0x0008_0000_0000_0001n,
);

// Length 4: halfway additions round across binade boundaries to even.
assertDotBits(
  "length 4 crosses the lower binade boundary",
  [bits.belowOne, bits.twoNeg54, bits.positiveZero, bits.positiveZero],
  repeated(bits.one, 4),
  bits.one,
);
assertDotBits(
  "length 4 crosses the upper binade boundary",
  [bits.belowTwo, bits.twoNeg53, bits.positiveZero, bits.positiveZero],
  repeated(bits.one, 4),
  bits.two,
);
assertDotBits(
  "length 4 preserves sequential cancellation order",
  [bits.half, bits.twoNeg54, bits.negativeHalf, bits.twoNeg54],
  repeated(bits.one, 4),
  bits.twoNeg54,
);

// Length 16: exact accumulations reach both unit headroom boundaries.
assertDotBits(
  "length 16 reaches positive headroom boundary",
  repeated(bits.twoNeg4, 16),
  repeated(bits.one, 16),
  bits.one,
);
assertDotBits(
  "length 16 reaches negative headroom boundary",
  repeated(bits.negativeTwoNeg4, 16),
  repeated(bits.one, 16),
  bits.negativeOne,
);

// Length 64: every adjacent pair cancels exactly.
const alternating64 = Array.from(
  { length: 64 },
  (_, index) => index % 2 === 0 ? bits.twoNeg6 : bits.negativeTwoNeg6,
);
assertDotBits(
  "length 64 mixed-sign cancellation",
  alternating64,
  repeated(bits.one, 64),
  bits.positiveZero,
);

// Length 256: exact power-of-two terms accumulate to the headroom boundary.
assertDotBits(
  "length 256 exact power-of-two accumulation",
  repeated(bits.twoNeg8, 256),
  repeated(bits.one, 256),
  bits.one,
);
assertDotBits(
  "length 256 aggregate headroom boundary",
  repeated(bits.one, 256),
  repeated(bits.headroom256Term, 256),
  bits.headroom256Result,
);

// Aligned arrays read the last and first slots on either side of a page edge.
assertDotBits(
  "aligned reads on both sides of internal page boundaries",
  [bits.one, bits.two],
  [bits.four, bits.eight],
  bits.twenty,
  { leftBase: pageBytes - 8, rightBase: 2 * pageBytes - 8 },
);

// A raw Wasm f64.load may also be unaligned and span an internal page edge.
assertDotBits(
  "unaligned reads spanning internal page boundaries",
  [bits.one],
  [bits.two],
  bits.two,
  { leftBase: pageBytes - 4, rightBase: 2 * pageBytes - 4 },
);

// The final complete f64 slot in memory remains readable.
assertDotBits(
  "last valid f64 slot",
  [bits.two],
  [bits.four],
  bits.eight,
  { leftBase: lastSlot },
);

write64Bits(defaultLeft, [bits.one, bits.one]);
write64Bits(defaultRight, [bits.one, bits.one]);

assertTrap(
  () => dot(memoryBytes - 7, defaultRight, 1),
  "left one-byte-out-of-bounds f64.load did not trap",
);
assertTrap(
  () => dot(defaultLeft, memoryBytes - 7, 1),
  "right one-byte-out-of-bounds f64.load did not trap",
);
assertTrap(
  () => dot(lastSlot, defaultRight, 2),
  "indexed f64.load one slot past memory did not trap",
);
assertTrap(
  () => dot(0xffff_fff8, defaultRight, 1),
  "near-u32-capacity aligned f64.load did not trap",
);
assertTrap(
  () => dot(0xffff_fff9, defaultRight, 1),
  "cross-u32-end f64.load did not trap",
);

console.log("f64_dot Wasm artifact regressions passed");
