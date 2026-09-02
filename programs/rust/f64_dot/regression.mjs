// Deterministic execution checks for the exact Wasm artifact emitted by:
//   cd programs
//   ../verifier/.lake/build/bin/verifier build f64_dot

import { readFile } from "node:fs/promises";

const artifact = new URL("../build/f64_dot/program.wasm", import.meta.url);
const bytes = await readFile(artifact);
const { instance } = await WebAssembly.instantiate(bytes);
const { dot, memory } = instance.exports;
const view = new DataView(memory.buffer);

function write64(base, values) {
  values.forEach((value, index) =>
    view.setFloat64(base + 8 * index, value, true));
}

function assert(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function assertTrap(thunk, message) {
  let trapped = false;
  try {
    thunk();
  } catch (error) {
    trapped = error instanceof WebAssembly.RuntimeError;
  }
  assert(trapped, message);
}

// Empty input must return positive zero without touching either pointer.
assert(Object.is(dot(-1, -1, 0), 0), "empty dot product is not +0");

write64(0, [0.25]);
write64(64, [0.5]);
assert(dot(0, 64, 1) === 0.125, "one-term dot product mismatch");

write64(0, [1, 2, 3]);
write64(64, [4, 5, 6]);
assert(dot(0, 64, 3) === 32, "three-term dot product mismatch");

const lastSlot = memory.buffer.byteLength - 8;
write64(lastSlot, [1.5]);
write64(64, [2]);
assert(dot(lastSlot, 64, 1) === 3, "last valid f64 slot mismatch");

assertTrap(
  () => dot(memory.buffer.byteLength - 4, 64, 1),
  "cross-end f64.load did not trap",
);
assertTrap(
  () => dot(-8, 64, 1),
  "near-2^32 f64.load did not trap",
);

console.log("f64_dot Wasm regressions passed");
