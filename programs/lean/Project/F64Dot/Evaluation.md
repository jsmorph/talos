# `f64_dot` evaluation

This report evaluates the theorem boundary and validation cost of the generated
runtime-length binary64 dot product at base commit `0f83742`. The proof target
is the exact non-fused WebAssembly expression emitted for `f64_dot`: one
rounded multiplication initializes a nonempty reduction, followed by one
separate `f64.mul` and one `f64.add` for every remaining term. The empty branch
returns positive zero before loading memory.

## What is proved

Write `n` for the list length,

- `S = sum_i (value a_i * value b_i)` for the exact real dot product,
- `M = sum_i |value a_i * value b_i|` for its absolute-product mass,
- `B_0 = 0` and `B_n = (2n - 1) * 2^-52` when `n > 0`,
- `u = 2^-53`, `k = 2n - 1` using natural subtraction, and
- `gamma_k = k*u/(1-k*u)`.

The public contracts in `Spec.lean` establish the following results.

| Contract | Additional numerical hypotheses | Proved numerical result |
| --- | --- | --- |
| `F64DotSpec` | None | Total execution returns exactly the pure `dot64List` IEEE64 fold and preserves the complete machine store. |
| `F64DotNumericalSpec` | Each input is finite and unit-bounded; `M + B_n <= 1`. | The result is finite and `|value(result) - S| <= B_n`. |
| `F64DotGammaSpec` | Absolute-contract hypotheses; every exact product is zero or normal; `k*u < 1`. | The result is finite and `|value(result) - S| <= gamma_k * M`. |
| `F64DotConditionedSpec` | Gamma-contract hypotheses; `S != 0`. | `|value(result)/S - 1| <= gamma_k * kappa`, where `kappa = M/|S|`. |

All four contracts also require both `Mem.words64` views to match the logical
inputs, `base + 8*n <= 2^32` for each base pointer, and
`base + 8*n <= pages*65536` for physical memory. Equality at `2^32` is allowed
because only the unused final increment can wrap. There is no alignment,
non-aliasing, or separation premise at the WAT level. The stronger
`f64Dot_empty_terminates` theorem needs no view, pointer, or capacity premise.

The absolute theorem is the broader numerical result: it covers subnormal and
underflowing products. The gamma theorem uses the tighter unit-roundoff scale
only after excluding nonzero underflowing products. Addition may still cancel
or produce a subnormal exact sum. The conditioned theorem deliberately excludes
`S = 0`; for cancellation-heavy inputs its condition number makes the loss of
relative accuracy explicit.

## Bound quality

For the regression lengths below, the table evaluates both forward bounds at
the largest mass allowed by the common aggregate-headroom premise,
`M_max = 1 - B_n`. These are evaluations of the proved formulas, not observed
errors.

| `n` | `k` | Absolute `B_n` | `gamma_k * M_max` |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 |
| 1 | 1 | 2.220446e-16 | 1.110223e-16 |
| 2 | 3 | 6.661338e-16 | 3.330669e-16 |
| 4 | 7 | 1.554312e-15 | 7.771561e-16 |
| 16 | 31 | 6.883383e-15 | 3.441691e-15 |
| 64 | 127 | 2.819966e-14 | 1.409983e-14 |
| 256 | 511 | 1.134648e-13 | 5.673240e-14 |

At maximum admitted mass, the gamma result is about twice as tight as the
absolute primitive-error budget; for smaller mass it scales down with `M`.
This comparison is only meaningful on the gamma theorem's stronger
normal-product domain. The `2n - 1` count is exact for the emitted sequence,
but applying `gamma` once per modeled floating operation is intentionally
conservative relative to a possible specialized termwise dot-product analysis.
Any external comparison must evaluate the same separate multiply/add sequence:
an FMA changes both the result and the rounding-operation count.

## Proof assurance and boundary

- `Program.lean` decodes the generated WAT during elaboration and its fidelity
  guard rejects a mismatch between that WAT and the Lean module. Module-shape
  guards check an import-free one-function ABI, and `dotExport` proves that the
  named `dot` export resolves to function index zero.
- `Proof.lean` gives explicit relational small-step traces for the empty path,
  initial product, loop back edge, and exit. `terminatesWith_of_loop` turns
  these into fuel-independent total correctness for every safe input length.
- The operational theorem accepts arbitrary binary64 words, including special
  values. Numerical restrictions enter only in the separately attached
  corollaries.
- `#print axioms` for the public operational and numerical theorems reports
  only `propext`, `Classical.choice`, and `Quot.sound`; `dotExport` is
  axiom-free. The relevant Lean sources contain no `sorry`, `admit`, axiom
  declaration, or `native_decide` dependency.
- The deterministic Node suite is independent black-box evidence from V8: 19
  exact-bit success cases and five expected traps at lengths `0`, `1`, `2`,
  `4`, `16`, `64`, and `256`. It covers signed zero, subnormals, tie-to-even,
  cancellation, headroom, page boundaries, address wrap, and out-of-bounds
  loads. It is a regression oracle, not a theorem premise or an exhaustive
  test.

The theorem is about the decoded WAT under Talos's Lean definitions of Wasm
and IEEE64 behavior. It does not prove rustc correct, prove the unsafe Rust
pointer/provenance preconditions, or independently certify that the handwritten
semantics is the WebAssembly standard. Invalid addresses are outside the
theorem premises; their traps are tested only by the regression suite. No
external floating-point prover was run, and no external proof result is
claimed.

## Reproducible validation cost

Measurements were taken on 2026-09-02 on Linux x86_64 with 9 vCPUs
(AMD EPYC 9V74) and 21 GiB RAM. Tool versions were Lean/Lake
`4.34.0-rc2`/`5.0.0-src+6a10ac8`, rustc/Cargo `1.95.0`, wasm-tools
`1.251.0`, and Node `24.19.0`. `LD_PRELOAD=/tmp/lean_procself.so` was an
environment-only workaround for this container's inconsistent `/proc` mount;
it is not needed on a normal host.

The worktree began at `0f83742`. Interpreter, CodeLib, Project, and Cargo
outputs were local to it. Only the repo-root third-party Lake package
checkout/cache was shared; the artifact and end-to-end verifier timings used a
prebuilt verifier executable from the same base revision. A prior interrupted
measurement had partially warmed that shared third-party cache. Immediately
before the recorded clean proof measurement, the local Interpreter, CodeLib,
and Project build outputs were removed; the OS page cache and shared
third-party cache were not flushed. The warm Lake measurement is therefore a
freshness/no-op build cost, not a second kernel replay.

| Validation | Cache state | Wall time |
| --- | --- | ---: |
| `lake build Project.F64Dot.Spec` from `programs/lean` | Clean local Interpreter/CodeLib/Project outputs; shared third-party cache | 1,485.180 s |
| Immediate repeat of the same focused build | Warm/no-op | 2.151 s |
| `verifier build f64_dot` artifact pipeline | Empty isolated Cargo target; prebuilt verifier executable | 0.973 s |
| Immediate artifact-pipeline repeat | Warm Cargo target | 0.130 s |
| `verifier check --force-emit f64_dot` | Warm end-to-end Cargo, emit, and focused proof state; prebuilt verifier executable | 2.165 s |
| `node programs/rust/f64_dot/regression.mjs` | Seven fresh Node processes | median 0.063 s; range 0.051--0.097 s |

The artifact timings exclude compilation of the verifier executable. Although
`f64_dot` alone was selected, the current artifact command invokes the Cargo
workspace build; the cold figure therefore includes compiling every workspace
member into the fresh target directory. The Node timing is whole-process suite
cost (startup, Wasm read/instantiation, 24 cases), not dot-product throughput.

Portable reproduction from the repository root is:

```bash
just lake-shared
just build-verifier
just verifier-build f64_dot

cd programs/lean
lake build Project.F64Dot.Spec
lake build Project.F64Dot.Spec

cd ../..
just verifier-check --force-emit f64_dot
node --check programs/rust/f64_dot/regression.mjs
for run in 1 2 3 4 5 6 7; do
  time node programs/rust/f64_dot/regression.mjs
done
```

Use a monotonic wall-clock wrapper in place of shell `time` if machine-readable
samples are required, and record cache state with the result. A fully fresh
checkout must run the artifact build before Lean elaboration because the
generated, ignored `program.wat` file is a compile-time input to `Program.lean`.
