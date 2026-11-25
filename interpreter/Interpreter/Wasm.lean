module

public import Interpreter.Wasm.Syntax
public import Interpreter.Wasm.Float
public import Interpreter.Wasm.Locals
public import Interpreter.Wasm.Continuation
public import Interpreter.Wasm.Semantics
public import Interpreter.Wasm.Semantics.Lemmas
public import Interpreter.Wasm.SmallStep
public import Interpreter.Wasm.Host.Registry
public import Interpreter.Wasm.Host.StdIO
public import Interpreter.Wasm.Host.OOM
public import Interpreter.Wasm.Host.Random.Probability
public import Interpreter.Wasm.Host.Universal
public import Interpreter.Wasm.MeasureTermination
public import Interpreter.Wasm.Wp.Defs
public import Interpreter.Wasm.Wp.Atomic
public import Interpreter.Wasm.Wp.Block
public import Interpreter.Wasm.Wp.Loop
public import Interpreter.Wasm.Wp.Call
public import Interpreter.Wasm.Wp.Tactic
public import Interpreter.Wasm.Spec.Termination

public section

/-! # Wasm

A minimal Wasm core paired with a weakest-precondition reasoning framework.
This umbrella module re-exports the public core surface; the implementation is
split into:

* `Wasm.Syntax`            — instructions, programs, functions, modules
* `Wasm.Float`             — `f32`/`f64` operations over IEEE-754 bit patterns
* `Wasm.Locals`            — per-frame locals/value-stack state + helpers
* `Wasm.Continuation`      — `Continuation` / `Result` outcome types
* `Wasm.Semantics`         — `execOne` / `exec` / `run` mutual interpreter
* `Wasm.Semantics.Lemmas`  — bridge lemmas between `exec` and `wp`
                                 (fuel monotonicity, atomic unfoldings, …)
* `Wasm.Wp.*`              — `wp` framework: definitions, atomic
                                 equations, block / loop / call rules, and
                                 the `wp_run` / `wp_done` tactics
* `Wasm.Host.Registry`     — name-keyed host registries: resolve a
                                 module's own imports, in its own order,
                                 into the positional `HostEnv` the
                                 interpreter expects
* `Wasm.Host.OOM`          — terminal `talos.oom` notification used only by
                                 the tiny Rust allocator
* `Wasm.Host.Universal`    — one host offering every host function; the
                                 default for specifications, so a proof
                                 never has to choose a host
* `Wasm.Spec.Termination`  — fuel-free `TerminatesWith` /
                                 `PartiallyMeets` predicates (user-facing
                                 spec API)

Worked examples live under `Interpreter.Wasm.Examples.*` and are bundled by
`Interpreter.Wasm.Examples.Basic`; decoder internals live under
`Interpreter.Wasm.Decoder.*`. They are intentionally not re-exported here so
downstream proof packages can import the core API without depending on examples
or verifier plumbing.
-/
