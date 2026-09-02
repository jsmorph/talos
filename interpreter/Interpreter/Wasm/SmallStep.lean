Warning: truncated output (original token count: 94150)
Total output lines: 7707

import Interpreter.Wasm.Semantics

set_option maxHeartbeats 2000000

/-!
# Small-step WebAssembly machine

This machine is the authoritative semantics.  The fuel-bounded big-step
interpreter remains available as a regression oracle, but none of the
definitions below call `execOne`, `exec`, or `run`.

The relational `Step` relation is the semantic interface.  `stepChecked?` is
its deterministic executable presentation.  An `InternalError` denotes a
configuration which validation should have ruled out — a malformed operand
stack, an out-of-range index, an unresolved import; it is not a Wasm trap.
-/

namespace Wasm
namespace SmallStep

inductive TrapReason where
  | unreachable
  | integerDivideByZero
  | integerOverflow
  | invalidConversionToInteger
  | outOfBoundsMemory
  | outOfBoundsTable
  | undefinedElement
  | uninitializedElement (index : Nat)
  | indirectCallTypeMismatch
  | nullReference
  | nullFunctionReference
  | nullExceptionReference
  | nullI31Reference
  | nullStructureReference
  | nullArrayReference
  | castFailure
  | outOfBoundsArray
  | uncaughtException (tag : Nat) (arguments : List Value)
  | host (message : String)
  /-- Forward-compatible category for a GC proposal trap that has not yet
  received a dedicated structural constructor. -/
  | gc (message : String)
deriving Repr, Inhabited, DecidableEq, BEq

/-- Stable driver-facing rendering of structural traps. The semantic machine
retains the constructor; CLI and testsuite surfaces use this text only at their
boundary. -/
def TrapReason.message : TrapReason → String
  | .unreachable => "unreachable"
  | .integerDivideByZero => "integer divide by zero"
  | .integerOverflow => "integer overflow"
  | .invalidConversionToInteger => "invalid conversion to integer"
  | .outOfBoundsMemory => "out of bounds memory access"
  | .outOfBoundsTable => "out of bounds table access"
  | .undefinedElement => "undefined element"
  | .uninitializedElement index => s!"uninitialized element {index}"
  | .indirectCallTypeMismatch => "indirect call type mismatch"
  | .nullReference => "null reference"
  | .nullFunctionReference => "null function reference"
  | .nullExceptionReference => "null exception reference"
  | .nullI31Reference => "null i31 reference"
  | .nullStructureReference => "null structure reference"
  | .nullArrayReference => "null array reference"
  | .castFailure => "cast failure"
  | .outOfBoundsArray => "out of bounds array access"
  | .uncaughtException tag _ => s!"uncaught exception with tag {tag}"
  | .host message | .gc message => message

inductive AdministrativeStep where
  | finish
  | exitControl
  | returnFromFunction
  | returnFromCall
  | returnFromCallCrossInstance
  | callCrossInstance
  | unwindException
  | catchException
deriving Repr, Inhabited, DecidableEq, BEq

inductive StepKind where
  | instruction (instr : Instruction)
  | administrative (kind : AdministrativeStep)
  | host (functionIndex : Nat)
deriving Repr

structure ModuleInstanceId where
  id : Nat
deriving DecidableEq, Ord, Repr, BEq

-- import resolved to either a host function or a wasm function in another instance
inductive ResolvedImport (α : Type) where
  | host : HostFn α → ResolvedImport α
  | wasm : ModuleInstanceId → Nat → ResolvedImport α

/-- Per-module execution metadata: the module's syntax, its host imports, and
the cross-instance resolution of its function imports.

**Modeling caveat (shared store).** Instances carry only *metadata*; all
runtime state — linear memories, globals, tables, exception instances — lives
in the single `MachineStore.wasm` pool shared by every instance. A
cross-instance call switches `RuntimeEnv.entry` and nothing else, so the
callee reads and writes the *same* physical store as the caller. Real Wasm
instantiation gives each instance its own address space (imports alias
selected resources explicitly). Consequently, cross-module results proved
against this semantics do **not** transfer to a spec-conforming engine
whenever the participating modules rely on disjoint address spaces; they are
faithful only for module systems that deliberately share one store (e.g. a
module split into components over one memory). -/
structure ModuleInstance (α : Type) where
  module : Module
  host : HostEnv α
  resolvedImports : Array (ResolvedImport α) := #[]
deriving Inhabited

/-- Immutable execution metadata.  Keeping the host parameter on the runtime
environment makes the eventual Iris language instance available uniformly for
each fixed host-state type `α`.

**Modeling caveat (shared store).** `instances` holds per-module metadata
only; see `ModuleInstance` — every instance executes against the single
shared `MachineStore.wasm` state, unlike real Wasm instance isolation. -/
structure RuntimeEnv (α : Type) where
  instances : Array (ModuleInstance α)
  entry : ModuleInstanceId

/-- The instance currently executing.

Precondition: `re.entry.id < re.instances.size`. The panicking index
(`[·]!`) silently yields the default (`Inhabited`) instance when `entry` is
out of range, so callers must only construct runtimes whose entry points at
an existing instance. `initConfig` and `addInstanceConfig` maintain this
invariant, and every `Step` preserves `instances` while only switching
`entry` to an id validated by `hcallee`/`returningInstance` hypotheses. -/
@[reducible] def RuntimeEnv.currentInstance (re : RuntimeEnv α) : ModuleInstance α :=
  re.instances[re.entry.id]!

@[reducible] def RuntimeEnv.currentModule (re : RuntimeEnv α) : Module :=
  re.currentInstance.module

@[reducible] def RuntimeEnv.currentHost (re : RuntimeEnv α) : HostEnv α :=
  re.currentInstance.host

@[simp] theorem RuntimeEnv.currentModule_mk1 (inst : ModuleInstance α) :
    ({ instances := #[inst], entry := ⟨0⟩ } : RuntimeEnv α).currentModule = inst.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

@[simp] theorem RuntimeEnv.currentHost_mk1 (inst : ModuleInstance α) :
    ({ instances := #[inst], entry := ⟨0⟩ } : RuntimeEnv α).currentHost = inst.host := by
  simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]

/-- Reserved funcref address range for function instances owned by another
module. Local Wasm function indices are far below this boundary. A funcref
`foreignFunctionBase + id` names the script-wide callable
`HostEnv.foreignFuncs[id]`, letting a funcref exported by one module travel
through a shared table and be `call_indirect`-ed from another module. -/
def foreignFunctionBase : Nat := 1 <<< 62

def isForeignFunctionIndex (importCount index : Nat) : Bool :=
  importCount ≤ index && foreignFunctionBase ≤ index

/-- Shared state visible to Wasm and host calls. -/
structure MachineStore (α : Type) where
  runtime : RuntimeEnv α
  wasm : Store α

inductive ControlKind where
  | block
  | loop
  | tryTable (catches : List CatchClause)
  | throwing (tag : Nat) (arguments : List Value)
deriving Repr, Inhabited, DecidableEq

/-- Whether a control frame is the administrative exception-propagation
marker. Exposed for primitive Iris rules that discharge ordinary block exits. -/
def ControlKind.isThrowing : ControlKind → Bool
  | .throwing _ _ => true
  | _ => false

/-- A structured-control label. Frames are thread-local and explicitly retain
the operand stack below the construct, the enclosing continuation, and the
loop body needed by a back-edge. -/
structure ControlFrame where
  kind : ControlKind
  paramArity : Nat
  resultArity : Nat
  body : Program
  continuation : Program
  belowStack : List Value
deriving Repr

/-- Suspended caller state. A direct call installs fresh callee locals and
control frames while retaining the caller continuation here. -/
structure CallFrame where
  locals : Locals
  continuation : Program
  resultArity : Nat
  callerRemainder : List Value
  control : List ControlFrame
  returningInstance : ModuleInstanceId
deriving Repr

/-- Per-invocation state. Control and call frames belong to the thread rather…90150 tokens truncated…n when the host-parametric store has no decidable
equality. -/
theorem runSteps_trapReason_trapsWith {fuel : Nat} {config : Config α}
    {reason : TrapReason}
    (h : (runSteps fuel config).result.trapReason? = some reason) :
    TrapsWith config reason (fun _ => True) := by
  cases hr : (runSteps fuel config).result with
  | success values store =>
    simp [RunnerResult.trapReason?, hr] at h
  | trapped actual store =>
    have : actual = reason := by
      simpa [RunnerResult.trapReason?, hr] using h
    subst actual
    apply runSteps_trapped_trapsWith hr
    trivial
  | outOfFuel final =>
    simp [RunnerResult.trapReason?, hr] at h
  | internalError error final =>
    simp [RunnerResult.trapReason?, hr] at h

/-- A successful value projection is sufficient for a fuel-free relational
termination result when the client postcondition depends only on values. This
is useful for decoded configurations whose runtime host fields intentionally
do not have propositional equality instances. -/
theorem runSteps_values_terminates {fuel : Nat} {config : Config α}
    {values : List Value}
    (h : (runSteps fuel config).result.values? = some values) :
    TerminatesWith config (fun actual _ => actual = values) := by
  cases hr : (runSteps fuel config).result with
  | success actual store =>
    have : actual = values := by
      simpa [RunnerResult.values?, hr] using h
    subst actual
    apply runSteps_success_terminates hr
    rfl
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?, hr] at h

theorem steps_irreducible_deterministic
    {config final₁ final₂ : Config α} {trace₁ trace₂ : List StepKind}
    (h₁ : Steps config trace₁ final₁)
    (h₂ : Steps config trace₂ final₂)
    (hirr₁ : ∀ kind next, ¬ Step final₁ kind next)
    (hirr₂ : ∀ kind next, ¬ Step final₂ kind next) :
    final₁ = final₂ := by
  induction h₁ generalizing trace₂ final₂ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | cons head _ => exact False.elim (hirr₁ _ _ head)
  | cons head₁ tail₁ ih =>
    cases h₂ with
    | refl => exact False.elim (hirr₂ _ _ head₁)
    | cons head₂ tail₂ =>
      obtain ⟨rfl, rfl⟩ := step_deterministic head₁ head₂
      exact ih tail₂ hirr₁ hirr₂

theorem steps_done_deterministic
    {config : Config α} {trace₁ trace₂ : List StepKind}
    {values₁ values₂ : List Value} {store₁ store₂ : MachineStore α}
    (h₁ : Steps config trace₁ ⟨.done values₁, store₁⟩)
    (h₂ : Steps config trace₂ ⟨.done values₂, store₂⟩) :
    values₁ = values₂ ∧ store₁ = store₂ := by
  have hconfig := steps_irreducible_deterministic h₁ h₂
    (fun _ _ => done_terminal) (fun _ _ => done_terminal)
  have parts := Config.mk.inj hconfig
  exact ⟨Expr.done.inj parts.1, parts.2⟩

/-- A terminating execution already pins down the result, so total correctness
implies partial correctness: `Step` is deterministic, so any other terminal
trace from the same machine ends in the same values and store.

This is the small-step twin of `Wasm.TerminatesWith.toPartiallyMeets`
(`Spec/Defs.lean`). Without it every `PartiallyMeets` theorem has to restate
its total-correctness twin's proof. -/
theorem TerminatesWith.toPartiallyMeets
    {initial : Config α} {post : List Value → MachineStore α → Prop}
    (execution : TerminatesWith initial post) :
    PartiallyMeets initial post := by
  obtain ⟨_, _, _, steps, hpost⟩ := execution
  intro _ _ _ observed
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic steps observed
  exact hpost

/-- Weaken the postcondition of a partial-correctness result. -/
theorem PartiallyMeets.mono
    {initial : Config α} {post post' : List Value → MachineStore α → Prop}
    (h : PartiallyMeets initial post)
    (himp : ∀ values store, post values store → post' values store) :
    PartiallyMeets initial post' :=
  fun _ _ _ steps => himp _ _ (h _ _ _ steps)

/-- Determinism rules out a normally completed and a trapped terminal trace
from the same initial machine. -/
theorem steps_done_ne_trapped
    {config : Config α} {doneTrace trapTrace : List StepKind}
    {values : List Value} {doneStore trapStore : MachineStore α}
    {reason : TrapReason}
    (doneSteps : Steps config doneTrace ⟨.done values, doneStore⟩)
    (trapSteps : Steps config trapTrace ⟨.trapped reason, trapStore⟩) :
    False := by
  have hconfig := steps_irreducible_deterministic doneSteps trapSteps
    (fun _ _ => done_terminal) (fun _ _ => trapped_terminal)
  cases hconfig

/-- A deterministic initial machine cannot satisfy both a normal-termination
and a trapping specification. -/
theorem TerminatesWith.not_trapsWith
    (done : TerminatesWith initial donePost)
    (trapped : TrapsWith initial reason trapPost) :
    False := by
  obtain ⟨doneTrace, values, doneStore, doneSteps, _⟩ := done
  obtain ⟨trapTrace, trapStore, trapSteps, _⟩ := trapped
  exact steps_done_ne_trapped doneSteps trapSteps

theorem steps_comparable
    {config final₁ final₂ : Config α} {trace₁ trace₂ : List StepKind}
    (h₁ : Steps config trace₁ final₁)
    (h₂ : Steps config trace₂ final₂) :
    (∃ suffix, Steps final₁ suffix final₂) ∨
      ∃ suffix, Steps final₂ suffix final₁ := by
  induction h₁ generalizing trace₂ final₂ with
  | refl => exact .inl ⟨trace₂, h₂⟩
  | cons head₁ tail₁ ih =>
    cases h₂ with
    | refl => exact .inr ⟨_, .cons head₁ tail₁⟩
    | cons head₂ tail₂ =>
      obtain ⟨rfl, rfl⟩ := step_deterministic head₁ head₂
      exact ih tail₂

theorem checked_ok_of_steps_to_done
    {config : Config α} {trace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (h : Steps config trace ⟨.done values, store⟩) :
    ∃ result, stepChecked? config = .ok result := by
  cases h with
  | refl => exact ⟨none, by simp [stepChecked?]⟩
  | cons head _ => exact ⟨some (_, _), stepChecked?_complete head⟩

theorem steps_from_done_eq
    {values : List Value} {store : MachineStore α}
    {trace : List StepKind} {final : Config α}
    (h : Steps ⟨.done values, store⟩ trace final) :
    final = ⟨.done values, store⟩ := by
  cases h with
  | refl => rfl
  | cons head _ => exact False.elim (done_terminal head)

theorem safe_of_steps_to_done
    {config : Config α} {trace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (execution : Steps config trace ⟨.done values, store⟩) :
    config.Safe := by
  intro reachedTrace final reached
  rcases steps_comparable execution reached with towardFinal | towardDone
  · obtain ⟨suffix, hterminal⟩ := towardFinal
    have : final = ⟨.done values, store⟩ := steps_from_done_eq hterminal
    subst final
    exact ⟨none, by simp [stepChecked?]⟩
  · obtain ⟨suffix, hdone⟩ := towardDone
    exact checked_ok_of_steps_to_done hdone

theorem runSteps_success_partiallyMeets {fuel : Nat} {config : Config α}
    {values : List Value} {store : MachineStore α}
    (h : (runSteps fuel config).result = .success values store)
    (post : List Value → MachineStore α → Prop)
    (hp : post values store) :
    PartiallyMeets config post :=
  (runSteps_success_terminates h post hp).toPartiallyMeets

/-- Partial-correctness companion to `runSteps_values_terminates`. -/
theorem runSteps_values_partiallyMeets {fuel : Nat} {config : Config α}
    {values : List Value}
    (h : (runSteps fuel config).result.values? = some values) :
    PartiallyMeets config (fun actual _ => actual = values) :=
  (runSteps_values_terminates h).toPartiallyMeets

theorem safe_of_runSteps_success {fuel : Nat} {config : Config α}
    {values : List Value} {store : MachineStore α}
    (h : (runSteps fuel config).result = .success values store) :
    config.Safe := by
  apply safe_of_steps_to_done
  apply runSteps_sound (fuel := fuel)
  rw [h]
  rfl

end SmallStep
end Wasm