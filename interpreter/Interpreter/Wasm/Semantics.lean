Warning: truncated output (original token count: 32697)
Total output lines: 2460

import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Float
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Host

namespace Wasm

/-! ## Numeric helpers. -/

/-- Number of leading zero bits in a 32-bit word; 32 if zero. -/
def clz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 0x80000000 ≠ 0 then 32 - (k + 1) else clz32 k (a <<< 1)

/-- Number of trailing zero bits in a 32-bit word; 32 if zero. -/
def ctz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 1 ≠ 0 then 32 - (k + 1) else ctz32 k (a >>> 1)

/-- Number of one bits in a 32-bit word. -/
def popcnt32 : Nat → UInt32 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt32 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Number of leading zero bits in a 64-bit word; 64 if zero. -/
def clz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 0x8000000000000000 ≠ 0 then 64 - (k + 1) else clz64 k (a <<< 1)

/-- Number of trailing zero bits in a 64-bit word; 64 if zero. -/
def ctz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 1 ≠ 0 then 64 - (k + 1) else ctz64 k (a >>> 1)

/-- Number of one bits in a 64-bit word. -/
def popcnt64 : Nat → UInt64 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt64 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Sign-extend the low `bits` bits of `n` to a signed `Int`. -/
def signExtend (n : Nat) (bits : Nat) : Int :=
  let half := 2 ^ (bits - 1)
  let bound := 2 ^ bits
  if n ≥ half then (n : Int) - (bound : Int) else (n : Int)

/-- Whether `ht` is one of the abstract heap types in the `any` hierarchy
(the only ones a managed `anyref` can inhabit), as opposed to the
`func`/`extern` families. Concrete struct/array type indices also live
under `any`. -/
def GcHeapType.inAnyHierarchy : GcHeapType → Bool
  | .any | .eq | .i31 | .structT | .arrayT | .noneT | .concrete _ => true
  | _ => false

/-- Decide whether a (non-null) managed reference `r` is a subtype of the
abstract heap type `ht`. Concrete struct/array type indices are resolved
against the module's GC type definitions and their declared supertypes. -/
def AnyRef.matchesHeap (m : Module) (st : Store α) (ht : GcHeapType) : AnyRef → Bool
  | .host _ => ht == .any
  | .i31 _ => match ht with
    | .any | .eq | .i31 => true
    | _ => false
  | .struct addr => match ht with
    | .any | .eq | .structT => true
    | .concrete t => match st.gcHeap[addr]? with
      | some obj => m.gcTypeSubtype obj.typeIdx t
      | none     => false
    | _ => false
  | .array addr => match ht with
    | .any | .eq | .arrayT => true
    | .concrete t => match st.gcHeap[addr]? with
      | some obj => m.gcTypeSubtype obj.typeIdx t
      | none     => false
    | _ => false

/-- Whether reference value `v` matches the target reference type
`(ref null?ₙ ht)` used by `ref.test`/`ref.cast`/`br_on_cast`. The null
reference matches exactly when the target is nullable and `ht` is in the
same (any vs func vs extern) bottom family.

A non-null funcref matches the abstract `func` heap type always, and a
concrete target `(ref $ft)` when the function's declared type is a
subtype of `$ft` (issue #96). When the declared type is unrecorded
(`funcTypeIdx? = none`, hand-built modules) the check degrades to
structural equality of the function's signature against the target's
composite type, mirroring `Module.indirectCallTypeOk`. -/
def gcRefMatches (m : Module) (st : Store α) (nullable : Bool)
    (ht : GcHeapType) : Value → Bool
  | .anyref none      => nullable && ht.inAnyHierarchy
  | .anyref (some r)  => r.matchesHeap m st ht
  | .funcref none     =>
    nullable &&
    (ht == .func || ht == .noFunc ||
     -- Null also inhabits every nullable *concrete* function type: the
     -- null funcref has type `nofunc`, the bottom of the func family.
     (match ht with
      | .concrete t => match m.gcComposite? t with
        | some (.func _) => true
        | _ => false
      | _ => false))
  | .funcref (some f) => match ht with
    | .func       => true
    | .concrete t =>
      (match m.funcTypeIdx? f with
       | some src => m.gcTypeSubtype src t
       | none     => match m.funcSig? f, m.gcComposite? t with
         | some fn, some (.func ty) => fn == ty
         | _, _ => false)
    | _ => false
  | .externref none   => nullable && (ht == .extern || ht == .noExtern)
  | .externref (some _) => ht == .extern
  | _                 => false

/-- Truncate a value to a packed field's width when storing it (GC
proposal); non-packed fields store the value unchanged. -/
def FieldType.pack (ft : FieldType) (v : Value) : Value :=
  match ft.storage, v with
  | .packed 8,  .i32 x => .i32 (x &&& 0xff)
  | .packed 16, .i32 x => .i32 (x &&& 0xffff)
  | _,          _      => v

/-- Read a field/element with sign extension (`*.get_s`): a packed
`i8`/`i16` slot is sign-extended to `i32`; everything else is unchanged. -/
def FieldType.readS (ft : FieldType) (v : Value) : Value :=
  match ft.storage, v with
  | .packed 8,  .i32 x => .i32 (if x &&& 0x80 ≠ 0 then x ||| 0xffffff00 else x)
  | .packed 16, .i32 x => .i32 (if x &&& 0x8000 ≠ 0 then x ||| 0xffff0000 else x)
  | _,          _      => v

/-- Read `n` little-endian bytes from a byte list as a `Nat`. Missing bytes
read as 0 (callers bounds-check first). -/
def readBytesLE (bytes : List UInt8) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (bytes[off + i]?.getD 0).toNat * 2 ^ (8 * i)) 0

/-- Read one storage-type element from a byte list (little-endian), for
`array.new_data` / `array.init_data`. -/
def readStorageLE (storage : StorageType) (bytes : List UInt8) (off : Nat) : Value :=
  let n := readBytesLE bytes off storage.byteSize
  match storage with
  | .packed _ => .i32 (UInt32.ofNat n)
  | .val .i32 => .i32 (UInt32.ofNat n)
  | .val .i64 => .i64 (UInt64.ofNat n)
  | .val .f32 => .f32 (UInt32.ofNat n)
  | .val .f64 => .f64 (UInt64.ofNat n)
  | .val _    => .i32 0

/-- Evaluate a simple element-segment item constant expression to its
reference value (GC proposal). Covers the forms element segments use:
`ref.func`; the null refs `ref.null func`/`extern`/`exn` and `ref.null`
of a GC heap type; the `i32`/`i64` scalar constants; and `ref.i31` of an
`i32.const`. Heap-allocating items (`struct.new`) are not handled here. -/
def evalConstRef : Program → Option Value
  | [.refFunc f]                 => some (.funcref (some f))
  | [.refNull _]                 => some (.funcref none)
  | [.refNullExtern _]           => some (.externref none)
  | [.refNullExn _]              => some (.exnref none)
  | [.gc (.refNullAny _)]        => some (.anyref none)
  | [.const n]                   => some (.i32 n)
  | [.constI64 n]                => some (.i64 n)
  | [.const n, .gc .refI31]      => some (.anyref (some (.i31 (n &&& 0x7fffffff))))
  | _                            => none

/-- The reference values a (passive, non-dropped) element segment yields,
preferring decoded GC const-expr items and falling back to funcref
indices. -/
def ElementSegment.values (seg : ElementSegment) : List Value :=
  if seg.exprs.isEmpty then seg.plainValues
  else seg.exprs.map (fun e => (evalConstRef e).getD (.anyref none))

/-- Host-supplied extern handles occupy the unsigned 64-bit range. Handles
at or above this boundary are deterministic encodings of Wasm-managed
references externalized by `extern.convert_any`. -/
def externInternalBase : Nat := 2 ^ 64

def AnyRef.toExternId : AnyRef → Nat
  | .host id => id
  | .i31 value => externInternalBase + 3 * value.toNat
  | .struct address => externInternalBase + 3 * address + 1
  | .array address => externInternalBase + 3 * address + 2

def anyRefOfExternId (id : Nat) : AnyRef :=
  if id < externInternalBase then .host id
  else
    let encoded := id - externInternalBase
    match encoded % 3 with
    | 0 => .i31 ((encoded / 3).toUInt32 &&& 0x7fffffff)
    | 1 => .struct (encoded / 3)
    | _ => .array (encoded / 3)

/-- Ex…28697 tokens truncated… -- Standard Wasm calling convention. Params are reversed so local 0
      -- is the first (deepest) argument; only the top `f.results.length`
      -- values are returned to the caller; remaining caller args pass
      -- through unchanged.
      let callerRemainder := params.drop f.numParams
      match exec fuel m initial (f.toLocals (params.take f.numParams).reverse) f.body env with
      | Continuation.Fallthrough st s => .Success (s.values.take f.results.length ++ callerRemainder) st
      | Continuation.Return st vs     => .Success (vs.take f.results.length ++ callerRemainder) st
      | Continuation.Break 0 st s     => .Success (s.values.take f.results.length ++ callerRemainder) st
      | Continuation.Break (_+1) _ _  => .Invalid "Unexpected break targeting scope out of function"
      | Continuation.Invalid msg      => .Invalid msg
      | Continuation.OutOfFuel        => .OutOfFuel
      | Continuation.Trap st msg      => .Trap st msg
      -- Tail call: the callee replaces this frame. Validation guarantees
      -- the callee's result types equal `f.results`, so truncating its
      -- results to `f.results.length` and restoring this frame's
      -- caller-remainder preserves the standard calling convention.
      | Continuation.Throwing tag args st' _ => .Thrown tag args st'
      | Continuation.ReturnCall id' st' vs =>
        match runTail fuel m id' st' vs env with
        | .Success vs2 st2 => .Success (vs2.take f.results.length ++ callerRemainder) st2
        | other => other
    | none => .Invalid "Function index out of bounds"

/-- Resolve a pending tail call: re-dispatch with one less fuel. Kept as
its own (mutual) definition so `run`'s equation lemma does not mention
`run` itself — `simp only [run]` unfolds one frame and stops at
`runTail`, exactly like the pre-tail-call unfolding discipline. -/
def runTail (fuel : Nat) (m : Module) (id : Nat)
    (st : Store α) (vs : List Value) (env : HostEnv α := {}) : Result α :=
  match fuel with
  | 0 => .OutOfFuel
  | f' + 1 => run f' m id st vs env

end

/-- Evaluate the constant-expression initializers of globals that need to
run at instantiation (GC proposal: `struct.new`/`array.new*` allocate heap
objects). Each global's `initExpr` is executed in order against the
current store — so a later initializer sees earlier globals (`global.get`)
and the accumulated `gcHeap` — and its result value is written into the
global slot. Globals with an empty `initExpr` keep their decoded `init`. -/
def Module.runConstGlobals (fuel : Nat) (m : Module) (st : Store α)
    (env : HostEnv α := {}) : Store α := Id.run do
  let mut st := st
  let mut gi := 0
  for g in m.globals do
    if !g.initExpr.isEmpty then
      match exec fuel m st {} g.initExpr env with
      | .Fallthrough st' s' =>
        match s'.values with
        | v :: _ =>
          st := { st' with globals := { globals := st'.globals.globals.set gi v } }
        | [] => pure ()
      | _ => pure ()
    gi := gi + 1
  return st

/-- Evaluate the constant-expression items of active GC element segments
(GC proposal) and write the resulting reference values into their tables.
Runs after `runConstGlobals` so items may read globals. Plain funcref
segments (`funcs`) are applied separately and have no `exprs`. -/
def Module.runConstElems (fuel : Nat) (m : Module) (st : Store α)
    (env : HostEnv α := {}) : Store α := Id.run do
  let mut st := st
  for (seg, segIndex) in m.elements.zipIdx do
    -- Passive/declarative GC segments need their item expressions evaluated
    -- into runtime values even though they are not written to a table yet.
    if seg.offset.isNone && !seg.exprs.isEmpty then
      let mut values : List Value := []
      for e in seg.exprs do
        match exec fuel m st {} e env with
        | .Fallthrough st' s' =>
          st := st'
          match s'.values with
          | value :: _ => values := values ++ [value]
          | [] => pure ()
        | _ => pure ()
      st :=
        { st with
          elementValues := st.elementValues.set segIndex (some values) }
    match seg.tableIdx, seg.offset with
    | some ti, some off =>
      -- Segments whose offset is itself a pending const-expr are written
      -- by `runActiveSegments` (which knows the real offset) instead.
      if !seg.exprs.isEmpty && seg.offsetExpr.isEmpty then
        let mut i := 0
        for e in seg.exprs do
          match exec fuel m st {} e env with
          | .Fallthrough st' s' =>
            st := st'
            match s'.values, st'.tables[ti]? with
            | v :: _, some tbl =>
              st := { st' with tables := st'.tables.set ti (tbl.set (off + i) v) }
            | _, _ => pure ()
          | _ => pure ()
          i := i + 1
    | _, _ => pure ()
  return st

/-- Write the active data/element segments whose offset is a constant
expression that could not be folded at decode time (`global.get` of an
imported global, extended-const arithmetic). `Module.initialStore` skips
these segments (their offset depends on the store); this pass evaluates
each `offsetExpr` against the current store and writes the segment at
the computed offset. Runs after `runConstGlobals` so the offsets see the
evaluated (and imported) globals. -/
def Module.runActiveSegments (fuel : Nat) (m : Module) (st : Store α)
    (env : HostEnv α := {}) : Store α := Id.run do
  let mut st := st
  -- Evaluate one offset const-expr to a byte/element offset. `i64`
  -- results come from memory64/table64 modules.
  let evalOffset (st : Store α) (prog : Program) : Option Nat :=
    match exec fuel m st {} prog env with
    | .Fallthrough _ s' =>
      match s'.values with
      | .i32 v :: _ => some v.toNat
      | .i64 v :: _ => some v.toNat
      | _           => none
    | _ => none
  -- Active data segments with a pending offset expression. Segments live
  -- in one global, source-ordered list (memory 0's `data`), routed to
  -- their memory by `DataSegment.memIdx`.
  let segs := match m.memory with
    | some decl => decl.data
    | none      => []
  for seg in segs do
    if seg.offset.isSome && !seg.offsetExpr.isEmpty then
      match evalOffset st seg.offsetExpr with
      | some off =>
        if seg.memIdx = 0 then
          if off + seg.bytes.length ≤ st.mem.pages * 65536 then
            st := { st with mem := st.mem.writeBytes off seg.bytes }
        else
          match st.extraMems[seg.memIdx - 1]? with
          | some mem0 =>
            if off + seg.bytes.length ≤ mem0.pages * 65536 then
              let mems := st.extraMems.set (seg.memIdx - 1)
                (mem0.writeBytes off seg.bytes)
              st := { st with extraMems := mems }
          | none => pure ()
      | none => pure ()
  -- Active element segments with a pending offset expression.
  for seg in m.elements do
    match seg.tableIdx, seg.offset with
    | some ti, some _ =>
      if !seg.offsetExpr.isEmpty then
        match evalOffset st seg.offsetExpr, st.tables[ti]? with
        | some off, some tbl =>
          let length := if seg.exprs.isEmpty then
            seg.funcs.length else seg.exprs.length
          if off + length ≤ tbl.length && seg.exprs.isEmpty then
            let tbls := st.tables.set ti (listWriteAt tbl off (seg.funcs.map Value.funcref))
            st := { st with tables := tbls }
          else if off + length ≤ tbl.length then
            -- GC const-expr items, as in `runConstElems`, but at the
            -- evaluated offset.
            let mut i := 0
            for e in seg.exprs do
              match exec fuel m st {} e env with
              | .Fallthrough st' s' =>
                st := st'
                match s'.values, st'.tables[ti]? with
                | v :: _, some tbl' =>
                  st := { st' with tables := st'.tables.set ti (tbl'.set (off + i) v) }
                | _, _ => pure ()
              | _ => pure ()
              i := i + 1
        | _, _ => pure ()
    | _, _ => pure ()
  return st

end Wasm