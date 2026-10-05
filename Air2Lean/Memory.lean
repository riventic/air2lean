import Air2Lean.Air.Op

/-!
# Memory analysis

Shared by `Check.lean` and `Emit.lean` (`docs/generated-code.md` §Memory):

* A **place** is an `alloc` (a `var`, or `ret_ptr`), a field pointer of a place (a struct
  field, or the length or item pointer of a slice), or a pointer `bitcast` with the same
  child type. A place whose `alloc` does not escape stays a `Locals` field.
* An `alloc` **escapes** if one of its places is used other than as the pointer operand of
  `load`, `store`, `struct_field_ptr`, `ptr_slice_len_ptr`, `ptr_slice_ptr_ptr`, `bitcast`,
  `set_union_tag`, `ret_load`, an atomic op, or in `dbg`. An escaping `alloc` is a stack block in
  memory. A cast to a different pointee also escapes: its loads and stores reinterpret bytes.
  A place passed to `Thread.spawn` escapes (it is not in this list), so a variable shared
  with a spawned thread is a memory block subject to the race check (`ZigLean/Mem/Thread.lean`).
* A function is **pure** if no parameter and not the return type contains a pointer (a top-level
  `[]const T` parameter with a pointer-free `T` is allowed), no `alloc` escapes, it has no
  pointer constant and no memory op (`memoryOp`, which includes a call to the allocator model),
  and it calls only pure functions. Every other function **uses memory**.
-/

namespace Air2Lean

mutual
partial def flattenInst (acc : Array Inst) (i : Inst) : Array Inst :=
  flattenOp (acc.push i) i.op

partial def flattenOp (acc : Array Inst) (op : Op) : Array Inst :=
  match op with
  | .block body => body.foldl flattenInst acc
  | .loop body => body.foldl flattenInst acc
  | .condBr _ t e => e.foldl flattenInst (t.foldl flattenInst acc)
  | .switchBr _ cases e | .loopSwitchBr _ cases e =>
    let acc := cases.foldl (fun acc c => c.body.foldl flattenInst acc) acc
    e.foldl flattenInst acc
  | .«try» _ errBody | .tryPtr _ errBody => errBody.foldl flattenInst acc
  | _ => acc
end

def Func.allInsts (f : Func) : Array Inst := f.body.foldl flattenInst #[]

/-- Every place of `insts` with its `alloc`: `(place, alloc)`. -/
def placeRoots (insts : Array Inst) : Array (InstId × InstId) :=
  insts.foldl (init := #[]) fun acc i =>
    let root? (v : Val) : Option InstId := match v with
      | .inst b => (acc.find? (·.1 == b)).map (·.2)
      | _ => none
    match i.op with
    | .alloc => acc.push (i.id, i.id)
    | .fieldPtr b _ | .bitcast b | .sliceFieldPtr _ b => match root? b with
      | some r => acc.push (i.id, r)
      | none => acc
    | _ => acc

/-- The operands of `op` that are read as values: every operand except the pointer operand of
`load`, `store`, `struct_field_ptr`, `bitcast`, `set_union_tag`, `ret_load`, and `dbg`. -/
def valueOperands (op : Op) : Array Val :=
  match op with
  | .arg _ | .alloc | .unreach | .trap | .line _ | .dbg _ _ | .«repeat» _ => #[]
  | .arith _ _ a b | .div _ a b | .divFloat a b | .minMax _ a b | .withOverflow _ a b
  | .shlWithOverflow a b | .bit _ a b | .shift _ a b | .cmp _ a b | .boolAnd a b | .boolOr a b => #[a, b]
  | .countBits _ a | .not a | .neg a | .abs a | .intCast a | .trunc a | .floatRound _ a | .sqrt a | .libm _ a
  | .floatConv a | .floatFromInt a | .intFromFloat _ a | .isNull a | .isNonNull a
  | .optPayload a | .wrapOptional a | .isErr a | .isNonErr a | .errPayload a | .errCode a
  | .wrapErrPayload a | .wrapErr a | .isNamedEnum a | .unionTag a | .unionInit _ a => #[a]
  -- A place has no optional-payload or error-union path: the local becomes a stack block.
  | .isNullPtr _ p | .optPayloadPtr _ p | .isErrPtr _ p | .errPayloadPtr _ p | .errCodePtr p => #[p]
  | .mulAdd a b c => #[a, b, c]
  | .splat a | .reduce _ a => #[a]
  | .select pred a b => #[pred, a, b]
  | .shuffle a b mask =>
    #[a] ++ (match b with | some v => #[v] | none => #[]) ++
      mask.filterMap fun l => match l with | .value v => some v | _ => none
  | .bitcast _ | .fieldPtr .. | .fieldParentPtr .. | .sliceFieldPtr .. | .load _ | .retLoad _ => #[]
  | .atomicLoad .. => #[]
  | .atomicStore _ v _ => #[v]
  | .atomicRmw _ _ _ v => #[v]
  | .cmpxchg _ _ expected new _ _ => #[expected, new]
  | .ptrAdd _ a b | .elemPtr a b | .ptrElemVal a b | .arrayElemVal a b | .slice a b
  | .memset a b | .memcpy a b => #[a, b]
  | .slicePtr a | .arrayToSlice a | .tagName a | .errorName a => #[a]
  | .setUnionTag _ tag => #[tag]
  | .store _ v => #[v]
  | .sliceLen s => #[s]
  | .sliceElemVal s i => #[s, i]
  | .structFieldVal s _ => #[s]
  | .aggregateInit elems => elems
  | .call callee args => #[callee] ++ args
  | .block _ | .loop _ => #[]
  | .br _ v | .switchDispatch _ v | .ret v | .«try» v _ | .tryPtr v _ => #[v]
  | .condBr c _ _ => #[c]
  | .switchBr v cases _ | .loopSwitchBr v cases _ =>
    #[v] ++ cases.foldl (fun acc c =>
      let acc := c.items.foldl Array.push acc
      c.ranges.foldl (fun acc (lo, hi) => (acc.push lo).push hi) acc) #[]
  -- Only the inputs are read as values (like `call`'s args); an output's `ref` (if present) is a
  -- place the result stores to, like `store`'s pointer operand, so it is excluded here.
  | .asm _ _ _ _ inputs =>
    inputs.foldl (init := #[]) fun acc i =>
      match i.ref with
      | some v => acc.push v
      | none => acc

/-- The `alloc`s of `f` that escape. -/
def escapingAllocs (f : Func) : Array InstId :=
  let insts := f.allInsts
  let roots := placeRoots insts
  insts.foldl (init := #[]) fun acc i =>
    let operands := valueOperands i.op ++ match i.op with
      | .bitcast v@(.inst id) =>
        match insts.find? (·.id == id) with
        | some source => if samePointee f.types source.ty i.ty then #[] else #[v]
        | none => #[]
      | _ => #[]
    operands.foldl (init := acc) fun acc v =>
      match v with
      | .inst id => match roots.find? (·.1 == id) with
        | some (_, r) => if acc.contains r then acc else acc.push r
        | none => acc
      | _ => acc

/-- The bit size of `id` as a field of a packed struct: an integer, a `bool`, an enum (its tag
integer), or another packed struct. `none` for every other type (outside the subset). -/
partial def packedBits (types : Array Ty) (id : TyId) : Option Nat :=
  match types[id]? with
  | some (.int _ bits) => some bits
  | some .bool => some 1
  | some (.enum _ tag _ _) => packedBits types tag
  | some (.struct _ "packed" fields) =>
    fields.foldlM (init := 0) fun acc (_, t) => (acc + ·) <$> packedBits types t
  | _ => none

/-- A packed struct field of type `id` has an enum, in any depth. -/
partial def packedHasEnum (types : Array Ty) (id : TyId) : Bool :=
  match types[id]? with
  | some (.enum ..) => true
  | some (.struct _ "packed" fields) => fields.any (packedHasEnum types ·.2)
  | _ => false

/-- The first bit of field `idx` of the packed struct `fields`: field 0 is at bit 0. -/
def packedFieldBit (types : Array Ty) (fields : Array (String × TyId)) (idx : Nat) : Nat :=
  (fields.extract 0 idx).foldl (fun acc (_, t) => acc + (packedBits types t).getD 0) 0

/-- The type `id` contains a pointer (a slice too), through struct, tuple, union and array
fields, optionals and error unions. -/
partial def hasPtr (types : Array Ty) (id : TyId) : Bool :=
  match types[id]? with
  | some (.ptr ..) | some .allocator | some .io => true
  | some (.array _ c _) | some (.optional c) | some (.errorUnion _ c) => hasPtr types c
  | some (.struct _ _ fs) | some (.union _ _ _ fs) => fs.any (hasPtr types ·.2)
  | some (.tuple fs) => fs.any (hasPtr types)
  | _ => false

/-- A parameter that a pure function can have: pointer-free, or a top-level `[]const T` with a
pointer-free `T`. -/
def pureParam (types : Array Ty) (id : TyId) : Bool :=
  match types[id]? with
  | some (.ptr "slice" true c) => !hasPtr types c
  | _ => !hasPtr types id

/-- A function of `std.mem.Allocator` that the model has (`ZigLean/Mem/Alloc.lean`). -/
inductive AllocFn where
  | create | destroy | alloc | alignedAlloc | free | dupe | remap
  deriving BEq, Repr

/-- The allocator function that the function `name` is an instance of
(`mem.Allocator.<fn>__anon_<n>`). -/
def allocFn? (name : String) : Option AllocFn :=
  match (name.splitOn "__anon_").head! with
  | "mem.Allocator.create" => some .create
  | "mem.Allocator.destroy" => some .destroy
  | "mem.Allocator.alloc" => some .alloc
  | "mem.Allocator.alignedAlloc" => some .alignedAlloc
  | "mem.Allocator.free" => some .free
  | "mem.Allocator.dupe" => some .dupe
  | "mem.Allocator.remap" => some .remap
  | _ => none

/-- `std.Thread.spawn`/`.join`, modelled like `AllocFn` (`ZigLean/Mem/Thread.lean`). -/
inductive ThreadFn where
  | spawn | join
  /-- Progress hints: scheduler opportunity, with no fairness guarantee. -/
  | yield | spinLoopHint
  /-- `Io.futexWait` (cancelable), `Io.futexWaitUncancelable`, `Io.futexWake` (0.16.0). -/
  | futexWait | futexWaitU | futexWake
  /-- `Thread.Futex.wait`, `Thread.Futex.wake` (0.14.1, 0.15.2). -/
  | threadFutexWait | threadFutexWake
  /-- `Thread.Mutex.DarwinImpl.lock`, `.unlock`, `.tryLock` (0.15.2 on macOS): each is one call of
  `os_unfair_lock_*`, a C function (the exporter does not name an `extern` function). -/
  | osLock | osUnlock | osTryLock
  /-- `time.Timer.start`, `time.Timer.read`, `Thread.Futex.timedWait`: a clock, which the model
  does not have. `Thread.Futex.Deadline` reaches them only with a timeout, so a call is
  `.unspecified` at run time (the diff test pins that count), not a rejection. -/
  | noClock
  /-- `Io.Group.async`, `.concurrent`, `.await`, `.cancel` (0.16.0): a task is a thread. -/
  | groupAsync | groupConcurrent | groupAwait | groupCancel
  deriving BEq, Repr

/-- The `Thread` function that the function `name` is an instance of
(`Thread.spawn__anon_<n>`, `Thread.join`). -/
def threadFn? (name : String) : Option ThreadFn :=
  match (name.splitOn "__anon_").head! with
  | "Thread.spawn" => some .spawn
  | "Thread.join" => some .join
  | "Thread.yield" => some .yield
  | "atomic.spinLoopHint" | "Thread.spinLoopHint" => some .spinLoopHint
  | "Io.futexWait" => some .futexWait
  | "Io.futexWaitUncancelable" => some .futexWaitU
  | "Io.futexWake" => some .futexWake
  | "Thread.Futex.wait" => some .threadFutexWait
  | "Thread.Futex.wake" => some .threadFutexWake
  | "Thread.Mutex.DarwinImpl.lock" => some .osLock
  | "Thread.Mutex.DarwinImpl.unlock" => some .osUnlock
  | "Thread.Mutex.DarwinImpl.tryLock" => some .osTryLock
  | "time.Timer.start" | "time.Timer.read" | "Thread.Futex.timedWait" => some .noClock
  | "Io.Group.async" => some .groupAsync
  | "Io.Group.concurrent" => some .groupConcurrent
  | "Io.Group.await" => some .groupAwait
  | "Io.Group.cancel" => some .groupCancel
  | _ => none

/-- A thread or sync primitive outside the fork-join subset (`docs/std-models.md` §Thread
model): `Check.lean` rejects a call to one of these, with this reason. -/
def rejectedThreadFn? (name : String) : Option String :=
  let base := (name.splitOn "__anon_").head!
  if base == "Io.futexWaitTimeout" then
    some "Io.futexWaitTimeout is outside the model: it has no clock"
  else if base == "Thread.detach" then
    some "Thread.detach is outside the fork-join subset: every spawned thread must be joined"
  else none

/-- Audited operand-free spin instructions emitted by `std.atomic.spinLoopHint` on
x86/x86_64 (and RISC-V with Zihintpause) and aarch64. Exact volatile instructions only:
other assembly keeps its opaque semantics. This is an extra scheduling opportunity, not a
memory fence or progress premise (`docs/progress-hints.md`). -/
def Op.isSpinHint : Op → Bool
  | .asm source true clobbers outputs inputs =>
    (source == "pause" || source == "isb") && clobbers.isEmpty && outputs.isEmpty && inputs.isEmpty
  | _ => false

/-- An op that only a function that uses memory has. -/
def memoryOp (op : Op) : Bool :=
  op.isSpinHint || match op with
  | .ptrAdd .. | .elemPtr .. | .ptrElemVal .. | .slice .. | .slicePtr _ | .arrayToSlice _
  | .sliceFieldPtr .. | .memset .. | .memcpy .. | .tagName _ | .errorName _ => true
  | .atomicLoad .. | .atomicStore .. | .atomicRmw .. | .cmpxchg .. | .tryPtr .. => true
  | .call (.func name ..) _ => (allocFn? name).isSome || (threadFn? name).isSome
  | _ => false

/-- A constant that points into memory. -/
partial def Val.pointsToMem (v : Val) : Bool :=
  match v with
  | .ptrConst .. | .ptrNull .. | .ptrOther .. | .sliceConst .. => true
  | .agg _ elems => elems.any Val.pointsToMem
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => v.pointsToMem
  | _ => false

/-- `f` uses memory by itself, not counting its calls. -/
def Func.usesMemoryLocally (f : Func) : Bool :=
  !f.params.all (pureParam f.types) || hasPtr f.types f.ret || !(escapingAllocs f).isEmpty ||
    f.allInsts.any fun i => memoryOp i.op || (valueOperands i.op).any Val.pointsToMem ||
      -- Nullable pointer temporaries need address observations even with no pointer
      -- parameters, no dereference and an integer/bool return.
      nullablePtrTy f.types f.layouts i.ty ||
      match i.op with
      | .load p | .store p _ | .fieldPtr p _ | .fieldParentPtr p _ | .retLoad p => p.pointsToMem
      | _ => false

/-- Is `id`'s value read anywhere in `f`, chasing it through a block-exit `br` that only
forwards it as the block's own value: a call to a generic/inline std function (e.g. `fetchAdd`)
always wraps its body in a `dbg_inline_block` that closes with a `br` carrying the call's
result, even when the caller discards it (`_ = ctx.counter.fetchAdd(...)`) — so `id` (the RMW
itself) is always referenced by that closing `br`, and the real "is it discarded" question is
whether the block's own id (the `br`'s target) is read afterward. -/
partial def valueUsed (allInsts : Array Inst) (id : InstId) : Bool :=
  allInsts.any fun i =>
    (valueOperands i.op).contains (.inst id) &&
    match i.op with
    | .br target _ => valueUsed allInsts target
    | _ => true

/-- A function type. The exporter writes it as `other`, with the name `fn (…) …`; it is only
behind a pointer (M20). -/
def isFnTy (t : Ty) : Bool := match t with | .other n => n.startsWith "fn (" | _ => false

/-- The functions whose address the program takes, as `(function type name, function name)`:
the globals whose initial value is a function. An indirect call through a pointer to that type
can call only these (M20). -/
def fnRefs (funcs : Array Func) : Array (String × String) :=
  funcs.foldl (init := #[]) fun acc f => f.globals.foldl (init := acc) fun acc g =>
    match g.init, f.types[g.ty]? with
    | some (.func nm ..), some (.other tn) => if acc.contains (tn, nm) then acc else acc.push (tn, nm)
    | _, _ => acc

/-- The function type name of the indirect callee `id` (a pointer to a function). -/
def Func.calleeFnTy? (f : Func) (id : InstId) : Option String := do
  let i ← f.allInsts.find? (·.id == id)
  let .ptr _ _ c ← f.types[i.ty]? | none
  let child ← f.types[c]?
  unless isFnTy child do none
  let .other tn := child | none
  pure tn

/-- The functions that an indirect call in `f` can call (`fnRefs`). -/
def Func.indirectCallees (f : Func) (refs : Array (String × String)) : Array String :=
  f.allInsts.flatMap fun i => match i.op with
    | .call (.inst v) _ => match f.calleeFnTy? v with
      | some tn => refs.filterMap fun (t, nm) => if t == tn then some nm else none
      | none => #[]
    | _ => #[]

def Func.callees (f : Func) (refs : Array (String × String)) : Array String :=
  f.allInsts.filterMap (fun i => match i.op with
    | .call (.func nm false ..) _ => some nm
    | _ => none) ++ f.indirectCallees refs

/-- The names of the functions in `funcs` that use memory: the local reasons, then every caller
of such a function, up to a fixpoint. -/
partial def memoryFunctions (funcs : Array Func) (externalMemory : Array String := #[]) : Array String :=
  let refs := fnRefs funcs
  let rec go (mem : Array String) : Array String :=
    let next := funcs.filterMap fun f =>
      if !mem.contains f.name && (f.callees refs).any mem.contains then some f.name else none
    if next.isEmpty then mem else go (mem ++ next)
  go (externalMemory ++ funcs.filterMap fun f => if f.usesMemoryLocally then some f.name else none)

/-- `f` has a sync op itself: an atomic op, or a call to `Thread.spawn`/`.join`. -/
def Func.syncLocally (f : Func) : Bool :=
  f.allInsts.any fun i => i.op.isSpinHint || match i.op with
    | .atomicLoad .. | .atomicStore .. | .atomicRmw .. | .cmpxchg .. => true
    | .call (.func name ..) _ => (threadFn? name).isSome
    | _ => false

/-- The names of the concurrent functions in `funcs` (`Zig.ConcM`): the ones with a sync op,
then every caller of such a function, up to a fixpoint. A concurrent function also uses memory
(`memoryOp`). -/
partial def concFunctions (funcs : Array Func) : Array String :=
  let refs := fnRefs funcs
  let rec go (conc : Array String) : Array String :=
    let next := funcs.filterMap fun f =>
      if !conc.contains f.name && (f.callees refs).any conc.contains then some f.name else none
    if next.isEmpty then conc else go (conc ++ next)
  go (funcs.filterMap fun f => if f.syncLocally then some f.name else none)

/-- The position of the args tuple of a call that spawns a thread: `Thread.spawn(config, f, args)`
(`f` is comptime), `Io.Group.async(g, io, f, args)`/`.concurrent`. -/
def ThreadFn.spawnArgs? : ThreadFn → Option Nat
  | .spawn => some 1
  | .groupAsync | .groupConcurrent => some 2
  | _ => none

/-- The spawn targets of `funcs`: each function that a `Thread.spawn` or an `Io.Group.async` runs,
with all captured argument types in source order, in first-use order. -/
def spawnTargets (funcs : Array Func) : Array (String × Func × Array TyId) :=
  funcs.foldl (init := #[]) fun acc f => f.allInsts.foldl (init := acc) fun acc i =>
    match i.op with
    | .call (.func name _ (some sf)) args =>
      if let some k := (threadFn? name).bind (·.spawnArgs?) then
        if acc.any (·.1 == sf) then acc else
        let argTys := ((args[k]? : Option Val).bind fun v => match v with
          | .inst p => (f.allInsts.find? (·.id == p)).map (·.ty)
          | v => v.constTy?).bind fun t => match f.types[t]? with
            | some (.tuple fs) => some fs
            | _ => none
        match argTys with
        | some fields => acc.push (sf, f, fields)
        | none => acc
      else acc
    | _ => acc

end Air2Lean
