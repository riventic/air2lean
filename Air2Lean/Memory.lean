import Std.Data.HashMap
import Air2Lean.Air.Op
import Air2Lean.StdModels

/-!
# Memory analysis

Shared by `Check.lean` and `Emit.lean` (`docs/generated-code.md` §Memory):

* A **place** is an `alloc` (a `var`, or `ret_ptr`), a field pointer of a place (a struct
  field, or the length or item pointer of a slice), a validated local `field_parent_ptr`,
  or a pointer `bitcast` with the same
  child type. A place whose `alloc` does not escape stays a `Locals` field.
* An `alloc` **escapes** if one of its places is used other than as the pointer operand of
  `load`, `store`, `struct_field_ptr`, `field_parent_ptr`, `ptr_slice_len_ptr`, `ptr_slice_ptr_ptr`, `bitcast`,
  `set_union_tag`, `ret_load`, an atomic op, or in `dbg`. An escaping `alloc` is a stack block in
  memory. A cast to a different pointee also escapes: its loads and stores reinterpret bytes.
  A place passed to `Thread.spawn` escapes (it is not in this list), so a variable shared
  with a spawned thread is a memory block subject to the race check (`ZigLean/Mem/Thread.lean`).
  A store of a partly `undefined` constant to a place also escapes: a `Locals` field has no
  undefined parts, memory has undefined bytes.
* A store of a wholly `undefined` value to a place that a read can observe (`deadUndefStores`)
  makes its `alloc` a **byte local** (`byteLocals`, a `Zig.Bytes T` field of `Locals`) if
  `byteLocalOk`, else it escapes.
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
    | .fieldPtr b _ | .fieldParentPtr b _ | .bitcast b | .sliceFieldPtr _ b => match root? b with
      | some r => acc.push (i.id, r)
      | none => acc
    | _ => acc

/-- Typed provenance for a local projection. Slice fields cannot be undone by
`field_parent_ptr`; a struct step remembers its actual container and pointer type. -/
inductive LocalPathStep where
  | field (parent : TyId) (index : Nat) (pointer : TyId)
  | slice
  deriving Inhabited

/-- Recover exactly the proven terminal ordinary-struct field. This is a place identity,
not address arithmetic: the root and all preceding steps remain unchanged. -/
def localParentPath? (types : Array Ty) (layouts : Array Layout) (source result : TyId)
    (index : Nat) (path : Array LocalPathStep) : Option (Array LocalPathStep) := do
  let some (.field parent actualIndex projected) := path.back? | none
  let some (.ptr "one" sourceConst child) := types[source]? | none
  let some (.ptr "one" resultConst container) := types[result]? | none
  let some (.ptr "one" _ projectedChild) := types[projected]? | none
  let some (.struct _ layout fields) := types[parent]? | none
  let (_, field) ← fields[index]?
  if (layout != "auto" && layout != "extern") || parent != container || index != actualIndex ||
      child != field || projectedChild != field || (sourceConst && !resultConst) then none
  else if nullablePtrTy types layouts source || nullablePtrTy types layouts result ||
      #[source, result, projected].any (fun t => (layouts[t]?.map (·.hostSize)).getD 0 != 0) then none
  else if (layouts[source]?.map (·.isVolatile)).getD false &&
      !(layouts[result]?.map (·.isVolatile)).getD false then none
  else some (path.pop)

/-- Local paths before escape lowering. Invalid parent recovery has no path, but its root
still propagates through `placeRoots` so it cannot evade the checker by escaping. -/
def localPlacePaths (types : Array Ty) (layouts : Array Layout) (insts : Array Inst) :
    Array (InstId × Array LocalPathStep) :=
  if !insts.any (fun i => match i.op with | .fieldParentPtr .. => true | _ => false) then #[] else
  -- Preserve `find?`'s first-occurrence semantics, including bare duplicate-ID callers.
  let instructionTypes := insts.foldl (init := ({} : Std.HashMap InstId TyId)) fun acc i =>
    if acc.contains i.id then acc else acc.insert i.id i.ty
  let type? (b : InstId) := instructionTypes[b]?
  insts.foldl (init := #[]) fun acc i =>
    let path? (b : InstId) := (acc.find? (·.1 == b)).map (·.2)
    match i.op with
    | .alloc => acc.push (i.id, #[])
    | .fieldPtr (.inst b) idx =>
      match path? b, (type? b).bind (fun t => match types[t]? with
          | some (.ptr _ _ c) => some c | _ => none) with
      | some path, some parent => acc.push (i.id, path.push (.field parent idx i.ty))
      | _, _ => acc
    | .sliceFieldPtr _ (.inst b) =>
      match path? b with
      | some path => acc.push (i.id, path.push .slice)
      | none => acc
    | .bitcast (.inst b) =>
      match path? b, type? b with
      | some path, some ty => if samePointee types ty i.ty then acc.push (i.id, path) else acc
      | _, _ => acc
    | .fieldParentPtr (.inst b) idx =>
      match path? b, type? b with
      | some path, some ty =>
        match localParentPath? types layouts ty i.ty idx path with
        | some parent => acc.push (i.id, parent)
        | none => acc
      | _, _ => acc
    | _ => acc

/-- The operands of `op` that are read as values: every operand except the pointer operand of
`load`, `store`, `struct_field_ptr`, `bitcast`, `set_union_tag`, `ret_load`, and `dbg`. -/
def valueOperands (op : Op) : Array Val :=
  match op with
  | .arg _ | .alloc | .unreach | .trap | .line _ | .dbg _ _ | .«repeat» _ => #[]
  | .arith _ _ a b | .div _ a b | .divFloat a b | .minMax _ a b | .withOverflow _ a b
  | .shlWithOverflow a b | .bit _ a b | .shift _ a b | .cmp _ a b | .boolAnd a b | .boolOr a b => #[a, b]
  | .countBits _ a | .permuteBits _ a | .not a | .neg a | .abs a | .intCast a | .trunc a | .floatRound _ a | .sqrt a | .libm _ a
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

/-- An `undefined` strictly below the root of a constant. Emission would read it as a typed
default (`0`, `false`), so a partly undefined global initializer fails closed. -/
partial def Val.hasNestedUndef (v : Val) : Bool :=
  let undefOrNested (v : Val) : Bool := match v with
    | .undef _ => true
    | v => v.hasNestedUndef
  match v with
  | .agg _ elems => elems.any undefOrNested
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => undefOrNested v
  | .sliceConst _ p l => undefOrNested p || undefOrNested l
  | _ => false

/-- The byte ranges `(offset, length)`, from `base`, of the `undefined` parts of the constant
`v` of type `tid` in memory: the bytes that a store of `v` leaves undefined. Only an `undefined`
item of an array, or field of a non-`packed` struct or tuple, at any depth, has a range (from
the exporter's sizes and field offsets, which `Check.lean` compares with the model's encoding).
`none` for an `undefined` part under an optional, error union, union, slice, vector or packed
struct, or an unknown layout: such a store is outside the subset. -/
partial def undefByteRanges (types : Array Ty) (layouts : Array Layout) (tid : TyId) (v : Val)
    (base : Nat := 0) : Option (Array (Nat × Nat)) := do
  match v with
  | .undef _ =>
    let size ← (layouts[tid]?).bind (·.size)
    pure (if size == 0 then #[] else #[(base, size)])
  | .agg _ elems =>
    if !v.hasNestedUndef then return #[]
    -- The type and byte offset of each item or field.
    let parts : Array (TyId × Nat) ← match types[tid]? with
      | some (.array _ child _) =>
        let stride ← (layouts[child]?).bind (·.size)
        pure (elems.mapIdx fun k _ => (child, k * stride))
      | some (.struct _ layout fields) =>
        let offsets := ((layouts[tid]?).map (·.offsets)).getD #[]
        if layout == "packed" || offsets.size != fields.size then none
        pure ((fields.zip offsets).map fun ((_, t), o) => (t, o))
      | some (.tuple fields) =>
        let offsets := ((layouts[tid]?).map (·.offsets)).getD #[]
        if offsets.size != fields.size then none
        pure (fields.zip offsets)
      | _ => none
    if parts.size != elems.size then none
    (elems.zip parts).foldlM (init := #[]) fun acc (e, t, o) =>
      (acc ++ ·) <$> undefByteRanges types layouts t e (base + o)
  | v => if v.hasNestedUndef then none else pure #[]

/-- The `alloc`s of `f` that escape by their uses. A store of a partly `undefined` constant to a
place makes its `alloc` escape: memory holds the undefined parts as undefined bytes
(`undefByteRanges`). -/
def usesEscapingAllocs (f : Func) : Array InstId :=
  let insts := f.allInsts
  let roots := placeRoots insts
  insts.foldl (init := #[]) fun acc i =>
    let operands := valueOperands i.op ++ match i.op with
      | .store p v => if v.hasNestedUndef then #[p] else #[]
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

/-- The instruction list of `body` and of each nested body. -/
partial def bodyLists (body : Array Inst) : Array (Array Inst) :=
  #[body] ++ body.flatMap fun i => match i.op with
    | .block b | .loop b | .«try» _ b | .tryPtr _ b => bodyLists b
    | .condBr _ t e => bodyLists t ++ bodyLists e
    | .switchBr _ cs e | .loopSwitchBr _ cs e => cs.flatMap (bodyLists ·.body) ++ bodyLists e
    | _ => #[]

/-- Every operand of `op` that can be a place: the value operands, the pointer operands and the
places that an asm output writes. -/
def placeOperands (op : Op) : Array Val :=
  valueOperands op ++ match op with
    | .load p | .store p _ | .fieldPtr p _ | .fieldParentPtr p _ | .retLoad p | .sliceFieldPtr _ p
    | .bitcast p | .setUnionTag p _ | .atomicLoad p _ | .atomicStore p .. | .atomicRmw _ _ p _
    | .cmpxchg _ p .. => #[p]
    | .asm _ _ _ outputs _ => outputs.filterMap (·.ref)
    | _ => #[]

/-- The places of the `alloc` `a`. -/
def placesOf (roots : Array (InstId × InstId)) (a : InstId) : Array InstId :=
  roots.filterMap fun (p, r) => if r == a then some p else none

/-- The stores of a wholly `undefined` value to an `alloc` itself that no read can observe: the
next instruction of the same body that uses a place of the `alloc` (`dbg` aside) writes the
whole local with a defined value (a `store`, or an output-only `=` asm output), and no
instruction before it can leave the body to an enclosing block or loop (`br`, `repeat`, a
dispatch), which could reach a read past the write. -/
def deadUndefStores (f : Func) : Array InstId :=
  let insts := f.allInsts
  -- `j` (or a body inside it) can jump to a block or loop that encloses `j`.
  let leaves (j : Inst) : Bool :=
    let inner := flattenInst #[] j
    inner.any fun x => match x.op with
      | .br t _ | .«repeat» t | .switchDispatch t _ => !inner.any (·.id == t)
      | _ => false
  let roots := placeRoots insts
  (bodyLists f.body).foldl (init := #[]) fun acc body =>
    body.zipIdx.foldl (init := acc) fun acc (i, k) => match i.op with
      | .store (.inst a) (.undef _) =>
        if !insts.any (fun j => j.id == a && j.op matches .alloc) then acc else
        let ps := placesOf roots a
        let usesA (j : Inst) : Bool := (flattenInst #[] j).any fun x => match x.op with
          | .dbg .. => false
          | op => (placeOperands op).any fun v => match v with
            | .inst id => ps.contains id
            | _ => false
        let overwrites (j : Inst) : Bool := match j.op with
          | .store (.inst p) v => p == a && !(v matches .undef _) && !v.hasNestedUndef
          | .asm _ _ _ outputs inputs =>
            outputs.any (fun o => o.ref == some (.inst a) && o.constraint.startsWith "=") &&
              !inputs.any fun o => match o.ref with
                | some (.inst id) => ps.contains id
                | _ => false
          | _ => false
        match (body.extract (k + 1) body.size).find? (fun j => usesA j || leaves j) with
        | some j => if overwrites j then acc.push i.id else acc
        | none => acc
      | _ => acc

/-- The `alloc`s that receive a store of a wholly `undefined` value that a read can observe
(not `deadUndefStores`), through any of their places. -/
def undefAllocs (f : Func) : Array InstId :=
  let insts := f.allInsts
  if !insts.any (fun i => i.op matches .store _ (.undef _)) then #[] else
  let roots := placeRoots insts
  let dead := deadUndefStores f
  insts.foldl (init := #[]) fun acc i => match i.op with
    | .store (.inst p) (.undef _) =>
      if dead.contains i.id then acc else
      match roots.find? (·.1 == p) with
      | some (_, r) => if acc.contains r then acc else acc.push r
      | none => acc
    | _ => acc

/-- The byte offset of field `idx` of the non-`packed` struct `tid`; `none` for every other type. -/
def structFieldOffset? (types : Array Ty) (layouts : Array Layout) (tid : TyId) (idx : Nat) :
    Option Nat := do
  let some (.struct _ layout fields) := types[tid]? | none
  if layout == "packed" then none
  let offsets := (layouts[tid]?.map (·.offsets)).getD #[]
  if offsets.size != fields.size then none
  offsets[idx]?

/-- The `alloc` `a` can be a byte local (`Zig.Bytes`): its type has no pointer, and each of its
places is the `alloc` or a field pointer of a non-`packed` struct, used only by `load`, `store`
(as the pointer), `struct_field_ptr` and `dbg`. -/
def byteLocalOk (f : Func) (insts : Array Inst) (roots : Array (InstId × InstId)) (a : InstId) :
    Bool :=
  let ps := placesOf roots a
  let isP (v : Val) : Bool := match v with | .inst id => ps.contains id | _ => false
  let tyOf (id : InstId) : Option TyId := (insts.find? (·.id == id)).map (·.ty)
  let child (id : InstId) : Option TyId := (tyOf id).bind fun t => match f.types[t]? with
    | some (.ptr _ _ c) => some c
    | _ => none
  (child a).any (!hasPtr f.types ·) &&
  insts.all fun i =>
    if !(placeOperands i.op).any isP then true else
    match i.op with
    | .load p => isP p
    | .store p v => isP p && !isP v
    | .fieldPtr p@(.inst b) idx =>
      isP p && (f.layouts[i.ty]?.map (·.hostSize)).getD 0 == 0 &&
        ((child b).bind (structFieldOffset? f.types f.layouts · idx)).isSome
    | .dbg .. => true
    | _ => false

/-- The byte locals of `f`: the `undefAllocs` that do not escape by their uses and are
`byteLocalOk`. Each is a `Locals` field of type `Zig.Bytes T`. -/
def byteLocals (f : Func) : Array InstId :=
  let insts := f.allInsts
  let roots := placeRoots insts
  let base := usesEscapingAllocs f
  (undefAllocs f).filter fun a => !base.contains a && byteLocalOk f insts roots a

/-- The `alloc`s of `f` that escape: by their uses (`usesEscapingAllocs`), and the `undefAllocs`
that cannot be byte locals (`byteLocalOk`), whose undefined bytes memory holds. -/
def escapingAllocs (f : Func) : Array InstId :=
  let insts := f.allInsts
  let roots := placeRoots insts
  let base := usesEscapingAllocs f
  base ++ (undefAllocs f).filter fun a => !base.contains a && !byteLocalOk f insts roots a

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
  | .call (.func name ..) _ => modelledStdFn name
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

/-- The function type name of the pointer type `ty`, if it points to a function. -/
def fnPtrTyName? (types : Array Ty) (ty : TyId) : Option String := do
  let .ptr _ _ c ← types[ty]? | none
  let child ← types[c]?
  unless isFnTy child do none
  let .other tn := child | none
  pure tn

/-- The function type name of the indirect callee `id` (a pointer to a function). -/
def Func.calleeFnTy? (f : Func) (id : InstId) : Option String := do
  let i ← f.allInsts.find? (·.id == id)
  fnPtrTyName? f.types i.ty

/-- An indirect callee: an instruction, or a constant address (`ptrConst`). Every function
pointer resolves through the one table of address-taken functions (`fnRefs`), whatever its
origin (L11). -/
def Val.isIndirectCallee : Val → Bool
  | .inst _ | .ptrConst .. => true
  | _ => false

/-- The function type name of an indirect callee (`Val.isIndirectCallee`). -/
def Func.calleeValFnTy? (f : Func) (callee : Val) : Option String :=
  match callee with
  | .inst id => f.calleeFnTy? id
  | .ptrConst ty .. => fnPtrTyName? f.types ty
  | _ => none

/-- The functions that an indirect call in `f` can call (`fnRefs`). -/
def Func.indirectCallees (f : Func) (refs : Array (String × String)) : Array String :=
  f.allInsts.flatMap fun i => match i.op with
    | .call v _ => if !v.isIndirectCallee then #[] else match f.calleeValFnTy? v with
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
