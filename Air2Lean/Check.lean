import Air2Lean.Memory
import ZigLean.Mem.Enc

/-!
# Subset checker

`check : Func → Except String Unit` rejects anything `Emit.lean` cannot translate: `other`
types, a union without a tag, a float type outside `16 32 64 80 128` bits, an integer `@abs`, a
pointer other than `*T` or a read-only slice `[]const T`, and a memory access to a value that
the memory model cannot encode (`memTyOk`). `checkProgram` rejects a function that uses memory
and has a slice (`Air2Lean/Memory.lean`). Errors name the function and the nearest `dbg_stmt`
line.
-/

namespace Air2Lean

/-- Reject `other` types, an out-of-subset float width, and a pointer that is `[*c]T`,
`allowzero` or a bit-pointer, recursively through struct fields, array/optional children, and
tuple fields. -/
partial def checkTy (fnName : String) (types : Array Ty) (layouts : Array Layout) (line : Nat)
    (id : TyId) : Except String Unit := do
  let some ty := types[id]?
    | throw s!"{fnName}: near line {line}: unknown type id {id}"
  let recur := checkTy fnName types layouts line
  match ty with
  | .other name =>
    throw s!"{fnName}: near line {line}: type '{name}' is outside the subset (otherwise \
      unsupported)"
  | .float bits =>
    if bits == 16 || bits == 32 || bits == 64 || bits == 80 || bits == 128 then pure ()
    else
      throw s!"{fnName}: near line {line}: float type of {bits} bits is outside the subset \
        (only 16, 32, 64, 80, 128)"
  | .ptr size isConst child =>
    let l := layouts[id]?.getD {}
    if l.allowzero then
      throw s!"{fnName}: near line {line}: an `allowzero` pointer is outside the subset"
    if l.hostSize != 0 then
      throw s!"{fnName}: near line {line}: a pointer to a packed struct field is outside the \
        subset (M20)"
    let _ := isConst
    match size with
    | "one" | "many" | "slice" => recur child
    | _ => throw s!"{fnName}: near line {line}: a C pointer `[*c]T` is outside the subset"
  | .array _ child => recur child
  | .optional child => recur child
  | .errorUnion set payload => do
    recur set
    recur payload
  | .errorSet _ => pure ()
  | .struct _ _ fields => fields.forM fun (_, fty) => recur fty
  | .enum _ tag _ _ => recur tag
  | .union name layout tag fields =>
    match tag with
    | none =>
      throw s!"{fnName}: near line {line}: union '{name}' ({layout}, no tag) is outside the \
        subset (only a tagged `union(enum)`)"
    | some t =>
      unless (match types[t]? with | some (.enum ..) => true | _ => false) do
        throw s!"{fnName}: near line {line}: union '{name}': tag type {t} is not an enum"
      recur t
    fields.forM fun (_, fty) => recur fty
  | .tuple fields => fields.forM recur
  | .int .. | .bool | .void | .noreturn => pure ()

/-- The size and alignment that the memory model (`ZigLean/Mem/Enc.lean`) gives the type `id`,
or an error naming what the model cannot encode yet. A struct and an enum take the exporter's
values: their encodings are generated from the exporter's offsets. -/
partial def modelLayout (types : Array Ty) (layouts : Array Layout) (id : TyId) :
    Except String (Nat × Nat) := do
  let exported : Except String (Nat × Nat) :=
    match layouts[id]? with
    | some { size := some s, align := some a, .. } => pure (s, a)
    | _ => throw s!"type {id} has no layout in the AIR file"
  match types[id]? with
  | some (.int _ bits) => pure (Zig.intSize bits, Zig.intAlign bits)
  | some .bool => pure (1, 1)
  | some (.float bits) => pure (Zig.intSize bits, Zig.intAlign bits)
  | some .void => pure (0, 1)
  | some (.ptr "slice" ..) => pure (16, 8)
  | some (.ptr ..) => pure (8, 8)
  | some (.optional c) =>
    match types[c]? with
    | some (.ptr "slice" ..) => pure (16, 8)
    | some (.ptr ..) => pure (8, 8)
    | _ =>
      let (s, a) ← modelLayout types layouts c
      pure (Zig.alignUp (s + 1) a, a)
  | some (.array len c) =>
    if (layouts[id]?.map (·.sentinel)).getD false then
      throw "an array with a sentinel as one value"
    let (s, a) ← modelLayout types layouts c
    pure (len * s, a)
  | some (.enum _ tag _ _) =>
    let _ ← modelLayout types layouts tag
    exported
  | some (.struct name layout fields) =>
    if layout == "packed" then throw s!"packed struct '{name}' (M20)"
    for (_, fty) in fields do
      let _ ← modelLayout types layouts fty
    if (layouts[id]?.map (·.offsets.size)).getD 0 != fields.size then
      throw s!"struct '{name}' has no field offsets in the AIR file"
    exported
  | some (.errorUnion ..) | some (.errorSet _) => throw "an error union or error set (M20)"
  | some (.union name ..) => throw s!"union '{name}' (M20)"
  | some t => throw s!"{repr t}"
  | none => throw s!"unknown type id {id}"

/-- The type `id` can be in memory: the model encodes it, with the exporter's size and alignment. -/
def checkMemTy (fnName : String) (types : Array Ty) (layouts : Array Layout) (line : Nat)
    (id : TyId) : Except String Unit := do
  match modelLayout types layouts id with
  | .error e =>
    throw s!"{fnName}: near line {line}: a value in memory is outside the subset: {e}"
  | .ok (s, a) =>
    match layouts[id]? with
    | some { size := some s', align := some a', .. } =>
      unless s == s' && a == a' do
        throw s!"{fnName}: near line {line}: the memory model gives type {id} size {s} and \
          alignment {a}, the compiler {s'} and {a'}"
    | _ => throw s!"{fnName}: near line {line}: type {id} has no layout in the AIR file"

/-- The child type of the pointer type `id`. -/
def ptrChild (types : Array Ty) (id : TyId) : Option TyId :=
  match types[id]? with
  | some (.ptr _ _ c) => some c
  | _ => none

structure CheckCtx where
  fnName : String
  types : Array Ty
  layouts : Array Layout
  /-- The type of each instruction. -/
  instTys : Array (InstId × TyId)
  /-- The places of non-escaping `alloc`s (`Air2Lean/Memory.lean`). -/
  places : Array InstId

def CheckCtx.valTy? (cx : CheckCtx) (v : Val) : Option TyId :=
  match v with
  | .inst p => (cx.instTys.find? (·.1 == p)).map (·.2)
  | v => v.constTy?

def CheckCtx.fail {α : Type} (cx : CheckCtx) (line : Nat) (msg : String) : Except String α :=
  throw s!"{cx.fnName}: near line {line}: {msg}"

/-- The pointer type of `ptr`, a pointer that is not a place, with its `ptr_align`. -/
def CheckCtx.memPtrTy (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String TyId := do
  let some pty := cx.valTy? ptr
    | cx.fail line "access through a value that is not a pointer"
  let some (.ptr ..) := cx.types[pty]?
    | cx.fail line "access through a value that is not a pointer"
  -- The access alignment is the pointer type's `align(N)`: no default.
  if (cx.layouts[pty]?.bind (·.ptrAlign)).isNone then
    cx.fail line s!"pointer type {pty} has no `ptr_align` in the AIR file"
  pure pty

/-- A memory access through `ptr` (not a place): the pointee must be a type the model encodes. -/
def CheckCtx.memAccess (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  if let .inst p := ptr then
    if cx.places.contains p then return
  let pty ← cx.memPtrTy line ptr
  checkMemTy cx.fnName cx.types cx.layouts line (ptrChild cx.types pty).get!

/-- The item type of the slice, many-pointer or array pointer type `pty`. -/
def itemTy (types : Array Ty) (pty : TyId) : Option TyId :=
  match types[pty]? with
  | some (.ptr "one" _ c) => match types[c]? with
    | some (.array _ e) => some e
    | _ => none
  | some (.ptr _ _ c) => some c
  | _ => none

/-- An access to the items of `ptr` (a slice, many-pointer or array pointer): the item type must be
one the model encodes. -/
def CheckCtx.itemAccess (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  let pty ← cx.memPtrTy line ptr
  let some e := itemTy cx.types pty
    | cx.fail line s!"item access through pointer type {pty}, which has no items"
  checkMemTy cx.fnName cx.types cx.layouts line e

/-- The size of the type `id` is in the AIR file (pointer arithmetic, `@memcpy`). -/
def CheckCtx.knownSize (cx : CheckCtx) (line : Nat) (id : TyId) : Except String Unit :=
  if (cx.layouts[id]?.bind (·.size)).isSome then pure ()
  else cx.fail line s!"type {id} has no size in the AIR file"

mutual

partial def checkInst (cx : CheckCtx) (line : Nat) (inst : Inst) : Except String Nat := do
  checkTy cx.fnName cx.types cx.layouts line inst.ty
  checkOp cx line inst.ty inst.op

partial def checkOp (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op) : Except String Nat := do
  let fnName := cx.fnName
  match op with
  | .arith _ mode _ _ =>
    -- Emit maps a float `add`/`sub`/`mul` to the IEEE op and ignores `mode`: reject a float
    -- operand with a wrapping or saturating mode (Zig has none today) instead of guessing.
    if mode != .checked then
      if let some (.float _) := cx.types[ty]? then
        throw s!"{fnName}: near line {line}: wrapping/saturating float arithmetic is outside the subset"
    pure line
  | .bitcast (.inst a) =>
    -- `@intFromPtr`: a pointer to an integer needs addresses in the model (M20).
    let isPtr (t : TyId) : Bool := match cx.types[t]? with
      | some (.ptr ..) => true
      | some (.optional c) => match cx.types[c]? with | some (.ptr ..) => true | _ => false
      | _ => false
    match cx.instTys.find? (·.1 == a) with
    | some (_, aty) =>
      if isPtr aty && !isPtr ty then
        throw s!"{fnName}: near line {line}: `@intFromPtr` (a pointer to an integer) is outside the subset (M20)"
      pure line
    | none => pure line
  | .abs _ =>
    match cx.types[ty]? with
    | some (.int ..) => throw s!"{fnName}: near line {line}: integer @abs is outside the subset"
    | _ => pure line
  | .setUnionTag ptr _ =>
    if let .inst p := ptr then
      if cx.places.contains p then return line
    throw s!"{fnName}: near line {line}: `set_union_tag` through a pointer to memory (M16b)"
  | .retLoad ptr | .isNullPtr _ ptr | .optPayloadPtr _ ptr => cx.memAccess line ptr; pure line
  | .load ptr => cx.memAccess line ptr; pure line
  | .store ptr _ => cx.memAccess line ptr; pure line
  | .fieldPtr base _ =>
    if let .inst b := base then
      if cx.places.contains b then return line
    -- A field pointer into memory needs the field offsets.
    let pty ← cx.memPtrTy line base
    checkMemTy fnName cx.types cx.layouts line (ptrChild cx.types pty).get!
    pure line
  | .ptrElemVal p _ | .memset p _ => cx.itemAccess line p; pure line
  | .ptrAdd _ _ _ | .elemPtr _ _ =>
    -- The result is a pointer to an item: its child is the item type.
    cx.knownSize line (ptrChild cx.types ty).get!
    pure line
  | .memcpy dst src =>
    let _ ← cx.memPtrTy line src
    let dty ← cx.memPtrTy line dst
    cx.knownSize line (itemTy cx.types dty).get!
    pure line
  | .arrayToSlice p =>
    let _ ← cx.memPtrTy line p
    pure line
  | .call callee _ =>
    match callee with
    | .func name true =>
      if (panicErrorFor? name).isNone then
        throw s!"{fnName}: near line {line}: noreturn callee '{name}' is not a known \
          panic-handler function (docs/generated-code.md §Panics)"
      pure line
    | .func .. => pure line
    | _ => throw s!"{fnName}: near line {line}: an indirect call is outside the subset (M20)"
  | .block body | .loop body => checkInsts cx line body
  | .condBr _ thenBody elseBody => do
    let _ ← checkInsts cx line thenBody
    let _ ← checkInsts cx line elseBody
    pure line
  | .switchBr _ cases elseBody => do
    for c in cases do
      let _ ← checkInsts cx line c.body
    let _ ← checkInsts cx line elseBody
    pure line
  | .«try» _ errBody => do
    let _ ← checkInsts cx line errBody
    pure line
  | .line n => pure n
  | _ => pure line

partial def checkInsts (cx : CheckCtx) (line : Nat) (insts : Array Inst) : Except String Nat :=
  insts.foldlM (checkInst cx) line

end

/-- A pointer constant without a global in `v` (`Val.ptrOther`). -/
partial def Val.ptrOther? (v : Val) : Option String :=
  match v with
  | .ptrOther _ k => some k
  | .agg _ elems => elems.findSome? Val.ptrOther?
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => v.ptrOther?
  | .sliceConst _ p l => p.ptrOther? <|> l.ptrOther?
  | _ => none

/-- The pointer operands that `valueOperands` leaves out. -/
def ptrOperands (op : Op) : Array Val :=
  match op with
  | .load p | .store p _ | .fieldPtr p _ | .retLoad p | .sliceFieldPtr _ p | .bitcast p
  | .setUnionTag p _ => #[p]
  | _ => #[]

/-- A global that a pointer constant points into: a `var` or `const` with its initial value, in a
type that the model encodes. An array with a sentinel is encoded with the sentinel. -/
def checkGlobal (f : Func) (g : Global) : Except String Unit := do
  let what := g.name.getD "an unnamed constant"
  if g.threadlocal then throw s!"{f.name}: global {what}: `threadlocal` is outside the subset"
  if g.isExtern then throw s!"{f.name}: global {what}: `extern` is outside the subset"
  let some init := g.init
    | throw s!"{f.name}: global {what}: the AIR file has no initial value"
  if let some k := init.ptrOther? then
    throw s!"{f.name}: global {what}: a pointer constant without a global ({k}) is outside the subset"
  let ty := match f.types[g.ty]?, f.layouts[g.ty]? with
    | some (.array _ c), some l => if l.sentinel then c else g.ty
    | _, _ => g.ty
  checkTy f.name f.types f.layouts 0 ty
  checkMemTy f.name f.types f.layouts 0 ty

/-- Reject anything `Emit.lean` cannot translate: see the module doc. -/
def check (f : Func) : Except String Unit := do
  for p in f.params do
    checkTy f.name f.types f.layouts 0 p
  checkTy f.name f.types f.layouts 0 f.ret
  let insts := f.allInsts
  let escaping := escapingAllocs f
  let places := (placeRoots insts).filterMap fun (p, r) => if escaping.contains r then none else some p
  -- An escaping local is a stack block: its type must be one the model encodes.
  for i in insts do
    if let .alloc := i.op then
      if escaping.contains i.id then
        if let some c := ptrChild f.types i.ty then
          checkMemTy f.name f.types f.layouts 0 c
  for g in f.globals do
    checkGlobal f g
  for i in insts do
    for v in valueOperands i.op ++ ptrOperands i.op do
      if let some k := v.ptrOther? then
        throw s!"{f.name}: a pointer constant without a global ({k}) is outside the subset"
      -- The block of a global has the alignment of its type.
      if let .ptrConst pty g _ := v then
        let pa := (f.layouts[pty]?.bind (·.ptrAlign)).getD 1
        let ga := (f.globals[g]?.bind (f.layouts[·.ty]?)).bind (·.align) |>.getD 1
        if pa > ga then
          throw s!"{f.name}: a pointer with `align({pa})` to a global of alignment {ga} is \
            outside the subset"
  let cx : CheckCtx := { fnName := f.name, types := f.types, layouts := f.layouts,
                         instTys := insts.map fun i => (i.id, i.ty), places }
  let _ ← checkInsts cx 0 f.body
  pure ()

/-- The checks that need every function. A function that uses memory reads a slice item from
memory, and a call to a pure function copies each `[]const T` argument from memory
(`Zig.readSlice`): `T` must be a type that the model encodes. -/
def checkProgram (funcs : Array Func) : Except String Unit := do
  let mem := memoryFunctions funcs
  for f in funcs do
    if mem.contains f.name then
      let insts := f.allInsts
      let tyOf (v : Val) : Option TyId := match v with
        | .inst p => (insts.find? (·.id == p)).map (·.ty)
        | v => v.constTy?
      let sliceItem (v : Val) : Option TyId := match (tyOf v).bind (f.types[·]?) with
        | some (.ptr "slice" _ c) => some c
        | _ => none
      for i in insts do
        let items := match i.op with
          | .sliceElemVal s _ => (sliceItem s).toArray
          | .call (.func callee _) args =>
            if mem.contains callee then #[] else args.filterMap sliceItem
          | _ => #[]
        for c in items do
          checkMemTy f.name f.types f.layouts 0 c

end Air2Lean
