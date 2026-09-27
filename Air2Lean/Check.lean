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

/-- Reject `other` types, an out-of-subset float width, and pointers other than `*T` (not
`allowzero`, not a bit-pointer) and `[]const T`, recursively through struct fields,
array/optional children, and tuple fields. -/
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
    match size, isConst with
    | "one", _ | "slice", true => recur child
    | "c", _ => throw s!"{fnName}: near line {line}: a C pointer `[*c]T` is outside the subset"
    | _, _ =>
      throw s!"{fnName}: near line {line}: pointer type (size={size}, const={isConst}) is \
        outside the subset (only `*T` and a read-only slice `[]const T`; M16b adds the others)"
  | .array _ child => recur child
  | .optional child =>
    if let some (.ptr "slice" ..) := types[child]? then
      throw s!"{fnName}: near line {line}: optional slice type is outside the subset (M16b)"
    recur child
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
  | some (.ptr "one" ..) => pure (8, 8)
  | some (.optional c) =>
    match types[c]? with
    | some (.ptr "one" ..) => pure (8, 8)
    | _ =>
      let (s, a) ← modelLayout types layouts c
      pure (Zig.alignUp (s + 1) a, a)
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
  | some (.array ..) => throw "an array (M16b)"
  | some (.ptr ..) => throw "a slice or many-pointer (M16b)"
  | some (.errorUnion ..) | some (.errorSet _) => throw "an error union or error set (M16b)"
  | some (.union name ..) => throw s!"union '{name}' (M16b)"
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

/-- A memory access through `ptr` (not a place): the pointee must be a type the model encodes. -/
def CheckCtx.memAccess (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  match ptr with
  | .inst p =>
    if cx.places.contains p then pure ()
    else
      match cx.instTys.find? (·.1 == p) with
      | some (_, pty) =>
        let some c := ptrChild cx.types pty
          | throw s!"{cx.fnName}: near line {line}: access through a value that is not a pointer"
        -- The access alignment is the pointer type's `align(N)`: no default.
        if (cx.layouts[pty]?.bind (·.ptrAlign)).isNone then
          throw s!"{cx.fnName}: near line {line}: pointer type {pty} has no `ptr_align` in the AIR file"
        checkMemTy cx.fnName cx.types cx.layouts line c
      | none => throw s!"{cx.fnName}: near line {line}: access through a value that is not a pointer"
  | _ => throw s!"{cx.fnName}: near line {line}: access through a constant pointer (M16b)"

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
    match base with
    | .inst b =>
      unless cx.places.contains b do
        -- A field pointer into memory needs the field offsets.
        match (cx.instTys.find? (·.1 == b)).bind (ptrChild cx.types ·.2) with
        | some c => checkMemTy fnName cx.types cx.layouts line c
        | none => throw s!"{fnName}: near line {line}: field pointer of a value that is not a pointer"
      pure line
    | _ => throw s!"{fnName}: near line {line}: field pointer of a constant pointer (M16b)"
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
  let cx : CheckCtx := { fnName := f.name, types := f.types, layouts := f.layouts,
                         instTys := insts.map fun i => (i.id, i.ty), places }
  let _ ← checkInsts cx 0 f.body
  pure ()

/-- The checks that need every function: a function that uses memory has no slice (M16b). -/
def checkProgram (funcs : Array Func) : Except String Unit := do
  let mem := memoryFunctions funcs
  for f in funcs do
    if mem.contains f.name then
      let tys := f.params ++ #[f.ret] ++ f.allInsts.map (·.ty)
      if tys.any fun t => match f.types[t]? with | some (.ptr "slice" ..) => true | _ => false then
        throw s!"{f.name}: a function that uses memory and has a slice is outside the subset (M16b)"

end Air2Lean
