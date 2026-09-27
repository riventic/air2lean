import Air2Lean.Air.Op

/-!
# Subset checker

`check : Func → Except String Unit` rejects anything `Emit.lean` cannot translate: `other`
types, a union without a tag, a float type outside `16 32 64 80 128` bits, an integer `@abs`, a
pointer that is not a place (a pointer into a local) or a read-only slice, and a place whose
address escapes past `load`/`store`/`dbg`. Errors name the function and the nearest `dbg_stmt` line.
-/

namespace Air2Lean

/-- Checker state threaded through a function body in program order: `line` is the most
recent `dbg_stmt`'s source line (for error messages), `places` is every pointer into a local seen
so far: an `alloc` (or `ret_ptr`), and a field pointer or `bitcast` of a place. -/
structure CheckState where
  line : Nat
  places : Array InstId

/-- The only pointer shapes in the subset: a read-only slice (`slice`, const) anywhere, and a
single pointer (`one`) only as the type of a place instruction (`place`; not in a parameter,
the return type, or a child type). -/
def ptrInSubset (size : String) (isConst : Bool) (place : Bool) : Bool :=
  (size == "one" && place) || (size == "slice" && isConst)

/-- Reject `other` types, an out-of-subset float width, and non-alloc/non-const-slice
pointers, recursively through struct fields, array/optional children, and tuple fields. -/
partial def checkTy (fnName : String) (types : Array Ty) (line : Nat) (id : TyId)
    (place : Bool := false) :
    Except String Unit := do
  let some ty := types[id]?
    | throw s!"{fnName}: near line {line}: unknown type id {id}"
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
    if ptrInSubset size isConst place then checkTy fnName types line child
    else
      throw s!"{fnName}: near line {line}: pointer type (size={size}, const={isConst}) is \
        outside the subset (only a pointer into a local or a read-only slice `[]const T`)"
  | .array _ child => checkTy fnName types line child
  | .optional child =>
    if let some (.ptr ..) := types[child]? then
      throw s!"{fnName}: near line {line}: optional pointer type is outside the subset (only \
        `?T` for a non-pointer T)"
    else checkTy fnName types line child
  | .errorUnion set payload => do
    checkTy fnName types line set
    checkTy fnName types line payload
  | .errorSet _ => pure ()
  | .struct _ _ fields => fields.forM fun (_, fty) => checkTy fnName types line fty
  | .enum _ tag _ _ => checkTy fnName types line tag
  | .union name layout tag fields =>
    match tag with
    | none =>
      throw s!"{fnName}: near line {line}: union '{name}' ({layout}, no tag) is outside the \
        subset (only a tagged `union(enum)`)"
    | some t =>
      unless (match types[t]? with | some (.enum ..) => true | _ => false) do
        throw s!"{fnName}: near line {line}: union '{name}': tag type {t} is not an enum"
      checkTy fnName types line t
    fields.forM fun (_, fty) => checkTy fnName types line fty
  | .tuple fields => fields.forM (checkTy fnName types line)
  | .int .. | .bool | .void | .noreturn => pure ()

/-- `v` is not a place (a pointer into a local) — the escape check. Any use of a place other than
the pointer operand of `load`/`store`/`struct_field_ptr`/`set_union_tag`/`ret_load`, a `bitcast`
of it, or `dbg` goes through here. -/
def checkNotEscaping (fnName : String) (st : CheckState) (ctxId : InstId) (v : Val) :
    Except String Unit :=
  match v with
  | .inst vid =>
    if st.places.contains vid then
      throw s!"{fnName}: near line {st.line}: inst {ctxId} uses local {vid}'s address outside \
        a load, store, field pointer, `bitcast`, `set_union_tag`, `ret_load` or `dbg`"
    else pure ()
  | _ => pure ()

/-- `v` is a place: a memory access through any other pointer is outside the subset. -/
def checkPlace (fnName : String) (st : CheckState) (ctxId : InstId) (v : Val) :
    Except String Unit :=
  match v with
  | .inst vid =>
    if st.places.contains vid then pure ()
    else throw s!"{fnName}: near line {st.line}: inst {ctxId}: access through a pointer that is \
      not a local (pointers are outside the subset)"
  | _ => throw s!"{fnName}: near line {st.line}: inst {ctxId}: access through a constant pointer \
      (outside the subset)"

mutual

partial def checkInst (fnName : String) (types : Array Ty) (st : CheckState) (inst : Inst) :
    Except String CheckState := do
  let place := match inst.op with
    | .alloc | .fieldPtr .. => true
    | .bitcast (.inst a) => st.places.contains a
    | _ => false
  checkTy fnName types st.line inst.ty place
  checkOp fnName types st inst.id inst.ty inst.op

partial def checkOp (fnName : String) (types : Array Ty) (st : CheckState) (id : InstId)
    (ty : TyId) (op : Op) : Except String CheckState := do
  let chk1 (v : Val) : Except String Unit := checkNotEscaping fnName st id v
  let chk (vs : Array Val) : Except String Unit := vs.forM chk1
  match op with
  | .arg _ => pure st
  | .arith _ mode a b =>
    chk #[a, b]
    -- Emit maps a float `add`/`sub`/`mul` to the IEEE op and ignores `mode`: reject a float
    -- operand with a wrapping or saturating mode (Zig has none today) instead of guessing.
    if mode != .checked then
      if let some (.float _) := types[ty]? then
        throw s!"{fnName}: near line {st.line}: wrapping/saturating float arithmetic is outside the subset"
    pure st
  | .div _ a b => chk #[a, b]; pure st
  | .divFloat a b => chk #[a, b]; pure st
  | .minMax _ a b => chk #[a, b]; pure st
  | .withOverflow _ a b => chk #[a, b]; pure st
  | .bit _ a b => chk #[a, b]; pure st
  | .not a => chk1 a; pure st
  | .neg a => chk1 a; pure st
  | .abs a =>
    chk1 a
    match types[ty]? with
    | some (.int ..) => throw s!"{fnName}: near line {st.line}: integer @abs is outside the subset"
    | _ => pure st
  | .floatRound _ a => chk1 a; pure st
  | .sqrt a => chk1 a; pure st
  | .libm _ a => chk1 a; pure st
  | .mulAdd a b c => chk #[a, b, c]; pure st
  | .floatConv a => chk1 a; pure st
  | .floatFromInt a => chk1 a; pure st
  | .intFromFloat _ a => chk1 a; pure st
  | .shift _ a b => chk #[a, b]; pure st
  | .cmp _ a b => chk #[a, b]; pure st
  | .boolAnd a b => chk #[a, b]; pure st
  | .boolOr a b => chk #[a, b]; pure st
  | .intCast a => chk1 a; pure st
  | .trunc a => chk1 a; pure st
  | .bitcast a =>
    match a with
    | .inst aid => if st.places.contains aid then pure { st with places := st.places.push id }
                   else pure st
    | _ => pure st
  | .isNull a => chk1 a; pure st
  | .isNonNull a => chk1 a; pure st
  | .optPayload a => chk1 a; pure st
  | .wrapOptional a => chk1 a; pure st
  | .isErr a => chk1 a; pure st
  | .isNonErr a => chk1 a; pure st
  | .errPayload a => chk1 a; pure st
  | .errCode a => chk1 a; pure st
  | .wrapErrPayload a => chk1 a; pure st
  | .wrapErr a => chk1 a; pure st
  | .isNamedEnum a => chk1 a; pure st
  | .unionTag a => chk1 a; pure st
  | .unionInit _ a => chk1 a; pure st
  | .alloc => pure { st with places := st.places.push id }
  | .fieldPtr base _ =>
    checkPlace fnName st id base; pure { st with places := st.places.push id }
  | .setUnionTag ptr tag => checkPlace fnName st id ptr; chk1 tag; pure st
  | .retLoad ptr => checkPlace fnName st id ptr; pure st
  | .load ptr => checkPlace fnName st id ptr; pure st
  | .store ptr v => checkPlace fnName st id ptr; chk1 v; pure st
  | .sliceLen s => chk1 s; pure st
  | .sliceElemVal s i => chk #[s, i]; pure st
  | .structFieldVal s _ => chk1 s; pure st
  | .aggregateInit elems => chk elems; pure st
  | .call callee args =>
    chk1 callee; chk args
    if let .func name true := callee then
      if (panicErrorFor? name).isNone then
        throw s!"{fnName}: near line {st.line}: noreturn callee '{name}' is not a known \
          panic-handler function (docs/generated-code.md §Panics)"
    pure st
  | .block body => checkInsts fnName types st body
  | .loop body => checkInsts fnName types st body
  | .br _target v => chk1 v; pure st
  | .«repeat» _ => pure st
  | .condBr c thenBody elseBody => do
    chk1 c
    let _ ← checkInsts fnName types st thenBody
    let _ ← checkInsts fnName types st elseBody
    pure st
  | .switchBr v cases elseBody => do
    chk1 v
    for c in cases do
      let _ ← checkInsts fnName types st c.body
    let _ ← checkInsts fnName types st elseBody
    pure st
  | .«try» v errBody => do
    chk1 v
    let _ ← checkInsts fnName types st errBody
    pure st
  | .ret v => chk1 v; pure st
  | .unreach => pure st
  | .trap => pure st
  | .line n => pure { st with line := n }
  | .dbg _ _ => pure st

partial def checkInsts (fnName : String) (types : Array Ty) (st : CheckState)
    (insts : Array Inst) : Except String CheckState :=
  insts.foldlM (checkInst fnName types) st

end

/-- Reject anything `Emit.lean` cannot translate: see the module doc. -/
def check (f : Func) : Except String Unit := do
  for p in f.params do
    checkTy f.name f.types 0 p
  checkTy f.name f.types 0 f.ret
  let _ ← checkInsts f.name f.types { line := 0, places := #[] } f.body
  pure ()

end Air2Lean
