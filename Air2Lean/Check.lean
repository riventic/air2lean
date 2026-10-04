import Air2Lean.Memory
import ZigLean.Mem.Enc
import ZigLean.Vec

/-!
# Subset checker

`check : Func → Except String Unit` rejects anything `Emit.lean` cannot translate: `other`
types, a union without a tag, a float type outside `16 32 64 80 128` bits, an integer `@abs`, a
`[*c]T`, `allowzero` or bit-pointer, a memory access to a value that the memory model cannot
encode (`modelLayout`), a pointer constant without a global, and a global that is `threadlocal`,
`extern` or has no initial value. `checkProgram` checks the slice items that a function that
uses memory reads (`Air2Lean/Memory.lean`). Errors name the function and the nearest `dbg_stmt`
line.

An `assembly` instruction (M21) is accepted only when every operand is an integer with a
register constraint (`=r`, `r`, `{reg}`, `={reg}`) or, for an input, a matching constraint that
names an output (`0`, `1`, …), and there is no `"memory"` clobber. At most one output is the asm
expression's own result (`ref = none`); every other output is an lvalue output, a store through
its pointer `ref`. Anything else (a memory operand, a read-write output, a `"memory"` clobber)
is outside the subset.
-/

namespace Air2Lean

/-- Is `c` a register constraint (`docs/generated-code.md` §asm)? Register class letter `r`, or a
named register in braces — either alone or with a leading `=` (write-only) marker. -/
def isRegisterConstraint (c : String) : Bool :=
  let body := if c.startsWith "=&" then c.drop 2 else if c.startsWith "=" then c.drop 1 else c
  body == "r" || (body.startsWith "{" && body.endsWith "}" && body.toString.length > 2)

/-- Is `c` a matching constraint on an input, tying it to output operand `k < outputs` — the
register a register-modify-in-place instruction (`bswap`) both reads and writes? -/
def isMatchingConstraint (outputs : Nat) (c : String) : Bool :=
  match c.toNat? with
  | some k => k < outputs
  | none => false

/-- Reject `other` types, an out-of-subset float width, and a pointer that is `[*c]T`,
`allowzero` or a bit-pointer, recursively through struct fields, array/optional children, and
tuple fields. `seen`: the types on the path to `id`; a type can point to itself (a list node). -/
partial def checkTy (fnName : String) (types : Array Ty) (layouts : Array Layout) (line : Nat)
    (id : TyId) (seen : Array TyId := #[]) : Except String Unit := do
  if seen.contains id then return
  let some ty := types[id]?
    | throw s!"{fnName}: near line {line}: unknown type id {id}"
  let recur (c : TyId) := checkTy fnName types layouts line c (seen.push id)
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
    -- A bit-pointer loads its host integer as a `BitVec (8 * hostSize)`, whose size must be
    -- `hostSize` (`Zig.loadBits`).
    if l.hostSize != 0 && Zig.intSize (8 * l.hostSize) != l.hostSize then
      throw s!"{fnName}: near line {line}: a pointer to a packed struct field whose host \
        integer is {l.hostSize} bytes is outside the subset (only 1, 2, 4, 8 or a multiple of 16)"
    if l.hostSize != 0 then
      if let some bits := packedBits types child then
        if l.bitOffset + bits > 8 * l.hostSize then
          throw s!"{fnName}: near line {line}: a bit-pointer field extends beyond its host integer"
    let _ := isConst
    match size with
    -- A function pointer: an indirect call dispatches on it (`Emit.lean`, M20). A `*anyopaque`
    -- (`Io.Group`'s `token`) is a value only: Zig cannot load through it (it has no size).
    | "one" =>
      if (types[child]?.map isFnTy).getD false || types[child]? == some (.other "anyopaque") then
        pure ()
      else recur child
    | "many" | "slice" => recur child
    | _ => throw s!"{fnName}: near line {line}: a C pointer `[*c]T` is outside the subset"
  | .array _ child _ => recur child
  | .vector _ child =>
    unless (match types[child]? with
      | some (.int ..) | some (.float _) | some .bool => true | _ => false) do
      throw s!"{fnName}: near line {line}: a vector with lanes other than integers, floats or bool is outside the subset"
    recur child
  | .optional child => recur child
  | .errorUnion set payload => do
    recur set
    recur payload
  | .errorSet _ => pure ()
  | .struct name layout fields =>
    if layout == "packed" && (packedBits types id).isNone then
      throw s!"{fnName}: near line {line}: packed struct '{name}' has a field other than an \
        integer, a `bool`, an enum or a packed struct: outside the subset"
    fields.forM fun (_, fty) => recur fty
  | .enum _ tag _ _ => recur tag
  | .union name layout tag fields =>
    match tag with
    | none =>
      -- `extern`, `packed`: the bytes (`ZigLean/Union.lean`). In `ReleaseSafe` a bare union
      -- has a hidden tag (`safety_tag`), so it is never here.
      unless layout == "extern" || layout == "packed" do
        throw s!"{fnName}: near line {line}: union '{name}' ({layout}, no tag) is outside the \
          subset"
      if layout == "packed" && fields.any (fun (_, t) => (packedBits types t).isNone) then
        throw s!"{fnName}: near line {line}: packed union '{name}' has a field other than an \
          integer, a `bool`, an enum or a packed struct: outside the subset"
    | some t =>
      unless (match types[t]? with | some (.enum ..) => true | _ => false) do
        throw s!"{fnName}: near line {line}: union '{name}': tag type {t} is not an enum"
      recur t
    fields.forM fun (_, fty) => recur fty
  | .tuple fields => fields.forM recur
  | .int .. | .bool | .void | .noreturn | .allocator | .thread | .io => pure ()

/-- The layout of a tagged union from the tag's and the payload's size and alignment (the
largest field's), as `(tag offset, payload offset, size, alignment)`: the compiler's rule puts
the one with the larger alignment first, the tag if they are equal. -/
def unionLayout (ts ta ps pa : Nat) : Nat × Nat × Nat × Nat :=
  if ta ≥ pa then (0, Zig.alignUp ts pa, Zig.alignUp (Zig.alignUp ts pa + ps) ta, ta)
  else (Zig.alignUp ps ta, 0, Zig.alignUp (Zig.alignUp ps ta + ts) pa, pa)

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
  | some .allocator => pure (16, 8)
  | some .thread => pure (8, 8)
  | some .io => pure (16, 8)
  | some (.optional c) =>
    match types[c]? with
    | some (.ptr "slice" ..) => pure (16, 8)
    | some (.ptr ..) => pure (8, 8)
    | _ =>
      let (s, a) ← modelLayout types layouts c
      pure (Zig.alignUp (s + 1) a, a)
  | some (.array len c sentinel) =>
    let (s, a) ← modelLayout types layouts c
    pure ((len + if sentinel then 1 else 0) * s, a)
  | some (.vector len c) =>
    match types[c]? with
    | some (.int _ bits) | some (.float bits) =>
      let (s, _) ← modelLayout types layouts c
      unless bits != 0 && bits == 8 * s do
        throw "a vector in memory with non-byte-width or ABI-padded lanes is outside the subset"
      pure (Zig.vecLayout len s, Zig.vecLayout len s)
    | some .bool => pure (Zig.boolVecLayout len, Zig.boolVecLayout len)
    | _ => throw "a vector of a type other than an integer, a float or `bool`"
  | some (.enum _ tag _ _) =>
    let _ ← modelLayout types layouts tag
    exported
  | some (.struct name layout fields) =>
    if layout == "packed" then
      -- Its backing integer (`Zig.Packed`).
      let some bits := packedBits types id | throw s!"packed struct '{name}' with a field other \
        than an integer, a `bool` or a packed struct"
      return (Zig.intSize bits, Zig.intAlign bits)
    for (_, fty) in fields do
      let _ ← modelLayout types layouts fty
    if (layouts[id]?.map (·.offsets.size)).getD 0 != fields.size then
      throw s!"struct '{name}' has no field offsets in the AIR file"
    exported
  | some (.errorUnion set payload) =>
    -- `Zig.errUnionOffsets`: the error code is 2 bytes.
    unless (layouts[set]?.map fun l => l.size == some 2 && l.align == some 2).getD false do
      throw "an error set that is not 2 bytes (`--error-limit`)"
    let (s, a) ← modelLayout types layouts payload
    pure (Zig.errUnionSize s a, Nat.max a 2)
  | some (.errorSet _) => throw "an error set value (not in an error union)"
  | some (.union _ _ (some tag) fields) =>
    let (ts, ta) ← modelLayout types layouts tag
    let fs ← fields.mapM fun (_, t) => modelLayout types layouts t
    let (_, _, s, a) := unionLayout ts ta (fs.foldl (Nat.max · ·.1) 0) (fs.foldl (Nat.max · ·.2) 1)
    pure (s, a)
  | some (.union name layout none fields) =>
    unless layout == "extern" || layout == "packed" do
      throw s!"union '{name}' ({layout}) without a tag"
    for (_, fty) in fields do
      let _ ← modelLayout types layouts fty
    exported
  | some t => throw s!"{repr t}"
  | none => throw s!"unknown type id {id}"

/-- The tag and payload offsets of a tagged union with the tag type `tag` and the field types
`fields` in memory (`unionLayout`). -/
def unionOffsets (types : Array Ty) (layouts : Array Layout) (tag : TyId) (fields : Array TyId) :
    Option (Nat × Nat) := do
  let (ts, ta) ← (modelLayout types layouts tag).toOption
  let fs ← fields.mapM fun t => (modelLayout types layouts t).toOption
  let (to, po, _, _) := unionLayout ts ta (fs.foldl (Nat.max · ·.1) 0) (fs.foldl (Nat.max · ·.2) 1)
  pure (to, po)

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
    | some (.array _ e _) => some e
    -- The lanes of a vector of integers or floats are bytes, as the items of an array. A lane
    -- of a `bool` vector is a bit (`CheckCtx.itemAccess`).
    | some (.vector _ e) => if types[e]? == some .bool then none else some e
    | _ => none
  | some (.ptr _ _ c) => some c
  | _ => none

/-- An atomic op's pointee must be an integer, an enum, a `bool` or a packed struct
(`docs/std-models.md` §Thread model: the subset does not model a float or pointer atomic). -/
def CheckCtx.atomicIntChild (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  let some pty := cx.valTy? ptr
    | cx.fail line "an atomic op through a value that is not a pointer"
  let some c := ptrChild cx.types pty
    | cx.fail line "an atomic op through a value that is not a pointer"
  match cx.types[c]? with
  | some (.int ..) | some (.enum ..) | some .bool | some (.struct _ "packed" _) => pure ()
  | _ => cx.fail line "an atomic op on a type other than an integer, an enum, a `bool` or a \
      packed struct is outside the subset"

/-- An access to the items of `ptr` (a slice, many-pointer or array pointer): the item type must be
one the model encodes. -/
def CheckCtx.itemAccess (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  let pty ← cx.memPtrTy line ptr
  if let some (.ptr "one" _ c) := cx.types[pty]? then
    if let some (.vector _ e) := cx.types[c]? then
      if cx.types[e]? == some .bool then
        cx.fail line "a pointer to a lane of a `bool` vector is outside the subset (the lane is a \
          bit, and the AIR file has no lane index)"
      checkMemTy cx.fnName cx.types cx.layouts line c
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
    -- operand (scalar or a vector of floats) with a wrapping or saturating mode (Zig has none
    -- today) instead of guessing.
    if mode != .checked then
      let elemTy := match cx.types[ty]? with
        | some (.vector _ c) => cx.types[c]?
        | t => t
      if let some (.float _) := elemTy then
        throw s!"{fnName}: near line {line}: wrapping/saturating float arithmetic is outside the subset"
    pure line
  | .bitcast a =>
    let sourceTy := cx.valTy? a
    let isVector (t : Option TyId) : Bool := match t.bind (cx.types[·]?) with
      | some (.vector ..) => true | _ => false
    if (isVector (some ty) || isVector sourceTy) && sourceTy != some ty then
      cx.fail line "a bitcast to, from, or between different vector types is outside the subset"
    -- `@intFromPtr`/`@ptrFromInt`/`@ptrCast`/`@alignCast`/`@constCast`/`@volatileCast` all
    -- normalize to a plain `bitcast`; `Emit.lean` picks the ptr<->int direction from the operand
    -- and result types and uses `Zig.ptrAddr`/`Zig.ptrFromAddr` (M20). An optional pointer
    -- (`?*T`) is `Option Zig.Ptr` in the model: a bitcast to another optional pointer (a
    -- `@constCast`) is a no-op, and one from a pointer is Lean's coercion `Zig.Ptr → Option
    -- Zig.Ptr`. Any other bitcast to or from it would need an unwrap/wrap `Emit.lean` does not
    -- have.
    let isOptPtr (t : TyId) : Bool := match cx.types[t]? with
      | some (.optional c) => match cx.types[c]? with | some (.ptr ..) => true | _ => false
      | _ => false
    match sourceTy with
    | some aty =>
      let isPtr (t : TyId) : Bool := match cx.types[t]? with | some (.ptr ..) => true | _ => false
      if (isOptPtr aty && !isOptPtr ty) || (isOptPtr ty && !isOptPtr aty && !isPtr aty) then
        throw s!"{fnName}: near line {line}: a bitcast between an optional pointer (`?*T`) and \
          another type is outside the subset"
      -- A packed struct or union is a bitcast of its backing integer only (`Zig.Packed`,
      -- `Zig.PackedU`; 0.16.0 builds a packed union from its field this way). A bitcast of
      -- another aggregate as a value (`[4]u8` to `u32`) has no model: through memory
      -- (`@ptrCast`), it is a load of other bytes.
      let kind (t : TyId) : String := match cx.types[t]? with
        | some (.struct _ "packed" _) | some (.union _ "packed" none _) => "packed"
        | some (.struct ..) | some (.array ..) | some (.union ..) | some (.tuple _) => "agg"
        | some (.int ..) => "int"
        | _ => "other"
      if aty == ty then return line
      match kind aty, kind ty with
      | "packed", "int" | "int", "packed" => pure line
      | "packed", _ | _, "packed" | "agg", _ | _, "agg" =>
        throw s!"{fnName}: near line {line}: a `@bitCast` of an aggregate other than a packed \
          struct or union to or from an integer is outside the subset"
      | _, _ => pure line
    | none => pure line
  | .setUnionTag ptr _ | .retLoad ptr | .isNullPtr _ ptr | .optPayloadPtr _ ptr | .isErrPtr _ ptr | .errPayloadPtr _ ptr
  | .errCodePtr ptr => cx.memAccess line ptr; pure line
  | .load ptr => cx.memAccess line ptr; pure line
  | .store ptr v =>
    cx.memAccess line ptr
    -- `Zig.storeBits` has no undefined bits: `undefined` would clobber the host's other fields.
    if let .undef _ := v then
      if let some pty := cx.valTy? ptr then
        if (cx.layouts[pty]?.map (·.hostSize)).getD 0 != 0 then
          cx.fail line "a store of `undefined` to a packed struct field is outside the subset"
    pure line
  | .atomicLoad _ .unordered | .atomicStore _ _ .unordered =>
    cx.fail line "an `unordered` atomic op is outside the subset (it has no read-read coherence)"
  | .atomicLoad ptr _ => cx.memAccess line ptr; cx.atomicIntChild line ptr; pure line
  | .atomicStore ptr _ _ => cx.memAccess line ptr; cx.atomicIntChild line ptr; pure line
  | .atomicRmw _ _ ptr _ => cx.memAccess line ptr; cx.atomicIntChild line ptr; pure line
  | .cmpxchg _ ptr _ _ _ _ => cx.memAccess line ptr; cx.atomicIntChild line ptr; pure line
  | .fieldPtr base _ =>
    if let .inst b := base then
      if cx.places.contains b then return line
    -- A field pointer into memory needs the field offsets.
    let pty ← cx.memPtrTy line base
    checkMemTy fnName cx.types cx.layouts line (ptrChild cx.types pty).get!
    pure line
  | .fieldParentPtr fieldPtr _ =>
    -- `@fieldParentPtr` on a place would need to walk back up the place's own field path
    -- (`Emit.lean`'s `FCtx.computePlaces`), which is outside the subset for now (M20); it needs a
    -- real memory pointer, whose parent struct's offsets the model must know.
    if let .inst b := fieldPtr then
      if cx.places.contains b then
        cx.fail line "`@fieldParentPtr` from a local's own place is outside the subset (M20)"
    let _ ← cx.memPtrTy line fieldPtr
    let some (.ptr _ _ parent) := cx.types[ty]?
      | cx.fail line "`@fieldParentPtr`'s result is not a pointer"
    checkMemTy fnName cx.types cx.layouts line parent
    pure line
  | .ptrElemVal p _ | .memset p _ => cx.itemAccess line p; pure line
  | .ptrAdd _ p _ | .elemPtr p _ =>
    -- The result is a pointer to an item: its child is the item type.
    if let some pty := cx.valTy? p then
      if let some (.ptr "one" _ c) := cx.types[pty]? then
        if let some (.vector ..) := cx.types[c]? then
          cx.itemAccess line p
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
    | .func name true .. =>
      if (panicErrorFor? name).isNone then
        throw s!"{fnName}: near line {line}: noreturn callee '{name}' is not a known \
          panic-handler function (docs/generated-code.md §Panics)"
      pure line
    | .func .. => pure line
    -- A pointer to a function (`checkTy`): `Emit.lean` dispatches on the address-taken
    -- functions of its type (`fnRefs`).
    | .inst _ => pure line
    | _ => throw s!"{fnName}: near line {line}: an indirect call through a constant is outside \
        the subset"
  | .block body | .loop body => checkInsts cx line body
  | .condBr _ thenBody elseBody => do
    let _ ← checkInsts cx line thenBody
    let _ ← checkInsts cx line elseBody
    pure line
  | .switchBr _ cases elseBody | .loopSwitchBr _ cases elseBody => do
    for c in cases do
      let _ ← checkInsts cx line c.body
    let _ ← checkInsts cx line elseBody
    pure line
  | .«try» _ errBody => do
    let _ ← checkInsts cx line errBody
    pure line
  | .line n => pure n
  | .asm _ _ clobbers outputs inputs =>
    -- Register operands only (M21): every operand value is an integer, so `Emit.lean` can map it
    -- to a `BitVec`.
    let isIntTy (tid : TyId) : Bool := match cx.types[tid]? with | some (.int ..) => true | _ => false
    if clobbers.contains "memory" then
      throw s!"{fnName}: near line {line}: an asm 'memory' clobber is outside the subset (M21)"
    -- One output can be the expression's own result (`-> T`, no `ref`); every other output
    -- is a store through its pointer `ref` (an lvalue output).
    for o in outputs do
      if !isRegisterConstraint o.constraint || !o.constraint.startsWith "=" then
        throw s!"{fnName}: near line {line}: asm output constraint '{o.constraint}' is not a \
          register output constraint (M21)"
      let outTy ← match o.ref with
        | none => pure ty
        | some r =>
          let some pty := cx.valTy? r
            | cx.fail line s!"asm output '{o.name}': operand has no known type"
          let some c := ptrChild cx.types pty
            | cx.fail line s!"asm output '{o.name}' is not a pointer"
          if (cx.layouts[pty]?.map (·.hostSize)).getD 0 != 0 then
            cx.fail line s!"asm output '{o.name}' is a bit-pointer"
          cx.memAccess line r
          pure c
      if !isIntTy outTy then
        throw s!"{fnName}: near line {line}: asm output is not an integer register value (M21)"
    if (outputs.filter (·.ref.isNone)).size > 1 then
      cx.fail line "an asm expression with two result outputs (malformed input in the AIR file)"
    for i in inputs do
      if !((!i.constraint.startsWith "=" && isRegisterConstraint i.constraint) ||
          isMatchingConstraint outputs.size i.constraint) then
        throw s!"{fnName}: near line {line}: asm input constraint '{i.constraint}' is not a \
          register or matching constraint (M21)"
      let some r := i.ref
        | cx.fail line s!"asm input '{i.name}' has no operand (malformed input in the AIR file)"
      let some rty := cx.valTy? r
        | cx.fail line s!"asm input '{i.name}': operand has no known type"
      if !isIntTy rty then
        throw s!"{fnName}: near line {line}: asm input '{i.name}' is not an integer register \
          value (M21)"
    pure line
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
  | .load p | .store p _ | .fieldPtr p _ | .fieldParentPtr p _ | .retLoad p | .sliceFieldPtr _ p
  | .bitcast p | .setUnionTag p _ | .atomicLoad p _ | .atomicStore p .. | .atomicRmw _ _ p _
  | .cmpxchg _ p .. => #[p]
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
  -- A function: a function pointer points to it (a 1-byte block, `Emit.lean`).
  if let .func .. := init then return
  checkTy f.name f.types f.layouts 0 g.ty
  checkMemTy f.name f.types f.layouts 0 g.ty

/-- Check loop-switch selector contracts and lexical targets even for direct Core callers. -/
partial def checkDispatchScopes (cx : CheckCtx) (body : Array Inst)
    (targets : Array (InstId × Ty) := #[]) : Except String Unit := do
  let valTy (v : Val) : Option Ty := match v with
    | .bool _ => some .bool
    | _ => (cx.valTy? v).bind (cx.types[·]?)
  for i in body do
    let recur (b : Array Inst) := checkDispatchScopes cx b targets
    match i.op with
    | .loopSwitchBr initial cases elseBody =>
      unless cx.types[i.ty]? == some .noreturn do
        cx.fail 0 s!"inst {i.id}: loop_switch_br must have noreturn type"
      let some selectorTy := valTy initial
        | cx.fail 0 s!"inst {i.id}: loop-switch selector has no known type"
      unless (match selectorTy with
        | .int .. | .bool | .enum .. | .errorSet _ => true | _ => false) do
        cx.fail 0 s!"inst {i.id}: loop-switch selector type is outside the scalar subset"
      for c in cases do
        for v in c.items ++ c.ranges.flatMap (fun (lo, hi) => #[lo, hi]) do
          unless valTy v == some selectorTy do
            cx.fail 0 s!"inst {i.id}: loop-switch case type differs from selector"
        unless c.ranges.isEmpty || (match selectorTy with | .int .. => true | _ => false) do
          cx.fail 0 s!"inst {i.id}: loop-switch ranges require an integer selector"
        unless !c.items.isEmpty || !c.ranges.isEmpty do
          cx.fail 0 s!"inst {i.id}: empty loop-switch case"
        checkDispatchScopes cx c.body (targets.push (i.id, selectorTy))
      checkDispatchScopes cx elseBody (targets.push (i.id, selectorTy))
    | .switchDispatch target v =>
      unless cx.types[i.ty]? == some .noreturn do
        cx.fail 0 s!"inst {i.id}: switch_dispatch must have noreturn type"
      let some (_, selectorTy) := targets.find? (·.1 == target)
        | cx.fail 0 s!"inst {i.id}: dispatch target {target} is not an enclosing loop-switch"
      unless valTy v == some selectorTy do
        cx.fail 0 s!"inst {i.id}: dispatch operand type differs from target selector"
    | .block b | .loop b | .«try» _ b => recur b
    | .condBr _ t e => recur t; recur e
    | .switchBr _ cases e =>
      for c in cases do recur c.body
      recur e
    | _ => pure ()

/-- Reject anything `Emit.lean` cannot translate: see the module doc. -/
def check (f : Func) : Except String Unit := do
  validateTypeGraph f.name f.types
  for p in f.params do
    checkTy f.name f.types f.layouts 0 p
  checkTy f.name f.types f.layouts 0 f.ret
  -- An `extern` or `packed` union is its bytes, also as a value: the model must encode it.
  for (t, id) in f.types.zipIdx do
    if let .union _ _ none _ := t then
      checkMemTy f.name f.types f.layouts 0 id
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
  checkDispatchScopes cx f.body
  let _ ← checkInsts cx 0 f.body
  pure ()

/-- A call to the allocator model (`ZigLean/Mem/Alloc.lean`): the pointers and slices in its
arguments and result have a known item size and `ptr_align`, and a slice that it remaps has no
sentinel. -/
def checkAllocCall (f : Func) (fn : AllocFn) (args : Array Val) (ret : TyId) : Except String Unit := do
  let tyOf (v : Val) : Option TyId := match v with
    | .inst p => (f.allInsts.find? (·.id == p)).map (·.ty)
    | v => v.constTy?
  -- `args[1]` is a pointer or slice, except the item count of `alloc`.
  let argPtr := if fn == .alloc || fn == .alignedAlloc then #[] else (args.extract 1 2).filterMap tyOf
  let ptrs := (match f.types[ret]? with
    | some (.errorUnion _ p) | some (.optional p) => #[p]
    | _ => #[]) ++ argPtr
  for p in ptrs do
    let known := (ptrChild f.types p).bind (f.layouts[·]?.bind (·.size)) |>.isSome
    let l := f.layouts[p]?.getD {}
    unless known && l.ptrAlign.isSome do
      throw s!"{f.name}: a call to the allocator ({repr fn}) with pointer type {p}, which has \
        no item size or `ptr_align` in the AIR file"
    if l.sentinel && fn == .remap then
      throw s!"{f.name}: a remap of a slice with a sentinel is outside the subset"

/-- A call to `Thread.spawn`: `args[1]` (the `.{...}` args tuple) must have exactly one field.
`Zig.Thread.spawn` runs the already-applied call `f args` directly (`ZigLean/Mem/Thread.lean`),
so `Emit.lean` needs the callee applied to exactly one Lean term; a 0- or 2+-field args tuple is
outside the subset (v1, `docs/std-models.md` §Thread model). -/
def checkThreadSpawn (f : Func) (callee : String) (k : Nat) (args : Array Val) :
    Except String Unit := do
  let tyOf (v : Val) : Option TyId := match v with
    | .inst p => (f.allInsts.find? (·.id == p)).map (·.ty)
    | v => v.constTy?
  let some argsTy := args[k]?.bind tyOf
    | throw s!"{f.name}: a call to {callee} has no args-tuple type"
  match f.types[argsTy]? with
  | some (.tuple fields) =>
    if fields.size != 1 then
      throw s!"{f.name}: {callee}'s args tuple has {fields.size} fields; only exactly 1 is \
        in the subset (v1, docs/std-models.md §Thread model)"
  | _ => throw s!"{f.name}: {callee}'s args argument is not a tuple"

/-- The checks that need every function. A function that uses memory reads a slice item from
memory, and a call to a pure function copies each `[]const T` argument from memory
(`Zig.readSlice`): `T` must be a type that the model encodes. Each callee is a translated
function or has a model (`allocFn?`, `threadFn?`). -/
def checkProgram (funcs : Array Func) : Except String Unit := do
  let mem := memoryFunctions funcs
  let names := funcs.map (·.name)
  for f in funcs do
    for i in f.allInsts do
      if let .call (.func callee false spawnFn) args := i.op then
        if ((threadFn? callee).bind (·.spawnArgs?)).isSome then
          let some worker := spawnFn
            | throw s!"{f.name}: a call to '{callee}' has no comptime_fn spawn target"
          unless names.contains worker do
            throw s!"{f.name}: the spawned callee '{worker}' has no AIR file (add its name to the filter, docs/std-models.md)"
        unless names.contains callee do
          if let some reason := rejectedThreadFn? callee then
            throw s!"{f.name}: the callee '{callee}' is outside the subset: {reason}"
          match allocFn? callee with
          | some fn => checkAllocCall f fn args i.ty
          | none =>
            match threadFn? callee with
            | some .spawn => checkThreadSpawn f "Thread.spawn" 1 args
            | some .groupAsync | some .groupConcurrent => checkThreadSpawn f "Io.Group.async" 2 args
            | some .groupAwait | some .groupCancel =>
              unless args.size == 2 do
                throw s!"{f.name}: a call to '{callee}' with {args.size} arguments, not 2"
            | some .join => pure ()
            | some .futexWait | some .futexWaitU | some .futexWake =>
              -- `(io, ptr, value)`: a `u32`-sized value (Zig asserts it), an enum or integer.
              unless args.size == 3 do
                throw s!"{f.name}: a call to '{callee}' with {args.size} arguments, not 3"
            | some .threadFutexWait | some .threadFutexWake =>
              -- `(ptr, u32)`: `ptr` is a `*const std.atomic.Value(u32)`.
              unless args.size == 2 do
                throw s!"{f.name}: a call to '{callee}' with {args.size} arguments, not 2"
            | some .noClock => pure ()
            | some .osLock | some .osUnlock | some .osTryLock =>
              unless args.size == 1 do
                throw s!"{f.name}: a call to '{callee}' with {args.size} arguments, not 1"
            | none =>
              throw s!"{f.name}: the callee '{callee}' has no AIR file and no model (add its \
                name to the example's `filter` file, docs/std-models.md)"
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
          | .call (.func callee _ spawnFn) args =>
            if let some k := (threadFn? callee).bind (·.spawnArgs?) then
              if (spawnFn.map mem.contains).getD true then #[] else
              let child := ((args[k]? : Option Val).bind tyOf).bind fun t =>
                match f.types[t]? with
                | some (.tuple fields) => fields[0]?
                | _ => none
              ((child.bind (f.types[·]?)).bind fun t => match t with
                | .ptr "slice" _ c => some c | _ => none).toArray
            else if mem.contains callee then #[] else args.filterMap sliceItem
          | _ => #[]
        for c in items do
          checkMemTy f.name f.types f.layouts 0 c

end Air2Lean
