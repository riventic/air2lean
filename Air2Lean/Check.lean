import Std.Data.HashMap
import Std.Data.HashSet
import Air2Lean.Memory
import Air2Lean.BitCast
import Air2Lean.Diagnostic
import Air2Lean.Air.Compat
import Air2Lean.ModelRegistry
import ZigLean.Mem.Enc
import ZigLean.Vec

/-!
# Subset checker

`check : Func → Except String Unit` rejects anything `Emit.lean` cannot translate: `other`
types, a union without a tag, a float type outside `16 32 64 80 128` bits, an integer `@abs`, a
an unsupported nullable-pointer representation, a memory access to a value that the memory model cannot
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

/-- Validate immutable declared error names in linear expected time, without repeatedly
running quadratic list deduplication for each instruction that references a domain. -/
def validErrorDomainNames (names : Array String) : Bool := Id.run do
  if names.size > 65535 then return false
  let mut seen : Std.HashSet String := {}
  for name in names do
    if name.isEmpty || seen.contains name then return false
    seen := seen.insert name
  return true

/-- A value's storage can contain symbolic error fragments. Pointer pointees are checked
separately: the representation of the pointer itself does not encode its child's bytes. -/
partial def hasErrorStorage (types : Array Ty) (id : TyId) (seen : Array TyId := #[]) : Bool :=
  if seen.contains id then false
  else if seen.size ≥ 256 then true
  else match types[id]? with
    | some (.errorSet _) | some (.errorUnion ..) => true
    | some (.ptr ..) => false
    | some ty => (childTys ty).any fun child => hasErrorStorage types child (seen.push id)
    | none => false

/-- Unlike byte-storage classification, capability classification follows pointer
edges. Unknown, cyclic and exhausted type traversals cannot prove a safe view. -/
private partial def errorCapabilityScan (types : Array Ty) (id fuel : Nat)
    (seen : Array TyId := #[]) : Option (Nat × Bool) := do
  if fuel == 0 || seen.contains id then none
  let ty ← types[id]?
  let count ← match ty with
    | .other _ | .errorSet none => none
    | .ptr .. | .array .. | .vector .. | .optional .. | .enum .. => some 1
    | .errorUnion .. => some 2
    | .struct _ _ fields => some fields.size
    | .union _ _ tag fields => some (tag.toArray.size + fields.size)
    | .tuple children => some children.size
    | _ => some 0
  let mut remaining := fuel - 1
  if count > remaining then none
  let mut symbolic := match ty with | .errorSet _ | .errorUnion .. => true | _ => false
  for child in childTys ty do
    let (next, childCap) ← errorCapabilityScan types child remaining (seen.push id)
    remaining := next
    symbolic := symbolic || childCap
  return (remaining, symbolic)

private def hasErrorCapability (types : Array Ty) (id : TyId) : Option Bool :=
  (errorCapabilityScan types id 1024).map (·.2)

/-- A closed error-free graph may contain sharing or cycles. This bounded absence proof
is used only for global aliases whose strict capability traversal could not finish;
casts and parent recovery retain the strict cycle-rejecting traversal. -/
private def closedErrorFreeAliasGraph (types : Array Ty) (root child : TyId) : Bool := Id.run do
  let mut pending : List TyId := [root, child]
  let mut visited : Std.HashSet TyId := {}
  for step in [:1024] do
    match pending with
    | [] => return true
    | id :: rest =>
      pending := rest
      if visited.contains id then continue
      let some ty := types[id]? | return false
      match ty with
      | .other _ | .errorSet _ | .errorUnion .. => return false
      | _ => pure ()
      let count := match ty with
        | .ptr .. | .array .. | .vector .. | .optional .. | .enum .. => 1
        | .struct _ _ fields => fields.size
        | .union _ _ tag fields => tag.toArray.size + fields.size
        | .tuple children => children.size
        | _ => 0
      let remaining := 1023 - step
      if count > remaining || rest.length + count > remaining then return false
      visited := visited.insert id
      pending := (childTys ty).toList ++ rest
  return pending.isEmpty

/-- Reject unsupported types and pointer representations, recursively through fields and
tuple fields. `seen`: the types on the path to `id`; a type can point to itself (a list node). -/
partial def checkTy (fnName : String) (types : Array Ty) (layouts : Array Layout) (line : Nat)
    (id : TyId) (seen : Array TyId := #[]) : Except String Unit := do
  if seen.contains id then return
  if seen.size ≥ 256 then throw s!"{fnName}: near line {line}: type traversal exceeds 256 levels"
  let some ty := types[id]?
    | throw s!"{fnName}: near line {line}: unknown type id {id}"
  let recur (c : TyId) := checkTy fnName types layouts line c (seen.push id)
  match ty with
  | .other name =>
    throw s!"{fnName}: near line {line}: type '{name}' is outside the subset (otherwise \
      unsupported)"
  | .float bits =>
    if supportedFloatWidth bits then pure ()
    else
      throw s!"{fnName}: near line {line}: float type of {bits} bits is outside the subset \
        (only 16, 32, 64, 80, 128)"
  | .ptr size isConst child =>
    let l := layouts[id]?.getD {}
    if nullablePtrTy types layouts id && l.isVolatile then
      throw s!"{fnName}: near line {line}: volatile nullable pointers are outside the qualified pointer fragment"
    if nullablePtrTy types layouts id && (size == "slice" || l.hostSize != 0) then
      throw s!"{fnName}: near line {line}: nullable slices and nullable bit-pointers are outside the qualified pointer fragment"
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
    | "many" | "slice" | "c" => recur child
    | _ => throw s!"{fnName}: near line {line}: pointer size '{size}' is outside the subset"
  | .array _ child _ =>
    if nullablePtrTy types layouts child then
      throw s!"{fnName}: near line {line}: nullable pointers in aggregate values are outside the qualified pointer fragment"
    recur child
  | .vector _ child =>
    unless (match types[child]? with
      | some (.int ..) | some (.float _) | some .bool => true | _ => false) do
      throw s!"{fnName}: near line {line}: a vector with lanes other than integers, floats or bool is outside the subset"
    recur child
  | .optional child =>
    if nullablePtrTy types layouts child then
      throw s!"{fnName}: near line {line}: an optional C/allowzero pointer needs a separate null flag and is outside the qualified pointer fragment"
    recur child
  | .errorUnion set payload => do
    if nullablePtrTy types layouts payload then
      throw s!"{fnName}: near line {line}: nullable pointer error-union payloads are outside the qualified pointer fragment"
    recur set
    recur payload
  | .errorSet none => pure ()
  | .errorSet (some names) =>
    if !validErrorDomainNames names then
      throw s!"{fnName}: near line {line}: an error encoding domain must have at most 65535 distinct nonempty names"
    pure ()
  | .struct name layout fields =>
    if fields.any (fun (_, c) => nullablePtrTy types layouts c) then
      throw s!"{fnName}: near line {line}: nullable pointers in aggregate values are outside the qualified pointer fragment"
    if layout == "packed" && (packedBits types id).isNone then
      throw s!"{fnName}: near line {line}: packed struct '{name}' has a field other than an \
        integer, a `bool`, an enum or a packed struct: outside the subset"
    fields.forM fun (_, fty) => recur fty
  | .enum _ tag _ _ => recur tag
  | .union name layout tag fields =>
    if fields.any (fun (_, c) => nullablePtrTy types layouts c) then
      throw s!"{fnName}: near line {line}: nullable pointers in aggregate values are outside the qualified pointer fragment"
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
  | .tuple fields =>
    if fields.any (nullablePtrTy types layouts) then
      throw s!"{fnName}: near line {line}: nullable pointers in aggregate values are outside the qualified pointer fragment"
    fields.forM recur
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
  | some (.ptr size ..) =>
    if nullablePtrTy types layouts id then
      throw "a C/allowzero pointer stored as a memory value needs qualified null-byte encoding"
    pure (if size == "slice" then 16 else 8, 8)
  | some .allocator => pure (16, 8)
  | some .thread => pure (8, 8)
  | some .io => pure (16, 8)
  | some (.optional c) =>
    if nullablePtrTy types layouts c then
      throw "an optional C/allowzero pointer needs a separate null flag"
    match types[c]? with
    | some (.ptr "slice" ..) => pure (16, 8)
    | some (.ptr ..) => pure (8, 8)
    | some (.errorSet _) => modelLayout types layouts c
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
    if let some (.errorSet (some names)) := types[set]? then
      -- An empty discriminator has no standalone value, but its union's success arm does.
      unless names.isEmpty do
        let _ ← modelLayout types layouts set
    let (s, a) ← modelLayout types layouts payload
    pure (Zig.errUnionSize s a, Nat.max a 2)
  | some (.errorSet none) =>
    throw "standalone anyerror or unresolved error storage has no finite declared encoding domain"
  | some (.errorSet (some names)) =>
    if names.isEmpty then throw "an empty standalone error domain has no runtime value"
    if names.size > 65535 then throw "an error encoding domain exceeds the 16-bit nonzero code capacity"
    if !validErrorDomainNames names then
      throw "an error encoding domain must have distinct nonempty names"
    unless (layouts[id]?.map fun l => l.size == some 2 && l.align == some 2).getD false do
      throw "an error set storage layout must be 2 bytes aligned to 2 (16-bit error codes)"
    pure (2, 2)
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
  /-- Provenance before escape lowering, for bounded local parent recovery. -/
  localRoots : Array (InstId × InstId) := #[]
  localPaths : Array (InstId × Array LocalPathStep) := #[]
  /-- Internal summaries populated by `check` only after all nested IDs are unique.
  Bare/public checker contexts default to the uncached path. -/
  tryErrorExits : Std.HashMap InstId Bool := {}
  /-- The function's `zig_version`: selects the `@bitCast` semantics (`Air2Lean/BitCast.lean`). -/
  zigVersion : String := ""

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

/-- Nullable pointer projections/arithmetic are not yet part of the qualified fragment.
Cast to a nonnullable pointer after a null check before projecting or constructing a slice. -/
def CheckCtx.rejectNullableProjection (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  if (cx.valTy? ptr |>.map (nullablePtrTy cx.types cx.layouts) |>.getD false) then
    cx.fail line "nullable pointer arithmetic, indexing and projections require a nonnull cast first (outside the qualified pointer fragment)"

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
  cx.rejectNullableProjection line ptr
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

/-- Reachable error-body outcomes. `valid` excludes falling off a sequence and
unsupported loop control; `branches` tracks block exits until an enclosing block consumes them. -/
private structure TryErrorFlow where
  valid : Bool
  branches : Std.HashSet InstId := {}
  deriving Inhabited

private def TryErrorFlow.merge (a b : TryErrorFlow) : TryErrorFlow :=
  ⟨a.valid && b.valid, a.branches.union b.branches⟩

/-- Separate contracts for pointer-try error bodies and outward-terminal block bodies.
Both maps are empty if any nested instruction ID is duplicated. -/
structure ControlFlowSummaries where
  tryErrorExits : Std.HashMap InstId Bool := {}
  outwardBlocks : Std.HashMap InstId Bool := {}
  deriving Inhabited

private structure ControlFlowCache where
  summaries : ControlFlowSummaries := {}
  ids : Std.HashSet InstId := {}
  unique : Bool := true
  deriving Inhabited

/-- Compute each child flow once, bottom-up, including unreachable child bodies for
later checking. Only reachable outcomes contribute to the parent flow: the first
terminator ends its sequence and a block consumes only its own branch. No diagnostics
are emitted here. The same traversal records every ID, including unreachable children;
the public helper discards both maps on any duplicate. -/
private partial def summarizeTryErrors (insts : Array Inst) (cache : ControlFlowCache) :
    TryErrorFlow × ControlFlowCache :=
  -- Array.foldr traverses flat siblings right-to-left without recursive pending
  -- frames for `rest`; this function recurses only into nested instruction arrays.
  insts.foldr (init := ((⟨false, {}⟩ : TryErrorFlow), cache)) fun inst (later, cache) =>
    let cache := { cache with
      unique := cache.unique && !cache.ids.contains inst.id
      ids := cache.ids.insert inst.id }
    match inst.op with
    | .ret _ | .retLoad _ | .unreach | .trap => (⟨true, {}⟩, cache)
    | .call (.func _ true ..) _ => (⟨true, {}⟩, cache)
    | .br target _ => (⟨true, ({} : Std.HashSet InstId).insert target⟩, cache)
    | .«repeat» _ | .switchDispatch .. => (⟨false, {}⟩, cache)
    | .loop body =>
      let (_, cache) := summarizeTryErrors body cache
      (⟨false, {}⟩, cache)
    | .loopSwitchBr _ cases e =>
      let (_, cache) := summarizeTryErrors e cache
      let cache := cases.foldl (init := cache) fun cache c =>
        (summarizeTryErrors c.body cache).2
      (⟨false, {}⟩, cache)
    | .condBr _ t e =>
      let (thenFlow, cache) := summarizeTryErrors t cache
      let (elseFlow, cache) := summarizeTryErrors e cache
      (thenFlow.merge elseFlow, cache)
    | .switchBr _ cases e =>
      let (elseFlow, cache) := summarizeTryErrors e cache
      cases.foldl (init := (elseFlow, cache)) fun (flow, cache) c =>
        let (caseFlow, cache) := summarizeTryErrors c.body cache
        (flow.merge caseFlow, cache)
    | .block body =>
      let (inner, cache) := summarizeTryErrors body cache
      let summaries := { cache.summaries with
        outwardBlocks := cache.summaries.outwardBlocks.insert inst.id
          (inner.valid && !inner.branches.contains inst.id) }
      let cache := { cache with summaries }
      let flow := if inner.branches.contains inst.id then
          (⟨inner.valid, inner.branches.erase inst.id⟩ : TryErrorFlow).merge later
        else inner
      (flow, cache)
    | .«try» _ errBody | .tryPtr _ errBody =>
      let (errorFlow, cache) := summarizeTryErrors errBody cache
      let summaries := { cache.summaries with
        tryErrorExits := cache.summaries.tryErrorExits.insert inst.id
          (errorFlow.valid && errorFlow.branches.isEmpty) }
      let cache := { cache with summaries }
      (errorFlow.merge later, cache)
    | _ => (later, cache)

/-- One bottom-up traversal for both control contracts and ID uniqueness. A block may
exit to an enclosing block; a pointer-try error body must exit the function instead. -/
def controlFlowSummaries (body : Array Inst) : ControlFlowSummaries :=
  let cache := (summarizeTryErrors body {}).2
  if cache.unique then cache.summaries else {}

/-- Every reachable path must exit the function, with no unconsumed block branch.
Loops, fallthrough and switches without an explicit else are conservative failures. -/
def tryErrorBodyExits (body : Array Inst) : Bool :=
  let flow := (summarizeTryErrors body {}).1
  flow.valid && flow.branches.isEmpty

/-- Scalar or vector integer shape: lane count, signedness and element width. -/
def CheckCtx.intShape? (cx : CheckCtx) (t : TyId) : Option (Option Nat × Bool × Nat) :=
  match cx.types[t]? with
  | some (.int s n) => some (none, s, n)
  | some (.vector len c) => match cx.types[c]? with
    | some (.int s n) => some (some len, s, n)
    | _ => none
  | _ => none

/-- Zig's bit counts return the smallest unsigned type able to represent the source width. -/
def bitCountWidth (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

mutual

partial def checkInst (cx : CheckCtx) (line : Nat) (inst : Inst) : Except String Nat := do
  checkTy cx.fnName cx.types cx.layouts line inst.ty
  checkOp cx line inst.ty inst.op cx.tryErrorExits[inst.id]?

partial def checkOp (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op)
    (cachedTryExit : Option Bool := none) : Except String Nat := do
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
  | .permuteBits op a =>
    let some aty := cx.valTy? a | cx.fail line "bit permutation operand has no known type"
    let some (_, _, bits) := cx.intShape? aty
      | cx.fail line "bit permutation requires an integer or integer vector operand"
    unless aty == ty do
      cx.fail line "bit permutation result must preserve the operand type"
    if op == .byteSwap && bits % 8 != 0 then
      cx.fail line "byte swap requires an integer width evenly divisible by 8"
    pure line
  | .countBits _ a =>
    let some aty := cx.valTy? a | cx.fail line "bit count operand has no known type"
    let some (alen, _, bits) := cx.intShape? aty
      | cx.fail line "bit count requires an integer or integer vector operand"
    let some (rlen, signed, width) := cx.intShape? ty
      | cx.fail line "bit count result must be an unsigned integer or integer vector"
    unless alen == rlen && !signed && width == bitCountWidth bits do
      cx.fail line "bit count result must preserve vector length and have the unsigned count width"
    pure line
  | .shlWithOverflow a b =>
    let some aty := cx.valTy? a | cx.fail line "shift-overflow operand has no known type"
    let some bty := cx.valTy? b | cx.fail line "shift-overflow count has no known type"
    let some (alen, _, abits) := cx.intShape? aty
      | cx.fail line "shift-overflow requires an integer or integer vector operand"
    let some (blen, bsign, bbits) := cx.intShape? bty
      | cx.fail line "shift-overflow count must be an unsigned integer or integer vector"
    unless alen == blen && !bsign && bbits == bitCountWidth (abits - 1) do
      cx.fail line "shift-overflow count must have the unsigned Log2Int width and preserve vector length"
    let some (.tuple fields) := cx.types[ty]?
      | cx.fail line "shift-overflow result must be a pair tuple"
    unless fields.size == 2 && fields[0]? == some aty do
      cx.fail line "shift-overflow result must pair the operand type with its overflow bit"
    let some flagTy := fields[1]? | cx.fail line "shift-overflow result is missing its overflow bit"
    unless cx.intShape? flagTy == some (alen, false, 1) do
      cx.fail line "shift-overflow flag must be u1 with the operand vector length"
    pure line
  | .intCast a =>
    if ((cx.valTy? a).map (fun id => hasErrorStorage cx.types id)).getD false || hasErrorStorage cx.types ty then
      cx.fail line "integer/error casts require compiler-wide finalized error ordinals and are outside the finite symbolic error-storage fragment"
    pure line
  | .bitcast a =>
    let sourceTy := cx.valTy? a
    let isError (t : Option Ty) := match t with | some (.errorSet _) => true | _ => false
    if isError (sourceTy.bind (cx.types[·]?)) != isError (cx.types[ty]?) then
      cx.fail line "raw error representation casts require finalized error ordinals and are outside the finite symbolic error-storage fragment"
    if let some aty := sourceTy then
      let bothErrors := isError (cx.types[aty]?) && isError (cx.types[ty]?)
      -- Duplicate finite error-union IDs preserve the same symbolic decoder only
      -- when ordered declared names, payload identity and all representation metadata agree.
      let sameFiniteErrorUnion := ((do
        let .errorUnion aset apayload ← cx.types[aty]? | none
        let .errorUnion bset bpayload ← cx.types[ty]? | none
        let .errorSet (some anames) ← cx.types[aset]? | none
        let .errorSet (some bnames) ← cx.types[bset]? | none
        let a ← cx.layouts[aty]?
        let b ← cx.layouts[ty]?
        let ae ← cx.layouts[aset]?
        let be ← cx.layouts[bset]?
        let _ ← cx.types[apayload]?
        let payload ← cx.layouts[apayload]?
        return apayload == bpayload && anames == bnames && validErrorDomainNames anames &&
          a.size.isSome && a.align.isSome && ae.size.isSome && ae.align.isSome &&
          payload.size.isSome && payload.align.isSome && a == b && ae == be : Option Bool)).getD false
      if aty != ty && !bothErrors && !sameFiniteErrorUnion && (hasErrorStorage cx.types aty || hasErrorStorage cx.types ty) then
        cx.fail line "an opaque bitcast involving optional, aggregate or error-union error storage is outside the finite symbolic error-storage fragment"
      let pointerChild (id : TyId) : Option TyId :=
        match cx.types[id]? with
        | some (.optional child) => ptrChild cx.types child
        | _ => ptrChild cx.types id
      -- Changing only const qualification preserves the decoder and pointer
      -- representation even when the unchanged pointee graph is recursive.
      let qualifierPointer (id : TyId) : Option (Bool × TyId × String × Bool × TyId) := do
        let (optional, pid) ← match cx.types[id]? with
          | some (.optional pid) => some (true, pid)
          | some (.ptr ..) => some (false, id)
          | _ => none
        let .ptr kind isConst child ← cx.types[pid]? | none
        return (optional, pid, kind, isConst, child)
      let qualifierOnly := ((do
        let (aopt, apid, akind, aconst, achild) ← qualifierPointer aty
        let (bopt, bpid, bkind, bconst, bchild) ← qualifierPointer ty
        let a ← cx.layouts[aty]?
        let b ← cx.layouts[ty]?
        let ap ← cx.layouts[apid]?
        let bp ← cx.layouts[bpid]?
        return aopt == bopt && akind == bkind && aconst != bconst && achild == bchild &&
          a.size.isSome && a.align.isSome && ap.size.isSome && ap.align.isSome &&
          ap.ptrAlign.isSome && a == b && ap == bp : Option Bool)).getD false
      -- Wrapping an exact non-null single pointer in its own optional type
      -- emits only the existing Ptr-to-Option coercion. No pointee/decoder changes.
      let optionalWrapOnly := ((do
        let .ptr "one" _ _ ← cx.types[aty]? | none
        let .optional pid ← cx.types[ty]? | none
        let a ← cx.layouts[aty]?
        let b ← cx.layouts[ty]?
        return pid == aty && a.size.isSome && a.align.isSome &&
          a.ptrAlign.isSome && b.ptrAlign.isNone &&
          a == { b with ptrAlign := a.ptrAlign } : Option Bool)).getD false
      match pointerChild aty, pointerChild ty with
      | some source, some target =>
        unless qualifierOnly || optionalWrapOnly do
          let some sourceCap := hasErrorCapability cx.types source
            | cx.fail line "a pointer cast has unresolved or cyclic symbolic storage provenance"
          let some targetCap := hasErrorCapability cx.types target
            | cx.fail line "a pointer cast has unresolved or cyclic symbolic storage provenance"
          if sourceCap != targetCap ||
              hasErrorStorage cx.types source != hasErrorStorage cx.types target ||
              ((sourceCap || targetCap) && source != target) then
            cx.fail line "a pointer cast exposing symbolic error storage as numeric or opaque bytes requires finalized error ordinals and is outside the finite error-storage fragment"
      | none, some target =>
        unless hasErrorCapability cx.types target == some false do
          cx.fail line "recovering a symbolic error pointer from an integer or opaque value needs unsupported storage provenance"
      | _, _ => pure ()
    -- Zig 0.17: an array, vector or enum on either side is a logical-bit-order cast
    -- (`Air2Lean/BitCast.lean`); a shape the model lacks is rejected, never translated with the
    -- ≤0.16 memory rules below.
    if let some aty := sourceTy then
      if logicalBitCastVersion cx.zigVersion && aty != ty &&
          (logicalBitCastTy cx.types aty || logicalBitCastTy cx.types ty) then
        match logicalBitCastShapes cx.types aty ty with
        | .ok _ => return line
        | .error e => cx.fail line e
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
      if isOptPtr ty && nullablePtrTy cx.types cx.layouts aty then
        cx.fail line "casting a C/allowzero pointer to an optional pointer needs explicit null wrapping and is outside the qualified pointer fragment"
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
    cx.rejectNullableProjection line base
    if let .inst b := base then
      if cx.places.contains b then return line
    -- A field pointer into memory needs the field offsets.
    let pty ← cx.memPtrTy line base
    checkMemTy fnName cx.types cx.layouts line (ptrChild cx.types pty).get!
    pure line
  | .fieldParentPtr fieldPtr idx =>
    cx.rejectNullableProjection line fieldPtr
    if let .inst b := fieldPtr then
      if cx.localRoots.any (·.1 == b) || cx.places.contains b then
        let some (_, path) := cx.localPaths.find? (·.1 == b)
          | cx.fail line "local `@fieldParentPtr` needs a proven terminal struct field"
        let some source := cx.valTy? fieldPtr
          | cx.fail line "local `@fieldParentPtr` operand has no known type"
        unless (localParentPath? cx.types cx.layouts source ty idx path).isSome do
          cx.fail line "local `@fieldParentPtr` requires the matching terminal ordinary struct field and pointer types (packed, union and bit-pointer recovery are outside the subset)"
        -- An escaped local still uses the existing memory offset lowering below.
        if cx.places.contains b then return line
    let _ ← cx.memPtrTy line fieldPtr
    let some (.ptr _ _ parent) := cx.types[ty]?
      | cx.fail line "`@fieldParentPtr`'s result is not a pointer"
    checkMemTy fnName cx.types cx.layouts line parent
    pure line
  | .ptrElemVal p _ | .memset p _ => cx.itemAccess line p; pure line
  | .ptrAdd _ p _ | .elemPtr p _ =>
    cx.rejectNullableProjection line p
    -- The result is a pointer to an item: its child is the item type.
    if let some pty := cx.valTy? p then
      if let some (.ptr "one" _ c) := cx.types[pty]? then
        if let some (.vector ..) := cx.types[c]? then
          cx.itemAccess line p
    cx.knownSize line (ptrChild cx.types ty).get!
    pure line
  | .memcpy dst src =>
    cx.rejectNullableProjection line dst
    cx.rejectNullableProjection line src
    let _ ← cx.memPtrTy line src
    let dty ← cx.memPtrTy line dst
    cx.knownSize line (itemTy cx.types dty).get!
    pure line
  | .wrapOptional p =>
    if (cx.valTy? p |>.map (nullablePtrTy cx.types cx.layouts) |>.getD false) then
      cx.fail line "wrapping a C/allowzero pointer as an optional needs explicit null wrapping"
    pure line
  | .slice p _ => cx.rejectNullableProjection line p; pure line
  | .arrayToSlice p =>
    cx.rejectNullableProjection line p
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
  | .tryPtr p errBody => do
    let pty ← cx.memPtrTy line p
    let some (.ptr "one" isConst unionTy) := cx.types[pty]?
      | cx.fail line "try_ptr requires a single pointer to an error union"
    let some (.errorUnion _ payload) := cx.types[unionTy]?
      | cx.fail line "try_ptr requires a pointer to an error union"
    unless cx.types[ty]? == some (.ptr "one" isConst payload) do
      cx.fail line "try_ptr result must be a pointer to the same payload with matching constness"
    for ptrTy in #[pty, ty] do
      let layout := cx.layouts[ptrTy]?.getD {}
      if layout.isVolatile then
        cx.fail line "try_ptr through a volatile pointer is outside the subset"
      if layout.hostSize != 0 then
        cx.fail line "try_ptr through a bit-pointer is outside the subset"
      if layout.ptrAlign.isNone then
        cx.fail line "try_ptr pointer type has no ptr_align in the AIR file"
    checkMemTy fnName cx.types cx.layouts line unionTy
    let exits := match cachedTryExit with
      | some exits => exits
      | none => tryErrorBodyExits errBody
    unless exits do
      cx.fail line "try_ptr error body must exit without fallthrough"
    let nested := errBody.foldl flattenInst #[]
    let emptyTargets : Std.HashSet InstId := {}
    let localTargets := nested.foldl (init := emptyTargets) fun targets i =>
      match i.op with | .block _ | .loop _ => targets.insert i.id | _ => targets
    for i in nested do
      match i.op with
      | .br target _ | .«repeat» target =>
        unless localTargets.contains target do
          cx.fail line "try_ptr error body must exit the function, not branch outside its body"
      | _ => pure ()
    let _ ← checkInsts cx line errBody
    pure line
  | .«try» _ errBody => do
    let _ ← checkInsts cx line errBody
    pure line
  | .line n => pure n
  | .asm _ _ clobbers outputs inputs =>
    if op.isSpinHint && cx.types[ty]? != some .void then
      throw s!"{fnName}: near line {line}: a spin hint must return void"
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

/-- Zero constants are permitted only for a nonoptional C/allowzero pointer. -/
partial def checkNullConstants (fnName : String) (types : Array Ty) (layouts : Array Layout)
    (v : Val) : Except String Unit := do
  match v with
  | .ptrNull ty =>
    unless nullablePtrTy types layouts ty do
      throw s!"{fnName}: address-zero constant requires a C/allowzero pointer type"
  | .agg _ elems => elems.forM (checkNullConstants fnName types layouts)
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => checkNullConstants fnName types layouts v
  | .sliceConst _ p l =>
    checkNullConstants fnName types layouts p
    checkNullConstants fnName types layouts l
  | _ => pure ()

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

/-- A shared budget proves absence of embedded pointer capabilities, including
inactive optional payload types. Unknown types, cycles and exhausted work fail closed. -/
private partial def pointerFreeInitializerType (f : Func) (root fuel : Nat) : Option Nat := do
  if fuel == 0 then none
  let ty ← f.types[root]?
  let count ← match ty with
    | .int .. | .float .. | .bool | .void | .errorSet (some _) => some 0
    | .array .. | .vector .. | .optional .. | .enum .. => some 1
    | .errorUnion .. => some 2
    | .struct _ _ fields => some fields.size
    | .tuple children => some children.size
    | _ => none
  let mut remaining := fuel - 1
  if count > remaining then none
  let children := childTys ty
  for child in children do
    remaining ← pointerFreeInitializerType f child remaining
  return remaining

/-- Complete constructor values whose typed encoding contains no `errFrag`.
Success error-union tags and null optional-error tags encode literal zero bytes.
Undefined/unknown values, error names/arms, pointers and opaque unions fail closed. -/
private partial def ordinaryInitializer (f : Func) (root : TyId) (v : Val) (fuel : Nat) :
    Option Nat := do
  if fuel == 0 then none
  let ty ← f.types[root]?
  if let some actual := v.constTy? then
    if actual != root then none
  let mut remaining := fuel - 1
  let items (children : Array TyId) (values : Array Val) : Option Nat := do
    if children.size != values.size || values.size > remaining then none
    let mut rest := remaining
    for (child, value) in children.zip values do
      rest ← ordinaryInitializer f child value rest
    return rest
  match ty, v with
  | .int .., .int .. | .float .., .float .. | .enum .., .enumTag ..
  | .bool, .bool _ | .void, .void => return remaining
  | .optional _, .optNull _ => return remaining
  | .optional child, .optSome _ value => ordinaryInitializer f child value remaining
  | .errorUnion set payload, .errUnionOk _ value =>
    let .errorSet (some _) ← f.types[set]? | none
    ordinaryInitializer f payload value remaining
  | .array count child sentinel, .agg _ values =>
    let count := count + if sentinel then 1 else 0
    if values.size != count || count > remaining then none
    for value in values do
      remaining ← ordinaryInitializer f child value remaining
    return remaining
  | .vector count child, .agg _ values =>
    if values.size != count || count > remaining then none
    for value in values do
      remaining ← ordinaryInitializer f child value remaining
    return remaining
  | .struct _ _ fields, .agg _ values =>
    if fields.size != values.size || fields.size > remaining then none
    items (fields.map (·.2)) values
  | .tuple children, .agg _ values => items children values
  | _, _ => none

/-- No mutable or unresolved backing qualifies. Both traversals consume one shared
1024-node budget. Encoding padding may be undefined; constructor values may not be. -/
private def immutableOrdinaryGlobal (f : Func) (g : Global) : Bool :=
  if !g.isConst || g.isExtern || g.threadlocal then false else
  ((do
    let value ← g.init
    let remaining ← pointerFreeInitializerType f g.ty 1024
    ordinaryInitializer f g.ty value remaining : Option Nat)).isSome

/-- Clipped overlap queries use a shared work budget. `none` means that the
layout or budget cannot establish absence of symbolic bytes, so callers fail closed. -/
private partial def errorFreeGlobalRange (f : Func) (root off width fuel : Nat) :
    Option (Nat × Bool) := do
  if fuel == 0 then none
  let mut remaining := fuel - 1
  let (size, _) ← (modelLayout f.types f.layouts root).toOption
  if off > size || width > size - off then return (remaining, false)
  if width == 0 || !hasErrorStorage f.types root then return (remaining, true)
  let recur (child base : Nat) : Option (Nat × Bool) := do
    let (childSize, _) ← (modelLayout f.types f.layouts child).toOption
    let lo := Nat.max off base
    let hi := Nat.min (off + width) (base + childSize)
    if hi ≤ lo then return (remaining, true)
    errorFreeGlobalRange f child (lo - base) (hi - lo) remaining
  match ← f.types[root]? with
  | .errorSet _ => return (remaining, false)
  | .optional child => recur child 0
  | .errorUnion _ payload =>
    let (size, align) ← (modelLayout f.types f.layouts payload).toOption
    let (code, base) := Zig.errUnionOffsets size align
    if off < code + 2 && code < off + width then return (remaining, false)
    recur payload base
  | .array len child sentinel =>
    let (stride, _) ← (modelLayout f.types f.layouts child).toOption
    if stride == 0 then return (remaining, true)
    let first := off / stride
    let last := (off + width - 1) / stride
    if last ≥ len + (if sentinel then 1 else 0) || last - first + 1 > remaining then none
    for k in List.range (last - first + 1) do
      let (next, safe) ← errorFreeGlobalRange f child
        (Nat.max off ((first + k) * stride) - (first + k) * stride)
        (Nat.min (off + width) ((first + k + 1) * stride) - Nat.max off ((first + k) * stride)) remaining
      remaining := next
      if !safe then return (remaining, false)
    return (remaining, true)
  | .struct _ _ fields =>
    let offsets := (f.layouts[root]?.getD {}).offsets
    if offsets.size != fields.size || fields.size > remaining then none
    for ((_, child), k) in fields.zipIdx do
      let (childSize, _) ← (modelLayout f.types f.layouts child).toOption
      let base := offsets[k]!
      let lo := Nat.max off base
      let hi := Nat.min (off + width) (base + childSize)
      if lo < hi then
        let (next, safe) ← errorFreeGlobalRange f child (lo - base) (hi - lo) remaining
        remaining := next
        if !safe then return (remaining, false)
    return (remaining, true)
  -- A union's active-member proof and other opaque aggregate projections are not
  -- reconstructed from a folded address. An identical typed root still works below.
  | _ => return (remaining, false)

/-- A symbolic alias must name a complete, structurally matching subobject. This
keeps typed E/aggregate roots and numeric error-union payloads distinct from raw codes. -/
private partial def matchingGlobalSubobject (f : Func) (root off target fuel : Nat) :
    Option (Nat × Bool) := do
  if fuel == 0 then none
  let mut remaining := fuel - 1
  if off == 0 && compatibleType f f root target then return (remaining, true)
  match ← f.types[root]? with
  | .optional child => matchingGlobalSubobject f child off target remaining
  | .errorUnion set payload =>
    let (size, align) ← (modelLayout f.types f.layouts payload).toOption
    let (code, base) := Zig.errUnionOffsets size align
    if off == code && compatibleType f f set target then return (remaining, true)
    if off < base then return (remaining, false)
    matchingGlobalSubobject f payload (off - base) target remaining
  | .array len child sentinel =>
    let (stride, _) ← (modelLayout f.types f.layouts child).toOption
    if stride == 0 || off / stride ≥ len + (if sentinel then 1 else 0) then return (remaining, false)
    matchingGlobalSubobject f child (off % stride) target remaining
  | .struct _ _ fields =>
    let offsets := (f.layouts[root]?.getD {}).offsets
    if offsets.size != fields.size || fields.size > remaining then none
    for ((_, child), k) in fields.zipIdx do
      let base := offsets[k]!
      let (childSize, _) ← (modelLayout f.types f.layouts child).toOption
      if base ≤ off && off < base + childSize then
        let (next, matched) ← matchingGlobalSubobject f child (off - base) target remaining
        remaining := next
        if matched then return (remaining, true)
    return (remaining, false)
  | _ => return (remaining, false)

private def globalAliasPointer? (f : Func) (id : TyId) : Option (String × TyId) :=
  match f.types[id]? with
  | some (.ptr kind _ child) => some (kind, child)
  | some (.optional p) => match f.types[p]? with
    | some (.ptr kind _ child) => some (kind, child)
    | _ => none
  | _ => none

/-- Ordinary backing permits numeric views only. Symbolic decoders still require
matching typed subobjects and cannot escape through this exception. -/
private def immutableOrdinaryNumericAlias (f : Func) (g : Global) (pty : TyId) : Bool :=
  match globalAliasPointer? f pty with
  | some (_, child) => hasErrorCapability f.types child == some false &&
      (pointerFreeInitializerType f child 1024).isSome && immutableOrdinaryGlobal f g
  | none => false

private def globalAliasPointerLayout (f : Func) (id : TyId) : Layout :=
  match f.types[id]? with
  | some (.optional p) => f.layouts[p]?.getD {}
  | _ => f.layouts[id]?.getD {}

/-- A multiple-item capability needs matching storage throughout its backing block,
not just a matching first field. Scalar/aggregate roots and homogeneous arrays qualify. -/
private def homogeneousGlobalItems (f : Func) (root target off : Nat) : Bool :=
  if off == 0 && compatibleType f f root target then true
  else match f.types[root]? with
  | some (.array len child sentinel) =>
    match (modelLayout f.types f.layouts child).toOption with
    | some (stride, _) => stride != 0 && off % stride == 0 &&
        off / stride < len + (if sentinel then 1 else 0) && compatibleType f f child target
    | none => false
  | _ => false

private def checkGlobalAliasAt (f : Func) (pty g off : Nat) : Except String Unit := do
  let some global := f.globals[g]? | throw s!"{f.name}: pointer has unknown global id {g}"
  let some (kind, child) := globalAliasPointer? f pty
    | throw s!"{f.name}: global alias has no pointer type"
  -- A named function block stores code identity (one undefined byte in Emit),
  -- not encoded pointee storage. Admit only its exact immutable zero-offset address.
  if let some (.func name ..) := global.init then
    let pointerLayout := f.layouts[pty]?.getD {}
    if off == 0 && kind == "one" && global.ty == child &&
        f.types[pty]? == some (.ptr "one" true child) &&
        (f.types[child]?.map isFnTy).getD false && global.name == some name &&
        global.isConst && !global.threadlocal && !global.isExtern &&
        pointerLayout.size.isSome && pointerLayout.align.isSome &&
        !pointerLayout.sentinel && pointerLayout.sentinelByte.isNone &&
        !pointerLayout.isVolatile && !pointerLayout.allowzero &&
        pointerLayout.hostSize == 0 && pointerLayout.bitOffset == 0 then return
  let scanned := hasErrorCapability f.types child
  if scanned.isNone && !hasErrorStorage f.types global.ty &&
      closedErrorFreeAliasGraph f.types global.ty child then return
  let some capability := scanned
    | throw s!"{f.name}: global alias has unresolved or cyclic symbolic storage provenance"
  if !hasErrorStorage f.types global.ty && !capability then return
  checkMemTy f.name f.types f.layouts 0 global.ty
  checkMemTy f.name f.types f.layouts 0 child
  let (size, _) ← (modelLayout f.types f.layouts child).mapError fun e => s!"{f.name}: {e}"
  let pointerLayout := globalAliasPointerLayout f pty
  let width := if pointerLayout.hostSize == 0 then size else pointerLayout.hostSize
  let (globalSize, _) ← (modelLayout f.types f.layouts global.ty).mapError fun e => s!"{f.name}: {e}"
  if off > globalSize || width > globalSize - off then
    throw s!"{f.name}: global alias subobject exceeds its backing storage"
  if immutableOrdinaryNumericAlias f global pty then return
  -- Moving either way must preserve element storage throughout the block.
  if kind != "one" && !homogeneousGlobalItems f global.ty child off then
    throw s!"{f.name}: a many/C/slice alias into mixed error-bearing storage is outside the finite error-storage fragment"
  if capability && pointerLayout.hostSize != 0 then
    throw s!"{f.name}: a bit-pointer view of symbolic error storage is outside the finite error-storage fragment"
  let allowed := if capability then
      (matchingGlobalSubobject f global.ty off child 1024).map (·.2)
    else (errorFreeGlobalRange f global.ty off width 1024).map (·.2)
  unless allowed == some true do
    throw s!"{f.name}: global pointer alias overlaps symbolic error bytes or has an unresolved subobject/layout; finalized error ordinals are outside the finite error-storage fragment"

private partial def checkGlobalAliasConstants (f : Func) (v : Val) (fuel : Nat := 256) : Except String Unit := do
  if fuel == 0 then throw s!"{f.name}: global alias constant traversal exceeds 256 levels"
  match v with
  | .ptrConst pty g off => checkGlobalAliasAt f pty g off
  | .agg _ vs => vs.forM fun v => checkGlobalAliasConstants f v (fuel - 1)
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => checkGlobalAliasConstants f v (fuel - 1)
  | .sliceConst _ p n => checkGlobalAliasConstants f p (fuel - 1); checkGlobalAliasConstants f n (fuel - 1)
  | _ => pure ()

private def aliasValueTy? (insts : Array Inst) (v : Val) : Option TyId :=
  match v with
  | .inst id => (insts.find? (·.id == id)).map (·.ty)
  | _ => v.constTy?

private partial def carriesPointer (f : Func) (ty : TyId) (fuel : Nat := 256) : Bool :=
  if fuel == 0 then true else
  match f.types[ty]? with
  | some (.ptr ..) => true
  | some ty => (childTys ty).any fun child => carriesPointer f child (fuel - 1)
  | none => true

/-- Bounded local expression dependencies, including block result branches and pointer
initializers. This is not an interprocedural/general pointer provenance analysis. -/
private partial def errorGlobalDependency (f : Func) (insts : Array Inst) (v : Val) (fuel : Nat) :
    Option (Nat × Bool) := do
  if fuel == 0 then none
  let mut remaining := fuel - 1
  let mut deps : Array Val := #[]
  match v with
  | .ptrConst _ g _ =>
    let global ← f.globals[g]?
    if hasErrorStorage f.types global.ty then return (remaining, true)
    deps := global.init.toArray
  | .inst id =>
    let i ← insts.find? (·.id == id)
    -- Scalar data can select a pointer or name string without aliasing its storage.
    if !carriesPointer f i.ty then return (remaining, false)
    deps := match i.op with
      | .block _ => insts.filterMap fun j => match j.op with
        | .br target value => if target == id then some value else none
        | _ => none
      | _ => valueOperands i.op ++ ptrOperands i.op
  | .agg _ vs => deps := vs
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => deps := #[v]
  | .sliceConst _ p n => deps := #[p, n]
  | _ => return (remaining, false)
  if deps.size > remaining then none
  for dep in deps do
    let (next, rooted) ← errorGlobalDependency f insts dep remaining
    remaining := next
    if rooted then return (remaining, true)
  return (remaining, false)

private def dependsOnErrorGlobal (f : Func) (insts : Array Inst) (v : Val) : Bool :=
  ((errorGlobalDependency f insts v 1024).map (·.2)).getD true

/-- Track only transparent local pointer constructors with fixed byte offsets.
A block result is transparent only with exactly one branch targeting that block.
Unknown arithmetic, multi-branch joins, loaded pointers and calls have no origin. -/
private partial def fixedGlobalOrigin? (f : Func) (insts : Array Inst) (v : Val) (fuel : Nat := 256) : Option (Nat × Nat) := do
  if fuel == 0 then none
  match v with
  | .ptrConst _ g off => some (g, off)
  | .optSome _ p => fixedGlobalOrigin? f insts p (fuel - 1)
  | .sliceConst _ p _ => fixedGlobalOrigin? f insts p (fuel - 1)
  | .inst id =>
    -- Public check also accepts constructed Func values; do not borrow an origin
    -- from a different definition sharing this ID before canonicalization.
    let definitions := insts.filter (·.id == id)
    if definitions.size != 1 then none
    let i ← definitions[0]?
    let sourceTy (p : Val) : Option TyId := do
      let pty ← aliasValueTy? insts p
      (globalAliasPointer? f pty).map (·.2)
    match i.op with
    | .block _ =>
      let branches := insts.filterMap fun j => match j.op with
        | .br target value => if target == id then some value else none
        | _ => none
      if branches.size != 1 then none else
        let value ← branches[0]?
        fixedGlobalOrigin? f insts value (fuel - 1)
    | .bitcast p | .wrapOptional p | .optPayload p | .optPayloadPtr _ p | .slicePtr p | .arrayToSlice p | .slice p _ =>
      fixedGlobalOrigin? f insts p (fuel - 1)
    | .fieldPtr p field =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      let child ← sourceTy p
      let base ← if (globalAliasPointerLayout f i.ty).hostSize != 0 then some 0
        else (f.layouts[child]?.getD {}).offsets[field]?
      some (g, off + base)
    | .fieldParentPtr p field =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      let (_, parent) ← globalAliasPointer? f i.ty
      let pty ← aliasValueTy? insts p
      let base ← if (globalAliasPointerLayout f pty).hostSize != 0 then some 0
        else (f.layouts[parent]?.getD {}).offsets[field]?
      if off < base then none else some (g, off - base)
    | .errCodePtr p | .errPayloadPtr _ p | .tryPtr p _ =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      let child ← sourceTy p
      let .errorUnion _ payload ← f.types[child]? | none
      let (size, align) ← (modelLayout f.types f.layouts payload).toOption
      let (code, base) := Zig.errUnionOffsets size align
      let delta := match i.op with | .errCodePtr _ => code | _ => base
      some (g, off + delta)
    | .ptrAdd sub p n =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      let .int _ k := n | none
      if k < 0 then none else
      let (_, child) ← globalAliasPointer? f i.ty
      let (size, _) ← (modelLayout f.types f.layouts child).toOption
      let delta := k.toNat * size
      if sub then if off < delta then none else some (g, off - delta)
      else some (g, off + delta)
    | .elemPtr p n =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      let .int _ k := n | none
      if k < 0 then none else
      let (_, child) ← globalAliasPointer? f i.ty
      let (size, _) ← (modelLayout f.types f.layouts child).toOption
      some (g, off + k.toNat * size)
    | _ => none
  | _ => none

/-- Exempt only the final fixed numeric capability; never discard its backing
provenance while traversing a derived pointer or a block/slice dependency. -/
private def immutableOrdinaryNumericValue (f : Func) (insts : Array Inst) (v : Val) : Bool :=
  ((do
    let pty ← aliasValueTy? insts v
    let (g, _) ← fixedGlobalOrigin? f insts v
    let global ← f.globals[g]?
    return immutableOrdinaryNumericAlias f global pty : Option Bool)).getD false

private def checkErrorGlobalInstruction (enabled : Bool) (f : Func) (insts : Array Inst) (i : Inst) : Except String Unit := do
  let reject : Except String Unit := throw s!"{f.name}: inst {i.id}: an escaping, arithmetic or unresolved pointer alias into an error-bearing global is outside the finite error-storage fragment"
  -- A numeric getter does not carry an interprocedural proof for recovering a
  -- symbolic parent. Enforce this also in callees with no local global table.
  if let .fieldParentPtr p _ := i.op then
    if let some (_, parent) := globalAliasPointer? f i.ty then
      let some parentCap := hasErrorCapability f.types parent
        | throw s!"{f.name}: inst {i.id}: parent recovery has unresolved or cyclic symbolic storage provenance"
      if parentCap then
        let source := ((aliasValueTy? insts p).bind (globalAliasPointer? f)).map (·.2)
        unless (source.bind (hasErrorCapability f.types)) == some true do
          throw s!"{f.name}: inst {i.id}: recovering an error-bearing parent from a numeric pointer needs unsupported interprocedural provenance"
  if !enabled then return
  if (globalAliasPointer? f i.ty).isSome && dependsOnErrorGlobal f insts (.inst i.id) then
    let some (g, off) := fixedGlobalOrigin? f insts (.inst i.id) | reject
    checkGlobalAliasAt f i.ty g off
  match i.op with
  | .bitcast p =>
    if (globalAliasPointer? f i.ty).isNone && ((aliasValueTy? insts p).bind (globalAliasPointer? f)).isSome && dependsOnErrorGlobal f insts p then reject
  | .ret v | .store _ v =>
    if ((aliasValueTy? insts v).map (fun t => carriesPointer f t)).getD false && dependsOnErrorGlobal f insts v && !immutableOrdinaryNumericValue f insts v then reject
  | .call _ args =>
    for v in args do
      if ((aliasValueTy? insts v).map (fun t => carriesPointer f t)).getD false && dependsOnErrorGlobal f insts v && !immutableOrdinaryNumericValue f insts v then reject
  | .memcpy dst src =>
    for v in #[dst, src] do
      if ((aliasValueTy? insts v).map (fun t => carriesPointer f t)).getD false && dependsOnErrorGlobal f insts v && !immutableOrdinaryNumericValue f insts v then reject
  | .memset p _ =>
    if dependsOnErrorGlobal f insts p then reject
  | .ptrElemVal p _ | .sliceElemVal p _ =>
    if dependsOnErrorGlobal f insts p && !immutableOrdinaryNumericValue f insts p then
      let some pty := aliasValueTy? insts p | reject
      let some item := itemTy f.types pty | reject
      let some (g, off) := fixedGlobalOrigin? f insts p | reject
      let some global := f.globals[g]? | reject
      unless hasErrorStorage f.types item && homogeneousGlobalItems f global.ty item off do reject
  | _ => pure ()

private def checkPointerPresence (v : Val) (message : String → String) : Except String Unit := do
  if let some k := v.ptrOther? then throw (message k)

/-- One pointer/global alignment policy, with caller-specific display context. -/
private def checkPointerConstant (f : Func) (v : Val) (missing : String → String)
    (alignment : Nat → Nat → String) : Except String Unit := do
  checkPointerPresence v missing
  checkGlobalAliasConstants f v
  if let .ptrConst pty g _ := v then
    let pa := (f.layouts[pty]?.bind (·.ptrAlign)).getD 1
    let ga := (f.globals[g]?.bind (f.layouts[·.ty]?)).bind (·.align) |>.getD 1
    if pa > ga then throw (alignment pa ga)

/-- A global that a pointer constant points into: a `var` or `const` with its initial value, in a
type that the model encodes. An array with a sentinel is encoded with the sentinel. -/
def checkGlobal (f : Func) (g : Global) : Except String Unit := do
  let what := g.name.getD "an unnamed constant"
  if g.threadlocal then throw s!"{f.name}: global {what}: `threadlocal` is outside the subset"
  if g.isExtern then throw s!"{f.name}: global {what}: `extern` is outside the subset"
  let some init := g.init
    | throw s!"{f.name}: global {what}: the AIR file has no initial value"
  checkNullConstants f.name f.types f.layouts init
  checkGlobalAliasConstants f init
  if f.globals.any (fun g => hasErrorStorage f.types g.ty) &&
      ((init.constTy?).map (fun t => carriesPointer f t)).getD false &&
      dependsOnErrorGlobal f f.allInsts init then
    throw s!"{f.name}: a global initializer cannot retain a pointer into an error-bearing global"
  checkPointerPresence init fun k =>
    s!"{f.name}: global {what}: a pointer constant without a global ({k}) is outside the subset"
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
    | .block b | .loop b | .«try» _ b | .tryPtr _ b => recur b
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
  let errorGlobals := f.globals.any (fun g => hasErrorStorage f.types g.ty)
  let escaping := escapingAllocs f
  let localRoots := placeRoots insts
  let places := localRoots.filterMap fun (p, r) => if escaping.contains r then none else some p
  -- An escaping local is a stack block: its type must be one the model encodes.
  for i in insts do
    if let .alloc := i.op then
      if escaping.contains i.id then
        if let some c := ptrChild f.types i.ty then
          checkMemTy f.name f.types f.layouts 0 c
  for g in f.globals do
    checkGlobal f g
  let mut checkedConstTypes : Std.HashSet TyId := {}
  for i in insts do
    checkErrorGlobalInstruction errorGlobals f insts i
    for v in valueOperands i.op ++ ptrOperands i.op do
      if let some vty := v.constTy? then
        unless checkedConstTypes.contains vty do
          checkTy f.name f.types f.layouts 0 vty
          checkedConstTypes := checkedConstTypes.insert vty
      checkNullConstants f.name f.types f.layouts v
      checkPointerConstant f v
        (fun k => s!"{f.name}: a pointer constant without a global ({k}) is outside the subset")
        (fun pa ga => s!"{f.name}: a pointer with `align({pa})` to a global of alignment {ga} is \
          outside the subset")
  -- Public `check` accepts unnormalized input: duplicate IDs disable the cache,
  -- without introducing a prepass diagnostic or changing subsequent check order.
  let tryErrorExits := if insts.any (fun i => match i.op with | .tryPtr .. => true | _ => false) then
      (controlFlowSummaries f.body).tryErrorExits
    else ({} : Std.HashMap InstId Bool)
  let cx : CheckCtx := { fnName := f.name, types := f.types, layouts := f.layouts,
                         instTys := insts.map fun i => (i.id, i.ty), places, tryErrorExits,
                         localRoots, localPaths := localPlacePaths f.types f.layouts insts,
                         zigVersion := f.zigVersion }
  checkDispatchScopes cx f.body
  let _ ← checkInsts cx 0 f.body
  pure ()

/-- First-occurrence instruction types and literal IDs for one function. Building this
index does not hide duplicate-ID errors: structural validation still scans in source order. -/
structure OperandTypes where
  insts : Array Inst
  instructions : Std.HashMap InstId TyId
  boolId : Option TyId
  voidId : Option TyId
  deriving Inhabited

def Func.operandTypes (f : Func) : OperandTypes := Id.run do
  let insts := f.allInsts
  let index := ModelRegistry.valueTypeIndex f.types insts
  return {
    insts
    instructions := index.instructions
    boolId := index.boolType
    voidId := index.voidType
  }

/-- A normalized operand's type, using a function's precomputed index. -/
def OperandTypes.valTy? (index : OperandTypes) (v : Val) : Option TyId :=
  match v with
  | .inst id => index.instructions[id]?
  | .bool _ => index.boolId
  | .void => index.voidId
  | v => v.constTy?

/-- A normalized operand's type. Bool/void literals carry no file-local ID. -/
def Func.valTy? (f : Func) (v : Val) : Option TyId := f.operandTypes.valTy? v

private def OperandTypes.calleeFnTy? (index : OperandTypes) (f : Func) (id : InstId) : Option String := do
  let ty ← index.instructions[id]?
  let .ptr _ _ child ← f.types[ty]? | none
  let childTy ← f.types[child]?
  unless isFnTy childTy do none
  let .other name := childTy | none
  pure name

/-- Exact argument type agreement between independent local type tables. -/
def valueCompatible (f target : Func) (v : Val) (expected : TyId)
    (index : OperandTypes := f.operandTypes) : Bool :=
  match v with
  | .bool _ => target.types[expected]? == some .bool
  | .void => target.types[expected]? == some .void
  | v => ((index.valTy? v).map fun t => compatibleType f target t expected).getD false

/-- The same known local ID needs no structural comparison. Only callers which already
validated the local table use this helper; constant form/range/payload checks remain separate. -/
private def localTypeCompatible (f : Func) (x y : TyId) : Bool :=
  if x == y then f.types[x]?.isSome else compatibleType f f x y

private def localValueCompatible (f : Func) (index : OperandTypes) (v : Val) (expected : TyId) : Bool :=
  match v with
  | .bool _ => f.types[expected]? == some .bool
  | .void => f.types[expected]? == some .void
  | v => ((index.valTy? v).map fun t => localTypeCompatible f t expected).getD false

private def checkCallSignatureWith (f target : Func) (i : Inst) (args : Array Val)
    (index : OperandTypes) (sameType : TyId → TyId → Bool) : Except String Unit := do
  unless args.size == target.params.size do
    throw s!"{f.name}: inst {i.id}: callee '{target.name}' has {args.size} arguments, expected {target.params.size}"
  unless sameType i.ty target.ret do
    throw s!"{f.name}: inst {i.id}: callee '{target.name}' has an incompatible result type ({i.ty} versus {target.ret})"
  for (arg, k) in args.zipIdx do
    if let .func .. := arg then
      throw s!"{f.name}: inst {i.id}: callee '{target.name}' argument {k}: function values lack a structured signature in this AIR schema"
    let agrees : Bool := match arg with
      | .bool _ => target.types[target.params[k]!]? == some .bool
      | .void => target.types[target.params[k]!]? == some .void
      | v => ((index.valTy? v).map fun t => sameType t target.params[k]!).getD false
    unless agrees do
      throw s!"{f.name}: inst {i.id}: callee '{target.name}' has an incompatible argument {k} type (expected local type {target.params[k]!})"

/-- Validate a direct call (or one possible indirect target) against its exported signature. -/
def checkCallSignature (f target : Func) (i : Inst) (args : Array Val)
    (index : OperandTypes := f.operandTypes) : Except String Unit :=
  checkCallSignatureWith f target i args index (compatibleType f target)

private abbrev SignaturePairs := Std.HashSet ((Nat × Nat) × (TyId × TyId))

/-- Cache structural equality only for an exact ordered function-table/type-ID pair.
Every call still checks its arity, operand types/forms and diagnostic context; only an
entirely successful signature check publishes new pairs. Untyped bool/void literals do
not establish a local type/layout pair and therefore never add one. -/
private def checkCallSignatureCached (f target : Func) (sourceIndex targetIndex : Nat)
    (i : Inst) (args : Array Val) (index : OperandTypes) (completed : SignaturePairs) :
    Except String SignaturePairs := do
  let key (x y : TyId) := ((sourceIndex, targetIndex), (x, y))
  let sameType (x y : TyId) := completed.contains (key x y) || compatibleType f target x y
  checkCallSignatureWith f target i args index sameType
  let mut completed := completed.insert (key i.ty target.ret)
  for (arg, k) in args.zipIdx do
    match arg with
    | .bool _ | .void => pure ()
    | _ =>
      if let some ty := index.valTy? arg then
        completed := completed.insert (key ty target.params[k]!)
  return completed

/-- Constant forms and nested payloads remain typed for direct normalized API clients too. -/
private partial def checkConstant (f : Func) (index : OperandTypes) (expected : TyId) (v : Val)
    (depth : Nat := 0) : Except String Unit := do
  if depth ≥ 256 then throw s!"{f.name}: constant traversal exceeds 256 levels"
  let fail : Except String Unit := throw s!"{f.name}: constant has an incompatible type or value form (type {expected})"
  unless localValueCompatible f index v expected do fail
  let some t := f.types[expected]? | fail
  let recur (ty : TyId) (v : Val) := checkConstant f index ty v (depth + 1)
  match v, t with
  | .undef _, _ => pure ()
  | .int _ n, .int signed bits =>
    unless integerFits signed bits n do throw s!"{f.name}: integer constant does not fit type {expected}"
  | .int _ n, .struct _ "packed" _ =>
    let some bits := packedBits f.types expected | fail
    if bits > 65535 then throw s!"{f.name}: packed integer width exceeds 65535 bits"
    unless integerFits false bits n do throw s!"{f.name}: packed integer constant does not fit type {expected}"
  | .float _ n, .float bits =>
    unless supportedFloatWidth bits do fail
    unless n < 2 ^ bits do throw s!"{f.name}: float bit pattern does not fit type {expected}"
  | .err _ name, .errorSet names =>
    if let some names := names then
      unless names.contains name do throw s!"{f.name}: error '{name}' is not in its error set"
  | .errUnionErr _ name, .errorUnion set _ =>
    let some (.errorSet names) := f.types[set]? | fail
    if let some names := names then
      unless names.contains name do throw s!"{f.name}: error '{name}' is not in its error set"
  | .enumTag _ n, .enum name tag exhaustive fields =>
    let some (.int signed bits) := f.types[tag]? | fail
    unless integerFits signed bits n do throw s!"{f.name}: enum constant '{name}' does not fit its tag type"
    if exhaustive && !fields.any (·.2 == n) then
      throw s!"{f.name}: enum constant '{name}' has no field with tag {n}"
  | .ptrNull _, .ptr .. =>
    unless nullablePtrTy f.types f.layouts expected do fail
  | .bool _, .bool | .void, .void | .optNull _, .optional _ => pure ()
  | .ptrConst .., .ptr "one" .. | .ptrConst .., .ptr "many" ..
  | .ptrConst .., .ptr "c" .. => checkGlobalAliasConstants f v
  | .ptrOther .., .ptr .. => pure ()
  | .optSome _ payload, .optional child => recur child payload
  | .errUnionOk _ payload, .errorUnion _ child => recur child payload
  | .unionVal _ field payload, .union _ _ _ fields =>
    let some (_, ty) := fields[field]? | fail
    recur ty payload
  | .agg _ elems, .array n child sentinel =>
    unless elems.size == n + (if sentinel then 1 else 0) do fail
    elems.forM (recur child)
  | .agg _ elems, .vector n child =>
    unless elems.size == n do fail
    elems.forM (recur child)
  | .agg _ elems, .struct _ _ fields =>
    unless elems.size == fields.size do fail
    for (v, k) in elems.zipIdx do recur fields[k]!.2 v
  | .agg _ elems, .tuple fields =>
    unless elems.size == fields.size do fail
    for (v, k) in elems.zipIdx do recur fields[k]! v
  | .sliceConst _ p n, .ptr "slice" _ child =>
    let some pty := p.constTy? | fail
    let some (.ptr "many" _ item) := f.types[pty]? | fail
    unless localTypeCompatible f child item do fail
    let some nty := n.constTy? | fail
    unless f.types[nty]? == some (.int false 64) do fail
    recur pty p
    recur nty n
  | _, _ => fail

/-- Check normalized signature/instruction/global references also for direct API clients.
Raw canonicalization additionally checks lexical SSA scope and enclosing branch targets. -/
private def checkFunctionStructure (f : Func) (index : OperandTypes) : Except String Unit := do
  validateTypeGraph f.name f.types
  unless f.layouts.size == f.types.size do
    throw s!"{f.name}: layout table has {f.layouts.size} entries, expected {f.types.size}"
  for t in f.params ++ #[f.ret] do
    unless t < f.types.size do throw s!"{f.name}: signature has unknown type id {t}"
  let insts := index.insts
  let mut ids : Std.HashSet InstId := {}
  for i in insts do
    if ids.contains i.id then throw s!"{f.name}: duplicate instruction id {i.id}"
    ids := ids.insert i.id
    unless i.ty < f.types.size do throw s!"{f.name}: inst {i.id}: unknown type id {i.ty}"
  let value (root : Val) (checkForm : Bool := true) : Except String Unit := do
    if let some t := root.constTy? then
      unless t < f.types.size do throw s!"{f.name}: constant has unknown type id {t}"
      if checkForm then checkConstant f index t root
    let mut todo : List (Val × Nat) := [(root, 0)]
    while !todo.isEmpty do
      let (v, depth) := todo.head!
      todo := todo.tail!
      if depth ≥ 256 then throw s!"{f.name}: constant traversal exceeds 256 levels"
      if let some t := v.constTy? then
        unless t < f.types.size do throw s!"{f.name}: constant has unknown type id {t}"
      match v with
      | .inst id => unless ids.contains id do throw s!"{f.name}: unknown instruction ref {id}"
      | .ptrConst _ g _ =>
        unless g < f.globals.size do throw s!"{f.name}: pointer has unknown global id {g}"
      | .agg _ vs => todo := (vs.toList.map fun v => (v, depth + 1)) ++ todo
      | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => todo := (v, depth + 1) :: todo
      | .sliceConst _ p n => todo := (p, depth + 1) :: (n, depth + 1) :: todo
      | _ => pure ()
  for g in f.globals do
    unless g.ty < f.types.size do throw s!"{f.name}: global has unknown type id {g.ty}"
    unless g.name.isSome || g.isConst do
      throw s!"{f.name}: unnamed mutable global is ambiguous (only unnamed constants are shared)"
    let some v := g.init | throw s!"{f.name}: global has no initial value"
    value v false
    if let .func name .. := v then
      unless g.name == some name && g.isConst && (f.types[g.ty]?.map isFnTy).getD false do
        throw s!"{f.name}: global function initializer must be its named constant function block"
    else checkConstant f index g.ty v
  for i in insts do
    let extra := match i.op with
      | .sliceFieldPtr _ p => #[p]
      | .dbg _ v => v.toArray
      | .asm _ _ _ outputs _ => outputs.flatMap fun o => o.ref.toArray
      | _ => #[]
    for v in valueOperands i.op ++ ptrOperands i.op ++ extra do value v
    match i.op with
    | .arg k =>
      let some p := f.params[k]? | throw s!"{f.name}: inst {i.id}: unknown parameter {k}"
      unless localTypeCompatible f i.ty p do
        throw s!"{f.name}: inst {i.id}: argument instruction has an incompatible parameter {k} type"
    | .ret v =>
      unless localValueCompatible f index v f.ret do
        throw s!"{f.name}: inst {i.id}: return value has an incompatible result type"
    | .retLoad ptr =>
      let some pty := index.valTy? ptr
        | throw s!"{f.name}: inst {i.id}: loaded return has no pointer type"
      let some (.ptr size _ child) := f.types[pty]?
        | throw s!"{f.name}: inst {i.id}: loaded return operand is not a pointer"
      unless size == "one" || size == "many" || size == "c" do
        throw s!"{f.name}: inst {i.id}: loaded return operand is not a loadable pointer"
      unless localTypeCompatible f child f.ret do
        throw s!"{f.name}: inst {i.id}: loaded return has an incompatible result type"
    | _ => pure ()

/-- The type graph reachable from emitted signatures, instructions, constants and globals.
Recognized model types have no implementation children in the normalized IR. -/
private def typeClosure (types : Array Ty) (roots : List TyId) (seen : Std.HashSet TyId) :
    Std.HashSet TyId := Id.run do
  let mut seen := seen
  let mut todo := roots
  while !todo.isEmpty do
    let id := todo.head!
    todo := todo.tail!
    if seen.contains id then continue
    seen := seen.insert id
    todo := ((types[id]?.map childTys).getD #[]).toList ++ todo
  return seen

/-- Collect reachable IDs without validating them; unknown IDs remain in the result. Roots
stream through one shared closure algorithm. SSA references add no roots because every
instruction type is already covered. This pure collector is exposed for equivalence tests. -/
def programUsedTypes (f : Func) (index : OperandTypes := f.operandTypes) : Std.HashSet TyId := Id.run do
  let mut seen := typeClosure f.types (f.params ++ #[f.ret]).toList {}
  let scan (root : Val) (seen : Std.HashSet TyId) : Std.HashSet TyId := Id.run do
    let mut seen := seen
    let mut values : List Val := [root]
    while !values.isEmpty do
      let v := values.head!
      values := values.tail!
      if let some ty := v.constTy? then seen := typeClosure f.types [ty] seen
      match v with
      | .agg _ vs => values := vs.toList ++ values
      | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => values := v :: values
      | .sliceConst _ p n => values := p :: n :: values
      | _ => pure ()
    return seen
  for i in index.insts do
    seen := typeClosure f.types [i.ty] seen
    for v in valueOperands i.op ++ ptrOperands i.op do
      if let .inst _ := v then continue
      seen := scan v seen
  for g in f.globals do
    seen := typeClosure f.types [g.ty] seen
    if let some v := g.init then seen := scan v seen
  return seen

/-- Definitions which emission shares by name must agree across every file. -/
private def checkSharedDefinitions (funcs : Array Func) : Except String (Array OperandTypes) := do
  let mut functions : Std.HashSet String := {}
  let mut indexes : Array OperandTypes := #[]
  for f in funcs do
    if functions.contains f.name then throw s!"duplicate function name '{f.name}'"
    functions := functions.insert f.name
    let index := f.operandTypes
    checkFunctionStructure f index
    indexes := indexes.push index
  let mut globals : Std.HashMap String (Nat × Nat) := {}
  let mut globalComparisons : Std.HashMap (Nat × Nat) (Std.HashSet (Nat × Nat)) := {}
  let mut namedTypes : Std.HashMap String (Func × TyId) := {}
  for (f, fileIndex) in funcs.zipIdx do
    for (g, k) in f.globals.zipIdx do
      if let some n := g.name then
        if functions.contains n then
          unless (match g.init with | some (.func nm ..) => nm == n | _ => false) do
            throw s!"{f.name}: global '{n}' collides with a function name"
        if let some (previousIndex, id) := globals[n]? then
          let some previous := funcs[previousIndex]?
            | throw s!"{f.name}: shared global '{n}' refers to unknown function table {previousIndex}"
          let key := (fileIndex, previousIndex)
          let completed : Std.HashSet (Nat × Nat) := globalComparisons[key]?.getD {}
          globalComparisons := globalComparisons.erase key
          let some completed := compatibleGlobalCached f previous k id completed
            | throw s!"{f.name}: inconsistent shared global '{n}' (previous definition in '{previous.name}')"
          globalComparisons := globalComparisons.insert key completed
        else globals := globals.insert n (fileIndex, k)
    let used := programUsedTypes f indexes[fileIndex]!
    for (t, k) in f.types.zipIdx do
      unless used.contains k do continue
      let name := match t with
        | .struct n .. | .enum n .. | .union n .. => some n
        | _ => none
      if let some n := name then
        if let some (previous, id) := namedTypes[n]? then
          unless compatibleType f previous k id do
            throw s!"{f.name}: inconsistent shared type '{n}' (previous definition in '{previous.name}')"
        else namedTypes := namedTypes.insert n (f, k)
  return indexes

/-- A call to the allocator model (`ZigLean/Mem/Alloc.lean`): the pointers and slices in its
arguments and result have a known item size and `ptr_align`, and a slice that it remaps has no
sentinel. -/
def checkAllocCall (f : Func) (fn : AllocFn) (args : Array Val) (ret : TyId)
    (index : OperandTypes := f.operandTypes) : Except String Unit := do
  let tyOf := index.valTy?
  -- `args[1]` is a pointer or slice, except the item count of `alloc`.
  let argPtr := if fn == .alloc || fn == .alignedAlloc || fn == .allocSentinel then #[] else (args.extract 1 2).filterMap tyOf
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

/-- Compare argument types across per-function type tables. Pointer values keep their
identity; the source alignment must satisfy the target and mutable pointers may become
const. Other implicit `@call` coercions require an explicit source cast before capture. -/
private abbrev SpawnTyCache := Std.HashMap (TyId × TyId × Bool) Bool

/-- Completed pairs are shared across sibling fields. Cycle assumptions remain
local to the current recursion path and are never inserted as completed checks. -/
private partial def sameSpawnTyCached (source target : Func) (a b : TyId)
    (seen : Array (TyId × TyId × Bool)) (allowPtrCoercion : Bool) :
    StateM SpawnTyCache Bool := do
  let key := (a, b, allowPtrCoercion)
  if seen.contains key then return true
  if let some result := (← get)[key]? then return result
  let recur := fun x y => sameSpawnTyCached source target x y (seen.push key) false
  let fields := fun (xs ys : Array (String × TyId)) => do
    if xs.size != ys.size then return false
    for (x, y) in xs.zip ys do
      if x.1 != y.1 then return false
      unless ← recur x.2 y.2 do return false
    return true
  let result ← match source.types[a]?, target.types[b]? with
    | some (.ptr sz c x), some (.ptr tz d y) => do
      let sl := source.layouts[a]?.getD {}
      let tl := target.layouts[b]?.getD {}
      if !(sz == tz && (if allowPtrCoercion then !c || d else c == d) &&
          (if allowPtrCoercion then decide (sl.ptrAlign.getD 1 ≥ tl.ptrAlign.getD 1)
           else sl.ptrAlign == tl.ptrAlign) &&
          sl.sentinel == tl.sentinel && sl.sameKnownSentinel tl &&
          sl.isVolatile == tl.isVolatile &&
          sl.hostSize == tl.hostSize && sl.bitOffset == tl.bitOffset) then return false
      recur x y
    | some (.array n x s), some (.array m y t) =>
      if n == m && s == t then recur x y else pure false
    | some (.vector n x), some (.vector m y) => if n == m then recur x y else pure false
    | some (.optional x), some (.optional y) => recur x y
    | some (.errorUnion sx x), some (.errorUnion sy y) => do
      unless ← recur sx sy do return false
      recur x y
    | some (.struct n l xs), some (.struct m k ys) =>
      if n == m && l == k then fields xs ys else pure false
    | some (.enum n x e fs), some (.enum m y d gs) => do
      if !(n == m && e == d) then return false
      unless ← recur x y do return false
      pure (fs == gs)
    | some (.union n l tx xs), some (.union m k ty ys) => do
      if !(n == m && l == k) then return false
      unless ← fields xs ys do return false
      match tx, ty with
      | none, none => pure true
      | some x, some y => recur x y
      | _, _ => pure false
    | some (.tuple xs), some (.tuple ys) => do
      if xs.size != ys.size then return false
      for (x, y) in xs.zip ys do
        unless ← recur x y do return false
      return true
    | some x, some y => pure (x == y)
    | _, _ => pure false
  modify (·.insert key result)
  return result

partial def sameSpawnTy (source target : Func) (a b : TyId)
    (seen : Array (TyId × TyId × Bool) := #[]) (allowPtrCoercion : Bool := true) : Bool :=
  (sameSpawnTyCached source target a b seen allowPtrCoercion).run' {}

/-- Capture exactly the worker's runtime parameters. Zero fields are valid; every field
is copied as a value, including pointer identity. Ownership remains an explicit proof
obligation on the captured target, not an automatic exclusive transfer. -/
def checkThreadSpawn (f : Func) (worker : Func) (callee : String) (k : Nat) (args : Array Val)
    (operandIndex : OperandTypes := f.operandTypes) : Except String Unit := do
  unless args.size == k + 1 do
    throw s!"{f.name}: {callee} has {args.size} runtime arguments, expected {k + 1}"
  let tyOf := operandIndex.valTy?
  let some argsTy := args[k]?.bind tyOf
    | throw s!"{f.name}: a call to {callee} has no args-tuple type"
  let some (.tuple fields) := f.types[argsTy]?
    | throw s!"{f.name}: {callee}'s args argument is not a tuple"
  unless fields.size == worker.params.size do
    throw s!"{f.name}: {callee}'s args tuple has {fields.size} fields, but worker '{worker.name}' has {worker.params.size} runtime parameters"
  let mut completed : SpawnTyCache := {}
  for index in [:fields.size] do
    let (compatible, cache) := (sameSpawnTyCached f worker fields[index]! worker.params[index]! #[] true).run completed
    completed := cache
    unless compatible do
      throw s!"{f.name}: {callee} argument {index} does not match worker '{worker.name}' parameter {index}; capture the exact runtime parameter type with an explicit cast"
  let validRet := match worker.types[worker.ret]? with
    | some .void | some .noreturn => true
    | some (.int false 8) => callee == "Thread.spawn"
    | _ => false
  unless validRet do
    throw s!"{f.name}: {callee} worker '{worker.name}' has an unsupported result; supported workers return void or noreturn, and Thread.spawn also accepts u8; error-return handling is outside the model"

/-- Progress model boundaries must preserve the source result shape and error outcome. -/
def checkProgressCall (f : Func) (callee : String) (fn : ThreadFn) (args : Array Val)
    (ret : TyId) : Except String Unit := do
  unless args.isEmpty do
    throw s!"{f.name}: a call to '{callee}' with {args.size} arguments, not 0"
  match fn with
  | .yield =>
    let some (.errorUnion errors payload) := f.types[ret]?
      | throw s!"{f.name}: Thread.yield must return an error union with void payload"
    unless f.types[payload]? == some .void do
      throw s!"{f.name}: Thread.yield must return an error union with void payload"
    match f.types[errors]? with
    | some (.errorSet none) => pure ()
    | some (.errorSet (some names)) =>
      unless names.contains "SystemCannotYield" do
        throw s!"{f.name}: Thread.yield result must include error.SystemCannotYield"
    | _ => throw s!"{f.name}: Thread.yield result must have an error set"
  | .spinLoopHint =>
    unless f.types[ret]? == some .void do
      throw s!"{f.name}: '{callee}' must return void"
  | _ => pure ()

/-- Recognized model names still require the runtime signature the emitter applies.
Comptime-only arguments are absent from AIR; worker arguments are checked separately. -/
def checkModelSignature (f : Func) (callee : String) (args : Array Val) (ret : TyId)
    (index : OperandTypes := f.operandTypes) : Except String Unit := do
  let argTy (k : Nat) := args[k]?.bind index.valTy? |>.bind (f.types[·]?)
  let result := f.types[ret]?
  let fail (what : String) : Except String Unit :=
    throw s!"{f.name}: model callee '{callee}' has an incompatible {what} signature"
  let count (n : Nat) := if args.size == n then pure () else fail s!"argument count ({args.size}, expected {n})"
  let require (ok : Bool) (what : String) := if ok then pure () else fail what
  let isPtr (size : String) (t : Option Ty) := match t with
    | some (.ptr s ..) => s == size | _ => false
  let isSize (t : Option Ty) := t == some (.int false 64)
  let isCode (t : Option Ty) := t == some (.int false 32)
  let errorPayload := match result with
    | some (.errorUnion s p) =>
      if (match f.types[s]? with | some (.errorSet _) => true | _ => false) then f.types[p]? else none
    | _ => none
  let optionalPayload := match result with | some (.optional p) => f.types[p]? | _ => none
  let pointer (k : Nat) := isPtr "one" (argTy k)
  let receiver (k : Nat) (name : String) := match argTy k with
    | some (.ptr "one" false c) => match f.types[c]? with
      | some (.struct n ..) => n == name
      | _ => false
    | _ => false
  let unit := result == some .void
  let errorUnit := errorPayload == some .void
  let checkFutex (ptrIndex valueIndex : Nat) (sameValue : Bool := true) : Except String Unit := do
    require (pointer ptrIndex) "pointer argument"
    let some v := args[valueIndex]?.bind index.valTy? | fail "value argument"
    require (packedBits f.types v == some 32) "32-bit futex value"
    let some p := args[ptrIndex]?.bind index.valTy? | fail "pointer argument"
    let some c := ptrChild f.types p | fail "pointer argument"
    let child := match f.types[c]? with
      | some (.struct _ _ fields) => if fields.size == 1 then fields[0]!.2 else c
      | _ => c
    require (packedBits f.types child == some 32) "32-bit futex pointee"
    if sameValue then require (compatibleType f f child v) "futex pointee/value"
  if let some model := stdModel? callee then
    unless model.qualifies f.zigVersion do
      fail s!"{model.symbol} qualified Zig {", ".intercalate model.zigVersions.toList}"
  if let some fn := allocFn? callee then
    count (if fn == .create then 1 else if fn == .remap then 3 else 2)
    require (argTy 0 == some .allocator) "allocator argument"
    if fn == .create || fn == .alloc || fn == .alignedAlloc || fn == .allocSentinel || fn == .dupe then
      let hasOutOfMemory := match result with
        | some (.errorUnion set _) => match f.types[set]? with
          | some (.errorSet none) => true
          | some (.errorSet (some names)) => names.contains "OutOfMemory"
          | _ => false
        | _ => false
      require hasOutOfMemory "error set admitting OutOfMemory"
    match fn with
    | .create => require (isPtr "one" errorPayload) "error-union pointer result"
    | .alloc | .alignedAlloc | .allocSentinel =>
      require (isSize (argTy 1)) "item-count argument"
      require (isPtr "slice" errorPayload) "error-union slice result"
    | .dupe =>
      require (isPtr "slice" (argTy 1)) "source slice argument"
      require (isPtr "slice" errorPayload) "error-union slice result"
    | .destroy => require (pointer 1 && unit) "pointer/void"
    | .free => require (isPtr "slice" (argTy 1) && unit) "slice/void"
    | .remap =>
      require (isPtr "slice" (argTy 1) && isSize (argTy 2)) "slice/item-count arguments"
      require (isPtr "slice" optionalPayload) "optional slice result"
    if fn == .dupe || fn == .remap then
      let some source := args[1]?.bind index.valTy? | fail "source slice argument"
      let some srcChild := ptrChild f.types source | fail "source slice argument"
      let payload := match result with | some (.errorUnion _ p) | some (.optional p) => some p | _ => none
      let some dstChild := payload.bind (ptrChild f.types) | fail "slice result"
      require (compatibleType f f srcChild dstChild) "slice item type"
    if fn == .allocSentinel then
      let some (.errorUnion _ p) := result | fail "error-union slice result"
      let some (.ptr "slice" false child) := f.types[p]?
        | fail "mutable byte sentinel slice result"
      require (f.types[child]? == some (.int false 8)) "allocSentinel supports only u8"
      let l := f.layouts[p]?.getD {}
      require (l.sentinel && l.ptrAlign == some 1) "byte sentinel slice with alignment 1"
      require (l.hostSize == 0 && l.bitOffset == 0) "ordinary byte sentinel pointer without packed metadata"
      let some sentinel := l.sentinelByte | fail "explicit exported sentinel_byte"
      require (decide (sentinel < 256)) "sentinel_byte in 0..255"
    checkAllocCall f fn args ret index
  else if let some fn := threadFn? callee then
    match fn with
    | .spawn =>
      count 2
      require (errorPayload == some .thread) "error-union Thread result"
      require (match argTy 0 with | some (.struct "Thread.SpawnConfig" ..) => true | _ => false) "spawn configuration"
    | .join => count 1; require (argTy 0 == some .thread && unit) "Thread/void"
    | .yield | .spinLoopHint => checkProgressCall f callee fn args ret
    | .groupAsync | .groupConcurrent =>
      count 3
      require (receiver 0 "Io.Group" && argTy 1 == some .io) "Group/Io arguments"
      require (if fn == .groupAsync then unit else errorUnit) "result"
    | .groupAwait | .groupCancel =>
      count 2
      require (receiver 0 "Io.Group" && argTy 1 == some .io) "Group/Io arguments"
      require (if fn == .groupAwait then errorUnit else unit) "result"
    | .futexWait | .futexWaitU | .futexWake =>
      count 3
      require (argTy 0 == some .io) "Io argument"
      checkFutex 1 2 (fn != .futexWake)
      if fn == .futexWake then require (isCode (argTy 2)) "wake-count argument"
      require (if fn == .futexWait then errorUnit else unit) "result"
    | .threadFutexWait | .threadFutexWake =>
      count 2
      checkFutex 0 1 (fn != .threadFutexWake)
      require (isCode (argTy 1) && unit) "u32/void"
    | .osLock | .osUnlock | .osTryLock =>
      count 1
      require (receiver 0 "Thread.Mutex.DarwinImpl") "lock pointer argument"
      require (if fn == .osTryLock then result == some .bool else unit) "result"
    | .timerStart =>
      count 0
      require (match errorPayload with | some (.struct "time.Timer" ..) => true | _ => false) "Timer result"
    | .timerRead =>
      count 1
      require (receiver 0 "time.Timer" && isSize result) "Timer pointer/u64"
    | .futexTimedWait =>
      count 3
      checkFutex 0 1
      require (isSize (argTy 2) && errorUnit) "timeout/error-union void"

/-- Explicit environment policy for translated thread assignment. The default retains
existing proofs under an availability assumption; fallible includes API failure. -/
inductive SpawnSemantics where
  | available
  | fallible
  deriving DecidableEq, Repr, Inhabited

/-- The fallible boundary accepts only the audited std versions and a constant
SpawnConfig requesting 1 MiB or the default 16 MiB and a null custom allocator. Other sizes, runtime configs
and allocator-specific semantics remain outside this model. -/
def checkFallibleSpawnCalls (funcs : Array Func) : Except String Unit := do
  for f in funcs do
    for i in f.allInsts do
      if let .call (.func name _ _) args := i.op then
        if let some kind := threadFn? name then
          if kind.spawnArgs?.isSome then
            unless #["0.14.1", "0.15.2", "0.16.0"].contains f.zigVersion do
              throw s!"{f.name}: fallible spawn requires an audited Zig version"
            if kind == .spawn then
              let some (Val.agg ty fields) := (args[0]? : Option Val)
                | throw s!"{f.name}: fallible Thread.spawn requires a constant SpawnConfig"
              let some (.struct "Thread.SpawnConfig" _ names) := f.types[ty]?
                | throw s!"{f.name}: fallible Thread.spawn requires Thread.SpawnConfig"
              unless names.size == 2 && names[0]!.1 == "stack_size" && names[1]!.1 == "allocator" do
                throw s!"{f.name}: fallible Thread.spawn has an unaudited SpawnConfig layout"
              unless fields.size == 2 do
                throw s!"{f.name}: fallible Thread.spawn has an incomplete SpawnConfig"
              let .int _ stack := fields[0]!
                | throw s!"{f.name}: fallible Thread.spawn requires a constant stack_size"
              unless stack == 1048576 || stack == 16777216 do
                throw s!"{f.name}: fallible Thread.spawn supports only audited 1 MiB or default 16 MiB stack_size requests"
              let .optNull _ := fields[1]!
                | throw s!"{f.name}: fallible Thread.spawn custom allocators are outside the model"
            else
              unless f.zigVersion == "0.16.0" do
                throw s!"{f.name}: fallible Io.Group requires Zig 0.16.0"

/-- Preserve reference traversal order within each exact function-type bucket. -/
private def referenceTargets (refs : Array (String × String)) : Std.HashMap String (Array String) := Id.run do
  let mut targetLists : Std.HashMap String (List String) := {}
  for (typ, callee) in refs do
    targetLists := targetLists.insert typ (callee :: targetLists.getD typ [])
  return targetLists.fold (fun buckets typ names => buckets.insert typ names.reverse.toArray)
    ({} : Std.HashMap String (Array String))

/-- Shared CLI/project policy spelling. The policy selects a supported model, not
an assertion that the host can create a thread. -/
def parseSpawnPolicy (value : String) : Except String SpawnSemantics :=
  match value with
  | "available" => .ok .available
  | "fallible" => .ok .fallible
  | _ => .error "invalid --spawn-policy (expected available or fallible)"

/-- The checks that need every function. A function that uses memory reads a slice item from
memory, and a call to a pure function copies each `[]const T` argument from memory
(`Zig.readSlice`): `T` must be a type that the model encodes. Each callee is a translated
function or has a built-in std model (`stdModel?`, `Air2Lean/StdModels.lean`); a translated
function cannot reuse the qualified name of a built-in std model. -/
def checkProgram (funcs : Array Func) (models : Array ModelBinding := #[])
    (profile : Option BuildProfile := none)
    (selectedCallees : Array String := #[]) : Except String Unit := do
  unless models.isEmpty do
    let some profile := profile | throw "external model bindings require a checked program profile"
    ModelRegistry.check models profile funcs
  let modelSymbols := models.foldl (fun symbols m => symbols.insert m.symbol) ({} : Std.HashSet String)
  let indexes ← checkSharedDefinitions funcs
  let targets := referenceTargets (fnRefs funcs)
  let mem := memoryFunctions funcs (models.map (·.symbol) ++ selectedCallees)
  let mut functionNames : Std.HashMap String Nat := {}
  for (f, fileIndex) in funcs.zipIdx do
    if let some model := stdModel? f.name then
      throw s!"{f.name}: translated function conflicts with built-in std model '{model.symbol}' (narrow the example's `filter`, docs/std-models.md)"
    functionNames := functionNames.insert f.name fileIndex
  let lookupFunction (name : String) : Option (Nat × Func) := do
    let index ← functionNames[name]?
    let target ← funcs[index]?
    pure (index, target)
  let mut signatures : SignaturePairs := {}
  for ((f, index), fileIndex) in (funcs.zip indexes).zipIdx do
    for i in index.insts do
      if let .call (.inst p) args := i.op then
        let some tn := index.calleeFnTy? f p
          | throw s!"{f.name}: inst {i.id}: indirect callee is not a function pointer"
        for callee in targets.getD tn #[] do
          let some (targetIndex, target) := lookupFunction callee
            | throw s!"{f.name}: inst {i.id}: indirect target '{callee}' has no AIR file"
          signatures ← checkCallSignatureCached f target fileIndex targetIndex i args index signatures
      if let .call (.func callee noreturn _) _ := i.op then
        if let some fn := threadFn? callee then
          if fn == .yield || fn == .spinLoopHint then
            if noreturn then throw s!"{f.name}: progress hint '{callee}' cannot be noreturn"
      if let .call (.func callee false spawnFn) args := i.op then
        checkModelSignature f callee args i.ty index
        if !modelledStdFn callee then
          if let some (targetIndex, target) := lookupFunction callee then
            signatures ← checkCallSignatureCached f target fileIndex targetIndex i args index signatures
        if let some kind := threadFn? callee then
          if let some k := kind.spawnArgs? then
            let some worker := spawnFn
              | throw s!"{f.name}: a call to '{callee}' has no comptime_fn spawn target"
            let some (_, target) := lookupFunction worker
              | throw s!"{f.name}: the spawned callee '{worker}' has no AIR file (add its name to the filter, docs/std-models.md)"
            checkThreadSpawn f target (if kind == .spawn then "Thread.spawn" else "Io.Group.async")
              k args index
        unless functionNames.contains callee || modelSymbols.contains callee || selectedCallees.contains callee do
          if let some reason := rejectedThreadFn? callee then
            throw s!"{f.name}: the callee '{callee}' is outside the subset: {reason}"
          unless modelledStdFn callee do
            throw s!"{f.name}: the callee '{callee}' has no AIR file and no model (add its name to the example's `filter` file, docs/std-models.md)"
  for (f, index) in funcs.zip indexes do
    if mem.contains f.name then
      let insts := index.insts
      let tyOf := index.valTy?
      let sliceItem (v : Val) : Option TyId := match (tyOf v).bind (f.types[·]?) with
        | some (.ptr "slice" _ c) => some c
        | _ => none
      for i in insts do
        let items := match i.op with
          | .sliceElemVal s _ => (sliceItem s).toArray
          | .call (.func callee _ spawnFn) args =>
            if let some k := (threadFn? callee).bind (·.spawnArgs?) then
              if (spawnFn.map mem.contains).getD true then #[] else
              let fields : Array TyId := (((args[k]? : Option Val).bind tyOf).bind fun t =>
                match f.types[t]? with
                | some (.tuple fields) => some fields
                | _ => none).getD #[]
              fields.filterMap fun (t : TyId) => match f.types[t]? with
                | some (.ptr "slice" _ c) => some c | _ => none
            else if mem.contains callee then #[] else args.filterMap sliceItem
          | _ => #[]
        for c in items do
          checkMemTy f.name f.types f.layouts 0 c

/-! Collection reuses validators without constructing partial IR. Failed units retain
their first error, but cannot suppress independent siblings. -/

def diagnosticStructure (f : Func) : Except String Unit :=
  checkFunctionStructure f f.operandTypes

private def checkDiagnostic (file : String) (f : Func) (code : Diagnostics.Code)
    (anchor : Diagnostics.Anchor := {}) : Diagnostics.Diagnostic :=
  {
    code
    phase := .check
    category := .validationFailure
    message := ""
    file := some file
    function := some f.name
    anchor
    prerequisites := #["normalized_function_structure"] }

private partial def collectInstChecks (file : String) (f : Func) (cx : CheckCtx)
    (body : Array Inst) (line : Nat) (log : Diagnostics.Log) : Nat × Diagnostics.Log := Id.run do
  let mut log := log
  let mut line := line
  for i in body do
    let anchor : Diagnostics.Anchor := {
      idSpace := .canonical
      instruction := some i.id
      nearestDbgLine := if line == 0 then none else some line }
    let typeCheck := checkTy f.name f.types f.layouts line i.ty
    log := log.record (checkDiagnostic file f .typeFailure { anchor with typeId := some i.ty }) typeCheck
    if typeCheck.toOption.isNone then
      log := log.add { (Diagnostics.skipped file (some f.name) .check "instruction_result_type") with anchor }
    match i.op with
    | .block b | .loop b =>
      let result := collectInstChecks file f cx b line log
      line := result.1; log := result.2
    | .condBr _ t e =>
      log := (collectInstChecks file f cx t line log).2
      log := (collectInstChecks file f cx e line log).2
    | .switchBr _ cases e | .loopSwitchBr _ cases e =>
      for c in cases do log := (collectInstChecks file f cx c.body line log).2
      log := (collectInstChecks file f cx e line log).2
    | .«try» _ b | .tryPtr _ b => log := (collectInstChecks file f cx b line log).2
    | .line n => line := n
    | _ =>
      if typeCheck.toOption.isSome then
        log := log.record (checkDiagnostic file f .instructionFailure anchor) (checkOp cx line i.ty i.op)
  return (line, log)

structure FunctionChecks where
  index : OperandTypes
  structureValid : Bool
  log : Diagnostics.Log

/-- Return the actual structural result and index alongside collected diagnostics. -/
def collectFunctionChecksDetailed (file : String) (f : Func) (initial : Diagnostics.Log) : FunctionChecks := Id.run do
  let index := f.operandTypes
  let mut log := initial
  match checkFunctionStructure f index with
  | .error message =>
    log := log.add { (checkDiagnostic file f .structureFailure) with
      category := .malformedInput
      message
      firstErrorInUnit := true }
    return {
      index
      structureValid := false
      log := log.add (Diagnostics.skipped file (some f.name) .check "normalized_function_structure") }
  | .ok _ => pure ()
  for p in f.params ++ #[f.ret] do
    log := log.record (checkDiagnostic file f .typeFailure { idSpace := .canonical, typeId := some p })
      (checkTy f.name f.types f.layouts 0 p)
  for (t, id) in f.types.zipIdx do
    if let .union _ _ none _ := t then
      log := log.record (checkDiagnostic file f .memoryFailure { idSpace := .canonical, typeId := some id })
        (checkMemTy f.name f.types f.layouts 0 id)
  let insts := index.insts
  let errorGlobals := f.globals.any (fun g => hasErrorStorage f.types g.ty)
  let escaping := escapingAllocs f
  let localRoots := placeRoots insts
  let places := localRoots.filterMap fun (p, r) => if escaping.contains r then none else some p
  for i in insts do
    if let .alloc := i.op then
      if escaping.contains i.id then
        if let some c := ptrChild f.types i.ty then
          log := log.record (checkDiagnostic file f .memoryFailure
            { idSpace := .canonical, instruction := some i.id, typeId := some c })
            (checkMemTy f.name f.types f.layouts 0 c)
  for (g, id) in f.globals.zipIdx do
    log := log.record (checkDiagnostic file f .globalFailure { idSpace := .canonical, globalId := some id }) (checkGlobal f g)
  for i in insts do
    log := log.record (checkDiagnostic file f .constantFailure
      { idSpace := .canonical, instruction := some i.id }) (checkErrorGlobalInstruction errorGlobals f insts i)
    for v in valueOperands i.op ++ ptrOperands i.op do
      let result := do
        checkNullConstants f.name f.types f.layouts v
        checkPointerConstant f v
          (fun k => s!"{f.name}: a pointer constant without a global ({k}) is outside the subset")
          (fun pa ga => s!"{f.name}: a pointer with align({pa}) to a global of alignment {ga} is outside the subset")
      log := log.record (checkDiagnostic file f .constantFailure
        { idSpace := .canonical, instruction := some i.id }) result
  let cx : CheckCtx := {
    fnName := f.name
    types := f.types
    layouts := f.layouts
    instTys := insts.map fun i => (i.id, i.ty)
    places
    localRoots
    localPaths := localPlacePaths f.types f.layouts insts
    zigVersion := f.zigVersion }
  return { index, structureValid := true, log := (collectInstChecks file f cx f.body 0 log).2 }

/-- Compatibility wrapper for clients that need only diagnostics. -/
def collectFunctionChecks (file : String) (f : Func) (initial : Diagnostics.Log) : Diagnostics.Log :=
  (collectFunctionChecksDetailed file f initial).log

structure CallChecksSnapshot where
  references : Array (String × String)
  targets : Std.HashMap String (Option Func)
  /-- Builder-populated index; bare compatibility snapshots derive it once per collection. -/
  referenceBuckets : Option (Std.HashMap String (Array String)) := none

/-- Preserve function-reference order and record ambiguity in the safe subset. -/
def CallChecksSnapshot.build (funcs : Array Func) : CallChecksSnapshot := Id.run do
  let mut targets : Std.HashMap String (Option Func) := {}
  for f in funcs do
    targets := targets.insert f.name (if targets.contains f.name then none else some f)
  let references := fnRefs funcs
  return { references, targets, referenceBuckets := some (referenceTargets references) }

def CallChecksSnapshot.unique (snapshot : CallChecksSnapshot) (name : String) : Option Func :=
  snapshot.targets[name]?.join

/-- Calls are independent units; the original whole-program check additionally covers
shared definitions, indirect targets and memory propagation. -/
def collectCallChecksIndexed (file : String) (f : Func) (index : OperandTypes) (snapshot : CallChecksSnapshot)
    (initial : Diagnostics.Log) : Diagnostics.Log := Id.run do
  let mut log := initial
  let referenceBuckets := match snapshot.referenceBuckets with
    | some buckets => buckets
    | none => referenceTargets snapshot.references
  for i in index.insts do
    let diagnostic := { (checkDiagnostic file f .signatureFailure
      { idSpace := .canonical, instruction := some i.id }) with
      phase := .program }
    match i.op with
    | .call (.func callee false worker) args =>
      log := log.record { diagnostic with code := .modelFailure }
        (checkModelSignature f callee args i.ty index)
      if !modelledStdFn callee then
        if let some target := snapshot.unique callee then
          log := log.record diagnostic (checkCallSignature f target i args index)
      if let some kind := threadFn? callee then
        if let some k := kind.spawnArgs? then
          if let some target := worker.bind snapshot.unique then
            log := log.record diagnostic (checkThreadSpawn f target
              (if kind == .spawn then "Thread.spawn" else "Io.Group.async") k args index)
    | .call (.inst p) args =>
      match index.calleeFnTy? f p with
      | none => log := log.add { diagnostic with message := "indirect callee is not a function pointer" }
      | some name =>
        for callee in referenceBuckets.getD name #[] do
          if let some target := snapshot.unique callee then
            log := log.record diagnostic (checkCallSignature f target i args index)
    | _ => pure ()
  return log

/-- Compatibility wrapper; program collection builds and reuses one snapshot. -/
def collectCallChecks (file : String) (f : Func) (funcs : Array Func)
    (initial : Diagnostics.Log) : Diagnostics.Log :=
  collectCallChecksIndexed file f f.operandTypes (CallChecksSnapshot.build funcs) initial

end Air2Lean
