import Std.Data.HashMap
import Std.Data.HashSet
import Air2Lean.Memory
import Air2Lean.BitCast
import Air2Lean.Diagnostic
import Air2Lean.Air.Compat
import Air2Lean.ModelRegistry
import Air2Lean.AsmContract
import ZigLean.Mem.Enc
import ZigLean.Mem.ErrWidth
import ZigLean.Vec
import Air2Lean.Device
import Air2Lean.AsmAllowlist

/-!
# Subset checker

`check : Func → Except String Unit` rejects anything `Emit.lean` cannot translate: `other`
types, a union without a tag, a float type outside `16 32 64 80 128` bits, an integer `@abs`, a
an unsupported nullable-pointer representation, a memory access to a value that the memory model cannot
encode (`modelLayout`), a pointer constant without a global or into a `threadlocal` global, a
`threadlocal` global outside `checkThreadlocalGlobal`'s storage, a `runtime_nav_ptr` of a global
that is not `threadlocal`, a global that has no initial value or a partly `undefined` one, and an
`extern` global outside `checkExternGlobal`'s storage. `checkProgram` checks the slice items that a function that
uses memory reads (`Air2Lean/Memory.lean`). Errors name the function and the nearest `dbg_stmt`
line.

An `assembly` instruction (M21, A01) is accepted only when every operand is an integer with a
constraint of `Air2Lean/AsmContract.lean`'s grammar: a register output (`=r`, `={reg}`, early
clobber `=&`), a read-write (`+r`, `+{reg}`) or memory (`=m`, `+m`) lvalue output, a register
input (`r`, `{reg}`) or a matching input (`0`, `1`, …) tied to a write-only register output. At
most one output is the asm expression's own result (`ref = none`); every other output is an
lvalue output, a store through its pointer `ref`. No two outputs write the same local, no
clobber names a pinned operand register, and a `"memory"` clobber needs a reviewed
`asmPureRegistry` entry. Anything else (an `m` input, an immediate, `=&m`) is outside the
subset.
-/

namespace Air2Lean

/-- Is `c` a register constraint (`docs/generated-code.md` §asm)? Register class letter `r`, or a
named register in braces — either alone or with a leading `=` (write-only) marker. -/
def isRegisterConstraint (c : String) : Bool :=
  let body := if c.startsWith "=&" then c.drop 2 else if c.startsWith "=" then c.drop 1 else c
  (asmRegBody? body.toString).isSome

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
  -- A function pointer stored as data is a code address: its pointee is no data storage
  -- (`Emit.lean`'s 1-byte function block, L11). A view of code itself stays unresolved.
  let fnPointer := match ty with
    | .ptr _ _ c => (types[c]?.map isFnTy).getD false
    | _ => false
  let count ← match ty with
    | .other _ | .errorSet none => none
    | .ptr .. => some (if fnPointer then 0 else 1)
    | .array .. | .vector .. | .optional .. | .enum .. => some 1
    | .errorUnion .. => some 2
    | .struct _ _ fields => some fields.size
    | .union _ _ tag fields => some (tag.toArray.size + fields.size)
    | .tuple children => some children.size
    | _ => some 0
  let mut remaining := fuel - 1
  if count > remaining then none
  let mut symbolic := match ty with | .errorSet _ | .errorUnion .. => true | _ => false
  for child in if fnPointer then #[] else childTys ty do
    let (next, childCap) ← errorCapabilityScan types child remaining (seen.push id)
    remaining := next
    symbolic := symbolic || childCap
  return (remaining, symbolic)

/-- What a type graph reaches through every edge, pointer pointees included (`typeReach`). -/
private inductive TypeReach where
  /-- Every reachable type is known; none is an error type or a symbolic model type. -/
  | plain
  /-- Known and error-free, but `std.mem.Allocator`, `std.Thread` or `std.Io` is reachable:
  the model keeps their storage symbolically (`Zig.Allocator`, `Zig.ThreadId`, `Zig.Io`), so
  their bytes are not the program's bytes. -/
  | symbolic
  /-- Known, and an error set or error union is reachable. -/
  | error
  /-- An unknown type (an `.other` but `anyopaque`, `anyerror`, a missing id) is reachable,
  or the walk needs more than the bounded work. -/
  | unknown
  deriving BEq

/-- Error capability as a least fixpoint (G2, `docs/c-frontend.md`): `cap t = isError t ∨
∃ c ∈ childTys t, cap c`. On a finite graph that is reachability, so a worklist with a visited
set computes it and stops on cycles: a self-referential struct (`struct node *next`) is
error-free when no error type is reachable from it. `anyopaque` is a leaf, an opaque byte view
with no storage of its own; every other `.other` is unknown. Work is bounded like
`errorCapabilityScan`: 1 per distinct type, and a type's edge count must fit the remainder. -/
private def typeReach (types : Array Ty) (id : TyId) : TypeReach := Id.run do
  let mut pending : List TyId := [id]
  let mut visited : Std.HashSet TyId := {}
  let mut budget := 1024
  let mut found := TypeReach.plain
  -- A step visits a type or skips a visited one. Any graph `errorCapabilityScan` accepts
  -- has at most 1024 tree edges, so it ends well within the steps; past them, unknown.
  for _ in [:2048] do
    match pending with
    | [] => return found
    | t :: rest =>
      pending := rest
      if visited.contains t then continue
      visited := visited.insert t
      let some ty := types[t]? | return .unknown
      match ty with
      | .other "anyopaque" => continue
      | .other _ | .errorSet none => return .unknown
      | .errorSet _ | .errorUnion .. => found := .error
      | .allocator | .thread | .io => if found == .plain then found := .symbolic
      | _ => pure ()
      let children := childTys ty
      if budget == 0 || children.size > budget - 1 then return .unknown
      budget := budget - 1
      pending := children.toList ++ pending
  return .unknown

/-- `some false`: no error storage is reachable (an error-free graph, cycles included).
`some true`: error storage is reachable; such a graph keeps the strict acyclic
`errorCapabilityScan` of the finite error-storage fragment (L10), so a cyclic error-bearing
graph stays `none`. `none`: unknown or exhausted. -/
private def hasErrorCapability (types : Array Ty) (id : TyId) : Option Bool :=
  match typeReach types id with
  | .plain | .symbolic => some false
  | .error => (errorCapabilityScan types id 1024).map (·.2)
  | .unknown => none

/-- The item type of nested arrays (`[n][m]T` gives `T`); any other type is its own. -/
private def arrayItemTy (types : Array Ty) (id : TyId) : TyId := Id.run do
  let mut t := id
  for _ in [:256] do
    match types[t]? with
    | some (.array _ child _) => t := child
    | _ => return t
  return t

/-- A pointer cast that would view `Allocator`/`Thread`/`Io` storage through another type. -/
private def symbolicViewMsg : String :=
  "a pointer cast to or from storage with a symbolic model encoding (std.mem.Allocator, \
    std.Thread, std.Io) is outside the subset: the model does not keep their bytes"

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
    -- `Canon.lean` rewrites the whole-byte lanes that 0.16.0 also addressed as elements.
    if l.isLanePtr && !l.laneBitPtr then
      throw s!"{fnName}: near line {line}: a pointer to a vector lane (vector_index) is outside \
        the subset, except a comptime lane of an integer or `bool` vector with a schema-12 \
        profile of Zig {String.intercalate ", " lanePtrVersions} for the LLVM backend (stage2_llvm) on x86_64 or aarch64"
    if nullablePtrTy types layouts id && l.isVolatile then
      throw s!"{fnName}: near line {line}: volatile nullable pointers are outside the qualified pointer fragment"
    if nullablePtrTy types layouts id && (size == "slice" || l.hostSize != 0) then
      throw s!"{fnName}: near line {line}: nullable slices and nullable bit-pointers are outside the qualified pointer fragment"
    -- A bit-pointer reads and writes its host's `hostSize` bytes, any count (`Zig.loadBits`):
    -- `(bits + 7) / 8` on LLVM (3 for a `packed struct(u24)`), the ABI size on x86_64.
    -- A lane pointer's host is the vector's integer bytes (`Zig.loadLane`), of any count.
    if l.hostSize != 0 then
      -- Its field's bit size is what `Zig.loadBits`/`Zig.storeUndefBits` read and write.
      let some bits := packedBits types child
        | throw s!"{fnName}: near line {line}: a bit-pointer to a type other than an integer, a \
            `bool`, an enum or a packed struct is outside the subset"
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
  -- Arrays and ordinary structs of C/allowzero pointers use the null-byte storage
  -- dictionary (`Zig.nullablePtrEnc`); unions, tuples and error-union payloads do not.
  | .array _ child _ => recur child
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
    if fields.any (fun (_, c) => nullablePtrTy types layouts c) && layout == "packed" then
      throw s!"{fnName}: near line {line}: nullable pointers in packed aggregates are outside the qualified pointer fragment"
    if layout == "packed" && (packedBits types id).isNone then
      throw s!"{fnName}: near line {line}: packed struct '{name}' has a field other than an \
        integer, a `bool`, an enum or a packed struct: outside the subset"
    fields.forM fun (_, fty) => recur fty
  | .enum _ tag _ _ => recur tag
  | .union name layout tag fields =>
    if fields.any (fun (_, c) => nullablePtrTy types layouts c) then
      throw s!"{fnName}: near line {line}: nullable pointers in aggregate values are outside the qualified pointer fragment"
    -- A `noreturn` field is a variant that is never active (`uninhabitedTy`); the union needs
    -- another field to have a value, and only a tagged union can have one.
    if fields.any (uninhabitedTy types ·.2) then
      if tag.isNone then
        throw s!"{fnName}: near line {line}: union '{name}' ({layout}, no tag) has a noreturn \
          field: outside the subset"
      if (inhabitedFields types fields).isEmpty then
        throw s!"{fnName}: near line {line}: union '{name}' has only noreturn fields: it has no \
          values, outside the subset"
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
  | .future result => recur result

/-- The layout of a tagged union from the tag's and the payload's size and alignment (the
largest field's), as `(tag offset, payload offset, size, alignment)`: the compiler's rule puts
the one with the larger alignment first, the tag if they are equal. -/
def unionLayout (ts ta ps pa : Nat) : Nat × Nat × Nat × Nat :=
  if ta ≥ pa then (0, Zig.alignUp ts pa, Zig.alignUp (Zig.alignUp ts pa + ps) ta, ta)
  else (Zig.alignUp ps ta, 0, Zig.alignUp (Zig.alignUp ps ta + ts) pa, pa)

/-- An integer or float lane type whose bits fill its ABI size (`u8`, `u32`, `f64`): a vector of
it is its lanes at a byte stride on every backend. Other lanes (`u9`, `u24`, `f80`) are
bit-packed (`Zig.Vec.packedEnc`). -/
def byteStridedLane (types : Array Ty) (lane : TyId) : Bool :=
  match types[lane]? with
  | some (.int _ bits) | some (.float bits) => bits != 0 && bits == 8 * Zig.intSize bits
  | _ => false

/-- The exporter's layout of type `id` is the profile's `errBits`-bit error integer. -/
def errCodeLayout (layouts : Array Layout) (id : TyId) (errBits : Nat) : Bool :=
  (layouts[id]?.map fun l => l.size == some (Zig.errCodeSize errBits) &&
    l.align == some (Zig.errCodeAlign errBits)).getD false

/-- The size and alignment that the memory model (`ZigLean/Mem/Enc.lean`) gives the type `id`,
or an error naming what the model cannot encode yet. A struct and an enum take the exporter's
values: their encodings are generated from the exporter's offsets. -/
partial def modelLayout (types : Array Ty) (layouts : Array Layout) (id : TyId)
    (errBits : Nat := 16) : Except String (Nat × Nat) := do
  let exported : Except String (Nat × Nat) :=
    match layouts[id]? with
    | some { size := some s, align := some a, .. } => pure (s, a)
    | _ => throw s!"type {id} has no layout in the AIR file"
  -- The pointer size of the profile (`Layout.ptrBytes`, `Zig.PtrWidth.bytes`).
  let pb := (layouts[id]?.map (·.ptrBytes)).getD 8
  match types[id]? with
  | some (.int _ bits) => pure (Zig.intSize bits, Zig.intAlign bits)
  | some .bool => pure (1, 1)
  | some (.float bits) => pure (Zig.intSize bits, Zig.intAlign bits)
  | some .void => pure (0, 1)
  | some .noreturn => throw "noreturn has no values and no storage"
  -- A C/allowzero pointer is stored with `Zig.nullablePtrEnc` (null = eight zero bytes).
  | some (.ptr size ..) =>
    if pb != 8 && nullablePtrTy types layouts id then
      throw "a C/allowzero pointer is outside the 32-bit pointer model"
    pure (if size == "slice" then 2 * pb else pb, pb)
  | some .allocator => pure (2 * pb, pb)
  | some .thread =>
    if pb != 8 then throw "a std.Thread handle is outside the 32-bit pointer model"
    pure (8, 8)
  | some .io =>
    if pb != 8 then throw "a std.Io value is outside the 32-bit pointer model"
    pure (16, 8)
  | some (.future r) =>
    if pb != 8 then throw "an Io.Future is outside the 32-bit pointer model"
    -- `Zig.Future`: `any_future` at 0, the result at `Zig.Future.resultOff`.
    let (s, a) ← modelLayout types layouts r errBits
    let off := Zig.alignUp 8 a
    unless (layouts[id]?.map (·.offsets)).getD #[] == #[0, off] do
      throw s!"Io.Future field offsets differ from any_future at 0 and result at {off}"
    pure (Zig.alignUp (off + s) (Nat.max 8 a), Nat.max 8 a)
  | some (.optional c) =>
    if nullablePtrTy types layouts c then
      throw "an optional C/allowzero pointer needs a separate null flag"
    match types[c]? with
    | some (.ptr "slice" ..) => pure (2 * pb, pb)
    | some (.ptr ..) => pure (pb, pb)
    | some (.errorSet _) => modelLayout types layouts c errBits
    | _ =>
      let (s, a) ← modelLayout types layouts c errBits
      pure (Zig.alignUp (s + 1) a, a)
  | some (.array len c sentinel) =>
    let (s, a) ← modelLayout types layouts c errBits
    pure ((len + if sentinel then 1 else 0) * s, a)
  | some (.vector len c) =>
    -- The vector memory images are qualified on the 64-bit LLVM targets only (L09).
    if pb != 8 then throw "a vector in memory is outside the 32-bit pointer model"
    match types[c]? with
    | some (.int _ bits) | some (.float bits) =>
      let (s, _) ← modelLayout types layouts c errBits
      if bits == 0 then throw "a vector of zero-bit lanes in memory is outside the subset"
      -- The size check compares the rest with the exporter's.
      if byteStridedLane types c then return (Zig.vecLayout len s, Zig.vecLayout len s)
      -- Non-byte (`u9`) or ABI-padded (`u24`, `u40`, `f80`) lanes: bit-packed (`Zig.Vec.packedEnc`),
      -- as observed for the LLVM backend only.
      unless (layouts[id]?.map (·.packedLanes)).getD false do
        throw "a vector in memory with non-byte-width or ABI-padded lanes needs a schema-12 \
          profile with the LLVM backend (stage2_llvm), whose bit-packed lane layout the model \
          encodes"
      pure (Zig.packedVecLayout len bits, Zig.packedVecLayout len bits)
    | some .bool => pure (Zig.boolVecLayout len, Zig.boolVecLayout len)
    | _ => throw "a vector of a type other than an integer, a float or `bool`"
  | some (.enum _ tag _ _) =>
    let _ ← modelLayout types layouts tag errBits
    exported
  | some (.struct name layout fields) =>
    if layout == "packed" then
      -- Its backing integer (`Zig.Packed`).
      let some bits := packedBits types id | throw s!"packed struct '{name}' with a field other \
        than an integer, a `bool` or a packed struct"
      return (Zig.intSize bits, Zig.intAlign bits)
    for (_, fty) in fields do
      let _ ← modelLayout types layouts fty errBits
    if (layouts[id]?.map (·.offsets.size)).getD 0 != fields.size then
      throw s!"struct '{name}' has no field offsets in the AIR file"
    exported
  | some (.errorUnion set payload) =>
    -- `Zig.errUnionOffsetsW`: the error code is the profile's `error_set_bits` integer.
    unless errCodeLayout layouts set errBits do
      throw s!"an error set whose layout is not the profile's {errBits}-bit error integer \
        ({Zig.errCodeSize errBits} bytes aligned to {Zig.errCodeAlign errBits}; `--error-limit`)"
    if let some (.errorSet (some names)) := types[set]? then
      -- An empty discriminator has no standalone value, but its union's success arm does.
      unless names.isEmpty do
        let _ ← modelLayout types layouts set errBits
    let (s, a) ← modelLayout types layouts payload errBits
    pure (Zig.errUnionSizeW errBits s a, Nat.max a (Zig.errCodeAlign errBits))
  | some (.errorSet none) =>
    throw "standalone anyerror or unresolved error storage has no finite declared encoding domain"
  | some (.errorSet (some names)) =>
    if names.isEmpty then throw "an empty standalone error domain has no runtime value"
    if names.size > 65535 then throw "an error encoding domain exceeds the 16-bit nonzero code capacity"
    if names.size > Zig.errCapacity errBits then
      throw s!"an error encoding domain of {names.size} names exceeds the {Zig.errCapacity errBits} \
        nonzero codes of the profile's {errBits}-bit error integer (`--error-limit`)"
    if !validErrorDomainNames names then
      throw "an error encoding domain must have distinct nonempty names"
    unless errCodeLayout layouts id errBits do
      throw s!"an error set storage layout must be the profile's {errBits}-bit error integer \
        ({Zig.errCodeSize errBits} bytes aligned to {Zig.errCodeAlign errBits})"
    pure (Zig.errCodeSize errBits, Zig.errCodeAlign errBits)
  | some (.union name _ (some tag) fields) =>
    -- A `noreturn` field is never active: no payload bytes (`uninhabitedTy`).
    let (ts, ta) ← modelLayout types layouts tag errBits
    let fs ← (inhabitedFields types fields).mapM fun (_, t) => modelLayout types layouts t errBits
    let (_, _, s, a) := unionLayout ts ta (fs.foldl (Nat.max · ·.1) 0) (fs.foldl (Nat.max · ·.2) 1)
    -- Also inside a struct, whose check compares only its own size: the generated `Zig.Enc`
    -- has the exporter's size and the model's offsets. 0.16.0 stores no tag for a union with
    -- one possible active field.
    let (s', a') ← exported
    unless s == s' && a == a' do
      throw s!"the memory model gives union '{name}' size {s} and alignment {a}, the compiler \
        {s'} and {a'}"
    pure (s, a)
  | some (.union name layout none fields) =>
    unless layout == "extern" || layout == "packed" do
      throw s!"union '{name}' ({layout}) without a tag"
    for (_, fty) in fields do
      let _ ← modelLayout types layouts fty errBits
    exported
  | some t => throw s!"{repr t}"
  | none => throw s!"unknown type id {id}"

/-- The tag and payload offsets of a tagged union with the tag type `tag` and the field types
`fields` in memory (`unionLayout`); a `noreturn` field adds no payload bytes. -/
def unionOffsets (types : Array Ty) (layouts : Array Layout) (tag : TyId) (fields : Array TyId)
    (errBits : Nat := 16) : Option (Nat × Nat) := do
  let (ts, ta) ← (modelLayout types layouts tag errBits).toOption
  let fs ← (fields.filter (!uninhabitedTy types ·)).mapM fun t =>
    (modelLayout types layouts t errBits).toOption
  let (to, po, _, _) := unionLayout ts ta (fs.foldl (Nat.max · ·.1) 0) (fs.foldl (Nat.max · ·.2) 1)
  pure (to, po)

/-! ## Zig ≤0.16 representation casts (`docs/aggregate-casts.md`) -/

/-- Up to 0.16.0, `@bitCast` reinterprets the in-memory representation. Zig 0.17.0 changed it
to the logical bit order; the representation-cast and optional-pointer cast rules below apply
to the listed versions only. -/
def memoryBitCastVersion (zigVersion : String) : Bool :=
  #["0.14.1", "0.15.2", "0.16.0"].contains zigVersion

/-- An aggregate whose ≤0.16 `@bitCast` is a representation cast: an array without a sentinel,
an `extern` struct, an `extern` union. -/
def reprAggregate (types : Array Ty) (id : TyId) : Bool :=
  match types[id]? with
  | some (.array _ _ false) | some (.struct _ "extern" _) | some (.union _ "extern" none _) => true
  | _ => false

/-- A single (non-slice) pointer type that cannot hold address zero, and its optional. -/
def singlePtrTy (types : Array Ty) (layouts : Array Layout) (id : TyId) : Bool :=
  match types[id]? with
  | some (.ptr size _ _) => size != "slice" && !nullablePtrTy types layouts id
  | _ => false

def optSinglePtrTy (types : Array Ty) (layouts : Array Layout) (id : TyId) : Bool :=
  match types[id]? with
  | some (.optional c) => singlePtrTy types layouts c
  | _ => false

/-- Zig 0.16.0's `Type.bitSize` of a type with a guaranteed in-memory layout (`src/Type.zig`):
an `extern` struct or union is its ABI size in bits; an array has `(len-1)·8·@sizeOf(E) +
@bitSizeOf(E)` bits (its trailing padding is dropped, padding between items counts). `none`
for a type without a guaranteed layout (`auto` struct, tuple, tagged union, slice, error
storage, sentinel array, packed union), which `@bitCast` rejects or the model leaves out, and
for a pointer or optional pointer at any depth: the model's pointer bytes carry provenance and
are not integer bits, so a pointer-bearing representation cast is rejected (fail closed). -/
partial def reprBitSize (types : Array Ty) (layouts : Array Layout) (id : TyId) : Option Nat := do
  let abiBits : Option Nat := (layouts[id]?.bind (·.size)).map (8 * ·)
  match ← types[id]? with
  | .int _ bits | .float bits => pure bits
  | .bool => pure 1
  | .enum _ tag _ _ => reprBitSize types layouts tag
  | .struct _ "packed" _ => packedBits types id
  | .struct _ "extern" fields | .union _ "extern" none fields =>
    for (_, t) in fields do let _ ← reprBitSize types layouts t
    abiBits
  | .array len child false =>
    let eb ← reprBitSize types layouts child
    let es ← layouts[child]?.bind (·.size)
    pure (if len == 0 then 0 else (len - 1) * 8 * es + eb)
  | _ => none

/-- A ≤0.16 `@bitCast` from `src` to `dst` that the representation cast (`Zig.reprCast`)
translates: different types, an array, `extern` struct or `extern` union on at least one side.
The checker then requires both sides to have a `reprBitSize` and equal ones. -/
def reprCastApplies (zigVersion : String) (types : Array Ty) (src dst : TyId) : Bool :=
  memoryBitCastVersion zigVersion && src != dst &&
    (reprAggregate types src || reprAggregate types dst)

/-- The type `id` can be in memory: the model encodes it, with the exporter's size and alignment. -/
def checkMemTy (fnName : String) (types : Array Ty) (layouts : Array Layout) (line : Nat)
    (id : TyId) (errBits : Nat := 16) : Except String Unit := do
  match modelLayout types layouts id errBits with
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
  /-- The profile's `error_set_bits` (`Func.errorSetBits`). -/
  errBits : Nat := 16
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
  /-- The function's `zig_version`: selects the `@bitCast` semantics. Up to 0.16.0 it reinterprets
  memory (`memoryBitCastVersion`); from 0.17.0 it uses the logical bit order
  (`Air2Lean/BitCast.lean`). Empty in bare contexts, which then reject representation casts. -/
  zigVersion : String := ""
  /-- `--device-contract` (L13): integer volatile loads and stores, and the declared
  `asm volatile`, are device events. -/
  device : Option DeviceContract := none
  /-- `Func.targetArch`, for the asm allowlist (`Air2Lean/AsmAllowlist.lean`). -/
  targetArch : String := ""

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
  checkMemTy cx.fnName cx.types cx.layouts line ((ptrChild cx.types pty).get!) cx.errBits

/-- Is `ty` a bit-pointer type whose AIR file has no `vector_index`? -/
def unverifiedBitPtrTy (layouts : Array Layout) (ty : TyId) : Bool :=
  (layouts[ty]?.getD {}).unverifiedBitPtr

/-- The rejection of an unverified bit-pointer that the function did not make. An export without
`vector_index` gives a lane pointer (`*align(2:0:4:2) u9`) the same type entry as a packed field
pointer, so only a `struct_field_ptr` of a packed struct or union is known to be a packed field
pointer: a parameter, a constant, or any other instruction result (a load, a call, a cast) is
rejected. -/
def unverifiedBitPtrError (fnName : String) (line : Nat) (what : String) : String :=
  s!"{fnName}: near line {line}: {what} is a bit-pointer without `vector_index` in the AIR file; \
    it may point to a vector lane (only a packed field pointer made by `struct_field_ptr` is \
    accepted; re-export with the current exporter)"

/-- The rule of `unverifiedBitPtrError` for the result of `op`, of type `ty`. -/
def CheckCtx.checkBitPtrSource (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op) :
    Except String Unit := do
  unless unverifiedBitPtrTy cx.layouts ty do return
  if let .fieldPtr base _ := op then
    if let some c := (cx.valTy? base).bind (ptrChild cx.types) then
      match cx.types[c]? with
      | some (.struct _ "packed" _) | some (.union _ "packed" _ _) => return
      | _ => pure ()
  throw (unverifiedBitPtrError cx.fnName line "a value not made by a packed `struct_field_ptr`")

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

/-- Nullable pointer slicing, bulk memory operations and parent recovery are not part of the
qualified fragment. Field/element projections and pointer arithmetic are
(`Zig.ptrProjectNullable`). Cast to a nonnullable pointer after a null check first. -/
def CheckCtx.rejectNullableProjection (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  if (cx.valTy? ptr |>.map (nullablePtrTy cx.types cx.layouts) |>.getD false) then
    cx.fail line "nullable pointer slicing, bulk memory operations and parent-pointer recovery require a nonnull cast first (outside the qualified pointer fragment)"

/-- An atomic op's pointer pointee (C09): `*T`/`[*]T` or `?*T`/`?[*]T`, not a slice, C or
allowzero pointer. Its value is `Zig.Ptr` or `Option Zig.Ptr`, whose message keeps the pointer's
block (`ZigLean/Mem/AtomicPtr.lean`). -/
def atomicPtrPointee (types : Array Ty) (layouts : Array Layout) (c : TyId) : Bool :=
  let plain (id : TyId) := match types[id]? with
    | some (.ptr size _ _) => (size == "one" || size == "many") && !nullablePtrTy types layouts id
    | _ => false
  plain c || match types[c]? with
    | some (.optional c') => plain c'
    | _ => false

/-- An atomic op's pointee must be an integer, an enum, a `bool`, a packed struct, or a pointer
(`atomicPtrPointee`; `docs/std-models.md` §Thread model). An RMW on a pointer must be `.Xchg`.
A float atomic is rejected with its own reason. -/
def CheckCtx.atomicChild (cx : CheckCtx) (line : Nat) (ptr : Val) (rmw : Option RmwOp := none) :
    Except String Unit := do
  let some pty := cx.valTy? ptr
    | cx.fail line "an atomic op through a value that is not a pointer"
  let some c := ptrChild cx.types pty
    | cx.fail line "an atomic op through a value that is not a pointer"
  if laneBitPtrTy cx.layouts pty then
    cx.fail line "an atomic op through a vector lane pointer is outside the subset"
  if atomicPtrPointee cx.types cx.layouts c then
    match rmw with
    | some op => if op != .xchg then
        cx.fail line "an atomic RMW on a pointer other than `.Xchg` is outside the subset"
    | none => pure ()
    return
  match cx.types[c]? with
  | some (.int ..) | some (.enum ..) | some .bool | some (.struct _ "packed" _) => pure ()
  | some (.float _) => cx.fail line "a float atomic is outside the subset: the model has no float \
      atomic messages (float RMW arithmetic and the bitwise compare of `cmpxchg` are not qualified)"
  | some (.ptr "c" ..) | some (.ptr "one" ..) | some (.ptr "many" ..) =>
    -- `atomicPtrPointee` admits these only when not C/allowzero (L05 stores those with a
    -- null-byte encoding: eight zero bytes, not the model's pointer message).
    cx.fail line "an atomic op on a C or allowzero pointer is outside the subset: its null-byte \
      encoding (L05) has no pointer atomic messages"
  | _ => cx.fail line "an atomic op on a type other than an integer, an enum, a `bool`, a packed \
      struct or a single/many pointer (`*T`, `?*T`) is outside the subset"

/-- A `cmpxchg` (strong or weak), or an RMW `.Max`/`.Min`, on an integer representation with
padding bits (`u24`, `u31`, `i40`, `enum(u24)`, a packed struct backed by `u40`: bit width other
than `8 * @sizeOf`). Zig lowers these to an LLVM op on the whole ABI cell (`cmpxchg ptr, i64` for
`u40`), so the padding bits take part in the comparison: they can hold anything a plain `iN`
store left untouched, a carry of an RMW `.Add`, the sign extension of a signed operand. Native
code then fails a `cmpxchg` (or keeps the old value of a `.Max`) whose value bits match, where
the model (padding undefined, value bits compared) succeeds. The other atomic ops are unaffected:
loads and RMW results are masked, and stores, `.Xchg` and the arithmetic/bitwise RMWs only write
the padding, which the model leaves undefined. -/
def CheckCtx.checkPaddedAtomic (cx : CheckCtx) (line : Nat) (op : Op) : Except String Unit := do
  let (ptr, what) ← match op with
    | .cmpxchg weak p .. => pure (p, if weak then "@cmpxchgWeak" else "@cmpxchgStrong")
    | .atomicRmw .max _ p _ => pure (p, "@atomicRmw .Max")
    | .atomicRmw .min _ p _ => pure (p, "@atomicRmw .Min")
    | _ => return
  let some c := (cx.valTy? ptr).bind (ptrChild cx.types) | return
  -- The integer, an enum's tag or a packed struct's backing integer. A `bool` is one whole
  -- byte, 0 or 1, in both the model and the native code.
  if cx.types[c]? == some .bool then return
  let some bits := packedBits cx.types c | return
  if bits != 8 * Zig.intSize bits then
    cx.fail line s!"{what} on type {c}, a {bits}-bit integer representation with padding bits \
      (ABI size {Zig.intSize bits} bytes), is outside the subset: the native op compares the whole \
      ABI cell, padding included, which the model leaves undefined; use an integer whose width \
      is a power-of-two number of bytes (u8, u16, u32, u64, u128) or a type backed by one"

/-- An access to the items of `ptr` (a slice, many-pointer or array pointer): the item type must be
one the model encodes. -/
def CheckCtx.itemAccess (cx : CheckCtx) (line : Nat) (ptr : Val) : Except String Unit := do
  let pty ← cx.memPtrTy line ptr
  if let some (.ptr "one" _ c) := cx.types[pty]? then
    if let some (.vector _ e) := cx.types[c]? then
      if cx.types[e]? == some .bool then
        cx.fail line "a pointer to a lane of a `bool` vector is outside the subset (the lane is a \
          bit, and the AIR file has no lane index)"
      -- A bit-packed lane (`u9`, `u24`, `f80`) is not an item at a byte stride.
      unless byteStridedLane cx.types e do
        cx.fail line "a pointer to a lane of a vector whose lanes are not byte-strided (non-byte \
          width or ABI padding) is outside the subset (the lane is a bit field, and the AIR file \
          has no lane index)"
      checkMemTy cx.fnName cx.types cx.layouts line c cx.errBits
  let some e := itemTy cx.types pty
    | cx.fail line s!"item access through pointer type {pty}, which has no items"
  checkMemTy cx.fnName cx.types cx.layouts line e cx.errBits

/-- `&v[idx]` of type `ty`, a lane pointer (`Layout.laneBitPtr`) into the bit-packed vector that
`ptr` points to: the lane type, lane count and comptime lane of `ty` must be the vector's and
`idx`. The result is `ptr` itself (`Emit.lean`); the type carries the lane's bits. -/
def CheckCtx.lanePtr (cx : CheckCtx) (line : Nat) (ty : TyId) (ptr idx : Val) :
    Except String Unit := do
  let pty ← cx.memPtrTy line ptr
  let some vec := ptrChild cx.types pty
    | cx.fail line "a lane pointer that does not point into a vector"
  let some (.vector n e) := cx.types[vec]?
    | cx.fail line "a lane pointer that does not point into a vector"
  let l := cx.layouts[ty]?.getD {}
  let lane := match idx with | .int _ k => if k ≥ 0 then some k.toNat else none | _ => none
  let w := ((cx.types[e]?).bind laneBits?).getD 0
  unless ptrChild cx.types ty == some e && l.vectorIndex == lane &&
      lane.any (· < n) && l.hostSize == (n * w + 7) / 8 do
    cx.fail line "a lane pointer whose type does not match its vector and comptime lane"
  checkMemTy cx.fnName cx.types cx.layouts line vec cx.errBits

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

/-- A device event under `--device-contract` (L13): a load (also of an item of a volatile
slice or many-pointer) or a store through the volatile pointer `p` (type `pty`) of an
8/16/32/64-bit integer, with a byte-aligned (non-bit) pointer
into memory, not a local place; a stored value must not be `undefined`. -/
def CheckCtx.checkDeviceAccess (cx : CheckCtx) (line : Nat) (p : Val) (pty : TyId)
    (value : Option Val) : Except String Unit := do
  let reject (why : String) : Except String Unit :=
    cx.fail line s!"volatile access through pointer type {pty} is outside the device contract: \
      {why} (docs/volatile-effects.md)"
  if let .inst i := p then
    if cx.places.contains i || cx.localRoots.any (·.1 == i) then
      reject "it points into a local, not a device register"
  if ((cx.layouts[pty]?.map (·.hostSize)).getD 0) != 0 then reject "a bit-pointer"
  match (ptrChild cx.types pty).bind (cx.types[·]?) with
  | some (.int _ bits) =>
    unless [8, 16, 32, 64].contains bits do reject s!"a {bits}-bit integer register"
  | _ => reject "the pointee is not an integer"
  if let some (.undef _) := value then reject "a store of `undefined`"

/-- Volatile and device effects (L13). A volatile access is an observable effect that may
read or change device state, so it is never an ordinary repeatable memory operation. The
memory model has no such effect: every volatile load, store, atomic, item access, `@memcpy`,
`@memset`, pointer-state test/set and asm lvalue output is rejected. So is dropping `volatile`
in a pointer cast and passing a volatile pointer to a built-in std model. Forming, casting to,
comparing, passing and returning a volatile pointer value remains supported: it is address
metadata only. A declared contract is a project model registry binding whose volatile pointer
parameter is in its `footprint.writes` (`ModelRegistry.check`), or, with `--device-contract`
(`cx.device`), an integer load or store that `checkDeviceAccess` admits as a device event. -/
def CheckCtx.checkVolatile (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op) :
    Except String Unit := do
  let guidance := "volatile accesses are device-facing effects outside the memory model, \
    not repeatable memory operations; move the access into a function bound by a project model \
    registry entry that lists the volatile pointer parameter in `footprint.writes`, or declare \
    the device with `--device-contract` (docs/volatile-effects.md)"
  let accesses : Array (Val × String) := match op with
    | .load p | .retLoad p | .ptrElemVal p _ | .sliceElemVal p _ => #[(p, "load")]
    | .store p _ | .memset p _ | .setUnionTag p _ => #[(p, "store")]
    | .atomicLoad p _ | .atomicStore p .. | .atomicRmw _ _ p _ | .cmpxchg _ p .. =>
      #[(p, "atomic access")]
    | .memcpy dst src => #[(dst, "store"), (src, "load")]
    | .isNullPtr _ p | .isErrPtr _ p | .errCodePtr p | .tryPtr p _ => #[(p, "load")]
    | .optPayloadPtr true p | .errPayloadPtr true p => #[(p, "store")]
    | .asm _ _ _ outputs _ => outputs.filterMap fun o => o.ref.map (·, "asm output store")
    | _ => #[]
  -- With a device contract, an integer load or store through a volatile pointer to memory is a
  -- device event (`Zig.vload`/`Zig.vstore`); every other volatile access stays rejected.
  let deviceAccess? : Option (Val × Option Val) := if cx.device.isNone then none else match op with
    | .load p | .ptrElemVal p _ | .sliceElemVal p _ => some (p, none)
    | .store p v => some (p, some v)
    | _ => none
  for (p, kind) in accesses do
    if let some pty := cx.valTy? p then
      if volatilePtrTy cx.types cx.layouts pty then
        if let some (dp, value) := deviceAccess? then
          if dp == p then
            cx.checkDeviceAccess line p pty value
            continue
        let guidance := if cx.device.isSome then
          "the device contract covers only an 8/16/32/64-bit integer load or store through a \
            volatile pointer to memory (docs/volatile-effects.md)" else guidance
        cx.fail line s!"volatile {kind} through pointer type {pty}: {guidance}"
  -- Derivations must keep the qualifier: a result without a volatile pointer (a `@volatileCast`
  -- away, `@intFromPtr`) would let a later device access look like an ordinary one.
  let derived? : Option Val := match op with
    | .bitcast p | .fieldPtr p _ | .fieldParentPtr p _ | .elemPtr p _ | .ptrAdd _ p _
    | .slice p _ | .slicePtr p | .arrayToSlice p | .sliceFieldPtr _ p | .optPayloadPtr _ p
    | .errPayloadPtr _ p | .wrapOptional p => some p
    | _ => none
  if let some p := derived? then
    if let some pty := cx.valTy? p then
      let keeps := volatilePtrTy cx.types cx.layouts ty || match cx.types[ty]? with
        | some (.optional c) => volatilePtrTy cx.types cx.layouts c
        | _ => false
      if volatilePtrTy cx.types cx.layouts pty && !keeps then
        cx.fail line s!"volatile pointer type {pty} becomes type {ty} without `volatile`, which \
          would make device accesses ordinary memory accesses: {guidance}"
  if let .call (.func name ..) args := op then
    if (stdModel? name).isSome then
      for a in args do
        if let some aty := cx.valTy? a then
          if containsVolatilePtr cx.types cx.layouts aty then
            cx.fail line s!"built-in std model '{name}' has no volatile contract (argument \
              type {aty}): {guidance}"

/-- Inline asm effects (L13, A01). An M21 `opaque` asm op is a repeatable function of its
inputs, which is sound only for input-determined instructions. So every asm must match the
reviewed allowlist (`Air2Lean/AsmAllowlist.lean`: template, ordered constraints, clobbers,
target), or, with `--device-contract`, a declared device asm: a `volatile` asm with at most one
output, which must be the expression's result, and no `memory` clobber (DEV-01), emitted as one
`Zig.vasm` event. Everything else, also non-volatile asm, is `ASM_VOLATILE_EFFECT`: `rdtsc`,
`rdrand`, port I/O, barriers, output-less asm and `memory` clobbers. The operand shapes are
checked by `checkOp` (M21). -/
def CheckCtx.checkAsmEffect (cx : CheckCtx) (line : Nat) (op : Op) : Except String Unit := do
  let .asm source isVolatile clobbers outputs inputs := op | return
  let constraints := asmConstraints outputs inputs
  if let some entry := op.asmAllowEntry? cx.targetArch then
    if entry.semantics == .spinHint && !op.isSpinHint then
      cx.fail line s!"asm {source.quote} is allowlisted as a spin hint, which has no operands"
    return
  -- A spin hint off its target's list stays rejected: the emitter would make it a hint, not an event.
  if op.isSpinHint then
    cx.fail line s!"spin hint {source.quote} is not allowlisted for target \
      '{if cx.targetArch.isEmpty then "x86_64" else cx.targetArch}' (Air2Lean/AsmAllowlist.lean)"
  let guidance := "an opaque asm is a repeatable function of its inputs, which is unsound for \
    effects and nondeterministic outputs (rdtsc, rdrand, port I/O, barriers, output-less asm, \
    memory clobbers); declare it as a device event with an `asm` entry of `--device-contract`, \
    or add a reviewed entry to Air2Lean/AsmAllowlist.lean if its outputs depend only on its \
    inputs (docs/volatile-effects.md)"
  let some contract := cx.device
    | cx.fail line s!"asm {source.quote} (constraints {constraints}, clobbers {clobbers.toList}) is \
        not on the reviewed asm allowlist: {guidance}"
  let some _ := contract.asm? source constraints clobbers.toList
    | cx.fail line s!"asm {source.quote} (constraints {constraints}, clobbers {clobbers.toList}) is \
        neither on the reviewed asm allowlist nor declared by the device contract: {guidance}"
  if clobbers.contains "memory" then
    cx.fail line s!"asm {source.quote}: a 'memory' clobber is outside the device contract (DEV-01)"
  unless isVolatile do
    cx.fail line s!"asm {source.quote} is not `volatile`: the compiler may merge or delete it, so it \
      cannot be one device event"
  if outputs.size > 1 || outputs.any (·.ref.isSome) then
    cx.fail line s!"device asm {source.quote}: only one output, the expression's result, is supported"

/-- The pointer to field `idx` of a packed struct (L08), from the pointer type `base` to it:
`(host size, bit offset)` of a bit-pointer, or `(0, byte offset)` of a byte pointer. The
compiler's rule (`Type.packedStructFieldPtrInfo`): the field's bit offset is the sum of the
earlier fields' bit sizes, plus the base's bit offset if the base is a bit-pointer, whose host it
keeps. Otherwise the host is the struct: `(bits + 7) / 8` bytes (LLVM) or its ABI size (the
self-hosted x86_64 backend), both accepted (`hosts`). A field at a byte boundary whose bit size
fills its ABI size can be a byte pointer instead. `none`: not a packed struct field, or a
size the exporter does not give. -/
def packedFieldPtr? (types : Array Ty) (layouts : Array Layout) (base : TyId) (idx : Nat) :
    Option (Array Nat × Nat × Option Nat) := do
  let some (.ptr _ _ s) := types[base]? | none
  let some (.struct _ "packed" fields) := types[s]? | none
  let (_, fty) ← fields[idx]?
  let bits ← packedBits types s
  let fieldBits ← packedBits types fty
  let bl := layouts[base]?.getD {}
  let bit := bl.bitPtrOffset + packedFieldBit types fields idx
  let hosts ← if bl.hostSize != 0 then pure #[bl.hostSize] else do
    let abi ← (layouts[s]?).bind (·.size)
    pure (if abi == (bits + 7) / 8 then #[abi] else #[(bits + 7) / 8, abi])
  let fieldAbi ← (layouts[fty]?).bind (·.size)
  let bytePtr := if bit % 8 == 0 && 8 * fieldAbi == fieldBits then some (bit / 8) else none
  pure (hosts, bit, bytePtr)

/-- Cross-boundary packed layout (L08): the exporter's pointer to a packed struct field (its
`host_size` and `bit_offset`, or a byte pointer) is the one the model computes from the struct's
field bit sizes (`packedFieldPtr?`); a mismatch is rejected, with `PACKED_LAYOUT`. Also for
`@fieldParentPtr`, from the field pointer back to the struct pointer. -/
def CheckCtx.checkPackedLayout (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op) :
    Except String Unit := do
  let (base, field, idx) ← match op with
    | .fieldPtr b idx => match cx.valTy? b with
      | some bt => pure (bt, ty, idx)
      | none => return
    | .fieldParentPtr f idx => match cx.valTy? f with
      | some ft => pure (ty, ft, idx)
      | none => return
    | _ => return
  let some (.ptr _ _ s) := cx.types[base]? | return
  let some (.struct name "packed" fields) := cx.types[s]? | return
  -- A field outside the packed subset is `checkTy`'s type error, not a layout mismatch.
  unless (packedBits cx.types s).isSome && idx < fields.size do return
  let some (hosts, bit, bytePtr) := packedFieldPtr? cx.types cx.layouts base idx
    | cx.fail line s!"packed layout of '{name}' field {idx}: the struct, field or pointer \
        sizes are not in the AIR file (a bit-pointer needs them)"
  let fl := cx.layouts[field]?.getD {}
  let hostText := String.intercalate " or " (hosts.toList.map toString)
  let expected := s!"host_size {hostText}, bit_offset {bit}" ++
    (match bytePtr with | some o => s!", or a byte pointer at byte {o}" | none => "")
  let fail {α : Type} (got : String) : Except String α :=
    cx.fail line s!"packed layout mismatch: field {idx} of '{name}' through pointer type {base} \
      is {got} in the AIR file, the model computes {expected} (the field bit offsets are the sums \
      of the earlier fields' bit sizes)"
  if fl.hostSize == 0 then
    if bytePtr.isNone then fail s!"a byte pointer (type {field})"
  else if !hosts.contains fl.hostSize || fl.bitOffset != bit then
    fail s!"host_size {fl.hostSize}, bit_offset {fl.bitOffset} (type {field})"

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

/-- The union and field names of field `idx` of the union `uty` if that field is `noreturn`
(`uninhabitedTy`): a variant that is never active. -/
def uninhabitedUnionField? (types : Array Ty) (uty : TyId) (idx : Nat) : Option (String × String) :=
  match types[uty]? with
  | some (.union name _ _ fields) => match fields[idx]? with
    | some (f, t) => if uninhabitedTy types t then some (name, f) else none
    | none => none
  | _ => none

/-- An instruction that activates, reads or points to a `noreturn` variant of a union. Zig code
that reaches one is unreachable, so the variant has no value in the translation; fail closed
instead of emitting one. -/
def CheckCtx.checkNoreturnVariant (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op) :
    Except String Unit := do
  let pointee (v : Val) : Option TyId := (cx.valTy? v).bind (ptrChild cx.types)
  let (what, hit) := match op with
    | .unionInit idx _ => ("union_init of", uninhabitedUnionField? cx.types ty idx)
    | .structFieldVal s idx =>
      ("a read of", (cx.valTy? s).bind (uninhabitedUnionField? cx.types · idx))
    | .fieldPtr b idx => ("a pointer to", (pointee b).bind (uninhabitedUnionField? cx.types · idx))
    | .setUnionTag p (.enumTag _ v) =>
      ("set_union_tag to", (pointee p).bind fun uty => do
        let some (.union _ _ (some tagTy) fields) := cx.types[uty]? | none
        let some (.enum _ _ _ tags) := cx.types[tagTy]? | none
        let (name, _) ← tags.find? (fun (t : String × Int) => t.2 == v)
        uninhabitedUnionField? cx.types uty
          (← fields.findIdx? (fun (field : String × TyId) => field.1 == name)))
    | _ => ("", none)
  if let some (u, f) := hit then
    cx.fail line s!"{what} the noreturn variant '{f}' of union '{u}': the variant has no \
      values, so this code is unreachable in Zig and outside the subset"

mutual

partial def checkInst (cx : CheckCtx) (line : Nat) (inst : Inst) : Except String Nat := do
  checkTy cx.fnName cx.types cx.layouts line inst.ty
  cx.checkBitPtrSource line inst.ty inst.op
  let line ← checkOp cx line inst.ty inst.op cx.tryErrorExits[inst.id]?
  -- Inline asm: A01's operand/effect-contract checks (in `checkOp`, with specific messages) come
  -- first, then the L13 allowlist.
  cx.checkAsmEffect line inst.op
  pure line

partial def checkOp (cx : CheckCtx) (line : Nat) (ty : TyId) (op : Op)
    (cachedTryExit : Option Bool := none) : Except String Nat := do
  let fnName := cx.fnName
  cx.checkVolatile line ty op
  cx.checkPackedLayout line ty op
  cx.checkPaddedAtomic line op
  cx.checkNoreturnVariant line ty op
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
  | .splat _ =>
    -- From Zig 0.17.0 a runtime `@splat` to an array is also `splat`; the model splats vectors only.
    unless (cx.types[ty]? matches some (.vector ..)) do
      cx.fail line "splat to a non-vector (Zig 0.17.0 array splat) is outside the subset"
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
    -- Only Sema's placeholder for a comptime-resolved local makes address 0 a non-allowzero
    -- pointer; `Canon.lean`'s `dropDeadAllocPlaceholders` drops it unless something reads it.
    if (a matches .int _ 0) && singlePtrTy cx.types cx.layouts ty then
      cx.fail line "a read of the address-0 placeholder that the compiler leaves for a comptime-resolved local is outside the subset"
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
      -- A code address carries no data storage: a function pointer may be reinterpreted,
      -- and a call through it dispatches over the table of its type (`.illegal` for any
      -- other block, L11).
      let castCapability (t : TyId) : Option Bool :=
        if (cx.types[t]?.map isFnTy).getD false then some false else hasErrorCapability cx.types t
      match pointerChild aty, pointerChild ty with
      | some source, some target =>
        unless qualifierOnly || optionalWrapOnly do
          let some sourceCap := castCapability source
            | cx.fail line "a pointer cast has unresolved or cyclic symbolic storage provenance"
          let some targetCap := castCapability target
            | cx.fail line "a pointer cast has unresolved or cyclic symbolic storage provenance"
          if sourceCap != targetCap ||
              hasErrorStorage cx.types source != hasErrorStorage cx.types target ||
              ((sourceCap || targetCap) && source != target) then
            cx.fail line "a pointer cast exposing symbolic error storage as numeric or opaque bytes requires finalized error ordinals and is outside the finite error-storage fragment"
          -- Array decay (`*[n]T` to `[*]T`) keeps the item type, so it keeps the decoder.
          if arrayItemTy cx.types source != arrayItemTy cx.types target &&
              (typeReach cx.types source == .symbolic || typeReach cx.types target == .symbolic) then
            cx.fail line symbolicViewMsg
      | none, some target =>
        unless castCapability target == some false do
          cx.fail line "recovering a symbolic error pointer from an integer or opaque value needs unsupported storage provenance"
        if typeReach cx.types target == .symbolic then cx.fail line symbolicViewMsg
      | _, _ => pure ()
    -- Zig 0.17: an array, vector or enum on either side is a logical-bit-order cast
    -- (`Air2Lean/BitCast.lean`); a shape the model lacks is rejected, never translated with the
    -- ≤0.16 memory rules below.
    if let some aty := sourceTy then
      if logicalBitCastApplies cx.zigVersion cx.types aty ty then
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
    -- (`?*T`) is `Option Zig.Ptr` in the model, null = `none` = address 0: a bitcast to another
    -- optional pointer (a `@constCast`) is a no-op, and one from a pointer is Lean's coercion
    -- `Zig.Ptr → Option Zig.Ptr` (wrapping). Up to 0.16.0 (`memoryBitCastVersion`) three more
    -- casts have explicit rules (`ZigLean/Mem/Repr.lean`): `?*T` → `*U` unwraps and requires
    -- non-null (`Zig.optPtrUnwrap`), `?*T` → `usize` gives 0 for null (`Zig.optPtrAddr`), and
    -- `usize` → `?*T` gives null for 0 (`Zig.optPtrFromAddr`). Any other bitcast to or from an
    -- optional pointer is rejected.
    let isOptPtr (t : TyId) : Bool := match cx.types[t]? with
      | some (.optional c) => match cx.types[c]? with | some (.ptr ..) => true | _ => false
      | _ => false
    -- A C/allowzero pointer and an ordinary optional single/many pointer convert with explicit
    -- null mapping (`Zig.ptrToOptional`/`Zig.ptrOfOptional`); address zero is `none`.
    let isOptScalarPtr (t : TyId) : Bool := (cx.types[t]?.map (optScalarPtr cx.types)).getD false
    match sourceTy with
    | some aty =>
      let isPtr (t : TyId) : Bool := match cx.types[t]? with | some (.ptr ..) => true | _ => false
      let isUsize (t : TyId) : Bool := cx.types[t]? == some (.int false 64)
      let memCast := memoryBitCastVersion cx.zigVersion
      let nullable (t : TyId) := nullablePtrTy cx.types cx.layouts t
      -- A nullable pointer is never optional, so at most one side is the optional pointer.
      if (isOptPtr ty && nullable aty) || (isOptPtr aty && nullable ty) then
        unless isOptScalarPtr (if isOptPtr ty then ty else aty) do
          cx.fail line "converting between a C/allowzero pointer and an optional slice is outside the qualified pointer fragment"
        return line
      let unwrapRule := memCast && optSinglePtrTy cx.types cx.layouts aty &&
        (singlePtrTy cx.types cx.layouts ty || isUsize ty)
      let fromAddrRule := memCast && isUsize aty && optSinglePtrTy cx.types cx.layouts ty
      if (isOptPtr aty && !isOptPtr ty && !unwrapRule) ||
          (isOptPtr ty && !isOptPtr aty && !isPtr aty && !fromAddrRule) then
        throw s!"{fnName}: near line {line}: a bitcast between an optional pointer (`?*T`) and \
          another type is outside the subset"
      -- A packed struct or union is a bitcast of its backing integer only (`Zig.Packed`,
      -- `Zig.PackedU`; 0.16.0 builds a packed union from its field this way). Up to 0.16.0 an
      -- array, `extern` struct or `extern` union is a representation cast (`Zig.reprCast`):
      -- encode, then decode the other type from the same bytes, padding bytes undefined.
      if reprCastApplies cx.zigVersion cx.types aty ty then
        let side (t : TyId) : Bool := match cx.types[t]? with
          | some (.int ..) | some (.float _) | some .bool | some (.struct _ "packed" _) => true
          | _ => reprAggregate cx.types t
        unless side aty && side ty do
          cx.fail line "a Zig ≤0.16 representation `@bitCast` between an array, `extern` struct \
            or `extern` union and a type other than an integer, float, `bool`, packed struct, \
            array, `extern` struct or `extern` union is outside the subset"
        let (some abits, some bbits) := (reprBitSize cx.types cx.layouts aty,
            reprBitSize cx.types cx.layouts ty)
          | cx.fail line "a Zig ≤0.16 representation `@bitCast` involving a pointer, an optional \
              pointer or a type without a guaranteed in-memory layout (an `auto` struct, tuple, \
              tagged union, packed union, slice, vector, sentinel array or error storage, at any \
              depth) is outside the subset"
        unless abits == bbits do
          cx.fail line s!"a Zig ≤0.16 representation `@bitCast` between types of {abits} and \
            {bbits} bits (`@bitSizeOf`) is outside the subset"
        checkMemTy fnName cx.types cx.layouts line aty cx.errBits
        checkMemTy fnName cx.types cx.layouts line ty cx.errBits
        return line
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
    -- `undefined` to a packed struct field: `Zig.storeUndefBits` makes only the field's bits
    -- undefined (a local with such a store is a stack block: `escapingAllocs`). A vector lane
    -- (`Zig.storeLane`) has no undefined-bits store.
    if v matches .undef _ && (cx.valTy? ptr).any (laneBitPtrTy cx.layouts) then
      cx.fail line "a store of `undefined` to a vector lane is outside the subset"
    pure line
  | .atomicLoad _ .unordered | .atomicStore _ _ .unordered =>
    cx.fail line "an `unordered` atomic op is outside the subset (it has no read-read coherence)"
  | .atomicLoad ptr _ => cx.memAccess line ptr; cx.atomicChild line ptr; pure line
  | .atomicStore ptr _ _ => cx.memAccess line ptr; cx.atomicChild line ptr; pure line
  | .atomicRmw op _ ptr _ => cx.memAccess line ptr; cx.atomicChild line ptr op; pure line
  | .cmpxchg _ ptr _ _ _ _ => cx.memAccess line ptr; cx.atomicChild line ptr; pure line
  | .fieldPtr base _ =>
    if let .inst b := base then
      if cx.places.contains b then return line
    -- A field pointer into memory needs the field offsets.
    let pty ← cx.memPtrTy line base
    checkMemTy fnName cx.types cx.layouts line ((ptrChild cx.types pty).get!) cx.errBits
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
    checkMemTy fnName cx.types cx.layouts line parent cx.errBits
    pure line
  | .ptrElemVal p _ => cx.itemAccess line p; pure line
  | .memset p _ => cx.rejectNullableProjection line p; cx.itemAccess line p; pure line
  | .ptrAdd _ p _ | .elemPtr p _ =>
    if let .elemPtr _ idx := op then
      if laneBitPtrTy cx.layouts ty then
        cx.lanePtr line ty p idx
        return line
    -- The result is a pointer to an item: its child is the item type.
    if let some pty := cx.valTy? p then
      if let some (.ptr "one" _ c) := cx.types[pty]? then
        if let some (.vector ..) := cx.types[c]? then
          cx.itemAccess line p
    let some child := ptrChild cx.types ty
      | cx.fail line "pointer arithmetic result is not a pointer"
    cx.knownSize line child
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
    let pty ← cx.memPtrTy line p
    -- The emitted slice takes its length from the pointee (`FCtx.itemsOf`).
    match (ptrChild cx.types pty).bind (cx.types[·]?) with
    | some (.array ..) | some (.vector ..) => pure line
    | _ => cx.fail line "`array_to_slice` operand is not a pointer to an array"
  | .call callee _ =>
    match callee with
    | .func name true .. =>
      if let some symbol := externSymbol? name then
        throw s!"{fnName}: near line {line}: a call to the noreturn extern function '{symbol}' \
          is outside the subset (docs/air-json.md §Extern calls)"
      if (panicErrorFor? name).isNone then
        throw s!"{fnName}: near line {line}: noreturn callee '{name}' is not a known \
          panic-handler function (docs/generated-code.md §Panics)"
      pure line
    | .func .. => pure line
    -- A pointer to a function (`checkTy`), from an instruction or a constant address:
    -- `Emit.lean` dispatches on the address-taken functions of its type (`fnRefs`), and
    -- `checkIndirectCallTarget` rejects a provably unknown or incompatible fixed address (L11).
    | .inst _ | .ptrConst .. => pure line
    | _ => throw s!"{fnName}: near line {line}: an indirect call through a constant that is \
        not a function address is outside the subset"
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
    checkMemTy fnName cx.types cx.layouts line unionTy cx.errBits
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
  | .asm source isVolatile clobbers outputs inputs =>
    if op.isSpinHint && cx.types[ty]? != some .void then
      throw s!"{fnName}: near line {line}: a spin hint must return void"
    -- Register operands (M21) and the explicit effect contract (A01, `Air2Lean/AsmContract.lean`):
    -- every operand value is an integer, so `Emit.lean` can map it to a `BitVec`.
    let isIntTy (tid : TyId) : Bool := match cx.types[tid]? with | some (.int ..) => true | _ => false
    if clobbers.contains "memory" &&
        (asmPureEntry? source isVolatile clobbers outputs inputs).isNone then
      throw s!"{fnName}: near line {line}: an asm 'memory' clobber is outside the subset (M21): \
        it may write any memory, and no reviewed registry entry declares this block pure \
        (`Air2Lean/AsmContract.lean`'s `asmPureRegistry`)"
    -- One output can be the expression's own result (`-> T`, no `ref`); every other output
    -- is a store through its pointer `ref` (an lvalue output).
    let mut parsed : Array AsmOutput := #[]
    for o in outputs do
      let some po := parseAsmOutput o.constraint
        | throw s!"{fnName}: near line {line}: asm output constraint '{o.constraint}' is not a \
          register, read-write or memory output constraint (M21, A01)"
      parsed := parsed.push po
      let outTy ← match o.ref with
        | none =>
          if po.isEffect then
            throw s!"{fnName}: near line {line}: asm output '{o.name}' with constraint \
              '{o.constraint}' needs an lvalue operand: a read-write or memory output has a \
              location (A01)"
          pure ty
        | some r =>
          let some pty := cx.valTy? r
            | cx.fail line s!"asm output '{o.name}': operand has no known type"
          let some c := ptrChild cx.types pty
            | cx.fail line s!"asm output '{o.name}' is not a pointer"
          if (cx.layouts[pty]?.map (·.hostSize)).getD 0 != 0 then
            cx.fail line s!"asm output '{o.name}' is a bit-pointer"
          if let some (.ptr _ true _) := cx.types[pty]? then
            cx.fail line s!"asm output '{o.name}' writes through a const pointer"
          cx.memAccess line r
          pure c
      if !isIntTy outTy then
        throw s!"{fnName}: near line {line}: asm output is not an integer register value (M21)"
      if po.memory then
        match cx.types[outTy]? with
        | some (.int _ b) =>
          unless [8, 16, 32, 64].contains b do
            throw s!"{fnName}: near line {line}: asm memory output '{o.name}' is a {b}-bit \
              integer, not a whole 1, 2, 4 or 8 byte memory operand (A01)"
        | _ => pure ()
    if (outputs.filter (·.ref.isNone)).size > 1 then
      cx.fail line "an asm expression with two result outputs (malformed input in the AIR file)"
    -- Aliases (A01): two outputs that write the same local (or the same pointer value) leave the
    -- final value to the instructions' store order, which the contract does not fix.
    let written := outputs.filterMap (·.ref)
    let root? (v : Val) : Option InstId := match v with
      | .inst id => (cx.localRoots.find? (·.1 == id)).map (·.2)
      | _ => none
    for h : a in [0:written.size] do
      for h' : b in [a + 1:written.size] do
        let same := written[a] == written[b] ||
          match root? written[a], root? written[b] with
          | some x, some y => x == y
          | _, _ => false
        if same then
          throw s!"{fnName}: near line {line}: two asm outputs write the same location: their \
            final value depends on the store order, which the asm contract does not fix (A01)"
    -- Pinned registers and clobbers (A01): a clobbered register cannot also carry an operand,
    -- two outputs (or two inputs) cannot share one pinned register, and an input cannot share an
    -- early-clobber output's register.
    let family? (pin : Option String) : Option Nat := pin.bind x86RegFamily
    let clobbered := clobbers.filterMap x86RegFamily
    let outPins := parsed.filterMap fun po => family? po.pin
    let inputPin? (c : String) : Option Nat := (asmRegBody? c).bind family?
    let inPins := inputs.filterMap fun i => inputPin? i.constraint
    let dup (xs : Array Nat) : Bool := xs.zipIdx.any fun (x, k) => (xs.extract 0 k).contains x
    if (outPins ++ inPins).any clobbered.contains then
      throw s!"{fnName}: near line {line}: an asm clobber names a register that also carries an \
        operand (A01)"
    if dup outPins || dup inPins then
      throw s!"{fnName}: near line {line}: two asm outputs or two inputs pin the same register \
        (A01)"
    -- An early-clobber output is written before the inputs are read; a read-write output's
    -- register already holds its old value. Neither can also hold an input.
    let busyPins := parsed.filterMap fun po =>
      if po.earlyClobber || po.readWrite then family? po.pin else none
    if inPins.any busyPins.contains then
      throw s!"{fnName}: near line {line}: an asm input pins the register of an early-clobber \
        or read-write output (A01)"
    for i in inputs do
      let tied := match i.constraint.toNat? with
        | some k => (parsed[k]?).map fun po => !po.readWrite && !po.memory && !po.earlyClobber
        | none => none
      if tied == some false then
        throw s!"{fnName}: near line {line}: asm input constraint '{i.constraint}' ties to a \
          read-write, memory or early-clobber output (A01)"
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

/-- `undefined` in an instruction operand is never replaced by a default (`0`, `false`) that a
later read could observe. A store writes undefined bytes: a wholly `undefined` value
(`Zig.storeUndef`) and a partly `undefined` one, whose undefined items and fields at any depth
(`undefByteRanges`) are undefined bytes of the one store. Its place becomes a stack block
(`escapingAllocs`). `memset` of a wholly `undefined` item writes undefined bytes. Every other
`undefined` operand (a call argument, a return or block result, an `aggregate_init` element,
an arithmetic, `select` or atomic operand, a partly `undefined` `memset` item, an `undefined`
`shuffle` lane) has no explicit form in a value and is outside the subset, except
`Thread.spawn`'s `SpawnConfig`, which the model does not read. `tyOf` is the operand's type. -/
def checkUndefOperands (f : Func) (tyOf : Val → Option TyId) (i : Inst) : Except String Unit := do
  let fail {α : Type} (what : String) : Except String α :=
    throw s!"{f.name}: inst {i.id}: {what} is outside the subset (`undefined` is never read as \
      a default; only a store or `memset` writes it, as undefined bytes)"
  let hasUndef (v : Val) : Bool := match v with
    | .undef _ => true
    | v => v.hasNestedUndef
  let (written, rest) : Option Val × Array Val := match i.op with
    | .store p v => (some v, #[p])
    | .memset p v => (some v, #[p])
    -- `Thread.spawn`'s `SpawnConfig` is not a value of the model (`FCtx.threadCall`); the
    -- fallible policy reads its fields and rejects an `undefined` one.
    | .call callee@(.func name ..) args =>
      (none, #[callee] ++ if threadFn? name == some .spawn then args.extract 1 else args)
    | op => (none, valueOperands op ++ ptrOperands op)
  if rest.any hasUndef then fail "an `undefined` operand"
  if let .shuffle _ _ mask := i.op then
    if mask.any (· matches .undef) then fail "an `undefined` `shuffle` lane"
  let some v := written | return
  unless v.hasNestedUndef do return
  if let .memset .. := i.op then fail "a `memset` of a partly `undefined` item"
  let some pty := (rest[0]?).bind tyOf | fail "a store of a partly `undefined` value"
  if (f.layouts[pty]?.map (·.hostSize)).getD 0 != 0 then
    fail "a store of a partly `undefined` value to a packed struct field"
  let some child := ptrChild f.types pty | fail "a store of a partly `undefined` value"
  if (undefByteRanges f.types f.layouts child v).isNone then
    fail "a store of a value with an `undefined` part under an optional, error union, union, \
      slice, vector or packed struct"

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
  let (size, _) ← (modelLayout f.types f.layouts root f.errorSetBits).toOption
  if off > size || width > size - off then return (remaining, false)
  if width == 0 || !hasErrorStorage f.types root then return (remaining, true)
  let recur (child base : Nat) : Option (Nat × Bool) := do
    let (childSize, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
    let lo := Nat.max off base
    let hi := Nat.min (off + width) (base + childSize)
    if hi ≤ lo then return (remaining, true)
    errorFreeGlobalRange f child (lo - base) (hi - lo) remaining
  match ← f.types[root]? with
  | .errorSet _ => return (remaining, false)
  | .optional child => recur child 0
  | .errorUnion _ payload =>
    let (size, align) ← (modelLayout f.types f.layouts payload f.errorSetBits).toOption
    let (code, base) := Zig.errUnionOffsetsW f.errorSetBits size align
    if off < code + Zig.errCodeSize f.errorSetBits && code < off + width then return (remaining, false)
    recur payload base
  | .array len child sentinel =>
    let (stride, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
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
      let (childSize, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
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
    let (size, align) ← (modelLayout f.types f.layouts payload f.errorSetBits).toOption
    let (code, base) := Zig.errUnionOffsetsW f.errorSetBits size align
    if off == code && compatibleType f f set target then return (remaining, true)
    if off < base then return (remaining, false)
    matchingGlobalSubobject f payload (off - base) target remaining
  | .array len child sentinel =>
    let (stride, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
    if stride == 0 || off / stride ≥ len + (if sentinel then 1 else 0) then return (remaining, false)
    matchingGlobalSubobject f child (off % stride) target remaining
  | .struct _ _ fields =>
    let offsets := (f.layouts[root]?.getD {}).offsets
    if offsets.size != fields.size || fields.size > remaining then none
    for ((_, child), k) in fields.zipIdx do
      let base := offsets[k]!
      let (childSize, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
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
    match (modelLayout f.types f.layouts child f.errorSetBits).toOption with
    | some (stride, _) => stride != 0 && off % stride == 0 &&
        off / stride < len + (if sentinel then 1 else 0) && compatibleType f f child target
    | none => false
  | _ => false

/-- Whether a value of type `id` holds, by value, an error union whose payload has nonzero size
and alignment below the error code's (2 for the default 16-bit error integer, `Zig.errCodeAlign`
of the profile's `error_set_bits` in general). Zig 0.14.1–0.17.0's LLVM backend
(`codegen/llvm.zig` `lowerPtr`) measures an `eu_payload` constant base with the error union type
instead of its payload, so it addresses such a payload at the error code
(`Zig.ConstPtr.llvmPayloadOffset_ne_iff`, `tests/roadmap/const-bases`). A shared budget bounds the
scan; `none` means unknown. -/
private partial def llvmPayloadTypeScan (f : Func) (id fuel : Nat) : Option (Nat × Bool) := do
  if fuel == 0 then none
  let mut remaining := fuel - 1
  match ← f.types[id]? with
  | .errorUnion _ payload =>
    let (size, align) ← (modelLayout f.types f.layouts payload f.errorSetBits).toOption
    if size != 0 && align < Zig.errCodeAlign f.errorSetBits then return (remaining, true)
    llvmPayloadTypeScan f payload remaining
  | ty =>
    for child in valueChildTys ty do
      let (next, hit) ← llvmPayloadTypeScan f child remaining
      remaining := next
      if hit then return (remaining, true)
    return (remaining, false)

/-- Whether byte `off` of a value of type `id` (a one-past-the-end address included) can lie in
an affected payload (`llvmPayloadTypeScan`). Every struct/tuple field or array item whose range
contains `off` is visited, so a folded offset is never attributed to only one candidate. Union
members are not reconstructed from an address: a union with an affected member counts. -/
private partial def llvmPayloadOffsetScan (f : Func) (id off fuel : Nat) : Option (Nat × Bool) := do
  if fuel == 0 then none
  let mut remaining := fuel - 1
  let (size, _) ← (modelLayout f.types f.layouts id f.errorSetBits).toOption
  if off > size then return (remaining, false)
  let within (members : Array (TyId × Nat)) : Option (Nat × Bool) := do
    let mut remaining := remaining
    for (child, base) in members do
      let (childSize, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
      if base ≤ off && off ≤ base + childSize then
        let (next, hit) ← llvmPayloadOffsetScan f child (off - base) remaining
        remaining := next
        if hit then return (remaining, true)
    return (remaining, false)
  match ← f.types[id]? with
  | .errorUnion _ payload =>
    let (payloadSize, payloadAlign) ← (modelLayout f.types f.layouts payload f.errorSetBits).toOption
    let (_, po) := Zig.errUnionOffsetsW f.errorSetBits payloadSize payloadAlign
    if po ≤ off && off ≤ po + payloadSize && payloadSize != 0 &&
        payloadAlign < Zig.errCodeAlign f.errorSetBits then
      return (remaining, true)
    within #[(payload, po)]
  | .optional child =>
    match f.types[child]? with
    | some (.ptr ..) | some (.errorSet _) => return (remaining, false)
    | _ => within #[(child, 0)]
  | .array len child sentinel =>
    let (stride, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
    if stride == 0 then return (remaining, false)
    let count := len + (if sentinel then 1 else 0)
    let k := off / stride
    -- `off` can start item `k` and end item `k - 1`.
    let items := (if k < count then #[(child, k * stride)] else #[]) ++
      (if off % stride == 0 && 0 < k && k ≤ count then #[(child, (k - 1) * stride)] else #[])
    within items
  | .struct _ layout fields =>
    if layout == "packed" then return (remaining, false)
    let offsets := (f.layouts[id]?.getD {}).offsets
    if offsets.size != fields.size then none
    within (fields.zipIdx.map fun ((_, child), k) => (child, offsets[k]!))
  | .tuple fields =>
    let offsets := (f.layouts[id]?.getD {}).offsets
    if offsets.size != fields.size then none
    within (fields.zipIdx.map fun (child, k) => (child, offsets[k]!))
  | .union .. => llvmPayloadTypeScan f id remaining
  | _ => return (remaining, false)

/-- The backends whose `lowerPtr` measures an `eu_payload` base with the error union type
instead of its payload: `codegen/llvm.zig` (Zig 0.14.1–0.17.0) and `codegen/wasm/CodeGen.zig`
(observed in 0.16.0). -/
def euPayloadMisplacedBackends : List String := ["stage2_llvm", "stage2_wasm"]

/-- Fail closed for the misplaced `eu_payload` constants of the LLVM and wasm backends
(`euPayloadMisplacedBackends`): a pointer constant on such a profile cannot address (or end) an
affected payload of its global. Other backends lower these constants with the payload offset
that the model uses. -/
private def checkLlvmPayloadConstant (f : Func) (g off : Nat) (global : Global) :
    Except String Unit := do
  unless euPayloadMisplacedBackends.contains f.backend do return
  let affected : Bool := match llvmPayloadTypeScan f global.ty 1024 with
    | some (_, false) => false
    | _ => ((llvmPayloadOffsetScan f global.ty off 1024).map (·.2)).getD true
  if affected then
    throw s!"{f.name}: a pointer constant at offset {off} of global {g} may address an \
      alignment-1 error-union payload, which this backend lowers at the error code \
      (codegen/llvm.zig and codegen/wasm/CodeGen.zig lowerPtr eu_payload); such constants are \
      outside the {f.backend} profile"

/-- A constant pointer stays within its global or one past its end. -/
private def checkGlobalOffset (f : Func) (g off : Nat) (global : Global) : Except String Unit := do
  if let some (.func ..) := global.init then return
  if let .ok (size, _) := modelLayout f.types f.layouts global.ty f.errorSetBits then
    if off > size then
      throw s!"{f.name}: a pointer constant at offset {off} is outside global {g} ({size} \
        bytes); constant provenance ends one past its object"

private def checkGlobalAliasAt (f : Func) (pty g off : Nat) : Except String Unit := do
  let some global := f.globals[g]? | throw s!"{f.name}: pointer has unknown global id {g}"
  checkGlobalOffset f g off global
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
  let some capability := hasErrorCapability f.types child
    | throw s!"{f.name}: global alias has unresolved or cyclic symbolic storage provenance"
  if !hasErrorStorage f.types global.ty && !capability then return
  checkMemTy f.name f.types f.layouts 0 global.ty f.errorSetBits
  checkMemTy f.name f.types f.layouts 0 child f.errorSetBits
  let (size, _) ← (modelLayout f.types f.layouts child f.errorSetBits).mapError fun e => s!"{f.name}: {e}"
  let pointerLayout := globalAliasPointerLayout f pty
  let width := if pointerLayout.hostSize == 0 then size else pointerLayout.hostSize
  let (globalSize, _) ← (modelLayout f.types f.layouts global.ty f.errorSetBits).mapError fun e => s!"{f.name}: {e}"
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

/-- `checkLlvmPayloadConstant` for every pointer constant in `v`, slices and aggregates
included. A profile limit, so it runs with the constant checks, not structural validation. -/
private partial def checkLlvmPayloadConstants (f : Func) (v : Val) (fuel : Nat := 256) :
    Except String Unit := do
  unless euPayloadMisplacedBackends.contains f.backend do return
  if fuel == 0 then throw s!"{f.name}: pointer constant traversal exceeds 256 levels"
  match v with
  | .ptrConst _ g off =>
    if let some global := f.globals[g]? then checkLlvmPayloadConstant f g off global
  | .agg _ vs => vs.forM fun v => checkLlvmPayloadConstants f v (fuel - 1)
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => checkLlvmPayloadConstants f v (fuel - 1)
  | .sliceConst _ p n => checkLlvmPayloadConstants f p (fuel - 1); checkLlvmPayloadConstants f n (fuel - 1)
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
      let (size, align) ← (modelLayout f.types f.layouts payload f.errorSetBits).toOption
      let (code, base) := Zig.errUnionOffsetsW f.errorSetBits size align
      let delta := match i.op with | .errCodePtr _ => code | _ => base
      some (g, off + delta)
    | .ptrAdd sub p n =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      let .int _ k := n | none
      if k < 0 then none else
      let (_, child) ← globalAliasPointer? f i.ty
      let (size, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
      let delta := k.toNat * size
      if sub then if off < delta then none else some (g, off - delta)
      else some (g, off + delta)
    | .elemPtr p n =>
      let (g, off) ← fixedGlobalOrigin? f insts p (fuel - 1)
      -- A lane pointer is the vector's address (`CheckCtx.lanePtr`).
      if laneBitPtrTy f.layouts i.ty then return (g, off)
      let .int _ k := n | none
      if k < 0 then none else
      let (_, child) ← globalAliasPointer? f i.ty
      let (size, _) ← (modelLayout f.types f.layouts child f.errorSetBits).toOption
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

/-- L11: an indirect callee whose address is a fixed global (`fixedGlobalOrigin?`) must be
the exact zero-offset address of a named function block of the callee's function type.
Any other fixed address is provably an unknown executable address or a target of an
incompatible signature, rejected here. A callee without a fixed origin dispatches at
runtime over the address-taken functions of its type (`Emit.lean`); any other address
throws `.illegal` there. -/
private def checkIndirectCallTarget (f : Func) (insts : Array Inst) (i : Inst) :
    Except String Unit := do
  let .call callee _ := i.op | return
  unless callee.isIndirectCallee do return
  let calleeTy? : Option TyId := match callee with
    | .inst id => (insts.find? (·.id == id)).map (·.ty)
    | v => v.constTy?
  -- A non-function instruction callee is reported by the program check.
  let some tn := calleeTy?.bind (fnPtrTyName? f.types)
    | if callee matches .inst _ then return
      else throw s!"{f.name}: inst {i.id}: a constant indirect callee is not a function pointer"
  let some (g, off) := fixedGlobalOrigin? f insts callee | return
  let unknown : Except String Unit :=
    throw s!"{f.name}: inst {i.id}: indirect callee is the fixed address {off} of global {g}, \
      not a function block (an unknown executable address)"
  let some global := f.globals[g]? | unknown
  let some (.func name ..) := global.init | unknown
  unless off == 0 do unknown
  unless f.types[global.ty]? == some (.other tn) do
    throw s!"{f.name}: inst {i.id}: indirect callee '{name}' has an incompatible signature \
      (called through '{tn}')"

/-- L11: a function-pointer value is the address of a function block (`&f`, a `ptrConst`),
which resolves through the callable-address table. A bare function constant outside a callee
or call argument (whose check is `checkCallSignature`) has no address in the model. -/
private def checkFunctionValues (f : Func) (i : Inst) : Except String Unit := do
  if let .call .. := i.op then return
  let rec bare (fuel : Nat) (v : Val) : Bool :=
    match fuel, v with
    | 0, _ => true
    | _, .func .. => true
    | fuel + 1, .agg _ vs => vs.any (bare fuel)
    | fuel + 1, .optSome _ v | fuel + 1, .errUnionOk _ v | fuel + 1, .unionVal _ _ v => bare fuel v
    | fuel + 1, .sliceConst _ p n => bare fuel p || bare fuel n
    | _, _ => false
  if (valueOperands i.op ++ ptrOperands i.op).any (bare 256) then
    throw s!"{f.name}: inst {i.id}: a function used as a value is outside the subset (its \
      address `&f` resolves through the callable-address table)"

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
  checkLlvmPayloadConstants f v
  if let .ptrConst pty g _ := v then
    let pa := (f.layouts[pty]?.bind (·.ptrAlign)).getD 1
    let ga := (f.globals[g]?.bind (f.layouts[·.ty]?)).bind (·.align) |>.getD 1
    if pa > ga then throw (alignment pa ga)

/-- An `extern` global has no initial value in the program: `mem0` takes it as an explicit
field of `ExternInit` (`docs/generated-code.md` §Globals). Only a named, pointer-free and
error-free type whose bytes the model encodes qualifies. -/
private def checkExternGlobal (f : Func) (g : Global) (what : String) : Except String Unit := do
  let fail (why : String) : Except String Unit :=
    throw s!"{f.name}: `extern` global {what}: {why}; external initial state is an explicit \
      `ExternInit` parameter of `mem0` only for named, pointer-free, error-free storage"
  if g.name.isNone then fail "it has no name"
  if g.init.isSome then fail "the AIR file gives it an initial value"
  if (f.types[g.ty]?.map isFnTy).getD true then fail "it is a function or has an unknown type"
  if (pointerFreeInitializerType f g.ty 1024).isNone then
    fail "its type can hold a pointer, a union or an unresolved type"
  if hasErrorStorage f.types g.ty then fail "its type holds error storage"
  checkTy f.name f.types f.layouts 0 g.ty
  checkMemTy f.name f.types f.layouts 0 g.ty f.errorSetBits

/-- A `threadlocal var` (`docs/generated-code.md` §Thread-local storage): one instance per
thread, initialized from the global's initial value. Only a named, non-`extern` `var` with a
resolved, wholly defined or wholly `undefined` initial value of a pointer-free, error-free type
that the model encodes qualifies. -/
private def checkThreadlocalGlobal (f : Func) (g : Global) (what : String) : Except String Unit := do
  let fail (why : String) : Except String Unit :=
    throw s!"{f.name}: `threadlocal` global {what}: {why}; a thread-local instance is modelled \
      only for a named, non-`extern` `var` with an initial value in pointer-free, error-free \
      storage"
  if g.name.isNone then fail "it has no name"
  if g.isExtern then fail "it is `extern` (its instances are defined outside the program)"
  if g.isConst then fail "it is `const`"
  let some init := g.init | fail "the AIR file has no initial value"
  if init.hasNestedUndef then fail "a partly `undefined` initial value"
  if (f.types[g.ty]?.map isFnTy).getD true then fail "it is a function or has an unknown type"
  if (pointerFreeInitializerType f g.ty 1024).isNone then
    fail "its type can hold a pointer, a union or an unresolved type"
  if hasErrorStorage f.types g.ty then fail "its type holds error storage"
  checkNullConstants f.name f.types f.layouts init
  checkTy f.name f.types f.layouts 0 g.ty
  checkMemTy f.name f.types f.layouts 0 g.ty

/-- The globals that the pointer constants of `v` point into, at any depth. -/
partial def Val.ptrGlobals (v : Val) : Array Nat :=
  match v with
  | .ptrConst _ g _ => #[g]
  | .agg _ elems => elems.flatMap Val.ptrGlobals
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => v.ptrGlobals
  | .sliceConst _ p l => p.ptrGlobals ++ l.ptrGlobals
  | _ => #[]

/-- A constant pointer has one address in every thread, so it cannot point into a `threadlocal`
global (0.14.1 writes the address of a thread-local as a constant). -/
private def checkNoThreadlocalConstant (f : Func) (v : Val) : Except String Unit := do
  for g in v.ptrGlobals do
    if let some global := f.globals[g]? then
      if global.threadlocal then
        throw s!"{f.name}: a constant pointer to the `threadlocal` global \
          {global.name.getD "an unnamed global"} is outside the subset (each thread has its own \
          instance; only `runtime_nav_ptr` addresses it)"

/-- `runtime_nav_ptr` (`Op.runtimeNavPtr`): the current thread's instance of a `threadlocal`
global, as a single-item pointer to the global's type with at most its alignment. A run-time
address of anything else (an `extern` the compiler reaches at run time, a DLL import, a
PC-relative `@extern`) is outside the subset. -/
private def checkRuntimeNavPtr (f : Func) (i : Inst) (g : Nat) : Except String Unit := do
  let some global := f.globals[g]?
    | throw s!"{f.name}: inst {i.id}: `runtime_nav_ptr` names no global (malformed input in the \
        AIR file)"
  unless global.threadlocal do
    throw s!"{f.name}: inst {i.id}: `runtime_nav_ptr` of {global.name.getD "an unnamed global"}, \
      which is not `threadlocal` (a run-time address of an `extern`, a DLL import or a \
      PC-relative `@extern`), is outside the subset"
  let some (.ptr "one" _ child) := f.types[i.ty]?
    | throw s!"{f.name}: inst {i.id}: `runtime_nav_ptr` must have a single-item pointer type"
  unless child == global.ty do
    throw s!"{f.name}: inst {i.id}: `runtime_nav_ptr` must point to its global's type"
  let some l := f.layouts[i.ty]?
    | throw s!"{f.name}: inst {i.id}: `runtime_nav_ptr` has no pointer layout"
  if l.isVolatile || l.allowzero || l.sentinel || l.hostSize != 0 then
    throw s!"{f.name}: inst {i.id}: a volatile, allowzero, sentinel or bit-pointer to a \
      `threadlocal` global is outside the subset"
  let pa := l.ptrAlign.getD 1
  let ga := (f.layouts[global.ty]?.bind (·.align)).getD 1
  if pa > ga then
    throw s!"{f.name}: inst {i.id}: a pointer with `align({pa})` to a `threadlocal` global of \
      alignment {ga} is outside the subset"

/-- A global that a pointer constant points into: a `var` or `const` with its initial value, in a
type that the model encodes, or an `extern` global (`checkExternGlobal`). An array with a
sentinel is encoded with the sentinel. A wholly `undefined` initial value is undefined bytes; a
partly `undefined` one is rejected, never replaced by a default. -/
def checkGlobal (f : Func) (g : Global) : Except String Unit := do
  let what := g.name.getD "an unnamed constant"
  if g.threadlocal then return ← checkThreadlocalGlobal f g what
  if g.isExtern then return ← checkExternGlobal f g what
  let some init := g.init
    | throw s!"{f.name}: global {what}: the AIR file has no initial value"
  if init.hasNestedUndef then
    throw s!"{f.name}: global {what}: a partly `undefined` initial value is outside the subset \
      (only a wholly `undefined` global is modelled, as undefined bytes)"
  checkNullConstants f.name f.types f.layouts init
  checkGlobalAliasConstants f init
  checkLlvmPayloadConstants f init
  if f.globals.any (fun g => hasErrorStorage f.types g.ty) &&
      ((init.constTy?).map (fun t => carriesPointer f t)).getD false &&
      dependsOnErrorGlobal f f.allInsts init then
    throw s!"{f.name}: a global initializer cannot retain a pointer into an error-bearing global"
  checkPointerPresence init fun k =>
    s!"{f.name}: global {what}: a pointer constant without a global ({k}) is outside the subset"
  -- A function: a function pointer points to it (a 1-byte block, `Emit.lean`).
  if let .func .. := init then return
  checkTy f.name f.types f.layouts 0 g.ty
  checkMemTy f.name f.types f.layouts 0 g.ty f.errorSetBits

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

/-- An unverified bit-pointer parameter (`unverifiedBitPtrError`). -/
private def checkBitPtrParam (f : Func) (p : TyId) : Except String Unit :=
  if unverifiedBitPtrTy f.layouts p then throw (unverifiedBitPtrError f.name 0 "a parameter")
  else pure ()

/-- An unverified bit-pointer constant operand (`unverifiedBitPtrError`). -/
private def checkBitPtrConstant (f : Func) (v : Val) : Except String Unit :=
  match v.constTy? with
  | some vty =>
    if unverifiedBitPtrTy f.layouts vty then throw (unverifiedBitPtrError f.name 0 "a constant")
    else pure ()
  | none => pure ()

/-- A big-endian profile (T03, `ZigLean/Endian.lean`) parameterizes the byte order of
integers, floats, slices, enums, packed structs (their backing integer and bit-pointer hosts),
whole-byte vector lanes and every aggregate built from them. The rest is unqualified on a
big-endian target and fails closed (`docs/profiles.md` §Byte order). -/
def checkBigEndian (f : Func) (insts : Array Inst) : Except String Unit := do
  let fail {α : Type} (what : String) : Except String α :=
    throw s!"{f.name}: {what} is outside the qualified big-endian model (`docs/profiles.md` §Byte order)"
  unless f.errorSetBits == 16 do fail s!"error_set_bits {f.errorSetBits}"
  for t in f.types do
    match t with
    | .float 80 => fail "`f80`"
    | .union _ "packed" none _ => fail "a `packed union`"
    | .vector _ c =>
      match f.types[c]? with
      | some (.int _ bits) => unless bits % 8 == 0 do fail "a vector of non-byte-multiple lanes"
      | some (.float 80) => fail "a vector of `f80` lanes"
      | some (.float _) => pure ()
      | _ => fail "a vector of `bool` or pointer lanes"
    | _ => pure ()
  let tyOf (v : Val) : Option TyId := match v with
    | .inst id => (insts.find? (·.id == id)).map (·.ty)
    | v => v.constTy?
  let packedPtr (t : TyId) : Bool := match f.types[t]? with
    | some (.ptr _ _ s) => match f.types[s]? with
      | some (.struct _ "packed" _) => true
      | _ => false
    | _ => false
  let hostOf (t : TyId) : Nat := (f.layouts[t]?.map (·.hostSize)).getD 0
  for i in insts do
    match i.op with
    | .atomicLoad .. | .atomicStore .. | .atomicRmw .. | .cmpxchg .. => fail "an atomic op"
    | .asm .. => fail "inline assembly"
    | .tagName _ => fail "`@tagName`"
    | .errorName _ => fail "`@errorName`"
    | .call (.func callee ..) _ =>
      if modelledStdFn callee then fail s!"the std model '{callee}'"
    -- The little-endian byte offset of a byte-aligned packed field (`FCtx.fieldOffsetIn`).
    | .fieldPtr b _ =>
      if (tyOf b).any packedPtr && hostOf i.ty == 0 then fail "a byte pointer to a packed struct field"
    | .fieldParentPtr p _ =>
      if packedPtr i.ty && (tyOf p).all (hostOf · == 0) then
        fail "`@fieldParentPtr` from a byte pointer to a packed struct field"
    | _ => pure ()

/-- Reject anything `Emit.lean` cannot translate: see the module doc. `device`: the
`--device-contract` (`CheckCtx.device`). -/
def check (f : Func) (device : Option DeviceContract := none) : Except String Unit := do
  validateTypeGraph f.name f.types
  if f.bigEndian then checkBigEndian f f.allInsts
  for p in f.params do
    checkTy f.name f.types f.layouts 0 p
    checkBitPtrParam f p
  checkTy f.name f.types f.layouts 0 f.ret
  -- An `extern` or `packed` union is its bytes, also as a value: the model must encode it.
  for (t, id) in f.types.zipIdx do
    if let .union _ _ none _ := t then
      checkMemTy f.name f.types f.layouts 0 id f.errorSetBits
  let insts := f.allInsts
  -- The 32-bit pointer model (`ZigLean/Mem/Width.lean`) parameterizes pointers, slices,
  -- `usize` and allocation; the ops below remain 64-bit only.
  let ptrBytes := ptrBytesOf f.layouts
  if ptrBytes != 8 then
    for i in insts do
      let what? : Option String := match i.op with
        | .atomicLoad .. | .atomicStore .. | .atomicRmw .. | .cmpxchg .. => some "an atomic op"
        | .tagName _ => some "`@tagName`"
        | .errorName _ => some "`@errorName`"
        | .asm .. => some "inline assembly"
        | _ => none
      if let some what := what? then
        throw s!"{f.name}: {what} is outside the {8 * ptrBytes}-bit pointer model"
  let errorGlobals := f.globals.any (fun g => hasErrorStorage f.types g.ty)
  let escaping := escapingAllocs f
  let localRoots := placeRoots insts
  let places := localRoots.filterMap fun (p, r) => if escaping.contains r then none else some p
  -- An escaping local is a stack block, a byte local is the bytes of its value: its type must
  -- be one the model encodes.
  let bytesLocals := byteLocals f
  for i in insts do
    if let .alloc := i.op then
      if escaping.contains i.id || bytesLocals.contains i.id then
        if let some c := ptrChild f.types i.ty then
          checkMemTy f.name f.types f.layouts 0 c f.errorSetBits
  for g in f.globals do
    checkGlobal f g
    if let some init := g.init then checkNoThreadlocalConstant f init
  let mut checkedConstTypes : Std.HashSet TyId := {}
  for i in insts do
    if let .runtimeNavPtr g := i.op then checkRuntimeNavPtr f i g
    checkErrorGlobalInstruction errorGlobals f insts i
    checkIndirectCallTarget f insts i
    checkFunctionValues f i
    checkUndefOperands f (fun v => match v with
      | .inst id => (insts.find? (·.id == id)).map (·.ty)
      | v => v.constTy?) i
    for v in valueOperands i.op ++ ptrOperands i.op do
      if let some vty := v.constTy? then
        unless checkedConstTypes.contains vty do
          checkTy f.name f.types f.layouts 0 vty
          checkedConstTypes := checkedConstTypes.insert vty
      checkBitPtrConstant f v
      checkNullConstants f.name f.types f.layouts v
      checkNoThreadlocalConstant f v
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
                         errBits := f.errorSetBits,
                         instTys := insts.map fun i => (i.id, i.ty), places, tryErrorExits,
                         localRoots, localPaths := localPlacePaths f.types f.layouts insts,
                         zigVersion := f.zigVersion, device, targetArch := f.targetArch }
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

private def OperandTypes.calleeFnTy? (index : OperandTypes) (f : Func) (callee : Val) :
    Option String := do
  unless callee.isIndirectCallee do none
  fnPtrTyName? f.types (← index.valTy? callee)

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
  | .unionVal _ field payload, .union name _ _ fields =>
    let some (fname, ty) := fields[field]? | fail
    if uninhabitedTy f.types ty then
      throw s!"{f.name}: a constant of union '{name}' with the noreturn variant '{fname}' active \
        is outside the subset (the variant has no values)"
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
    unless f.types[nty]? == some (.int false (8 * ptrBytesOf f.layouts)) do fail
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
  -- Debug instructions bind no value: the emitter has no name for a reference to one.
  let mut debugIds : Std.HashSet InstId := {}
  for i in insts do
    if ids.contains i.id then throw s!"{f.name}: duplicate instruction id {i.id}"
    ids := ids.insert i.id
    match i.op with
    | .dbg .. | .line _ => debugIds := debugIds.insert i.id
    | _ => pure ()
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
      | .inst id =>
        unless ids.contains id do throw s!"{f.name}: unknown instruction ref {id}"
        if debugIds.contains id then
          throw s!"{f.name}: instruction ref {id} names a debug instruction, which has no value"
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
    match g.init with
    | none =>
      -- Only `extern` storage is absent by definition (`checkExternGlobal`).
      unless g.isExtern do throw s!"{f.name}: global has no initial value"
    | some v =>
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

/-- Which boundary reports a whole-program finding. The diagnostic collector separately
collects call signatures, model signatures, spawn tuples, missing callees and indirect
callee types per call; the other kinds exist only in the whole-program validator. -/
inductive ProgramIssueKind where
  | model | structure | sharedDefinition | stdConflict | indirectCallee | indirectTarget
  | callSignature | progressHint | modelSignature | spawnTarget | spawnWorker | threadSpawn
  | callee | memory | fallibleSpawn | futureCancel | ioTaskThreadlocal
  deriving BEq, Repr

def ProgramIssueKind.collectedPerCall : ProgramIssueKind → Bool
  | .indirectCallee | .callSignature | .modelSignature | .spawnWorker | .threadSpawn | .callee => true
  | _ => false

/-- One independent whole-program finding: each comes from a first-error validator of one
definition, call site or memory item. -/
structure ProgramIssue where
  kind : ProgramIssueKind
  function : Option String := none
  instruction : Option Nat := none
  message : String

/-- Definitions which emission shares by name must agree across every file. -/
private def sharedDefinitionIssues (funcs : Array Func) : Array OperandTypes × Array ProgramIssue := Id.run do
  let mut issues : Array ProgramIssue := #[]
  let mut functions : Std.HashSet String := {}
  let mut indexes : Array OperandTypes := #[]
  for f in funcs do
    if functions.contains f.name then
      issues := issues.push { kind := .sharedDefinition, function := f.name, message := s!"duplicate function name '{f.name}'" }
    functions := functions.insert f.name
    let index := f.operandTypes
    if let .error message := checkFunctionStructure f index then
      issues := issues.push { kind := .structure, function := f.name, message }
    indexes := indexes.push index
  -- Later checks index structurally valid functions only.
  if issues.any (·.kind == .structure) then return (indexes, issues)
  let mut globals : Std.HashMap String (Nat × Nat) := {}
  let mut globalComparisons : Std.HashMap (Nat × Nat) (Std.HashSet (Nat × Nat)) := {}
  let mut namedTypes : Std.HashMap String (Func × TyId) := {}
  for (f, fileIndex) in funcs.zipIdx do
    let shared (message : String) : ProgramIssue := { kind := .sharedDefinition, function := f.name, message }
    for (g, k) in f.globals.zipIdx do
      if let some n := g.name then
        if functions.contains n then
          unless (match g.init with | some (.func nm ..) => nm == n | _ => false) do
            issues := issues.push (shared s!"{f.name}: global '{n}' collides with a function name")
        if let some (previousIndex, id) := globals[n]? then
          match funcs[previousIndex]? with
          | none =>
            issues := issues.push (shared s!"{f.name}: shared global '{n}' refers to unknown function table {previousIndex}")
          | some previous =>
            let key := (fileIndex, previousIndex)
            let completed : Std.HashSet (Nat × Nat) := globalComparisons[key]?.getD {}
            globalComparisons := globalComparisons.erase key
            match compatibleGlobalCached f previous k id completed with
            | some completed => globalComparisons := globalComparisons.insert key completed
            | none =>
              issues := issues.push (shared s!"{f.name}: inconsistent shared global '{n}' (previous definition in '{previous.name}')")
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
            issues := issues.push (shared s!"{f.name}: inconsistent shared type '{n}' (previous definition in '{previous.name}')")
        else namedTypes := namedTypes.insert n (f, k)
  return (indexes, issues)

/-- A call to the allocator model (`ZigLean/Mem/Alloc.lean`): the pointers and slices in its
arguments and result have a known item size and `ptr_align`, and a slice that it remaps or
reallocates has no sentinel. -/
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
    if l.sentinel && fn == .realloc then
      throw s!"{f.name}: a realloc of a slice with a sentinel is outside the subset; reallocate \
        the absorbed len + 1 byte buffer and store the sentinel"

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
    | some (.future x), some (.future y) => recur x y
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
    (operandIndex : OperandTypes := f.operandTypes) (futureResult : Option TyId := none) :
    Except String Unit := do
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
  if let some r := futureResult then
    -- `Io.async`: the task's result is the future's `result` (`docs/futures.md`).
    unless compatibleType f worker r worker.ret do
      throw s!"{f.name}: {callee} worker '{worker.name}' does not return the Io.Future result type"
    return
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
  let usizeBits := 8 * ptrBytesOf f.layouts
  let isSize (t : Option Ty) := t == some (.int false usizeBits)
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
      fail s!"{model.symbol} qualified Zig {", ".intercalate model.qualifiedVersions.toList}"
  if let some fn := allocFn? callee then
    -- `ZigLean/Mem/Width.lean` parameterizes create/alloc/alignedAlloc/destroy/free.
    if usizeBits != 64 && !(fn == .create || fn == .alloc || fn == .alignedAlloc ||
        fn == .destroy || fn == .free) then
      throw s!"{f.name}: model callee '{callee}' is outside the {usizeBits}-bit pointer model \
        (only create, alloc, alignedAlloc, destroy and free are width-parameterized)"
    count (if fn == .create then 1 else if fn == .remap || fn == .realloc then 3 else 2)
    require (argTy 0 == some .allocator) "allocator argument"
    if fn == .create || fn == .alloc || fn == .alignedAlloc || fn == .allocSentinel || fn == .dupe ||
        fn == .realloc then
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
    | .realloc =>
      require (isPtr "slice" (argTy 1) && isSize (argTy 2)) "slice/item-count arguments"
      require (isPtr "slice" errorPayload) "error-union slice result"
    if fn == .dupe || fn == .remap || fn == .realloc then
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
    if fn == .realloc then
      -- The model (`Zig.Allocator.realloc`) is byte-only: alignment-1 `u8` slices.
      let some (.errorUnion _ p) := result | fail "error-union slice result"
      for t in (args[1]?.bind index.valTy?).toArray.push p do
        let some (.ptr "slice" _ child) := f.types[t]? | fail "byte slice"
        require (f.types[child]? == some (.int false 8)) "realloc supports only u8"
        let l := f.layouts[t]?.getD {}
        require (l.ptrAlign == some 1) "byte slice with alignment 1"
        require (l.hostSize == 0 && l.bitOffset == 0) "ordinary byte slice without packed metadata"
    checkAllocCall f fn args ret index
  else if let some fn := threadFn? callee then
    if usizeBits != 64 then
      throw s!"{f.name}: model callee '{callee}' is outside the {usizeBits}-bit pointer model \
        (thread handles, futexes and Io groups are modelled for 64-bit targets only)"
    match fn with
    | .spawn =>
      count 2
      require (errorPayload == some .thread) "error-union Thread result"
      require (match argTy 0 with | some (.struct "Thread.SpawnConfig" ..) => true | _ => false) "spawn configuration"
    | .join | .detach => count 1; require (argTy 0 == some .thread && unit) "Thread/void"
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
    | .futureAsync =>
      -- `Io.async(io, function, args)`: `function` is comptime (`comptime_fn`).
      count 2
      require (argTy 0 == some .io) "Io argument"
      require (match result with | some (.future _) => true | _ => false) "Io.Future result"
    | .futureAwait | .futureCancel =>
      count 2
      let futureResult := match argTy 0 with
        | some (.ptr "one" false c) => match f.types[c]? with
          | some (.future r) => some r
          | _ => none
        | _ => none
      require (futureResult.isSome && argTy 1 == some .io) "Future pointer/Io arguments"
      require (futureResult.any (compatibleType f f · ret)) "Future result"
    | .checkCancel =>
      count 1
      require (argTy 0 == some .io) "Io argument"
      let canceled := match result with
        | some (.errorUnion set _) => match f.types[set]? with
          | some (.errorSet (some names)) => names == #["Canceled"]
          | _ => false
        | _ => false
      require (errorUnit && canceled) "error{Canceled}!void result"

/-- Explicit environment policy for translated thread assignment. The default retains
existing proofs under an availability assumption; fallible includes API failure. -/
inductive SpawnSemantics where
  | available
  | fallible
  deriving DecidableEq, Repr, Inhabited

/-- The fallible boundary accepts only the audited std versions and a constant
SpawnConfig requesting 1 MiB or the default 16 MiB and a null custom allocator. Other sizes, runtime configs
and allocator-specific semantics remain outside this model. -/
private def checkFallibleSpawnCall (f : Func) (kind : ThreadFn) (args : Array Val) : Except String Unit := do
  unless #["0.14.1", "0.15.2", "0.16.0", "0.17.0"].contains f.zigVersion do
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
    unless f.zigVersion == "0.16.0" || f.zigVersion == "0.17.0" do
      throw s!"{f.name}: fallible Io.Group requires Zig 0.16.0 or 0.17.0"

/-- The first unsupported configuration of every spawn call under the fallible policy. -/
def fallibleSpawnIssues (funcs : Array Func) : Array ProgramIssue := Id.run do
  let mut issues := #[]
  for f in funcs do
    for i in f.allInsts do
      if let .call (.func name _ _) args := i.op then
        if let some kind := threadFn? name then
          if kind.spawnArgs?.isSome then
            if let .error message := checkFallibleSpawnCall f kind args then
              issues := issues.push { kind := .fallibleSpawn, function := f.name, instruction := i.id, message }
  return issues

def checkFallibleSpawnCalls (funcs : Array Func) : Except String Unit :=
  match (fallibleSpawnIssues funcs)[0]? with
  | some issue => throw issue.message
  | none => pure ()

/-- The names of the functions that a direct call in `f` names (translated functions and std
models alike). -/
private def Func.callNames (f : Func) : Array String := f.allInsts.filterMap fun i => match i.op with
  | .call (.func name ..) _ => some name
  | _ => none

/-- The task functions (`comptime_fn` targets) of the calls in `funcs` to a std model in
`kinds`. -/
private def taskTargetsOf (funcs : Array Func) (kinds : List ThreadFn) : List String :=
  funcs.toList.flatMap fun f => (f.allInsts.filterMap fun i => match i.op with
    | .call (.func name _ (some sf)) _ =>
      if (threadFn? name).any kinds.contains then some sf else none
    | _ => none).toList

/-- The functions of `funcs` that the functions `roots` reach (the roots included): through
calls (`Func.callees`), and with `viaAsync` also through the tasks of their `Io.async` calls,
which the `fallible` policy may run on the caller's thread (`Zig.asyncEagerC`). -/
private def reachableFuncs (funcs : Array Func) (roots : List String) (viaAsync : Bool := false) :
    Array Func := Id.run do
  let refs := fnRefs funcs
  let byName := funcs.foldl (fun m f => m.insert f.name f) ({} : Std.HashMap String Func)
  let mut todo := roots
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some f := byName[name]? | continue
    out := out.push f
    let tasks := if viaAsync then taskTargetsOf #[f] [.futureAsync] else []
    todo := (f.callees refs).toList ++ tasks ++ todo
  return out

/-- `docs/futures.md` §Cancelation. The qualified future subset observes a `Future.cancel`
request only at `Io.checkCancel`: `Future.cancel` does not interrupt a task blocked at another
cancelation point (unlike `Io.Group.cancel`, `docs/std-models.md` §Cancelation), and a nested
`Future.await` is no cancelation point of the model. A program that cancels a future therefore
must not reach another cancelation point from an `Io.async` task: a cancelable futex wait (also
inside `Io.Mutex.lock`, `Io.Condition.wait`, ...), `Io.Group.await` or a nested `Future.await`.
Programs without `Future.cancel` never request a future cancelation.

`Io.Group.cancel` requests share `Mem.cancels` with `Future.cancel`, but std's `Future.await`
by a task with a request hands that request to the awaited future (`await` in
`Io/Threaded.zig`: its cancelable wait fails, the future is canceled, and the request returns
to the awaiter only if the future did not acknowledge it). The model's `Zig.awaitC` is a plain
join, so in a program with `Io.Group.cancel` no `Io.Group` task (nor a task it may run inline)
may await a future. -/
def checkFutureCancelation (funcs : Array Func) : Except String Unit := do
  let has (fn : ThreadFn) := funcs.any fun f => f.callNames.any (threadFn? · == some fn)
  if has .futureCancel then
    for f in reachableFuncs funcs ((futureTargets funcs).toList.map (·.1)) do
      for callee in f.callNames do
        if let some fn := threadFn? callee then
          if fn == .futexWait || fn == .groupAwait || fn == .futureAwait then
            throw s!"{f.name}: '{callee}' is a cancelation point that the model does not deliver \
              a Future.cancel request to; in a program with Future.cancel, Io.async tasks may only \
              observe cancelation through Io.checkCancel (docs/futures.md)"
  if has .groupCancel then
    let groupTasks := taskTargetsOf funcs [.groupAsync, .groupConcurrent]
    for f in reachableFuncs funcs groupTasks (viaAsync := true) do
      for callee in f.callNames do
        if threadFn? callee == some .futureAwait then
          throw s!"{f.name}: '{callee}' in an Io.Group task of a program with Io.Group.cancel: \
            std's await hands the task's cancelation request to the awaited future, which the \
            model does not (docs/futures.md)"

/-- `docs/generated-code.md` §Thread-local storage. `std.Io.Threaded` runs `Io.Group` and
`Io.async` tasks on a pool of worker threads, each of which runs task after task (`worker` in
`Io/Threaded.zig`), and a fallback runs a task on its caller's thread. A task's `threadlocal`
instances are those of whichever thread runs it, holding what earlier tasks left there; the
model gives each task fresh instances (`Zig.ConcM.tlsThread`). So no function that an `Io` task
reaches may use `threadlocal` storage (`runtime_nav_ptr`). `Thread.spawn` threads are new OS
threads and keep their per-thread instances. -/
def checkIoTaskThreadlocals (funcs : Array Func) : Except String Unit := do
  let tasks := taskTargetsOf funcs [.groupAsync, .groupConcurrent, .futureAsync]
  for f in reachableFuncs funcs tasks do
    if f.allInsts.any (fun i => match i.op with | .runtimeNavPtr _ => true | _ => false) then
      throw s!"{f.name}: an Io.Group or Io.async task uses `threadlocal` storage; std.Io runs \
        tasks on pooled worker threads whose instances outlive each task, which the model's \
        per-task instances do not cover (docs/generated-code.md)"

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

/-- `i` with every direct callee renamed by `rename` (nested bodies included). -/
private partial def renameCallees (rename : String → String) (i : Inst) : Inst :=
  let body := Array.map (renameCallees rename)
  let cases := Array.map fun (c : SwitchCase) => { c with body := body c.body }
  { i with op := match i.op with
    | .call (.func name noreturn spawnFn) args => .call (.func (rename name) noreturn spawnFn) args
    | .block b => .block (body b)
    | .loop b => .loop (body b)
    | .condBr c t e => .condBr c (body t) (body e)
    | .switchBr v cs e => .switchBr v (cases cs) (body e)
    | .loopSwitchBr v cs e => .loopSwitchBr v (cases cs) (body e)
    | .«try» v e => .«try» v (body e)
    | .tryPtr p e => .tryPtr p (body e)
    | op => op }

/-- The rejection of an extern call that `resolveExterns` cannot bind. -/
def externUnbound (caller : String) (e : ExternDecl) (why : String) : String :=
  s!"{caller}: CALLEE_EXTERN_UNBOUND: extern function '{e.name}'\
    {(e.library.map (s!" (library '{·}')")).getD ""} {why} (docs/air-json.md §Extern calls)"

/-- The first difference between an extern declaration (types of the calling function `f`)
and the definition `target`, if any (exact agreement; `abiThunk` admits conversions). -/
def externSignatureMismatch (f target : Func) (e : ExternDecl) : Option String := Id.run do
  unless e.params.size == target.params.size do
    return some s!"{e.params.size} parameters declared, {target.params.size} defined"
  for (p, k) in e.params.zipIdx do
    unless compatibleType f target p target.params[k]! do
      return some s!"parameter {k} has another type"
  unless compatibleType f target e.ret target.ret do
    return some "the result has another type"
  return none

/-! ### C ABI conversion at an extern binding

A program's extern declaration and the definition the linker resolves it to are two C
declarations of one symbol, which may name different Zig types: translate-c declares
`memset(?*anyopaque, c_int, usize) ?*anyopaque` from the musl header, Zig's compiler_rt defines
`memset(?[*]u8, u8, usize) ?[*]u8`. The call passes machine words, so the binding converts each
argument from the declared to the defined type, and the result back (`abiThunk`): a generated
function `abi:<symbol>:<caller>` with the declared signature that converts, calls the definition
and converts the result. Only conversions that keep the value are admitted:

* a pointer (`*T`, `[*]T`, `[*c]T`) or optional pointer (`?*T`, `?[*]T`) to another such type:
  the same address; `null` reaching a pointer that cannot be `null` is `unreachable` (the
  definition may assume it is not null, so the call has no defined behaviour). A pointer whose
  defined alignment exceeds the declared one, a slice, a volatile or bit-pointer, and a
  function pointer are rejected;
* an integer to an integer: the same value; a value outside the receiving type's range is
  `unreachable` (the C calling convention extends a narrow argument by its declared
  signedness, which the definition may rely on);
* every other parameter or result type must be the definition's exactly. -/

/-- The prefix of generated C ABI conversion functions (`abiThunk`); no input function may
have it. -/
def abiThunkPrefix : String := "abi:"

private inductive AbiClass where
  /-- `*T`, `[*]T` or `[*c]T` (a `Zig.Ptr`); `nullable` for a C or `allowzero` pointer. -/
  | ptr (nullable : Bool) (align : Nat)
  /-- `?*T` or `?[*]T` (an `Option Zig.Ptr`). -/
  | optPtr (align : Nat)
  | int (signed : Bool) (bits : Nat)

private def abiPtrChildOk (types : Array Ty) (c : TyId) : Bool :=
  match types[c]? with
  | some (.other n) => !(n.startsWith "fn ") && !(n.startsWith "fn(")
  | some _ => true
  | none => false

/-- A pointer type's size and alignment, if the ABI conversion admits it. -/
private def abiPlainPtr (types : Array Ty) (layouts : Array Layout) (id : TyId) :
    Option (String × Nat) := do
  let .ptr size _ c := (← types[id]?) | none
  let l ← layouts[id]?
  unless size != "slice" && !l.isVolatile && l.hostSize == 0 && abiPtrChildOk types c do none
  pure (size, l.ptrAlign.getD 1)

private def abiClass (types : Array Ty) (layouts : Array Layout) (t : TyId) : Option AbiClass :=
  match types[t]? with
  | some (.ptr ..) => do
    let (size, align) ← abiPlainPtr types layouts t
    pure (.ptr (size == "c" || (layouts[t]?.map (·.allowzero)).getD false) align)
  | some (.optional c) => do
    let (size, align) ← abiPlainPtr types layouts c
    if size == "c" || (layouts[c]?.map (·.allowzero)).getD false then none
    pure (.optPtr align)
  | some (.int signed bits) => pure (.int signed bits)
  | _ => none

private def abiIntRange (signed : Bool) (bits : Nat) : Int × Int :=
  if signed then (-(2 ^ (bits - 1) : Int), 2 ^ (bits - 1) - 1) else (0, 2 ^ bits - 1)

private def mapChildTys (f : TyId → TyId) : Ty → Ty
  | .ptr s c x => .ptr s c (f x)
  | .array n x s => .array n (f x) s
  | .vector n x => .vector n (f x)
  | .optional x => .optional (f x)
  | .future x => .future (f x)
  | .errorUnion a b => .errorUnion (f a) (f b)
  | .struct n l fs => .struct n l (fs.map fun (k, x) => (k, f x))
  | .enum n t e fs => .enum n (f t) e fs
  | .union n l t fs => .union n l (t.map f) (fs.map fun (k, x) => (k, f x))
  | .tuple fs => .tuple (fs.map f)
  | t => t

private structure ThunkState where
  types : Array Ty
  layouts : Array Layout
  imported : Std.HashMap TyId TyId := {}
  next : Nat := 0

private abbrev ThunkM := StateT ThunkState (Except String)

/-- Copy `src`'s type `t` (and every type it names) into the thunk's table. -/
private partial def importTy (src : Func) (t : TyId) : ThunkM TyId := do
  if let some id := (← get).imported[t]? then return id
  let some ty := src.types[t]? | throw s!"type {t} of '{src.name}' does not exist"
  let id := (← get).types.size
  modify fun s => { s with types := s.types.push .void, layouts := s.layouts.push {},
                           imported := s.imported.insert t id }
  let mut map : Std.HashMap TyId TyId := {}
  for k in childTys ty do map := map.insert k (← importTy src k)
  let ty' := mapChildTys (fun c => map.getD c c) ty
  modify fun s => { s with types := s.types.set! id ty', layouts := s.layouts.set! id (src.layouts[t]?.getD {}) }
  return id

/-- A type the thunk's own instructions need (`bool`, `usize`, `noreturn`): an identical entry of
the table, else a new one. -/
private def thunkTy (ty : Ty) (layout : Layout) : ThunkM TyId := do
  let st ← get
  if let some id := (st.types.zip st.layouts).findIdx? (· == (ty, layout)) then return id
  modify fun s => { s with types := s.types.push ty, layouts := s.layouts.push layout }
  return st.types.size

private def freshInst (ty : TyId) (op : Op) : ThunkM Inst := do
  let id := (← get).next
  modify fun s => { s with next := s.next + 1 }
  return { id, ty, op }

/-- Convert `v` from the type `src` (class `a`) to `dst` (class `b`, both thunk-table IDs),
then continue with `k`. A check wraps the continuation in a `cond_br` whose other branch is
`unreach`. -/
private def abiConvert (types : Array Ty) (v : Val) (src dst : TyId) (a b : AbiClass)
    (k : Val → ThunkM (Array Inst)) : ThunkM (Array Inst) := do
  let noret ← thunkTy .noreturn {}
  let boolTy ← thunkTy .bool { size := some 1, align := some 1 }
  let guarded (pre : Array Inst) (c : Val) (rest : Array Inst) : ThunkM (Array Inst) := do
    let br ← freshInst noret (.condBr c rest #[← freshInst noret .unreach])
    return pre.push br
  let cast (x : Val) (ty : TyId) (op : Val → Op) (more : Val → ThunkM (Array Inst)) :
      ThunkM (Array Inst) := do
    let i ← freshInst ty (op x)
    return #[i] ++ (← more (.inst i.id))
  match a, b with
  | .int sa wa, .int sb wb =>
    let (lo, hi) := abiIntRange sb wb
    let (slo, shi) := abiIntRange sa wa
    let op : Val → Op := if wa == wb then .bitcast else .intCast
    if lo ≤ slo && shi ≤ hi then cast v dst op k
    else
      let ge ← freshInst boolTy (.cmp .ge v (.int src (max lo slo)))
      let le ← freshInst boolTy (.cmp .le v (.int src (min hi shi)))
      let both ← freshInst boolTy (.boolAnd (.inst ge.id) (.inst le.id))
      guarded #[ge, le, both] (.inst both.id) (← cast v dst op k)
  | .optPtr _, .optPtr _ | .optPtr _, .ptr true _ | .ptr true _, .ptr true _
  | .ptr true _, .optPtr _ | .ptr false _, .ptr _ _ => cast v dst .bitcast k
  | .ptr false _, .optPtr _ =>
    let some (.optional child) := types[dst]? | throw "optional pointer without a payload type"
    cast v child .bitcast fun p => cast p dst .wrapOptional k
  | .optPtr _, .ptr false _ =>
    let some (.optional child) := types[src]? | throw "optional pointer without a payload type"
    let c ← freshInst boolTy (.isNonNull v)
    guarded #[c] (.inst c.id) (← cast v child .optPayload fun p => cast p dst .bitcast k)
  | .ptr true _, .ptr false _ =>
    let usize ← thunkTy (.int false 64) { size := some 8, align := some 8 }
    let addr ← freshInst usize (.bitcast v)
    let c ← freshInst boolTy (.cmp .ne (.inst addr.id) (.int usize 0))
    guarded #[addr, c] (.inst c.id) (← cast v dst .bitcast k)
  | _, _ => throw "no C ABI conversion"

/-- Why the type `d` of `f` cannot be converted to the type `u` of `target` (`toDef`: from the
declaration to the definition, else back) at the C ABI boundary, if it cannot. -/
private def abiMismatch (f target : Func) (d u : TyId) (what : String) (toDef : Bool) :
    Option String := Id.run do
  if compatibleType f target d u then return none
  let (srcF, srcT, dstF, dstT) := if toDef then (f, d, target, u) else (target, u, f, d)
  match abiClass srcF.types srcF.layouts srcT, abiClass dstF.types dstF.layouts dstT with
  | some (.int ..), some (.int ..) => return none
  | some (.ptr _ a), some (.ptr _ b) | some (.ptr _ a), some (.optPtr b)
  | some (.optPtr a), some (.ptr _ b) | some (.optPtr a), some (.optPtr b) =>
    if b > a then
      return some (if toDef then s!"{what} needs alignment {b}, more than the declared {a}"
        else s!"{what} is declared with alignment {b}, more than the defined {a}")
    return none
  | _, _ => return some s!"{what} has another type, with no value-preserving C ABI conversion"

/-- The function that binds `f`'s extern declaration `e` to `target`: `none` if every type
agrees (the call binds to `target` directly), else a C ABI conversion thunk, or why there is
none. Pointer conversions assume 64-bit addresses (x86_64, aarch64). -/
def abiThunk (f target : Func) (e : ExternDecl) : Except String (Option Func) := do
  let some why := externSignatureMismatch f target e | return none
  unless (f.targetArch == "x86_64" || f.targetArch == "aarch64") &&
      e.params.size == target.params.size do
    throw why
  for (p, k) in e.params.zipIdx do
    if let some why := abiMismatch f target p target.params[k]! s!"parameter {k}" true then throw why
  if let some why := abiMismatch f target e.ret target.ret "the result" false then throw why
  let build : ThunkM (Array Inst) := do
    let args ← e.params.zipIdx.mapM fun (p, k) => freshInst p (.arg k)
    let defParams ← target.params.mapM (importTy target)
    let defRet ← importTy target target.ret
    let noret ← thunkTy .noreturn {}
    let ret (v : Val) : ThunkM (Array Inst) := return #[← freshInst noret (.ret v)]
    let classes (src dst : TyId) : ThunkM (AbiClass × AbiClass) := do
      let st ← get
      let some a := abiClass st.types st.layouts src | throw "no C ABI class"
      let some b := abiClass st.types st.layouts dst | throw "no C ABI class"
      return (a, b)
    let finish (converted : Array Val) : ThunkM (Array Inst) := do
      let call ← freshInst defRet (.call (.func target.name false) converted)
      let rest ← if compatibleType target f target.ret e.ret then ret (.inst call.id) else do
        let (a, b) ← classes defRet e.ret
        abiConvert (← get).types (.inst call.id) defRet e.ret a b ret
      return #[call] ++ rest
    -- Convert the arguments in order; each conversion continues with the next one.
    let rec go (fuel k : Nat) (acc : Array Val) : ThunkM (Array Inst) := do
      match fuel with
      | 0 => finish acc
      | fuel + 1 =>
        let some arg := args[k]? | finish acc
        let v : Val := .inst arg.id
        if compatibleType f target e.params[k]! target.params[k]! then go fuel (k + 1) (acc.push v)
        else
          let (a, b) ← classes e.params[k]! defParams[k]!
          abiConvert (← get).types v e.params[k]! defParams[k]! a b fun x => go fuel (k + 1) (acc.push x)
    return args ++ (← go args.size 0 #[])
  let (body, st) ← build.run { types := f.types, layouts := f.layouts }
  let thunk : Func := { f with name := s!"{abiThunkPrefix}{e.name}:{f.name}", params := e.params,
                               ret := e.ret, body, types := st.types, layouts := st.layouts,
                               globals := #[], externs := #[], exportDecl := none }
  check thunk |>.mapError fun err => s!"the generated C ABI conversion is rejected: {err}"
  return some thunk

/-- Bind each extern call (`externCallee`, `docs/air-json.md` §Extern calls) at its linker
symbol, never at a Zig declaration name:
(a) to a registry model whose `symbol` is the extern callee and whose `extern.library` is the
    declared library, if the program does not define the symbol; the call stays an extern
    callee, which the model implements;
(b) else to the one function of the program that exports the symbol (`export fn` or
    `@export`, under any of its names, with any linkage but `internal`), with the declared
    calling convention; the call becomes a direct call of that function, whose signature
    `checkProgram` then checks like any direct call's. Two definitions are ambiguous whatever
    their linkage: a strong definition is never taken to override a weak one.
    A declaration whose types differ from the definition's binds through a generated C ABI
    conversion (`abiThunk`) if every difference keeps the value.
A variadic extern is outside the subset. The result is the rewritten functions (in input order),
then the C ABI conversions, and one rejection per (caller, symbol) that neither binds; callers that need all-or-nothing use
`resolveExterns`. -/
def resolveExternsCollect (funcs : Array Func) (models : Array ModelBinding := #[]) :
    Except String (Array Func × Array (String × String)) := do
  -- Every definition of each symbol; more than one is ambiguous only for a call that needs it.
  let mut exports : Std.HashMap String (Array Func) := {}
  for f in funcs do
    if (externSymbol? f.name).isSome then
      throw s!"{f.name}: a function name cannot have the extern callee form 'extern:<symbol>'"
    if f.name.startsWith abiThunkPrefix then
      throw s!"{f.name}: a function name cannot start with '{abiThunkPrefix}', the prefix of C ABI conversions"
    if let some e := f.exportDecl then
      for s in e.linkable do
        exports := exports.insert s.name ((exports.getD s.name #[]).push f)
  let mut unbound : Array (String × String) := #[]
  let mut out : Array Func := #[]
  let mut thunks : Array Func := #[]
  for f in funcs do
    -- Without an `externs` table a function has no extern call (`checkProgram` rejects one).
    if f.externs.isEmpty then
      out := out.push f
      continue
    let mut renames : Std.HashMap String String := {}
    let mut seen : Std.HashSet String := {}
    for i in f.allInsts do
      let .call (.func callee ..) args := i.op | continue
      let some symbol := externSymbol? callee | continue
      let some e := f.externs.find? (·.name == symbol)
        | throw s!"{f.name}: inst {i.id}: extern callee '{symbol}' has no 'externs' entry"
      -- The declaration must describe each call (a variadic one is rejected below).
      unless e.varargs || (args.size == e.params.size && i.ty == e.ret) do
        throw s!"{f.name}: inst {i.id}: the call of extern '{symbol}' does not match its 'externs' entry"
      if seen.contains callee then continue
      seen := seen.insert callee
      let reject (why : String) := unbound.push (f.name, externUnbound f.name e why)
      let definitions := exports.getD symbol #[]
      let names := ", ".intercalate (definitions.map (·.name)).toList
      if e.varargs then
        unbound := reject "is variadic, which is outside the subset"
      else if definitions.size > 1 then
        unbound := reject s!"is defined by several functions ({names}) (CALLEE_AMBIGUOUS)"
      else if let some m := models.find? (·.symbol == callee) then
        let some binding := m.externBinding
          | throw s!"{f.name}: model '{m.symbol}' has no extern binding"
        -- The linker would resolve the symbol to the program's own definition, not the model's.
        if let some target := definitions[0]? then
          unbound := reject s!"is both defined by '{target.name}' and bound to registry model '{callee}' (CALLEE_AMBIGUOUS)"
        else unless binding.library == e.library do
          unbound := reject s!"is declared with another library than its registry model's ({binding.library.getD "none"})"
      else if let some target := definitions[0]? then
        let cc := (target.exportDecl.map (·.cc)).getD ""
        if cc != e.cc then
          unbound := reject (s!"is declared with calling convention '{e.cc}', but its \
            definition '{target.name}' has '{cc}'")
        else match abiThunk f target e with
          | .error why => unbound := reject s!"is declared with another signature than its \
              definition '{target.name}': {why}"
          | .ok none => renames := renames.insert callee target.name
          | .ok (some thunk) =>
            renames := renames.insert callee thunk.name
            thunks := thunks.push thunk
      else
        unbound := reject s!"has no definition in the program (a function of the AIR set that exports \
          '{symbol}' with `export fn` or `@export`) and no registry model '{callee}' (--model-registry, \
          docs/external-models.md)"
    out := out.push (if renames.isEmpty then f
      else { f with body := f.body.map (renameCallees (fun n => renames.getD n n)) })
  return (out ++ thunks, unbound)

/-- `resolveExternsCollect`, rejecting the program at the first unbound extern call. -/
def resolveExterns (funcs : Array Func) (models : Array ModelBinding := #[]) :
    Except String (Array Func) := do
  let (resolved, unbound) ← resolveExternsCollect funcs models
  if let some (_, message) := unbound[0]? then throw message
  return resolved

/-- The checks that need every function. A function that uses memory reads a slice item from
memory, and a call to a pure function copies each `[]const T` argument from memory
(`Zig.readSlice`): `T` must be a type that the model encodes. Each callee is a translated
function or has a built-in std model (`stdModel?`, `Air2Lean/StdModels.lean`); a translated
function cannot reuse the qualified name of a built-in std model.

Every independent whole-program finding is returned, in the order the fail-fast
`checkProgram` meets them. Model-binding and structural failures stop collection: later
checks need them. -/
def programIssues (funcs : Array Func) (models : Array ModelBinding := #[])
    (profile : Option BuildProfile := none)
    (selectedCallees : Array String := #[]) : Array ProgramIssue := Id.run do
  let mut issues : Array ProgramIssue := #[]
  unless models.isEmpty do
    let some profile := profile
      | return #[{ kind := .model, message := "external model bindings require a checked program profile" }]
    if profile.isBigEndian then
      return #[{ kind := .model, message :=
        "external model bindings are outside the qualified big-endian model (`docs/profiles.md` §Byte order)" }]
    if let .error message := ModelRegistry.check models profile funcs then
      return #[{ kind := .model, message }]
  let modelSymbols := models.foldl (fun symbols m => symbols.insert m.symbol) ({} : Std.HashSet String)
  let (indexes, shared) := sharedDefinitionIssues funcs
  issues := issues ++ shared
  if shared.any (·.kind == .structure) then return issues
  let targets := referenceTargets (fnRefs funcs)
  let mem := memoryFunctions funcs (models.map (·.symbol) ++ selectedCallees)
  let mut functionNames : Std.HashMap String Nat := {}
  for (f, fileIndex) in funcs.zipIdx do
    if let some model := stdModel? f.name then
      issues := issues.push { kind := .stdConflict, function := f.name, message :=
        s!"{f.name}: translated function conflicts with built-in std model '{model.symbol}' (narrow the example's `filter`, docs/std-models.md)" }
    functionNames := functionNames.insert f.name fileIndex
  let lookupFunction (name : String) : Option (Nat × Func) := do
    let index ← functionNames[name]?
    let target ← funcs[index]?
    pure (index, target)
  let mut signatures : SignaturePairs := {}
  for ((f, index), fileIndex) in (funcs.zip indexes).zipIdx do
    for i in index.insts do
      let issue (kind : ProgramIssueKind) (message : String) : ProgramIssue :=
        { kind, function := f.name, instruction := i.id, message }
      if let .call p args := i.op then if p.isIndirectCallee then
        match index.calleeFnTy? f p with
        | none => issues := issues.push (issue .indirectCallee s!"{f.name}: inst {i.id}: indirect callee is not a function pointer")
        | some tn =>
          for callee in targets.getD tn #[] do
            match lookupFunction callee with
            | none => issues := issues.push (issue .indirectTarget s!"{f.name}: inst {i.id}: indirect target '{callee}' has no AIR file")
            | some (targetIndex, target) =>
              match checkCallSignatureCached f target fileIndex targetIndex i args index signatures with
              | .ok cache => signatures := cache
              | .error message => issues := issues.push (issue .callSignature message)
      if let .call (.func callee noreturn _) _ := i.op then
        if let some fn := threadFn? callee then
          if fn == .yield || fn == .spinLoopHint then
            if noreturn then issues := issues.push (issue .progressHint s!"{f.name}: progress hint '{callee}' cannot be noreturn")
      if let .call (.func callee false spawnFn) args := i.op then
        if let .error message := checkModelSignature f callee args i.ty index then
          issues := issues.push (issue .modelSignature message)
        if !modelledStdFn callee then
          if let some (targetIndex, target) := lookupFunction callee then
            match checkCallSignatureCached f target fileIndex targetIndex i args index signatures with
            | .ok cache => signatures := cache
            | .error message => issues := issues.push (issue .callSignature message)
        if let some kind := threadFn? callee then
          if let some k := kind.spawnArgs? then
            match spawnFn with
            | none => issues := issues.push (issue .spawnTarget s!"{f.name}: a call to '{callee}' has no comptime_fn spawn target")
            | some worker =>
              match lookupFunction worker with
              | none => issues := issues.push (issue .spawnWorker
                  s!"{f.name}: the spawned callee '{worker}' has no AIR file (add its name to the filter, docs/std-models.md)")
              | some (_, target) =>
                if let .error message := checkThreadSpawn f target
                    (if kind == .spawn then "Thread.spawn" else "Io.Group.async") k args index then
                  issues := issues.push (issue .threadSpawn message)
          if kind == .futureAsync then
            match spawnFn with
            | none => issues := issues.push (issue .spawnTarget s!"{f.name}: a call to '{callee}' has no comptime_fn task")
            | some worker =>
              match lookupFunction worker with
              | none => issues := issues.push (issue .spawnWorker
                  s!"{f.name}: the Io.async task '{worker}' has no AIR file (add its name to the filter, docs/futures.md)")
              | some (_, target) =>
                match f.types[i.ty]? with
                | some (.future r) =>
                  if let .error message := checkThreadSpawn f target "Io.async" 1 args index (some r) then
                    issues := issues.push (issue .threadSpawn message)
                | _ => issues := issues.push (issue .threadSpawn s!"{f.name}: Io.async has no Io.Future result")
        unless functionNames.contains callee || modelSymbols.contains callee || selectedCallees.contains callee do
          if let some symbol := externSymbol? callee then
            issues := issues.push (issue .callee s!"{f.name}: CALLEE_EXTERN_UNBOUND: extern function \
              '{symbol}' is bound to neither a definition nor a registry model (docs/air-json.md \
              §Extern calls)")
          else if let some reason := rejectedThreadFn? callee then
            issues := issues.push (issue .callee s!"{f.name}: the callee '{callee}' is outside the subset: {reason}")
          else if !modelledStdFn callee then
            issues := issues.push (issue .callee
              s!"{f.name}: the callee '{callee}' has no AIR file and no model (add its name to the example's `filter` file, docs/std-models.md)")
  -- Needs the whole program (before the memory items, as `checkProgram` always reported them): every task an `Io.async` reaches (`checkFutureCancelation`).
  if let .error message := checkFutureCancelation funcs then
    issues := issues.push { kind := .futureCancel, message }
  if let .error message := checkIoTaskThreadlocals funcs then
    issues := issues.push { kind := .ioTaskThreadlocal, message }
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
            if let some k := (threadFn? callee).bind (·.taskArgs?) then
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
          if let .error message := checkMemTy f.name f.types f.layouts 0 c f.errorSetBits then
            issues := issues.push { kind := .memory, function := f.name, instruction := i.id, message }
  return issues

def checkProgram (funcs : Array Func) (models : Array ModelBinding := #[])
    (profile : Option BuildProfile := none)
    (selectedCallees : Array String := #[]) : Except String Unit :=
  match (programIssues funcs models profile selectedCallees)[0]? with
  | some issue => throw issue.message
  | none => pure ()

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
    else
      log := log.record (checkDiagnostic file f .instructionFailure anchor) (cx.checkBitPtrSource line i.ty i.op)
    -- L13: a volatile access has its own stable code; it supersedes the generic check.
    let volatileCheck := cx.checkVolatile line i.ty i.op
    log := log.record { (checkDiagnostic file f .volatileAccess anchor) with
      category := .unsupportedSemantics } volatileCheck
    -- L08: an exporter packed field pointer that the model's layout does not match.
    let packedCheck := cx.checkPackedLayout line i.ty i.op
    log := log.record { (checkDiagnostic file f .packedLayout anchor) with
      category := .unsupportedSemantics } packedCheck
    -- A padded-width `cmpxchg` or RMW `.Max`/`.Min` also has its own stable code.
    let paddedCheck := cx.checkPaddedAtomic line i.op
    log := log.record { (checkDiagnostic file f .paddedAtomic anchor) with
      category := .unsupportedSemantics } paddedCheck
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
      if typeCheck.toOption.isSome && volatileCheck.toOption.isSome &&
          packedCheck.toOption.isSome && paddedCheck.toOption.isSome then
        let opCheck := checkOp cx line i.ty i.op
        log := log.record (checkDiagnostic file f .instructionFailure anchor) opCheck
        -- L13: inline asm that passes A01's operand checks but is off the reviewed allowlist and
        -- not a declared device event has its own stable code.
        if opCheck.toOption.isSome then
          log := log.record { (checkDiagnostic file f .asmVolatileEffect anchor) with
            category := .unsupportedSemantics } (cx.checkAsmEffect line i.op)
  return (line, log)

structure FunctionChecks where
  index : OperandTypes
  structureValid : Bool
  log : Diagnostics.Log

/-- Return the actual structural result and index alongside collected diagnostics. -/
def collectFunctionChecksDetailed (file : String) (f : Func) (initial : Diagnostics.Log)
    (device : Option DeviceContract := none) : FunctionChecks := Id.run do
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
  for p in f.params do
    log := log.record (checkDiagnostic file f .typeFailure { idSpace := .canonical, typeId := some p })
      (checkBitPtrParam f p)
  for (t, id) in f.types.zipIdx do
    if let .union _ _ none _ := t then
      log := log.record (checkDiagnostic file f .memoryFailure { idSpace := .canonical, typeId := some id })
        (checkMemTy f.name f.types f.layouts 0 id f.errorSetBits)
  let insts := index.insts
  let errorGlobals := f.globals.any (fun g => hasErrorStorage f.types g.ty)
  let escaping := escapingAllocs f
  let localRoots := placeRoots insts
  let places := localRoots.filterMap fun (p, r) => if escaping.contains r then none else some p
  let bytesLocals := byteLocals f
  for i in insts do
    if let .alloc := i.op then
      if escaping.contains i.id || bytesLocals.contains i.id then
        if let some c := ptrChild f.types i.ty then
          log := log.record (checkDiagnostic file f .memoryFailure
            { idSpace := .canonical, instruction := some i.id, typeId := some c })
            (checkMemTy f.name f.types f.layouts 0 c f.errorSetBits)
  for (g, id) in f.globals.zipIdx do
    log := log.record (checkDiagnostic file f .globalFailure { idSpace := .canonical, globalId := some id })
      (do checkGlobal f g; if let some init := g.init then checkNoThreadlocalConstant f init)
  for i in insts do
    if let .runtimeNavPtr g := i.op then
      log := log.record (checkDiagnostic file f .globalFailure
        { idSpace := .canonical, instruction := some i.id, globalId := some g }) (checkRuntimeNavPtr f i g)
    log := log.record (checkDiagnostic file f .constantFailure
      { idSpace := .canonical, instruction := some i.id }) (checkErrorGlobalInstruction errorGlobals f insts i)
    log := log.record (checkDiagnostic file f .signatureFailure
      { idSpace := .canonical, instruction := some i.id }) (checkIndirectCallTarget f insts i)
    log := log.record (checkDiagnostic file f .constantFailure
      { idSpace := .canonical, instruction := some i.id }) (checkFunctionValues f i)
    log := log.record { (checkDiagnostic file f .constantFailure
      { idSpace := .canonical, instruction := some i.id }) with category := .unsupportedSemantics }
      (checkUndefOperands f index.valTy? i)
    for v in valueOperands i.op ++ ptrOperands i.op do
      let result := do
        checkNullConstants f.name f.types f.layouts v
        checkBitPtrConstant f v
        checkNoThreadlocalConstant f v
        checkPointerConstant f v
          (fun k => s!"{f.name}: a pointer constant without a global ({k}) is outside the subset")
          (fun pa ga => s!"{f.name}: a pointer with align({pa}) to a global of alignment {ga} is outside the subset")
      log := log.record (checkDiagnostic file f .constantFailure
        { idSpace := .canonical, instruction := some i.id }) result
  let cx : CheckCtx := {
    fnName := f.name
    types := f.types
    layouts := f.layouts
    errBits := f.errorSetBits
    instTys := insts.map fun i => (i.id, i.ty)
    places
    localRoots
    localPaths := localPlacePaths f.types f.layouts insts
    zigVersion := f.zigVersion
    device
    targetArch := f.targetArch }
  return { index, structureValid := true, log := (collectInstChecks file f cx f.body 0 log).2 }

/-- Compatibility wrapper for clients that need only diagnostics. -/
def collectFunctionChecks (file : String) (f : Func) (initial : Diagnostics.Log)
    (device : Option DeviceContract := none) : Diagnostics.Log :=
  (collectFunctionChecksDetailed file f initial device).log

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
        if kind == .futureAsync then
          if let (some target, some (.future r)) := (worker.bind snapshot.unique, f.types[i.ty]?) then
            log := log.record diagnostic (checkThreadSpawn f target "Io.async" 1 args index (some r))
    | .call p@(.inst _) args | .call p@(.ptrConst ..) args =>
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
