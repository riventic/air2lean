import Std.Data.HashMap
import Std.Data.HashSet
import Air2Lean.Air.Json

/-!
# Canonical AIR

Six rewrites of the raw JSON (`Raw.RawFunc`), the same for every Zig version, before
`Normalize.lean` reads the tags. After them, the same Zig code gives the same `Func` in every
supported version, so one translation (and the proofs over it) serves all versions.

0. `versionTags`. The canonical tag vocabulary is 0.16.0's. Zig 0.17.0 renamed `intcast`,
   `intcast_safe` and `struct_field_val` (`int_cast`, `int_cast_safe`, `agg_field_val`) and split
   the overloaded `bitcast` by operand kind (`bit_cast`, `bit_cast_safe`, `ptr_cast`,
   `ptr_from_int`, `int_from_ptr`, `error_cast`, `error_from_int`, `int_from_error`); 0.16.0
   lowered every one of these through `bitcast`, and `Check.lean`/`Emit.lean` dispatch a
   `bitcast` on its operand and result types. `bit_cast_safe` adds only
   the invalid-tag check for an exhaustive-enum destination, which the `bitcast` emission of an
   enum destination already performs (`Zig.enumOf`). The pass renames them back, so the
   rewrites below match one vocabulary. 0.17.0 also dropped `bool_and`/`bool_or`: Sema's
   safety checks combine their conditions with `bit_and`/`bit_or` on `bool` (or `bool` vector)
   operands, which the pass renames to `bool_and`/`bool_or` (both evaluate both operands, so
   the meaning is the same). A `ptr_cast` to a whole-byte vector lane becomes 0.16.0's
   `ptr_elem_ptr` (`laneElemPtrs`). It rejects a tag that the file's `zig_version` does not
   have (`versionTagReason?`), before the rename can make a misplaced tag look canonical.

1. `forwardReadOnlyCopies`. Sema lowers `&v` of a constant value `v` (a parameter, a union
   payload) to a read-only stack copy: `alloc`, one `store` of `v`, and `bitcast`s to a const
   pointer after the store in the store's own body. Only this shape is rewritten: a `bitcast`
   outside that body, or a second store, keeps the `alloc`. Zig 0.16.0 reads a field, the
   length or an element of a struct, union or slice value through such a copy
   (`struct_field_ptr_index_N`, `ptr_slice_len_ptr`, `slice_elem_ptr`, then `load`), where 0.15.2
   reads the value (`struct_field_val`, `slice_len`, `slice_elem_val`). Nothing writes the copy,
   so a read through it equals the read of the value. The pass changes each such pointer
   projection to the value read, and drops the copy, the `bitcast`s and the `load`s. A slice's
   elements remain memory: only an adjacent, single projection/load chain can read them early.
2. `itemReads`. A read of one item through a pointer is `ptr_elem_val` in 0.15.2, and
   `ptr_elem_ptr` then `load` in 0.16.0. A read of one item of a local array is a `load` of the
   whole array then `array_elem_val` in 0.15.2, and the same `ptr_elem_ptr` and `load` in 0.16.0.
   The pass changes both pairs to one `ptr_elem_val`, if the first instruction has no other use
   and is not a lane pointer (`vector_index`), which stays a bit-pointer; a load of a vector whose
   lanes are not power-of-two bytes (`bool`, `u3`, `u24`, `f80`) is not folded either.
   A `slice_elem_ptr`/`load` pair similarly becomes `slice_elem_val` at the load's position.
   For the second pair, the `array_elem_val` must come directly after the `load` in its body, so
   no write comes between them.
3. `dropTrueChecks`. For `s[a..b]`, 0.15.2 checks `a <= b` a second time, after the check
   that panics when it is false, and for `s[0..b]` it checks `0 <= b`; 0.16.0 does neither. The
   pass drops a safety check (`checkCond?`) that is always true, and its comparison: a comparison
   with the same tag and operands as an earlier check in the same body, `0 <= x`, or `x <= x + y`
   after the `add` (it does not wrap), for unsigned `x` and `y`. For `s[a..][0..n]`, 0.15.2
   checks `a <= a + n`.
4. `argRanks`. An `arg`'s `param` is the source index of the parameter, and it counts the
   `comptime` parameters of a generic instance (`dupeSentinel(allocator, comptime T, m)` reads
   `m` as `param 2`). The pass ranks these indices against runtime parameter slots that have
   AIR args, preserving slots for one-possible-value parameters (such as `void` and `u0`).
5. `dropDeadAllocPlaceholders`. When Sema resolves a local's value at compile time (a
   `const` whose address is taken, `const u: U = .{ .b = 0 }; _ = &u;`), it puts the value in
   a constant global, points every live use at it, and rewrites the local's now-dead `alloc` and
   stores to `bitcast` of the integer 0 to the `alloc`'s pointer type (0.15.2, 0.16.0;
   0.14.1 uses `bitcast` of a `u8` 0). Liveness marks these and their field/element pointers
   unused, so no code is generated for them. The pass drops them when nothing but other such
   pointers and debug instructions reads them; a read one is rejected by `Check.lean`.
6. `renumber`. Instruction IDs name generated definitions (`<fn>.loop<id>`, `.br<id>`), and the
   debug instructions that a version adds shift them. The pass gives the non-debug instructions
   the IDs `0, 1, …` in body order, then the debug instructions the IDs after them.
-/

namespace Air2Lean.Raw

/-- Zig 0.17.0 AIR tags renamed to their 0.16.0 spelling (`versionTags`, module doc). -/
def tagAliases017 : List (String × String) :=
  [("int_cast", "intcast"), ("int_cast_safe", "intcast_safe"), ("agg_field_val", "struct_field_val"),
   ("bit_cast", "bitcast"), ("bit_cast_safe", "bitcast"), ("ptr_cast", "bitcast"),
   ("ptr_from_int", "bitcast"), ("int_from_ptr", "bitcast"), ("error_cast", "bitcast"),
   ("error_from_int", "bitcast"), ("int_from_error", "bitcast")]

/-- Zig 0.17.0 AIR tags without a 0.16.0 spelling. -/
def tagsOnly017 : List String :=
  ["div_ceil", "div_ceil_optimized", "array_to_vector", "union_from_enum", "spirv_runtime_array_len"] ++
    tagAliases017.map (·.1)

/-- 0.16.0 AIR tags that Zig 0.17.0 removed or renamed (0.17.0 writes `bool_and`/`bool_or` as
`bit_and`/`bit_or` on `bool` operands). -/
def tagsRemoved017 : List String :=
  ["bitcast", "intcast", "intcast_safe", "struct_field_val", "bool_and", "bool_or"]

/-- The tag spelling of a `zig_version`. A version outside the registry, which `normalize`
rejects later, reads as the 0.16.0 spelling. -/
def airTagsOf (zigVersion : String) : ZigVersion.AirTags :=
  ((ZigVersion.ofString? zigVersion).map (·.airTags)).getD .base

/-- Why `tag` cannot occur in an AIR file of the tag spelling `tags`, if it cannot. -/
def airTagReason? (tags : ZigVersion.AirTags) (zigVersion tag : String) : Option String :=
  if tags == .v017 then
    if tagsRemoved017.contains tag then
      some s!"is not a Zig 0.17.0 AIR tag (removed or renamed in 0.17.0)"
    else none
  else if tagsOnly017.contains tag then
    some s!"is not a Zig {zigVersion} AIR tag (introduced in 0.17.0)"
  else none

/-- Why `tag` cannot occur in an AIR file of `zigVersion`, if it cannot. -/
def versionTagReason? (zigVersion tag : String) : Option String :=
  airTagReason? (airTagsOf zigVersion) zigVersion tag

/-- Every instruction of `body`, nested bodies included, in body order. -/
partial def flatten (body : Array RawInst) : Array RawInst :=
  body.foldl (init := #[]) fun acc i =>
    let acc := acc.push i ++ flatten i.body ++ flatten i.thenBody ++ flatten i.elseBody
    i.cases.foldl (fun acc c => acc ++ flatten c.body) acc

/-- `body` with `g` applied to each instruction, nested bodies included. `g` returns `none` to
drop the instruction. -/
partial def rewriteBody (g : RawInst → Option RawInst) (body : Array RawInst) : Array RawInst :=
  body.filterMap fun i => (g i).map fun i =>
    { i with
      body := rewriteBody g i.body, thenBody := rewriteBody g i.thenBody,
      elseBody := rewriteBody g i.elseBody,
      cases := i.cases.map fun c => { c with body := rewriteBody g c.body } }

/-- Zig 0.17.0 writes `&v[i]` as a `ptr_cast` of the vector pointer to a lane pointer
(`Layout.vectorIndex`). 0.16.0 wrote `ptr_elem_ptr` of the vector pointer and the lane index,
typed as a plain element pointer, when the lane is a power-of-two number of whole bytes. This
gives those lanes the 0.16.0 form (adding the element pointer and `usize` types if the table
lacks them); other lane pointers stay, and `Check.lean` rejects them. A lane pointer carries the
vector pointer's alignment (`*align(16:0:4:1) u32`); the element pointer gets the alignment of
its own address, as in 0.16.0: `gcd(align, k * size)`, the power of two the lane offset keeps. -/
def laneElemPtrs (f : RawFunc) : RawFunc := Id.run do
  let mut types := f.types
  let mut layouts := f.layouts
  let producers : Std.HashMap InstId TyId := (flatten f.body).foldl (init := {}) fun m i =>
    match i.ty with | some t => m.insert i.id t | none => m
  let mut repl : Std.HashMap InstId (TyId × Nat) := {}
  for i in flatten f.body do
    let (true, #[.inst p], some ty) := (i.tag == "ptr_cast", i.args, i.ty) | continue
    let some (.ptr "one" isConst lane) := types[ty]? | continue
    let some l := layouts[ty]? | continue
    let some k := l.vectorIndex | continue
    let some (.ptr "one" _ vec) := (producers[p]?).bind (types[·]?) | continue
    let some (.vector n child) := types[vec]? | continue
    let bits := match types[lane]? with | some (.int _ b) | some (.float b) => b | _ => 0
    let bytes := ((layouts[lane]?).bind (·.size)).getD 0
    unless child == lane && k < n && bytes ∈ [1, 2, 4, 8, 16] && bits == 8 * bytes do continue
    let plain : Layout :=
      { l with hostSize := 0, bitOffset := 0, vectorIndex := none, vectorIndexExported := false,
               ptrAlign := l.ptrAlign.map (Nat.gcd · (k * bytes)) }
    let t := Ty.ptr "one" isConst lane
    let id := match (types.zip layouts).findIdx? (· == (t, plain)) with
      | some id => id
      | none => types.size
    if id == types.size then
      types := types.push t
      layouts := layouts.push plain
    repl := repl.insert i.id (id, k)
  if repl.isEmpty then return f
  let usize : Layout := { size := some 8, align := some 8 }
  let u := match (types.zip layouts).findIdx? (· == (.int false 64, usize)) with
    | some u => u
    | none => types.size
  if u == types.size then
    types := types.push (.int false 64)
    layouts := layouts.push usize
  let body := rewriteBody (body := f.body) fun i =>
    some <| match repl[i.id]? with
      | some (ty, k) => { i with tag := "ptr_elem_ptr", ty := some ty, args := #[i.args[0]!, .int u k] }
      | none => i
  return { f with body, types, layouts }

/-- `versionTags` (module doc). -/
def versionTags (f : RawFunc) : Except String RawFunc := do
  let tags := airTagsOf f.zigVersion
  for i in flatten f.body do
    if let some reason := airTagReason? tags f.zigVersion i.tag then
      throw s!"{f.name}: inst {i.id}: tag '{i.tag}' {reason}"
  if tags != .v017 then return f
  let f := laneElemPtrs f
  let boolTyped (ty : Option TyId) : Bool :=
    match ty.bind (f.types[·]?) with
    | some .bool => true
    | some (.vector _ c) => f.types[c]? == some .bool
    | _ => false
  let rename (i : RawInst) : RawInst :=
    match tagAliases017.lookup i.tag, i.tag with
    | some tag, _ => { i with tag }
    | none, "bit_and" => if boolTyped i.ty then { i with tag := "bool_and" } else i
    | none, "bit_or" => if boolTyped i.ty then { i with tag := "bool_or" } else i
    | none, _ => i
  return { f with body := rewriteBody (body := f.body) fun i => some (rename i) }

/-- `i` with `f` applied to each value operand (not to nested bodies), asm operands included. -/
def RawInst.mapVals (f : Val → Val) (i : RawInst) : RawInst :=
  let op (o : RawAsmOperand) : RawAsmOperand := { o with ref := o.ref.map f }
  { i with
    args := i.args.map f, callee := i.callee.map f,
    asm := i.asm.map fun a => { a with outputs := a.outputs.map op, inputs := a.inputs.map op },
    cases := i.cases.map fun c =>
      { c with items := c.items.map f, ranges := c.ranges.map fun (a, b) => (f a, f b) } }

/-- The instructions that `i` reads as operands. -/
def RawInst.uses (i : RawInst) : Array InstId :=
  let ids (v : Val) : Array InstId := match v with | .inst id => #[id] | _ => #[]
  i.args.flatMap ids ++ (i.callee.map ids).getD #[] ++
    i.cases.flatMap (fun c => c.items.flatMap ids ++ c.ranges.flatMap fun (a, b) => ids a ++ ids b) ++
    (i.asm.map fun a => (a.outputs ++ a.inputs).flatMap fun o => (o.ref.map ids).getD #[]).getD #[]

/-- Instruction references inside a value, constants included. -/
partial def valRefs (v : Val) : Array InstId :=
  match v with
  | .inst id => #[id]
  | .agg _ vs => vs.flatMap valRefs
  | .optSome _ v | .errUnionOk _ v | .unionVal _ _ v => valRefs v
  | .sliceConst _ p n => valRefs p ++ valRefs n
  | _ => #[]

/-- One malformed-input finding, anchored at an exported instruction when it has one. -/
structure Violation where
  inst : Option InstId
  message : String

/-- Branch targets must be enclosing blocks; repeats must name an enclosing loop; dispatches
must name an enclosing loop-switch (including an outer one across nested control flow). -/
private partial def targetViolations (fnName : String) (ids : Std.HashSet InstId) (body : Array RawInst)
    (blocks loops dispatches : Array InstId) (available : Std.HashSet InstId)
    (acc : Array Violation) : Array Violation := Id.run do
  let mut acc := acc
  let mut available := available
  for i in body do
    -- An unknown reference was already reported; only a known one can be out of scope.
    for r in i.uses do
      unless available.contains r || !ids.contains r do
        acc := acc.push ⟨some i.id, s!"{fnName}: inst {i.id}: instruction ref {r} is not available in this scope"⟩
    if i.tag == "br" || i.tag == "repeat" || i.tag == "switch_dispatch" then
      let (targetKind, allowed) := match i.tag with
        | "repeat" => ("loop", loops)
        | "switch_dispatch" => ("loop-switch", dispatches)
        | _ => ("block", blocks)
      match i.target with
      | none => acc := acc.push ⟨some i.id, s!"{fnName}: inst {i.id}: missing target"⟩
      | some t =>
        unless allowed.contains t do
          acc := acc.push ⟨some i.id, s!"{fnName}: inst {i.id}: target {t} is not an enclosing {targetKind}"⟩
    let nestedBlocks := if i.tag == "block" || i.tag == "dbg_inline_block" || i.tag == "loop"
      then blocks.push i.id else blocks
    let nestedLoops := if i.tag == "loop" then loops.push i.id else loops
    let nestedDispatches := if i.tag == "loop_switch_br" then dispatches.push i.id else dispatches
    for b in #[i.body, i.thenBody, i.elseBody] ++ i.cases.map (·.body) do
      acc := targetViolations fnName ids b nestedBlocks nestedLoops nestedDispatches available acc
    available := available.insert i.id
  return acc

/-- Every invalid reference, in the order `validateRefs` meets them. A check that depends on
an already reported finding of the same operand is skipped; independent findings are not. -/
def refViolations (f : RawFunc) : Array Violation := Id.run do
  let all := flatten f.body
  let mut acc : Array Violation := #[]
  let mut ids : Std.HashSet InstId := {}
  for i in all do
    if ids.contains i.id then acc := acc.push ⟨some i.id, s!"{f.name}: duplicate instruction id {i.id}"⟩
    ids := ids.insert i.id
  for i in all do
    let values := i.args ++ i.callee.toArray ++
      i.cases.flatMap (fun c => c.items ++ c.ranges.flatMap fun (a, b) => #[a, b]) ++
      (i.asm.map fun a => (a.outputs ++ a.inputs).flatMap fun o =>
        o.ref.toArray).getD #[]
    for v in values do
      let refs := valRefs v
      -- Exported constants contain constants, never SSA references. Renumbering and use
      -- analysis operate on instruction operands; reject a hidden dynamic operand before
      -- those passes can lose its use or leave its original ID embedded in a constant.
      if let .inst _ := v then
        for r in refs do
          unless ids.contains r do acc := acc.push ⟨some i.id, s!"{f.name}: inst {i.id}: unknown instruction ref {r}"⟩
      else if let some r := refs[0]? then
        acc := acc.push ⟨some i.id, s!"{f.name}: inst {i.id}: nested instruction ref {r} inside a constant is outside the subset"⟩
    -- Shuffle masks are comptime values; an SSA lane would need use tracking and ID
    -- rewriting, and cannot occur in an ordinary compiler export.
    for lane in i.mask do
      if let .value v := lane then
        if let some r := (valRefs v)[0]? then
          acc := acc.push ⟨some i.id, s!"{f.name}: inst {i.id}: instruction ref {r} inside a shuffle mask is outside the subset"⟩
  for g in f.globals do
    if let some v := g.init then
      if let some r := (valRefs v)[0]? then
        acc := acc.push ⟨none, s!"{f.name}: instruction ref {r} inside a global initializer is outside the subset"⟩
  return targetViolations f.name ids f.body #[] #[] #[] {} acc

/-- Reject invalid references before renumbering can turn an absent old ID into a fresh ID:
the first of `refViolations`. -/
def validateRefs (f : RawFunc) : Except String Unit :=
  match (refViolations f)[0]? with
  | some v => throw v.message
  | none => pure ()

def isDbgTag (tag : String) : Bool :=
  tag == "dbg_stmt" || tag == "dbg_empty_stmt" || tag == "dbg_var_ptr" || tag == "dbg_var_val" ||
    tag == "dbg_arg_inline"

/-- Each body's next non-debug instruction, including every nested body. -/
def nextNonDebug (body : Array RawInst) : Std.HashMap InstId InstId := Id.run do
  let all := flatten body
  let bodies := #[body] ++ all.flatMap fun i =>
    #[i.body, i.thenBody, i.elseBody] ++ i.cases.map (·.body)
  let mut next : Std.HashMap InstId InstId := {}
  for b in bodies do
    let ids := (b.filter (!isDbgTag ·.tag)).map (·.id)
    for (a, c) in ids.zip (ids.extract 1 ids.size) do next := next.insert a c
  return next

/-- For a pointer projection: the value read that a `load` through it equals, and the field
index for a struct field. `slice_elem_ptr` takes the slice value itself, not a pointer. -/
def projection? (i : RawInst) : Option (String × Option Nat) :=
  match i.tag with
  | "struct_field_ptr" => some ("struct_field_val", i.index)
  | "struct_field_ptr_index_0" => some ("struct_field_val", some 0)
  | "struct_field_ptr_index_1" => some ("struct_field_val", some 1)
  | "struct_field_ptr_index_2" => some ("struct_field_val", some 2)
  | "struct_field_ptr_index_3" => some ("struct_field_val", some 3)
  | "ptr_slice_len_ptr" => some ("slice_len", none)
  | "slice_elem_ptr" => some ("slice_elem_val", none)
  | _ => none

/-- For each instruction (nested bodies included): its position as a chain of (body number,
index in that body), from the function's own body (number 0) down to the body that holds it.
Bodies are numbered in order. -/
partial def positions (body : Array RawInst) : Std.HashMap InstId (Array (Nat × Nat)) :=
  let rec go (body : Array RawInst) (bid : Nat) (chain : Array (Nat × Nat))
      (st : Nat × Std.HashMap InstId (Array (Nat × Nat))) :
      Nat × Std.HashMap InstId (Array (Nat × Nat)) :=
    (body.mapIdx fun k i => (k, i)).foldl (init := st) fun (next, m) (k, i) =>
      let c := chain.push (bid, k)
      let nested := #[i.body, i.thenBody, i.elseBody] ++ i.cases.map (·.body)
      nested.foldl (init := (next, m.insert i.id c)) fun (next, m) b =>
        go b (next + 1) c (next + 1, m)
  (go body 0 #[] (0, {})).2

/-- `u` runs after `s` on every path that reaches `u` from `s`'s body: it is later in `s`'s body,
or nested in an instruction that is. -/
def runsAfter (pos : Std.HashMap InstId (Array (Nat × Nat))) (s u : InstId) : Bool :=
  match (pos.getD s #[]).back? with
  | some (b, k) => (pos.getD u #[]).any fun (b', k') => b' == b && k' > k
  | none => false

/-- `forwardReadOnlyCopies` (module doc). A copy is forwarded only if every use of every pointer
derived from it is a `load`, another such projection, or a debug instruction; otherwise the
function keeps its pointers, and `Check.lean` decides. -/
def forwardReadOnlyCopies (f : RawFunc) : RawFunc := Id.run do
  let all := flatten f.body
  let mut users : Std.HashMap InstId (Array RawInst) := {}
  for i in all do
    for u in i.uses do
      users := users.insert u ((users.getD u #[]).push i)
  let isConstPtr (ty : Option TyId) : Bool :=
    match ty.bind (f.types[·]?) with | some (.ptr _ c _) => c | _ => false
  -- A volatile read is an observable device effect (L13), never a forwardable copy read.
  let isVolatilePtr (ty : Option TyId) : Bool :=
    ((ty.bind (f.layouts[·]?)).map (·.isVolatile)).getD false
  let pos := positions f.body
  -- Adjacent projection/load chains have no intervening write or call. This retains the
  -- value form for pure slice reads, while delayed or repeated reads stay at each load.
  let next := nextNonDebug f.body
  let rec adjacentRead (p : InstId) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
    match (users.getD p #[]).filter (!isDbgTag ·.tag) with
    | #[u] =>
      next[p]? == some u.id && u.args[0]? == some (.inst p) &&
        !isVolatilePtr u.ty &&
        (u.tag == "load" || (u.tag != "slice_elem_ptr" && (projection? u).isSome &&
          adjacentRead u.id fuel))
    | _ => false
  -- Copies: an `alloc` whose uses are one `store` of a value into it, and `bitcast`s to a const
  -- pointer after that store in the store's own body (`runsAfter`). So the store runs before
  -- every read on every path, and the stored value (an SSA value) never changes.
  let mut copyVal : Std.HashMap InstId Val := {}
  for a in all do
    if a.tag != "alloc" then continue
    let us := users.getD a.id #[]
    let stores := us.filter fun u =>
      (u.tag == "store" || u.tag == "store_safe") && u.args[0]? == some (.inst a.id) &&
        u.args[1]? != some (.inst a.id)
    let rest := us.filter fun u => !(stores.any (·.id == u.id))
    if let #[s] := stores then
      if let some v := s.args[1]? then
        if (match v with | .undef _ => false | _ => true) &&
            rest.all (fun u => u.tag == "bitcast" && isConstPtr u.ty && !isVolatilePtr u.ty &&
              (a.ty.bind fun sourceTy => u.ty.map (samePointee f.types sourceTy)).getD false &&
              runsAfter pos s.id u.id) then
          copyVal := copyVal.insert a.id v
  -- Read-only pointers into the copy itself. Slice elements live in separate, mutable memory;
  -- their loads must stay at the load's position even if the slice value is immutable.
  let mut ptrs : Std.HashSet InstId := {}
  for i in all do
    match i.tag, (i.args[0]? : Option Val) with
    | "bitcast", some (.inst a) => if copyVal.contains a then ptrs := ptrs.insert i.id
    | "slice_elem_ptr", _ =>
      if !isVolatilePtr i.ty && adjacentRead i.id all.size then
        ptrs := ptrs.insert i.id
    | _, some (.inst p) =>
      if i.tag != "slice_elem_ptr" && (projection? i).isSome && ptrs.contains p then
        ptrs := ptrs.insert i.id
    | _, _ => pure ()
  -- Keep only pointers read by `load`, by a kept projection, or by a debug instruction, and
  -- projections of a kept pointer.
  let byId : Std.HashMap InstId RawInst := all.foldl (fun m i => m.insert i.id i) {}
  let mut changed := true
  while changed do
    changed := false
    for p in ptrs.toArray do
      let baseOk := match byId[p]? with
        | some i => i.tag == "bitcast" || i.tag == "slice_elem_ptr" ||
          match (i.args[0]? : Option Val) with | some (.inst b) => ptrs.contains b | _ => false
        | none => false
      let ok := baseOk && (users.getD p #[]).all fun u =>
        isDbgTag u.tag || (u.tag == "load" && u.args[0]? == some (.inst p)) ||
          ((projection? u).isSome && u.tag != "slice_elem_ptr" && u.args[0]? == some (.inst p) &&
            ptrs.contains u.id)
      if !ok then ptrs := ptrs.erase p; changed := true
  -- A copy is dropped only if every `bitcast` of it is kept.
  let copies := copyVal.toArray.filterMap fun (a, _) =>
    if (users.getD a #[]).all (fun u => u.tag != "bitcast" || ptrs.contains u.id) then some a
    else none
  -- The value that replaces each dropped `bitcast` and `load`, in body order.
  let mut subst : Std.HashMap InstId Val := {}
  let sv (subst : Std.HashMap InstId Val) (v : Val) : Val :=
    match v with | .inst id => subst.getD id v | _ => v
  for i in all do
    match i.tag, (i.args[0]? : Option Val) with
    | "bitcast", some (.inst a) =>
      if ptrs.contains i.id then
        if let some v := copyVal[a]? then subst := subst.insert i.id (sv subst v)
    | "load", some (.inst p) =>
      if ptrs.contains p then subst := subst.insert i.id (sv subst (.inst p))
    | _, _ => pure ()
  let dropped (i : RawInst) : Bool :=
    (i.tag == "alloc" && copies.contains i.id) ||
    ((i.tag == "store" || i.tag == "store_safe") &&
      match (i.args[0]? : Option Val) with | some (.inst a) => copies.contains a | _ => false) ||
    subst.contains i.id ||
    (isDbgTag i.tag && i.uses.any fun u => subst.contains u || copies.contains u)
  let body := rewriteBody (body := f.body) fun i =>
    if dropped i then none
    else
      let i := i.mapVals (sv subst)
      match projection? i with
      | some (tag, index) =>
        if ptrs.contains i.id then
          let child := match i.ty.bind (f.types[·]?) with | some (.ptr _ _ c) => some c | _ => i.ty
          some { i with tag, index := index.orElse fun _ => i.index, ty := child }
        else some i
      | none => some i
  return { f with body }

/-- A safety check: `block { cond_br c then { br } else { … unreach } }`, whose `then` body only
leaves the block and whose `else` body cannot branch out. After it, `c` is true. The condition
`c`, if the block is one. -/
def checkCond? (b : RawInst) : Option InstId :=
  match b.tag, b.body with
  | "block", #[cb] =>
    match cb.tag, (cb.args[0]? : Option Val), cb.thenBody, cb.elseBody.back? with
    | "cond_br", some (.inst c), #[br], some last =>
      if br.tag == "br" && br.target == some b.id && br.args == #[.void] &&
          (last.tag == "unreach" || last.tag == "trap") &&
          !(flatten cb.elseBody).any (·.tag == "br")
      then some c else none
    | _, _, _, _ => none
  | _, _ => none

/-- `dropTrueChecks` (module doc). -/
partial def dropTrueChecks (f : RawFunc) : RawFunc := Id.run do
  let all := flatten f.body
  let mut users : Std.HashMap InstId (Array RawInst) := {}
  for i in all do
    for u in i.uses do
      users := users.insert u ((users.getD u #[]).push i)
  let byId : Std.HashMap InstId RawInst := all.foldl (fun m i => m.insert i.id i) {}
  let key (c : InstId) : Option (String × Array Val) :=
    (byId[c]?).bind fun i => if i.tag.startsWith "cmp_" then some (i.tag, i.args) else none
  let mut gone : Std.HashSet InstId := {}
  let bodies := #[f.body] ++ all.flatMap fun i =>
    #[i.body, i.thenBody, i.elseBody] ++ i.cases.map (·.body)
  for b in bodies do
    let mut known : Array (String × Array Val) := #[]
    for i in b do
      let some c := checkCond? i | continue
      unless (i.ty.bind (f.types[·]?)) == some .void && (users.getD i.id #[]).isEmpty do continue
      let some k := key c | continue
      let unsigned (t : Option TyId) : Bool :=
        match t.bind (f.types[·]?) with | some (.int false _) => true | _ => false
      -- `0 <= x` and `x <= x + y` (an `add` does not wrap) for unsigned `x`, `y`.
      let alwaysLe := match k with
        | ("cmp_lte", #[.int t 0, _]) => unsigned (some t)
        | ("cmp_lte", #[x, .inst y]) => match byId[y]? with
          | some a => (a.tag == "add" || a.tag == "add_safe") && a.args[0]? == some x && unsigned a.ty
          | none => false
        | _ => false
      -- The condition has no use but this check, and it is always true.
      if (alwaysLe || known.contains k) &&
          (users.getD c #[]).all (fun u => some u.id == (i.body[0]?.map (·.id))) then
        gone := (gone.insert c).insert i.id
      else known := known.push k
  let body := rewriteBody (body := f.body) fun i =>
    if gone.contains i.id || (isDbgTag i.tag && i.uses.any gone.contains) then none else some i
  return { f with body }

/-- `itemReads` (module doc). -/
def itemReads (f : RawFunc) : RawFunc := Id.run do
  let all := flatten f.body
  let mut users : Std.HashMap InstId (Array RawInst) := {}
  for i in all do
    for u in i.uses do
      users := users.insert u ((users.getD u #[]).push i)
  let only (x : InstId) : Option RawInst :=
    match (users.getD x #[]).filter (!isDbgTag ·.tag) with
    | #[u] => some u
    | _ => none
  -- The non-debug instruction after each one in the same body.
  let next := nextNonDebug f.body
  -- The item read that replaces each instruction, and the instructions that go.
  let mut repl : Std.HashMap InstId (String × Val × Val) := {}
  let mut gone : Std.HashSet InstId := {}
  for x in all do
    match x.tag, x.args[0]?, x.args[1]?, only x.id with
    | "slice_elem_ptr", some s, some idx, some u =>
      if u.tag == "load" && u.args[0]? == some (.inst x.id) then
        repl := repl.insert u.id ("slice_elem_val", s, idx); gone := gone.insert x.id
    | "ptr_elem_ptr", some p, some i, some u =>
      -- A lane pointer (`&v[i]` of a bit-packed vector) is a bit-pointer, not an item.
      let lane := ((x.ty.bind (f.layouts[·]?)).map (·.isLanePtr)).getD false
      if !lane && u.tag == "load" && u.args[0]? == some (.inst x.id) then
        repl := repl.insert u.id ("ptr_elem_val", p, i); gone := gone.insert x.id
    | "load", some p, _, some u =>
      -- A lane of a bit-packed vector (`bool`, `u3`, `u24`, `f80`) is not an item at a byte
      -- stride: the whole-vector load and `array_elem_val` stay.
      let packed := match x.ty.bind (f.types[·]?) with
        | some (.vector _ c) => match f.types[c]? with
          | some (.int _ bits) | some (.float bits) => bits < 8 || bits &&& (bits - 1) != 0
          | _ => true
        | _ => false
      if !packed && u.tag == "array_elem_val" && u.args[0]? == some (.inst x.id) &&
          next[x.id]? == some u.id then
        if let some i := u.args[1]? then
          repl := repl.insert u.id ("ptr_elem_val", p, i); gone := gone.insert x.id
    | _, _, _, _ => pure ()
  let body := rewriteBody (body := f.body) fun i =>
    if gone.contains i.id || (isDbgTag i.tag && i.uses.any gone.contains) then none
    else match repl[i.id]? with
      | some (tag, p, idx) => some { i with tag, args := #[p, idx] }
      | none => some i
  return { f with body }

/-- The side-effect-free pointer projections that Sema maps from a comptime-known `alloc` to its
constant (`resolveComptimeKnownAllocPtr`); operand 0 is the parent pointer. Sema rewrites the
writing ones (`optional_payload_ptr_set`, `errunion_payload_ptr_set`) to placeholders itself, so
one that reads a placeholder is not dropped. -/
def allocProjectionTags : List String :=
  ["struct_field_ptr", "struct_field_ptr_index_0", "struct_field_ptr_index_1",
   "struct_field_ptr_index_2", "struct_field_ptr_index_3", "ptr_slice_ptr_ptr",
   "ptr_slice_len_ptr", "ptr_elem_ptr", "bitcast"]

/-- `dropDeadAllocPlaceholders` (module doc). A placeholder is a `bitcast` of the integer 0 to a
non-`allowzero`, non-C pointer: Sema's rewrite of the `alloc` and the stores of a comptime-known
local (`finishResolveComptimeKnownAllocPtr`, 0.15.2 and 0.16.0), whose live uses it redirects to
a constant pointer into a global. Source code cannot make it: `@ptrFromInt(0)` to such a pointer
is a compile error. The placeholders and their projections go, with their debug uses, only if
nothing else reads them; otherwise they stay and `Check.lean` rejects the placeholder. -/
def dropDeadAllocPlaceholders (f : RawFunc) : RawFunc := Id.run do
  let all := flatten f.body
  let placeholder (i : RawInst) : Bool :=
    i.tag == "bitcast" && i.args.size == 1 &&
      (match (i.args[0]? : Option Val) with | some (.int _ 0) => true | _ => false) &&
      match i.ty with
      | some t => (match f.types[t]? with | some (.ptr size _ _) => size != "slice" | _ => false) &&
          !nullablePtrTy f.types f.layouts t
      | none => false
  if !all.any placeholder then return f
  -- The placeholders and, to a fixpoint, the projections of one.
  let mut dead : Std.HashSet InstId := {}
  for i in all do
    if placeholder i then dead := dead.insert i.id
  let mut changed := true
  while changed do
    changed := false
    for i in all do
      if !dead.contains i.id && allocProjectionTags.contains i.tag then
        if let some (.inst p) := (i.args[0]? : Option Val) then
          if dead.contains p then dead := dead.insert i.id; changed := true
  -- Every non-debug reader must itself go.
  let read := all.any fun i => !isDbgTag i.tag && !dead.contains i.id && i.uses.any dead.contains
  if read then return f
  let body := rewriteBody (body := f.body) fun i =>
    if dead.contains i.id || (isDbgTag i.tag && i.uses.any dead.contains) then none else some i
  return { f with body }

/-- `renumber` (module doc). -/
def renumber (f : RawFunc) : RawFunc :=
  let all := flatten f.body
  let order := all.filter (!isDbgTag ·.tag) ++ all.filter (isDbgTag ·.tag)
  let ids : Std.HashMap InstId InstId :=
    (order.mapIdx fun k i => (i.id, k)).foldl (fun m (a, b) => m.insert a b) {}
  let r (id : InstId) : InstId := ids.getD id id
  let rv (v : Val) : Val := match v with | .inst id => .inst (r id) | _ => v
  let body := rewriteBody (body := f.body) fun i =>
    some { (i.mapVals rv) with id := r i.id, target := i.target.map r }
  { f with body }

/-- Types whose parameter has no AIR `arg`: Zig still keeps their slot in the runtime
function signature. Comptime parameters, in contrast, have no slot in `params`. -/
partial def onePossibleValue (types : Array Ty) (id : TyId) (seen : Array TyId := #[]) : Bool :=
  if seen.contains id then false else
  let recur := fun t => onePossibleValue types t (seen.push id)
  match types[id]? with
  | some .void | some (.int _ 0) => true
  | some (.enum _ _ true fields) => fields.size == 1
  | some (.errorSet (some names)) => names.size == 1
  | some (.array len c _) | some (.vector len c) => len == 0 || recur c
  | some (.struct _ _ fields) => fields.all (recur ·.2)
  | some (.tuple fields) => fields.all recur
  | some (.union _ _ _ fields) => fields.size == 1 && fields.all (recur ·.2)
  | some (.optional c) => types[c]? == some .noreturn
  | some (.errorUnion set payload) =>
    match types[set]? with
    | some (.errorSet (some names)) =>
      (names.isEmpty && recur payload) || (names.size == 1 && types[payload]? == some .noreturn)
    | _ => false
  | _ => false

private def argRanking (f : RawFunc) : Array Nat × Array Nat :=
  let ps := ((flatten f.body).filterMap fun i => if i.tag == "arg" then i.param else none)
  let ranks := (ps.qsort (· < ·)).toList.eraseDups.toArray
  let slots := (Array.range f.params.size).filter fun k => !onePossibleValue f.types f.params[k]!
  (ranks, slots)

/-- Every `arg` that cannot be ranked. A count mismatch makes every rank meaningless, so it
is reported alone; otherwise each malformed `arg` is reported. -/
def argViolations (f : RawFunc) : Array Violation := Id.run do
  let (ranks, slots) := argRanking f
  unless ranks.size == slots.size do
    return #[⟨none, s!"{f.name}: AIR args do not match non-OPV runtime parameters ({ranks.size} args, {slots.size} slots)"⟩]
  let rank (p : Nat) : Nat := slots[(ranks.idxOf? p).getD slots.size]!
  let mut acc := #[]
  for i in flatten f.body do
    if i.tag == "arg" then
      match i.param with
      | none => acc := acc.push ⟨some i.id, s!"{f.name}: inst {i.id}: 'arg' needs 'param'"⟩
      | some p =>
        unless i.ty == some f.params[rank p]! do
          acc := acc.push ⟨some i.id, s!"{f.name}: inst {i.id}: arg type does not match its runtime parameter"⟩
  return acc

/-- Rank source indexes against non-OPV runtime slots, preserving omitted OPV parameters. -/
def argRanks (f : RawFunc) : Except String RawFunc := do
  if let some v := (argViolations f)[0]? then throw v.message
  let (ranks, slots) := argRanking f
  let rank (p : Nat) : Nat := slots[(ranks.idxOf? p).getD slots.size]!
  let body := rewriteBody (body := f.body) fun i =>
    some (if i.tag == "arg" then { i with param := i.param.map rank } else i)
  pure { f with body }

/-- The six rewrites (module doc). -/
def canonicalize (f : RawFunc) : Except String RawFunc := do
  let f ← versionTags f
  validateRefs f
  let f ← argRanks f
  let f := dropTrueChecks (itemReads (forwardReadOnlyCopies (dropDeadAllocPlaceholders f)))
  validateRefs f
  pure (renumber f)

end Air2Lean.Raw
