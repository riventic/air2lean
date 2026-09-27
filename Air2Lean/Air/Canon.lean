import Std.Data.HashMap
import Std.Data.HashSet
import Air2Lean.Air.Json

/-!
# Canonical AIR

Two rewrites of the raw JSON (`Raw.RawFunc`), the same for every Zig version, before
`Normalize.lean` reads the tags. After them, the same Zig code gives the same `Func` in every
supported version, so one translation (and the proofs over it) serves all versions.

1. `forwardReadOnlyCopies`. Sema lowers `&v` of a constant value `v` (a parameter, a union
   payload) to a read-only stack copy: `alloc`, one `store` of `v`, and `bitcast`s to a const
   pointer after the store in the store's own body. Only this shape is rewritten: a `bitcast`
   outside that body, or a second store, keeps the `alloc`. Zig 0.16.0 reads a field, the
   length or an element of a struct, union or slice value through such a copy
   (`struct_field_ptr_index_N`, `ptr_slice_len_ptr`, `slice_elem_ptr`, then `load`), where 0.15.2
   reads the value (`struct_field_val`, `slice_len`, `slice_elem_val`). Nothing writes the copy,
   so a read through it equals the read of the value. The pass changes each such pointer
   projection to the value read, and drops the copy, the `bitcast`s and the `load`s.
2. `renumber`. Instruction IDs name generated definitions (`<fn>.loop<id>`, `.br<id>`), and the
   debug instructions that a version adds shift them. The pass gives the non-debug instructions
   the IDs `0, 1, …` in body order, then the debug instructions the IDs after them.
-/

namespace Air2Lean.Raw

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

/-- `i` with `f` applied to each value operand (not to nested bodies). -/
def RawInst.mapVals (f : Val → Val) (i : RawInst) : RawInst :=
  { i with
    args := i.args.map f, callee := i.callee.map f,
    cases := i.cases.map fun c =>
      { c with items := c.items.map f, ranges := c.ranges.map fun (a, b) => (f a, f b) } }

/-- The instructions that `i` reads as operands. -/
def RawInst.uses (i : RawInst) : Array InstId :=
  let ids (v : Val) : Array InstId := match v with | .inst id => #[id] | _ => #[]
  i.args.flatMap ids ++ (i.callee.map ids).getD #[] ++
    i.cases.flatMap fun c => c.items.flatMap ids ++ c.ranges.flatMap fun (a, b) => ids a ++ ids b

def isDbgTag (tag : String) : Bool :=
  tag == "dbg_stmt" || tag == "dbg_empty_stmt" || tag == "dbg_var_ptr" || tag == "dbg_var_val" ||
    tag == "dbg_arg_inline"

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

/-- For each instruction `i` of `body` (nested bodies included): the instructions after `i` in
its own body, and everything nested in them. They run after `i` on every path that reaches
them. -/
partial def afterIds (body : Array RawInst) : Std.HashMap InstId (Std.HashSet InstId) :=
  let nested (i : RawInst) : Array (Array RawInst) :=
    #[i.body, i.thenBody, i.elseBody] ++ i.cases.map (·.body)
  (body.mapIdx fun k i => (k, i)).foldl (init := {}) fun m (k, i) =>
    let later := (flatten (body.extract (k + 1) body.size)).foldl (fun s j => s.insert j.id) {}
    (nested i).foldl (fun m b => (afterIds b).fold (fun m a s => m.insert a s) m)
      (m.insert i.id later)

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
  let after := afterIds f.body
  -- Copies: an `alloc` whose uses are one `store` of a value into it, and `bitcast`s to a const
  -- pointer after that store in the store's own body (`afterIds`). So the store runs before
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
        let later := after.getD s.id {}
        if (match v with | .undef _ => false | _ => true) &&
            rest.all (fun u => u.tag == "bitcast" && isConstPtr u.ty && later.contains u.id) then
          copyVal := copyVal.insert a.id v
  -- Read-only pointers: a `bitcast` of a copy, or a projection of one (or of a slice value).
  let mut ptrs : Std.HashSet InstId := {}
  for i in all do
    match i.tag, (i.args[0]? : Option Val) with
    | "bitcast", some (.inst a) => if copyVal.contains a then ptrs := ptrs.insert i.id
    | "slice_elem_ptr", _ => ptrs := ptrs.insert i.id
    | _, some (.inst p) => if (projection? i).isSome && ptrs.contains p then ptrs := ptrs.insert i.id
    | _, _ => pure ()
  -- Keep only pointers read by `load`, by a kept projection, or by a debug instruction.
  let mut changed := true
  while changed do
    changed := false
    for p in ptrs.toArray do
      let ok := (users.getD p #[]).all fun u =>
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

/-- Both rewrites (module doc). -/
def canonicalize (f : RawFunc) : RawFunc := renumber (forwardReadOnlyCopies f)

end Air2Lean.Raw
