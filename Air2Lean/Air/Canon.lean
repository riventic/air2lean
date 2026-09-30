import Std.Data.HashMap
import Std.Data.HashSet
import Air2Lean.Air.Json

/-!
# Canonical AIR

Five rewrites of the raw JSON (`Raw.RawFunc`), the same for every Zig version, before
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
2. `itemReads`. A read of one item through a pointer is `ptr_elem_val` in 0.15.2, and
   `ptr_elem_ptr` then `load` in 0.16.0. A read of one item of a local array is a `load` of the
   whole array then `array_elem_val` in 0.15.2, and the same `ptr_elem_ptr` and `load` in 0.16.0.
   The pass changes both pairs to one `ptr_elem_val`, if the first instruction has no other use.
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
   `m` as `param 2`). The pass gives each `arg` the rank of its index among the `arg`s, so
   `param` is the index of the runtime parameter (`p0, p1, …`).
5. `renumber`. Instruction IDs name generated definitions (`<fn>.loop<id>`, `.br<id>`), and the
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
  let pos := positions f.body
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
            rest.all (fun u => u.tag == "bitcast" && isConstPtr u.ty && runsAfter pos s.id u.id) then
          copyVal := copyVal.insert a.id v
  -- Read-only pointers: a `bitcast` of a copy, or a projection of one (or of a slice value).
  let mut ptrs : Std.HashSet InstId := {}
  for i in all do
    match i.tag, (i.args[0]? : Option Val) with
    | "bitcast", some (.inst a) => if copyVal.contains a then ptrs := ptrs.insert i.id
    | "slice_elem_ptr", _ => ptrs := ptrs.insert i.id
    | _, some (.inst p) => if (projection? i).isSome && ptrs.contains p then ptrs := ptrs.insert i.id
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
leaves the block. After it, `c` is true. The condition `c`, if the block is one. -/
def checkCond? (b : RawInst) : Option InstId :=
  match b.tag, b.body with
  | "block", #[cb] =>
    match cb.tag, (cb.args[0]? : Option Val), cb.thenBody, cb.elseBody.back? with
    | "cond_br", some (.inst c), #[br], some last =>
      if br.tag == "br" && br.target == some b.id && (last.tag == "unreach" || last.tag == "trap")
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
  let mut next : Std.HashMap InstId InstId := {}
  let bodies := #[f.body] ++ all.flatMap fun i =>
    #[i.body, i.thenBody, i.elseBody] ++ i.cases.map (·.body)
  for b in bodies do
    let ids := (b.filter (!isDbgTag ·.tag)).map (·.id)
    for (a, c) in ids.zip (ids.extract 1 ids.size) do
      next := next.insert a c
  -- The item read that replaces each instruction, and the instructions that go.
  let mut repl : Std.HashMap InstId (Val × Val) := {}
  let mut gone : Std.HashSet InstId := {}
  for x in all do
    match x.tag, x.args[0]?, x.args[1]?, only x.id with
    | "ptr_elem_ptr", some p, some i, some u =>
      if u.tag == "load" && u.args[0]? == some (.inst x.id) then
        repl := repl.insert u.id (p, i); gone := gone.insert x.id
    | "load", some p, _, some u =>
      if u.tag == "array_elem_val" && u.args[0]? == some (.inst x.id) && next[x.id]? == some u.id then
        if let some i := u.args[1]? then
          repl := repl.insert u.id (p, i); gone := gone.insert x.id
    | _, _, _, _ => pure ()
  let body := rewriteBody (body := f.body) fun i =>
    if gone.contains i.id || (isDbgTag i.tag && i.uses.any gone.contains) then none
    else match repl[i.id]? with
      | some (p, idx) => some { i with tag := "ptr_elem_val", args := #[p, idx] }
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

/-- `argRanks` (module doc). -/
def argRanks (f : RawFunc) : RawFunc :=
  let ps := ((flatten f.body).filterMap fun i => if i.tag == "arg" then i.param else none)
  let ranks := (ps.qsort (· < ·)).toList.eraseDups.toArray
  let rank (p : Nat) : Nat := (ranks.idxOf? p).getD p
  let body := rewriteBody (body := f.body) fun i =>
    some (if i.tag == "arg" then { i with param := i.param.map rank } else i)
  { f with body }

/-- The five rewrites (module doc). -/
def canonicalize (f : RawFunc) : RawFunc :=
  renumber (dropTrueChecks (itemReads (forwardReadOnlyCopies (argRanks f))))

end Air2Lean.Raw
