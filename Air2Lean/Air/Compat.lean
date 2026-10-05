import Air2Lean.Air.Op
import Std.Data.HashSet

/-! Equality across file-local tables is structural, including every modeled layout fact.
The worklists track pairs, so pointer type cycles and global initializer cycles terminate. -/
namespace Air2Lean

private def typeShape (t : Ty) : Ty :=
  match t with
  | .ptr s c _ => .ptr s c 0
  | .array n _ s => .array n 0 s
  | .vector n _ => .vector n 0
  | .optional _ => .optional 0
  | .errorUnion _ _ => .errorUnion 0 0
  | .struct n l fs => .struct n l (fs.map fun (n, _) => (n, 0))
  | .enum n _ e fs => .enum n 0 e fs
  | .union n l t fs => .union n l (t.map fun _ => 0) (fs.map fun (n, _) => (n, 0))
  | .tuple fs => .tuple (fs.map fun _ => 0)
  | t => t

/-- Exact modeled type/layout equality; IDs themselves are local to each file. No casts. -/
def compatibleType (a b : Func) (x y : TyId) : Bool := Id.run do
  let mut todo := [(x, y)]
  let mut seen : Std.HashSet (TyId × TyId) := {}
  while !todo.isEmpty do
    let (i, j) := todo.head!
    todo := todo.tail!
    if seen.contains (i, j) then continue
    let some t := a.types[i]? | return false
    let some u := b.types[j]? | return false
    if typeShape t != typeShape u || a.layouts[i]? != b.layouts[j]? then return false
    seen := seen.insert (i, j)
    todo := (childTys t |>.zip (childTys u)).toList ++ todo
  return true

private inductive DefinitionTask where
  | global (a b : Nat)
  | value (a b : Val)
  deriving Inhabited

/-- Compare globals within one exact ordered pair of file-local tables. Only a complete
successful traversal publishes visited global pairs; failure leaves the caller's cache intact. -/
def compatibleGlobalCached (a b : Func) (x y : Nat)
    (completed : Std.HashSet (Nat × Nat) := {}) : Option (Std.HashSet (Nat × Nat)) := Id.run do
  let mut todo := [DefinitionTask.global x y]
  let mut seen := completed
  let mut typePairs : Std.HashSet (TyId × TyId) := {}
  while !todo.isEmpty do
    let task := todo.head!
    todo := todo.tail!
    let ty (i j : TyId) : Bool := typePairs.contains (i, j) || compatibleType a b i j
    match task with
    | .global i j =>
      if seen.contains (i, j) then continue
      let some g := a.globals[i]? | return none
      let some h := b.globals[j]? | return none
      unless g.name == h.name && g.isConst == h.isConst && g.threadlocal == h.threadlocal &&
          g.isExtern == h.isExtern && ty g.ty h.ty do return none
      typePairs := typePairs.insert (g.ty, h.ty)
      seen := seen.insert (i, j)
      match g.init, h.init with
      | some v, some w => todo := .value v w :: todo
      | none, none => pure ()
      | _, _ => return none
    | .value v w =>
      match v, w with
      | .int i v, .int j w | .enumTag i v, .enumTag j w =>
        unless v == w && ty i j do return none
      | .float i v, .float j w => unless v == w && ty i j do return none
      | .bool v, .bool w => unless v == w do return none
      | .void, .void => pure ()
      | .undef i, .undef j | .optNull i, .optNull j
      | .ptrNull i, .ptrNull j => unless ty i j do return none
      | .err i v, .err j w | .errUnionErr i v, .errUnionErr j w
      | .ptrOther i v, .ptrOther j w => unless v == w && ty i j do return none
      | .func v n s, .func w m t => unless v == w && n == m && s == t do return none
      | .optSome i v, .optSome j w | .errUnionOk i v, .errUnionOk j w =>
        unless ty i j do return none
        todo := .value v w :: todo
      | .unionVal i k v, .unionVal j l w =>
        unless k == l && ty i j do return none
        todo := .value v w :: todo
      | .agg i vs, .agg j ws =>
        unless vs.size == ws.size && ty i j do return none
        todo := (vs.zip ws |>.toList.map fun (v, w) => .value v w) ++ todo
      | .ptrConst i g off, .ptrConst j h off' =>
        unless off == off' && ty i j do return none
        todo := .global g h :: todo
      | .sliceConst i p n, .sliceConst j q m =>
        unless ty i j do return none
        todo := .value p q :: .value n m :: todo
      | _, _ => return none
      -- Every typed constructor above checked `ty`; credit only that complete successful
      -- comparison, never provisional child pairs. This cache is local to this exact a/b.
      if let (some i, some j) := (v.constTy?, w.constTy?) then
        typePairs := typePairs.insert (i, j)
  return some seen

/-- Same global definition, following initializer pointers through each file's own table.
Named references retain their identity; unnamed constants compare by their definition. -/
def compatibleGlobal (a b : Func) (x y : Nat) : Bool :=
  (compatibleGlobalCached a b x y).isSome
end Air2Lean
