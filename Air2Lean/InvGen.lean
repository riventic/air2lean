import Lean
import Air2Lean.Revision

/-!
# `air2lean-invgen`: generated loop invariants and measures (P09)

The offline, untrusted invariant generator of `docs/invariant-synthesis.md`. It reads the loops
of a translated module (the `Zig.loop` bodies `F.loopN` with their `F.againN`), as the elaborated
terms that `fsym` walks, and writes their invariants and measures as plain `def`s into a Lean
file (`Inv.lean`). It adds no tactic, judgment or command: the proofs that use the definitions are
`fsym` walks that the kernel checks, so a wrong or too weak invariant makes a proof fail, never a
wrong proof. A loop outside the families below gets no definition: the generator records why in
the file's header and on stderr, and a proof that needs it does not build (fail closed).

Families (layer 2 of the design: numeric facts and measures over the variables of the shape):

* **Counted loop.** One iteration either exits, when an unsigned test `x R b` fails, and writes
  no memory, runs no add or subtraction and changes no local; or it moves the counter `x` (a
  local) by 1 towards `b`, adds a constant `cₖ` to each cell `*pₖ` it writes (`pₖ` a loop
  parameter, the cell an unsigned word), leaves every other local unchanged, runs no other add or
  subtraction, and repeats. `R` is `<` or `<=` when `x` goes up, `>` or `>=` when it goes down,
  or `!=` (either way), with the counter on either side and either branch of `<`/`<=` repeating
  (`¬ x < b` is `x >= b`; a `==` test is outside the family). The bound `b` is a local
  the loop does not write, a loop parameter, a literal, the length of a slice parameter
  (`p.len`) or a cell the loop only reads (`*p`). The invariant pins the other locals and the
  read-only cells to their entry values, bounds the counter between its entry value `x₀` and the
  value it exits at (`b`, or one past `b` for `<=`/`>=`, with the fact that the step there does
  not wrap), states each written cell as `vₖ + cₖ * d` from its entry value `vₖ` (`d` the
  iterations so far), and carries the no-overflow fact `vₖ + cₖ * n < 2 ^ w` (`n` all
  iterations) that the checked adds need. The measure is the iterations left. A body that takes
  a step (`Zig.tick`) runs in the plain mode, so the invariant carries `plain`. The invariant
  holds at entry only for a counter that starts on the repeating side of its exit value (or at
  it): a client proves that, and a loop entered past it is not an instance.

Outside the family (each one recorded with its reason): a cell at an offset of a parameter
(`Zig.ptrProject`), an increment that depends on the counter, a bound of another width
(`@intCast`), a `>= 0` or `<= maxInt` test (it holds until the step wraps), a nested loop, a call.

The body is read by a symbolic run over its monadic term (`bind`, `pure`, `get`, `modify`, `ite`,
the lifted `Zig.load`/`Zig.store`/`Zig.add`/`Zig.sub`/`Zig.intCast`, the unsigned comparisons
`Zig.lt`/`gt`/`le`/`ge`, `!=` (`bne`), a slice's `len`, `Zig.tick`, a `match` on a known exit):
this is a reading of the generated term, not a second semantics. Nothing it concludes is trusted.

The reading proposes candidate facts, and `fsym` decides which of them stay (Houdini pruning,
`houdini`): each candidate is true at loop entry (the counter on either side of its entry value,
a written cell counted up or down from it) or an entry obligation of the family (the counter on
the repeating side of its exit value, the no-wrap and no-overflow facts), the generator walks the step triple of one iteration
over them with `fsym` in its own environment, drops the candidates that the walk's report names
as residuals, and repeats until a walk proves the step. The file's record lists each dropped
candidate with the walk that dropped it.
-/

open Lean Meta

namespace Air2Lean.InvGen

/-- A symbolic value of one iteration, over the values at its start. -/
inductive Sym where
  /-- The local `f` at the start of the iteration. -/
  | local (f : Name)
  /-- The cell at loop parameter `i` at the start of the iteration. -/
  | cell (i : Nat)
  /-- Loop parameter `i`. -/
  | param (i : Nat)
  /-- A literal. -/
  | lit (n : Nat)
  /-- The length of the slice that is loop parameter `i`. -/
  | slen (i : Nat)
  /-- A sum that does not wrap (`Zig.add`: an overflow fails). -/
  | add (a b : Sym)
  /-- A difference that does not wrap (`Zig.sub`: an underflow fails). -/
  | sub (a b : Sym)
  /-- An unsigned widening (`Zig.intCast`). -/
  | widen (a : Sym)
  /-- An unsigned `<` (`a > b` is `b < a`). -/
  | lt (a b : Sym)
  /-- An unsigned `≤` (`a ≥ b` is `b ≤ a`). -/
  | le (a b : Sym)
  /-- `≠` of two words. -/
  | ne (a b : Sym)
  /-- A closed value: an exit constructor, `()`. -/
  | val (e : Expr)
  /-- Snapshot `k` of the locals (a `get`). -/
  | snap (k : Nat)
  deriving Inhabited, BEq

/-- `s` as a base and a constant summand. -/
partial def Sym.split : Sym → Sym × Int
  | .add a (.lit n) | .add (.lit n) a => let (b, k) := a.split; (b, k + n)
  | .sub a (.lit n) => let (b, k) := a.split; (b, k - n)
  | s => (s, 0)

/-- One cell the body accesses: its loop parameter, value type, width and alignment, its current
value, and whether the path stored to it. -/
structure Cell where
  param : Nat
  ty : Expr
  width : Nat
  align : Nat
  val : Sym
  stored : Bool := false
  deriving Inhabited

/-- `()`, the result of a step that returns nothing. -/
def unitV : Sym := .val (.const ``Unit.unit [])

/-- The state of one path through the body. -/
structure St where
  /-- The current value of each local, in field order. -/
  locals : Array Sym
  /-- The accessed cells, in order of first access. -/
  cells : Array Cell := #[]
  /-- The value of every `Zig.add` and `Zig.sub` the path ran: each one fails when it wraps, so
  the invariant must bound it, also when its result is not used. -/
  checked : Array Sym := #[]
  snaps : Array (Array Sym) := #[]
  /-- Whether the path took a step (`Zig.tick`). -/
  tick : Bool := false
  /-- The test the path passed, with its outcome (the families test once per iteration). -/
  cond : Option (Sym × Bool) := none

/-- A path through the body and its result. -/
structure Path where
  st : St
  res : Sym

/-- The loop under analysis. -/
structure Ctx where
  structName : Name
  fields : Array Name
  params : Array FVarId
  env : Std.HashMap FVarId Sym := {}

/-- A natural-number literal (raw or `OfNat.ofNat`). -/
def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then
      match (e.getArg! 1).consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- The width `n` of `BitVec n`. -/
def bitVecWidth? (ty : Expr) : Option Nat :=
  if ty.isAppOfArity ``BitVec 1 then natLit? ty.appArg! else none

def paramIdx? (ctx : Ctx) (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .fvar id => match ctx.env[id]? with
    | some (.param i) => some i
    | some _ => none
    | none => ctx.params.idxOf? id
  | _ => none

/-- The value of a pure term. -/
partial def evalPure (ctx : Ctx) (st : St) (e : Expr) : MetaM Sym := do
  let e := e.headBeta.consumeMData
  if let .fvar id := e then
    if let some v := ctx.env[id]? then return v
    if let some i := ctx.params.idxOf? id then return .param i
    throwError "a free variable outside the body: {e}"
  if let some n := natLit? e then
    -- A word literal is read as its value: one that wraps is outside the families.
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if let some w := bitVecWidth? (e.getArg! 0) then
        unless n < 2 ^ w do throwError "a literal {n} that wraps in {w} bits"
    return .lit n
  -- An unsigned comparison, as `<` or `≤` (`>` and `≥` with the operands swapped).
  for (op, swap, mk) in [(`Zig.lt, false, Sym.lt), (`Zig.gt, true, Sym.lt),
      (`Zig.le, false, Sym.le), (`Zig.ge, true, Sym.le)] do
    if e.isAppOfArity op 4 then
      unless (e.getArg! 1).isConstOf ``Bool.false do throwError "a signed comparison: {e}"
      let a ← evalPure ctx st (e.getArg! 2)
      let b ← evalPure ctx st (e.getArg! 3)
      return if swap then mk b a else mk a b
  if e.isAppOfArity ``bne 4 then
    unless (bitVecWidth? (e.getArg! 0)).isSome do throwError "a `!=` of values that are not words: {e}"
    return .ne (← evalPure ctx st (e.getArg! 2)) (← evalPure ctx st (e.getArg! 3))
  -- The length of a slice, as a projection function or a primitive projection.
  let len? : Option Expr := match e with
    | .proj `Zig.Slice 1 x => some x
    | _ => if e.isAppOfArity `Zig.Slice.len 1 then some e.appArg! else none
  if let some x := len? then
    let some i := paramIdx? ctx x | throwError "the length of a slice that is not a loop parameter"
    return .slen i
  -- A field of the locals, as a projection function or a primitive projection.
  let field? : Option (Nat × Expr) := match e with
    | .proj s i x => if s == ctx.structName then some (i, x) else none
    | _ => match e.getAppFn.constName? with
      | some (.str pre f) =>
        if pre == ctx.structName && e.getAppNumArgs == 1 then
          (ctx.fields.idxOf? (Name.mkSimple f)).map (·, e.appArg!)
        else none
      | _ => none
  if let some (i, x) := field? then
    match ← evalPure ctx st x with
    | .snap k => return st.snaps[k]![i]!
    | _ => throwError "a projection of a value that is not the locals: {e}"
  if !e.hasFVar && !e.hasLooseBVars then return .val e
  throwError "an unsupported term: {e}"

/-- Access the cell at parameter `i` with value type `ty` and alignment `align` (the same at every
access; a new cell holds its entry value): its index in `st.cells`. -/
def St.access (st : St) (i : Nat) (ty : Expr) (align : Nat) : MetaM (St × Nat) := do
  match st.cells.findIdx? (·.param == i) with
  | some k =>
    let c := st.cells[k]!
    unless c.ty == ty && c.align == align do throwError "a cell accessed at two types or alignments"
    return (st, k)
  | none =>
    let some width := bitVecWidth? ty | throwError "a cell that is not an unsigned word: {ty}"
    return ({ st with cells := st.cells.push { param := i, ty, width, align, val := .cell i } },
      st.cells.size)

mutual

/-- The paths of the monadic term `e` from `st`. -/
partial def exec (ctx : Ctx) (st : St) (e : Expr) : MetaM (Array Path) := do
  let e := e.headBeta.consumeMData
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Bind.bind =>
    if args.size != 6 then throwError "a partial bind: {e}"
    let mut out := #[]
    for p in ← exec ctx st args[4]! do
      out := out ++ (← apply ctx p.st args[5]! p.res)
    return out
  | some ``Pure.pure =>
    if args.size != 4 then throwError "a partial pure: {e}"
    return #[{ st, res := ← evalPure ctx st args[3]! }]
  | some ``MonadState.get =>
    unless args.size == 3 && args[0]!.isConstOf ctx.structName do throwError "a get of another state: {e}"
    return #[{ st := { st with snaps := st.snaps.push st.locals }, res := .snap st.snaps.size }]
  | some ``modify =>
    unless args.size == 4 && args[0]!.isConstOf ctx.structName do throwError "a modify of another state: {e}"
    let st' := { st with snaps := st.snaps.push st.locals }
    let k := st.snaps.size
    let new ← withLocalDeclD `s (.const ctx.structName []) fun x => do
      let body := (mkApp args[3]! x).headBeta.consumeMData
      let ctx' := { ctx with env := ctx.env.insert x.fvarId! (.snap k) }
      unless body.isAppOfArity (ctx.structName ++ `mk) ctx.fields.size do
        throwError "a modify that does not rebuild the locals: {body}"
      body.getAppArgs.mapM (evalPure ctx' st')
    return #[{ st := { st' with locals := new }, res := unitV }]
  | some `Zig.callM =>
    let callee := (args.getD 2 default).consumeMData
    if args.size == 3 && callee.isAppOf `Zig.ptrProject then
      throwError "a pointer projection (a cell at an offset)"
    unless args.size == 3 && callee.isConstOf `Zig.tick do throwError "a call: {e}"
    return #[{ st := { st with tick := true }, res := unitV }]
  | some ``ite =>
    unless args.size == 5 && args[1]!.isAppOfArity ``Eq 3 && args[1]!.appArg!.isConstOf ``Bool.true do
      throwError "a condition that is not a Bool test: {e}"
    -- The families test once per iteration: a second test on a path is outside them (and
    -- stopping here keeps the paths from doubling at every test).
    if st.cond.isSome then throwError "a second test in one iteration"
    let c ← evalPure ctx st (args[1]!.getArg! 1)
    return (← exec ctx { st with cond := some (c, true) } args[3]!) ++
      (← exec ctx { st with cond := some (c, false) } args[4]!)
  | some n =>
    if (n == ``liftM || n == ``MonadLiftT.monadLift) && args.size == 5 then
      return #[← execLift ctx st args[4]!]
    if n == `Zig.loop then throwError "a nested loop"
    match ← reduceMatcher? e with
    | .reduced e' => exec ctx st e'
    | .stuck e' => throwError "a match on an unknown value: {e'}"
    | .partialApp => throwError "a partial match: {n}"
    | .notMatcher => throwError "an unsupported command {n}"
  | none => throwError "an unsupported command: {e}"

/-- One lifted memory or arithmetic step. -/
partial def execLift (ctx : Ctx) (st : St) (x : Expr) : MetaM Path := do
  let x := x.headBeta.consumeMData
  let args := x.getAppArgs
  if x.isAppOfArity `Zig.load 4 then
    let some i := paramIdx? ctx args[3]! | throwError "a load through a pointer that is not a loop parameter"
    let some al := natLit? args[2]! | throwError "a load with an unknown alignment"
    let (st, k) ← st.access i args[0]! al
    return { st, res := st.cells[k]!.val }
  if x.isAppOfArity `Zig.store 5 then
    let some i := paramIdx? ctx args[3]! | throwError "a store through a pointer that is not a loop parameter"
    let some al := natLit? args[2]! | throwError "a store with an unknown alignment"
    let v ← evalPure ctx st args[4]!
    let (st, k) ← st.access i args[0]! al
    return { st := { st with cells := st.cells.modify k ({ · with val := v, stored := true }) },
             res := unitV }
  for (op, mk) in [(`Zig.add, Sym.add), (`Zig.sub, Sym.sub)] do
    if x.isAppOfArity op 5 then
      unless args[1]!.isConstOf ``Bool.false do throwError "a signed {op}"
      let v := mk (← evalPure ctx st args[2]!) (← evalPure ctx st args[3]!)
      return { st := { st with checked := st.checked.push v }, res := v }
  if x.isAppOfArity `Zig.intCast 6 then
    let some n := natLit? args[0]! | throwError "a cast from an unknown width"
    let some m := natLit? args[3]! | throwError "a cast to an unknown width"
    unless args[1]!.isConstOf ``Bool.false && args[2]!.isConstOf ``Bool.false && n ≤ m do
      throwError "a cast that is not an unsigned widening"
    return { st, res := .widen (← evalPure ctx st args[4]!) }
  throwError "an unsupported lifted step: {x.getAppFn}"

/-- Continue with `f` applied to the result `v`. -/
partial def apply (ctx : Ctx) (st : St) (f : Expr) (v : Sym) : MetaM (Array Path) := do
  if let .val e := v then return ← exec ctx st (mkApp f e)
  match f.consumeMData with
  | .lam n ty body _ =>
    withLocalDeclD n ty fun x =>
      exec { ctx with env := ctx.env.insert x.fvarId! v } st (body.instantiate1 x)
  | _ => throwError "a continuation that is not a function: {f}"

end

/-- The relation `x R b` under which a counted loop repeats, `x` the counter. -/
inductive Rel where
  | lt | le | gt | ge | ne
  deriving BEq

/-- `R` as Zig writes it. -/
def Rel.text : Rel → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .ne => "!="

/-- `¬ x R b` as `x R' b`; none for `!=` (its negation is a `==`). -/
def Rel.neg? : Rel → Option Rel
  | .lt => some .ge | .le => some .gt | .gt => some .le | .ge => some .lt | .ne => none

/-- The test `c` with the outcome `o` as `x R b`, for the counter `x`: `none` if `c` is not a
comparison of `x` with something else, or the outcome is a `==`. -/
def relOf (x : Name) (c : Sym) (o : Bool) : Option (Rel × Sym) := do
  -- `a R b` with the counter on either side (`R'` the relation with the sides swapped).
  let side (r r' : Rel) (a b : Sym) : Option (Rel × Sym) :=
    if a == .local x then some (r, b) else if b == .local x then some (r', a) else none
  let (r, b) ← match c with
    | .lt a b => side .lt .gt a b
    | .le a b => side .le .ge a b
    | .ne a b => side .ne .ne a b
    | _ => none
  if o then pure (r, b) else return (← r.neg?, b)

/-- A recognized counted loop. -/
structure Counted where
  /-- The counter, a local. -/
  counter : Name
  /-- The test under which the loop repeats: `counter R bound`. -/
  rel : Rel
  /-- The bound: another local, a loop parameter, a literal, the length of a slice parameter or a
  cell the body only reads. -/
  bound : Sym
  /-- The counter goes down by 1 (else up by 1). -/
  down : Bool
  /-- The cells the body accesses, in order, with their increments (`0` for a cell it only
  reads). -/
  cells : Array (Cell × Nat)
  plain : Bool

/-- `R` includes the bound: the counter passes it by one before the loop exits. -/
def Counted.incl (c : Counted) : Bool := c.rel == .le || c.rel == .ge

/-- Classify the paths of one iteration as a counted loop, or say why not. -/
def counted (ctx : Ctx) (again : Expr → MetaM Bool) (paths : Array Path) : MetaM Counted := do
  let mut cont := #[]
  let mut exits := #[]
  for p in paths do
    let .val e := p.res | throwError "an iteration whose exit is not a constructor"
    if ← again e then cont := cont.push p else exits := exits.push p
  let #[c] := cont | throwError "{cont.size} repeating paths, not one"
  if exits.isEmpty then throwError "no exit"
  -- The counter: the one local the iteration changes, by 1 up or down.
  let changed := (c.st.locals.zip ctx.fields).filter fun (v, f) => v != .local f
  let #[(v, x)] := changed | throwError "the body writes {changed.size} locals, not one counter"
  let (base, step) := v.split
  unless base == .local x && step.natAbs == 1 do throwError "the counter `{x}` does not step by 1"
  let down := step == -1
  let some (cnd, o) := c.st.cond | throwError "the repeating path is not guarded by a test"
  let some (rel, b) := relOf x cnd o | throwError "the repeating path is not guarded by a test of `{x}`"
  unless (if down then rel != .lt && rel != .le else rel != .gt && rel != .ge) do
    throwError "the counter `{x}` steps away from its bound (`{x} {rel.text} …`)"
  let mut cells := #[]
  for cell in c.st.cells do
    if !cell.stored then cells := cells.push (cell, 0); continue
    let (base, k) := cell.val.split
    unless base == .cell cell.param && 0 ≤ k do
      throwError "a cell that does not go up by a constant (its increment depends on a value)"
    cells := cells.push (cell, k.toNat)
  match b with
  | .local y => if y == x then throwError "a bound that is the counter"
  | .param _ | .lit _ | .slen _ => pure ()
  | .cell i =>
    unless cells.any (fun (cell, _) => cell.param == i && !cell.stored) do
      throwError "a bound in a cell the body writes"
  | _ => throwError "a bound that is not a local, a parameter, a literal, a slice length or a cell"
  for p in exits do
    unless p.st.cond == some (cnd, !o) do throwError "an exit guarded by another test"
    unless p.st.checked.isEmpty && (p.st.locals.zip ctx.fields).all (fun (v, f) => v == .local f) do
      throwError "an exit that adds, subtracts or changes a local"
    for cell in p.st.cells do
      unless !cell.stored && cells.any (fun (k, _) => k.param == cell.param && k.ty == cell.ty && k.align == cell.align) do
        throwError "an exit that writes memory or reads a cell the repeating path does not"
  -- Every add and subtraction of the repeating path is a partial step of the counter or a partial
  -- sum of a cell's increment, so the counter's bounds and the no-overflow facts cover it.
  for a in c.st.checked do
    let (base, k) := a.split
    unless (base == .local x && (k == 0 || k == step)) ||
        cells.any (fun (cell, n) => cell.stored && base == .cell cell.param && 0 ≤ k && k ≤ n) do
      throwError "an add or subtraction that the counter's and the cells' bounds do not cover"
  return { counter := x, rel, bound := b, down, cells, plain := paths.any (·.st.tick) }

/-- `n` without the namespace `ns`. -/
def relName (ns n : Name) : String :=
  (n.replacePrefix ns .anonymous).toString

/-- Names the generated text binds next to the loop's parameters (`r`: the step's result in the
check of `walk`). -/
def reserved (n : Name) : Bool :=
  match n with
  | .str .anonymous s => ["s", "s0", "v", "r", "up", "pts", "plain", "FAssn", "Zig", "BitVec"].contains s ||
      (s.startsWith "v" && s.length > 1 && (s.toList.drop 1).all Char.isDigit)
  | _ => false

/-- A candidate fact of a loop invariant, as source text over the loop's parameters, the entry
locals `s0`, the cells' entry values `vₖ` and the locals `s`. -/
structure Fact where
  text : String
  /-- The written cell `k` (with its value type) whose current value `v` the fact states: the fact
  stands inside that cell's existential. -/
  cell? : Option (Nat × String) := none
  deriving Inhabited

/-- A resource of the invariant, in order. -/
inductive Owned where
  /-- A cell the loop only reads, owned at its entry value. -/
  | read (atom : String)
  /-- The written cell `k`, owned at a value `v : ty` that its facts state. -/
  | written (k : Nat) (ty atom : String)
  | plain

/-- The candidate invariant `name.inv` of a loop and its measure `name.meas`, as source text: the
facts are candidates, which `houdini` prunes. -/
structure Cand where
  /-- The loop body's name and its exit test's, without the namespace. -/
  name : String
  again : String
  /-- The invariant's doc comment, with its line break. -/
  doc : String
  /-- The loop's parameters as binders and as arguments, the locals' structure, the cells' entry
  values `vₖ` as binders and as arguments, and those of the measure. -/
  binders : String
  args : String
  loc : String
  entry : String
  vargs : String
  measEntry : String
  measArgs : String
  facts : Array Fact
  owned : Array Owned
  meas : String

/-- The invariant's body with the kept facts (`keep`), each written by `fact`. -/
def Cand.body (c : Cand) (keep : Array Bool) (fact : Nat → String) : String := Id.run do
  let kept := (List.range c.facts.size).filter (keep[·]!)
  let top := kept.filter (c.facts[·]!.cell?.isNone)
  let mut atoms := #[]
  if !top.isEmpty then atoms := atoms.push s!"⟪{" ∧\n      ".intercalate (top.map fact)}⟫"
  for o in c.owned do
    match o with
    | .read atom => atoms := atoms.push atom
    | .plain => atoms := atoms.push "plain"
    | .written k ty atom =>
      let fs := kept.filter fun i => (c.facts[i]!.cell?.map (·.1)) == some k
      atoms := atoms.push <| if fs.isEmpty then s!"(FAssn.ex fun v : {ty} => {atom})"
        else s!"(FAssn.ex fun v : {ty} => ⟪{" ∧ ".intercalate (fs.map fact)}⟫ ⋆ {atom})"
  return if atoms.isEmpty then "⟪True⟫" else " ⋆\n    ".intercalate atoms.toList

/-- The definitions `name.inv` and `name.meas` with the kept facts, each written by `fact`. -/
def Cand.defs (c : Cand) (keep : Array Bool) (fact : Nat → String) : String :=
  s!"{c.doc}def {c.name}.inv {c.binders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) : FAssn :=\n  \
    {c.body keep fact}\n\n\
    /-- The measure of `{c.name}`: the iterations left. -/\n\
    def {c.name}.meas {c.binders}{c.measEntry}(s : {c.loc}) : Nat :=\n  {c.meas}\n"

/-- The generated definitions with the kept facts. -/
def Cand.output (c : Cand) (keep : Array Bool) : String :=
  c.defs keep (c.facts[·]!.text)

/-- The check of the kept facts: each one a definition `name.candᵢ` (so that a residual goal
names it), the invariant over them, the measure, and the step triple of one iteration, walked by
`fsym` with its report on: from the invariant, a repeating iteration ends in it with a smaller
measure, an exiting one in it. (The exit post is the invariant: in the counted family an exit
changes no local and no memory.) -/
def Cand.check (ns : Name) (c : Cand) (keep : Array Bool) : String := Id.run do
  let mut defs := ""
  for h : i in [0:c.facts.size] do
    if !keep[i]! then continue
    let v := match c.facts[i].cell? with | some (_, ty) => s!"(v : {ty}) " | none => ""
    defs := defs ++ s!"def {c.name}.cand{i} {c.binders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) {v}: Prop :=\n  \
      {c.facts[i].text}\n\n"
  -- The uses are qualified from the root: under the parameters' binders, a parameter named like
  -- the body's first component (`p0.loop5 (p0 : …)`) would capture a relative name.
  let q (n : String) := s!"_root_.{ns}.{n}"
  let use (i : Nat) := s!"{q c.name}.cand{i} {c.args}s0 {c.vargs}s" ++ if c.facts[i]!.cell?.isSome then " v" else ""
  let inv (s : String) := s!"{q c.name}.inv {c.args}s0 {c.vargs}{s}"
  let meas (s : String) := s!"{q c.name}.meas {c.args}{c.measArgs}{s}"
  return s!"{defs}{c.defs keep use}\n\
    set_option fsym.report true in\n\
    theorem {c.name}.houdini {c.binders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) :\n    \
      FTotalTriple ({inv "s"}) (({q c.name} {c.args}).run s)\n      \
      (fun r => if {q c.again} r.1 then ⟪{meas "r.2"} < {meas "s"}⟫ ⋆ {inv "r.2"} else {inv "r.2"}) := by\n  \
      unfold {q c.name} {q c.name}.inv {q c.name}.meas\n  fsym\n"

/-- The opens of the generated file, which the pruning walks elaborate under too. -/
def opens : String := "open Zig Zig.Full Zig.Full.FAssn"

/-- The prefix of `fsym`'s report message (`Zig.Full.Auto.Report.line`). -/
def reportPrefix : String := "fsym-report "

/-- One `fsym` walk of the step with the kept facts (`Cand.check`, elaborated in the current
environment, which imports the library, with the opens of the generated file): each kept fact
that it does not re-establish, with its residual goal, read off its report (P09-E1: a residual of
the postcondition whose goal is a candidate's definition). It throws why the walk is no proof of
the step: a residual that no candidate explains (the measure, an overflow), an error other than
the unsolved goals of those residuals (a check that does not elaborate: a candidate whose text is
ill-typed is an error here, never a pruned fact), or not exactly one report. The walk is not
trusted: the generated definitions are checked by the proofs that use them. -/
def walk (ns : Name) (c : Cand) (keep : Array Bool) : MetaM (Array (Nat × String)) := do
  let text := s!"namespace {ns}\n{opens}\n\
    set_option linter.unusedVariables false\n\n{c.check ns keep}\nend {ns}\n"
  let opts := ({} : Options).setBool `Elab.async false
  let (_, msgs) ← Lean.Elab.process text (← getEnv) opts (some "<air2lean-invgen check>")
  let mut reports := #[]
  let mut errors := #[]
  for m in msgs.toList do
    let s ← m.data.toString
    if s.startsWith reportPrefix then reports := reports.push (toString (s.drop reportPrefix.length))
    else if m.severity == .error then errors := errors.push s
  let #[report] := reports
    | throwError "the step check gave {reports.size} `fsym` reports, not one: {errors.getD 0 ""}"
  let .ok residuals := (Json.parse report).bind (·.getObjValAs? (Array Json) "residuals")
    | throwError "an `fsym` report without residuals: {report}"
  -- Each residual leaves the step theorem with unsolved goals; any other error is fatal.
  if let some e := errors.find? fun e => residuals.isEmpty || !e.startsWith "unsolved goals" then
    throwError "the step check failed: {e}"
  let pre := s!"{ns}.{c.name}.cand"
  let mut drop := #[]
  for res in residuals do
    let goal := res.getObjValD "goal"
    let origin := res.getObjValD "origin"
    let field (j : Json) (k : String) := (j.getObjValAs? String k).toOption.getD ""
    let goalText := field goal "text"
    let head := field goal "head"
    let i? := if head.startsWith pre then (toString (head.drop pre.length)).toNat? else none
    if let some i := i? then
      if field origin "reason" == "postcondition_not_proved" && field origin "condition" == "postcondition" &&
          keep[i]?.getD false then
        unless drop.any (·.1 == i) do drop := drop.push (i, goalText)
        continue
    throwError "a residual of the step that no candidate explains: `{goalText}` \
      ({field origin "reason"}, {field origin "condition"})"
  return drop

/-- Houdini pruning (Flanagan and Leino, `docs/invariant-synthesis.md`): walk the step with the
kept facts and drop those that the walk does not re-establish, until a walk drops none; its last
walk is a proof of the step. Returns the kept facts and each pruning decision (the fact, the walk
that dropped it and its residual goal there). Each walk drops at least one fact, so there are at
most `facts + 1`. -/
def houdini (ns : Name) (c : Cand) : MetaM (Array Bool × Array Json) := do
  let mut keep := Array.replicate c.facts.size true
  let mut pruned := #[]
  for n in [1:c.facts.size + 2] do
    let drop ← walk ns c keep
    if drop.isEmpty then return (keep, pruned)
    for (i, goal) in drop do
      keep := keep.set! i false
      pruned := pruned.push (Json.mkObj [("fact", c.facts[i]!.text), ("walk", n), ("residual", goal)])
  throwError "Houdini pruning reached no fixpoint"

/-- The candidate invariant and measure of the loop `body` (the definition run by `Zig.loop`) with
exit test `again`; throws why there are none. -/
def candLoop (ns body again : Name) : MetaM Cand := do
    let some (.defnInfo d) := (← getEnv).find? body | throwError "not a definition"
    lambdaTelescope d.value fun xs code => do
      let ty ← inferType code
      unless ty.isAppOfArity `Zig.MM 2 do throwError "not a loop body of `Zig.MM`"
      let some structName := (ty.getArg! 0).constName? | throwError "locals that are not a structure"
      unless isStructure (← getEnv) structName do throwError "locals that are not a structure"
      for x in xs do
        let n := (← x.fvarId!.getDecl).userName
        if n.hasMacroScopes || reserved n then throwError "a parameter named {n}"
      let fields := getStructureFields (← getEnv) structName
      let ctx : Ctx := { structName, fields, params := xs.map (·.fvarId!) }
      let st : St := { locals := fields.map .local }
      let paths ← exec ctx st code
      let isAgain (e : Expr) : MetaM Bool := do
        return (← whnf (mkApp (.const again []) e)).isConstOf ``Bool.true
      let c ← counted ctx isAgain paths
      -- The text.
      let mut binders := ""
      let mut args := ""
      for x in xs do
        let decl ← x.fvarId!.getDecl
        binders := binders ++ s!"({decl.userName} : {← ppExpr decl.type}) "
        args := args ++ s!"{decl.userName} "
      let pname (i : Nat) : MetaM String := return (← xs[i]!.fvarId!.getDecl).userName.toString
      let loc := relName ns structName
      let x := c.counter
      -- Each cell's type, and its entry value `vₖ` as a binder (the measure binds the bound's).
      let tys ← c.cells.mapM fun (cell, _) => return toString (← ppExpr cell.ty)
      let binder (k : Nat) := s!"(v{k} : {tys[k]!}) "
      let entry := String.join ((List.range tys.size).map binder)
      let vargs := String.join ((List.range tys.size).map (s!"v{·} "))
      let boundCell? := c.cells.findIdx? fun (cell, _) => c.bound == .cell cell.param
      let measEntry := (boundCell?.map binder).getD ""
      let measArgs := (boundCell?.map (s!"v{·} ")).getD ""
      let (bound, boundName) ← match c.bound with
        | .local y => pure (s!"s.{y}.toNat", y.toString)
        | .param i => do
          unless (bitVecWidth? (← inferType xs[i]!)).isSome do throwError "a bound that is not a word"
          let p ← pname i
          pure (s!"{p}.toNat", p)
        | .lit n => pure (toString n, toString n)
        | .slen i => do
          unless (← inferType xs[i]!).isConstOf `Zig.Slice do throwError "a length of a value that is not a slice"
          let p ← pname i
          pure (s!"{p}.len.toNat", s!"{p}.len")
        | .cell i => do
          let some k := boundCell? | throwError "a bound cell"
          pure (s!"v{k}.toNat", s!"*{← pname i}")
        | _ => throwError "a bound"
      -- `X` the counter, `X0` its entry value: the loop counts `delta` iterations so far, `total`
      -- in all, and its measure is `left`.
      let X := s!"s.{x}.toNat"
      let X0 := s!"s0.{x}.toNat"
      let mut facts : Array Fact := #[]
      for f in fields do
        if f != x then facts := facts.push { text := s!"s.{f} = s0.{f}" }
      -- The counter runs from `X0` to the value it exits at: the bound, or one past it for
      -- `<=`/`>=` (`one`), where the counter's last step must not wrap (`noWrap`; a literal bound
      -- that makes it false is outside the family). Which side of `X0` it stays on is left to
      -- Houdini: both are candidates (true at entry), and the step keeps one.
      let one := if c.incl then " + 1" else ""
      let (total, left, toExit) := if c.down then
          (s!"{X0}{one} - {bound}", s!"{X}{one} - {bound}", s!"{bound} ≤ {X}{one}")
        else
          (s!"{bound}{one} - {X0}", s!"{bound}{one} - {X}", s!"{X} ≤ {bound}{one}")
      facts := facts ++ #[{ text := s!"{X0} ≤ {X}" }, { text := s!"{X} ≤ {X0}" }, { text := toExit }]
      if c.incl then
        let ty ← withLocalDeclD `s (.const structName []) fun s =>
          inferType (mkApp (.const (structName ++ x) []) s)
        let some w := bitVecWidth? ty | throwError "a counter that is not a word"
        let (noWrap, never) := match c.down, c.bound with
          | true, b => (s!"1 ≤ {bound}", b == Sym.lit 0)
          | false, .lit n => (s!"{bound} + 1 < 2 ^ {w}", n + 1 ≥ 2 ^ w)
          | false, _ => (s!"{bound} + 1 < 2 ^ {w}", false)
        if never then
          throwError "a test `{x} {c.rel.text} {boundName}` that holds until the counter's step wraps"
        facts := facts.push { text := noWrap }
      let scaled (k : Nat) (t : String) := if k == 1 then s!"({t})" else s!"{k} * ({t})"
      let mut owned := #[]
      let mut doc := #[]
      for h : k in [0:c.cells.size] do
        let (cell, inc) := c.cells[k]
        let p ← pname cell.param
        let ty := tys[k]!
        if !cell.stored then
          owned := owned.push (.read s!"up (pts {p} {cell.align} v{k})")
          doc := doc.push s!"\n`v{k}` is `*{p}`, which the loop only reads."
          continue
        facts := facts.push { text := s!"v{k}.toNat + {scaled inc total} < 2 ^ {cell.width}" }
        -- The cell's value after the iterations so far, counted up or down from `X0`: both are
        -- candidates (true at entry), Houdini keeps the one of the counter's direction (a cell
        -- that goes up by 0 keeps both, so it gets the one of the reading's direction only).
        let up := s!"{X} - {X0}"
        let down := s!"{X0} - {X}"
        for d in (if inc != 0 then #[up, down] else if c.down then #[down] else #[up]) do
          facts := facts.push { text := s!"v.toNat = v{k}.toNat + {scaled inc d}", cell? := some (k, ty) }
        owned := owned.push (.written k ty s!"up (pts {p} {cell.align} v)")
        doc := doc.push s!"\n`v{k}` is `*{p}` there, which goes up by {inc} per iteration."
      if c.plain then owned := owned.push .plain
      let name := relName ns body
      return {
        name, again := relName ns again, binders, args, loc, entry, vargs, measEntry, measArgs,
        facts, owned, meas := left,
        doc := s!"/-- The invariant of `{name}`, a counted loop: `{x}` goes {if c.down then "down" else "up"} \
          by 1 while `{x} {c.rel.text} {boundName}`.\n`s0` holds the locals at loop entry.{String.join doc.toList} -/\n" }

/-- The invariant `body.inv` and measure `body.meas` of the loop `body` with exit test `again`
(`candLoop`, pruned by `houdini`) as source text with the pruning decisions, or why there are
none. Each loop has its own heartbeat budget: the walks of the loops before it do not count. -/
def genLoop (ns body again : Name) : MetaM (Except String (String × Array Json)) :=
  -- (a heartbeat or recursion limit, too, only costs this loop its invariant)
  withCurrHeartbeats <| tryCatchRuntimeEx
    (do
      let c ← candLoop ns body again
      let (keep, pruned) ← houdini ns c
      return .ok (c.output keep, pruned))
    fun ex => return .error (← ex.toMessageData.toString)

/-- The loops that `e` runs: each `Zig.loop (body …) again` as the body's definition and the
exit test, read off the term (no naming convention). A loop whose body is not an applied
definition or whose test is not a constant is an error. -/
def loopApps (e : Expr) : MetaM (Array (Name × Name)) := do
  let out ← IO.mkRef #[]
  e.forEachWhere (·.isAppOfArity `Zig.loop 7) fun l =>
    match l.getArg! 5 |>.getAppFn.constName?, l.getArg! 6 |>.constName? with
    | some b, some a => out.modify (·.push (b, a))
    | _, _ => throwError "a `Zig.loop` whose body is not an applied definition: {l}"
  out.get

/-- The loops of `module`, all with their bodies in the namespace `ns`, sorted. -/
def loopsOf (module ns : Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? module | throwError "module {module} is not imported"
  let mut out : Array (Name × Name) := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    if let some (.defnInfo d) := env.find? n then
      for l in ← loopApps d.value do
        if !out.contains l then out := out.push l
  if out.isEmpty then throwError "module {module} runs no `Zig.loop`"
  if let some (b, _) := out.find? (!ns.isPrefixOf ·.1) then
    throwError "the loop body {b} is outside the namespace {ns}"
  return out.qsort (fun a b => a.1.toString < b.1.toString)

/-- The generated file for `module` (whose translated names are in `ns`), and the loops it has no
invariant for, with the reason. The record on its first line holds `generator` (the generator's
revision record) and `inputs` (the files read, as `[path, sha256]`) as given, and `output`, the
SHA-256 of the rest of the file: with them, `scripts/gen-integrity.py invgen` finds a stale or
hand-edited file without running the generator, except one made stale by a library change that
changes the pruning (the library is not hashed; `scripts/invgen.py check` finds it). Each loop's
entry in `loops` names its family and the facts Houdini pruned (`pruned`), or why it has no
invariant (`none`). The current environment
must import `ZigLean.Sep.Full.AutoAll`: the pruning walks run `fsym`. -/
def generate (module ns : Name) (generator inputs : Json) :
    MetaM (String × Array (String × String)) := do
  let mut loops := #[]
  let mut defs := #[]
  let mut skipped := #[]
  for (b, a) in ← loopsOf module ns do
    let loop := relName ns b
    match ← genLoop ns b a with
    | .ok (t, pruned) =>
      loops := loops.push (Json.mkObj [("loop", loop), ("family", "counted"), ("pruned", Json.arr pruned)])
      defs := defs.push t
    | .error why =>
      loops := loops.push (Json.mkObj [("loop", loop), ("none", why)])
      skipped := skipped.push (loop, why)
  let body := s!"import {module}\n\
    import ZigLean.Sep.Full.Ghost\n\n\
    /-!\n\
    Generated by `air2lean-invgen` (`docs/invariant-synthesis.md`) from `{module}`: do not edit.\n\
    Untrusted: the proofs that use these definitions are checked by the kernel.\n\
    -/\n\n\
    set_option linter.unusedVariables false\n\n\
    namespace {ns}\n\
    {opens}\n\n\
    {"\n".intercalate defs.toList}\n\
    end {ns}\n"
  let record := Json.mkObj [
    ("version", (2 : Nat)), ("generator", generator), ("inputs", inputs),
    ("module", module.toString), ("namespace", ns.toString), ("loops", Json.arr loops),
    ("output", Air2Lean.Revision.sha256 body.toUTF8)]
  return (s!"-- air2lean-invgen: {record.compress}\n" ++ body, skipped)

end Air2Lean.InvGen
