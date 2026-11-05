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
  or `!=` (either way; the outcome of the test may be either branch). The bound `b` is a local
  the loop does not write, a loop parameter, a literal, the length of a slice parameter
  (`p.len`) or a cell the loop only reads (`*p`). The invariant pins the other locals and the
  read-only cells to their entry values, bounds the counter between its entry value `x₀` and the
  value it exits at (`b`, or one past `b` for `<=`/`>=`, with the fact that the step there does
  not wrap), states each written cell as `vₖ + cₖ * d` from its entry value `vₖ` (`d` the
  iterations so far), and carries the no-overflow fact `vₖ + cₖ * n < 2 ^ w` (`n` all
  iterations) that the checked adds need. The measure is the iterations left. A body that takes
  a step (`Zig.tick`) runs in the plain mode, so the invariant carries `plain`.

Outside the family (each one recorded with its reason): a cell at an offset of a parameter
(`Zig.ptrProject`), an increment that depends on the counter, a nested loop, a call.

The body is read by a symbolic run over its monadic term (`bind`, `pure`, `get`, `modify`, `ite`,
the lifted `Zig.load`/`Zig.store`/`Zig.add`/`Zig.lt`, a `match` on a known exit): this is a
reading of the generated term, not a second semantics. Nothing it concludes is trusted.
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
  | .fvar id => ctx.params.idxOf? id
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
    if args.size == 3 && args[2]!.isAppOf `Zig.ptrProject then
      throwError "a pointer projection (a cell at an offset)"
    unless args.size == 3 && args[2]!.isConstOf `Zig.tick do throwError "a call: {e}"
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

/-- The test `c` with the outcome `o` as `x R b`, for the counter `x`: `none` if `c` is not a
comparison of `x` with something else, or the outcome is a `==`. -/
def relOf (x : Name) (c : Sym) (o : Bool) : Option (Rel × Sym) :=
  let neg : Rel → Option Rel
    | .lt => some .ge | .le => some .gt | .gt => some .le | .ge => some .lt | .ne => none
  let pos : Option (Rel × Sym) := match c with
    | .lt (.local y) b => if y == x then some (.lt, b) else none
    | .lt b (.local y) => if y == x then some (.gt, b) else none
    | .le (.local y) b => if y == x then some (.le, b) else none
    | .le b (.local y) => if y == x then some (.ge, b) else none
    | .ne (.local y) b | .ne b (.local y) => if y == x then some (.ne, b) else none
    | _ => none
  match pos with
  | some (r, b) => if o then some (r, b) else (neg r).map (·, b)
  | none => none

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
  let down ← match v.split with
    | (.local y, 1) => if y == x then pure false else throwError "the counter `{x}` does not step by 1"
    | (.local y, -1) => if y == x then pure true else throwError "the counter `{x}` does not step by 1"
    | _ => throwError "the counter `{x}` does not step by 1"
  let some (cnd, o) := c.st.cond | throwError "the repeating path is not guarded by a test"
  let some (rel, b) := relOf x cnd o | throwError "the repeating path is not guarded by a test of `{x}`"
  unless (if down then rel != .lt && rel != .le else rel != .gt && rel != .ge) do
    throwError "the counter `{x}` steps away from its bound (`{x} {rel.text} …`)"
  let mut cells := #[]
  for cell in c.st.cells do
    if !cell.stored then cells := cells.push (cell, 0); continue
    let (base, k) := cell.val.split
    unless base == .cell cell.param && 0 ≤ k do throwError "a cell that does not go up by a constant"
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
    unless (base == .local x && (if down then -1 ≤ k && k ≤ 0 else 0 ≤ k && k ≤ 1)) ||
        cells.any (fun (cell, n) => cell.stored && base == .cell cell.param && 0 ≤ k && k ≤ n) do
      throwError "an add or subtraction that the counter's and the cells' bounds do not cover"
  return { counter := x, rel, bound := b, down, cells, plain := paths.any (·.st.tick) }

/-- `n` without the namespace `ns`. -/
def relName (ns n : Name) : String :=
  (n.replacePrefix ns .anonymous).toString

/-- Names the generated text binds next to the loop's parameters. -/
def reserved (n : Name) : Bool :=
  match n with
  | .str .anonymous s => s == "s" || s == "s0" || s == "v" ||
      (s.startsWith "v" && s.length > 1 && (s.toList.drop 1).all Char.isDigit)
  | _ => false

/-- The invariant `body.inv` and measure `body.meas` of the loop `body` (the definition run by
`Zig.loop`) with exit test `again`, as source text, or why there are none. -/
def genLoop (ns body again : Name) : MetaM (Except String String) := do
  try
    let some (.defnInfo d) := (← getEnv).find? body | throwError "not a definition"
    let text ← lambdaTelescope d.value fun xs code => do
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
      for x in xs do
        let decl ← x.fvarId!.getDecl
        binders := binders ++ s!"({decl.userName} : {← ppExpr decl.type}) "
      let pname (i : Nat) : MetaM String := return (← xs[i]!.fvarId!.getDecl).userName.toString
      let loc := relName ns structName
      let x := c.counter
      let mut entry := ""
      let mut measEntry := ""
      for h : k in [0:c.cells.size] do
        let (cell, _) := c.cells[k]
        let b := s!"(v{k} : {← ppExpr cell.ty}) "
        entry := entry ++ b
        if c.bound == .cell cell.param then measEntry := b
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
          let some k := c.cells.findIdx? (·.1.param == i) | throwError "a bound cell"
          pure (s!"v{k}.toNat", s!"*{← pname i}")
        | _ => throwError "a bound"
      -- `X` the counter, `X0` its entry value: the loop counts `delta` iterations so far, `total`
      -- in all, and its measure is `left`.
      let X := s!"s.{x}.toNat"
      let X0 := s!"s0.{x}.toNat"
      let mut facts := #[]
      for f in fields do
        if f != x then facts := facts.push s!"s.{f} = s0.{f}"
      let mut delta := s!"{X} - {X0}"
      let mut total := ""
      let mut left := ""
      if c.down then
        delta := s!"{X0} - {X}"
        facts := facts.push s!"{X} ≤ {X0}"
        if c.incl then
          facts := facts.push s!"1 ≤ {bound}" |>.push s!"{bound} ≤ {X} + 1"
          total := s!"{X0} + 1 - {bound}"
          left := s!"{X} + 1 - {bound}"
        else
          facts := facts.push s!"{bound} ≤ {X}"
          total := s!"{X0} - {bound}"
          left := s!"{X} - {bound}"
      else
        let last := if c.incl then s!"{bound} + 1" else bound
        facts := facts.push s!"{X0} ≤ {X}" |>.push s!"{X} ≤ {last}"
        if c.incl then
          let ty ← withLocalDeclD `s (.const structName []) fun s =>
            inferType (mkApp (.const (structName ++ x) []) s)
          let some w := bitVecWidth? ty | throwError "a counter that is not a word"
          facts := facts.push s!"{bound} + 1 < 2 ^ {w}"
        total := s!"{last} - {X0}"
        left := s!"{last} - {X}"
      let scaled (k : Nat) (t : String) := if k == 1 then s!"({t})" else s!"{k} * ({t})"
      let mut owned := #[]
      let mut doc := #[]
      for h : k in [0:c.cells.size] do
        let (cell, inc) := c.cells[k]
        let p ← pname cell.param
        let ty ← ppExpr cell.ty
        if !cell.stored then
          owned := owned.push s!"up (pts {p} {cell.align} v{k})"
          doc := doc.push s!"\n`v{k}` is `*{p}`, which the loop only reads."
          continue
        facts := facts.push s!"v{k}.toNat + {scaled inc total} < 2 ^ {cell.width}"
        owned := owned.push <|
          s!"(FAssn.ex fun v : {ty} => ⟪v.toNat = v{k}.toNat + {scaled inc delta}⟫ ⋆ up (pts {p} {cell.align} v))"
        doc := doc.push s!"\n`v{k}` is `*{p}` there, which goes up by {inc} per iteration."
      if c.plain then owned := owned.push "plain"
      let name := relName ns body
      let factText := " ∧\n      ".intercalate facts.toList
      let ownedText := " ⋆\n    ".intercalate owned.toList
      let bodyText := if owned.isEmpty then s!"⟪{factText}⟫" else s!"⟪{factText}⟫ ⋆\n    {ownedText}"
      return s!"/-- The invariant of `{name}`, a counted loop: `{x}` goes {if c.down then "down" else "up"} \
        by 1 while `{x} {c.rel.text} {boundName}`.\n`s0` holds the locals at loop entry.{String.join doc.toList} -/\n\
        def {name}.inv {binders}(s0 : {loc}) {entry}(s : {loc}) : FAssn :=\n  {bodyText}\n\n\
        /-- The measure of `{name}`: the iterations left. -/\n\
        def {name}.meas {binders}{measEntry}(s : {loc}) : Nat :=\n  {left}\n"
    pure (.ok text)
  catch ex => pure (.error (← ex.toMessageData.toString))

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
hand-edited file without running the generator. -/
def generate (module ns : Name) (generator inputs : Json) :
    MetaM (String × Array (String × String)) := do
  let mut loops := #[]
  let mut defs := #[]
  let mut skipped := #[]
  for (b, a) in ← loopsOf module ns do
    let loop := relName ns b
    match ← genLoop ns b a with
    | .ok t =>
      loops := loops.push (Json.mkObj [("loop", loop), ("family", "counted")])
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
    open Zig Zig.Full Zig.Full.FAssn\n\n\
    {"\n".intercalate defs.toList}\n\
    end {ns}\n"
  let record := Json.mkObj [
    ("version", (2 : Nat)), ("generator", generator), ("inputs", inputs),
    ("module", module.toString), ("namespace", ns.toString), ("loops", Json.arr loops),
    ("output", Air2Lean.Revision.sha256 body.toUTF8)]
  return (s!"-- air2lean-invgen: {record.compress}\n" ++ body, skipped)

end Air2Lean.InvGen
