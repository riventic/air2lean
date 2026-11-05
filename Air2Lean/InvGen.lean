import Lean

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

* **Counted loop.** One iteration either exits, when an unsigned `x < b` fails (`x` a local, `b`
  a local the loop does not write, a loop parameter or a literal), and touches no memory and no
  local; or it adds 1 to `x`, adds a constant `cₖ` to each cell `*pₖ` (`pₖ` a loop parameter, the
  cell an unsigned word), leaves every other local unchanged, runs no other add, and repeats. The invariant pins the other locals to their
  entry values, bounds `x₀ ≤ x ≤ b`, states each cell as `vₖ + cₖ * (x - x₀)` from its entry
  value `vₖ`, and carries the no-overflow fact `vₖ + cₖ * (b - x₀) < 2 ^ w` that the checked adds
  need. The measure is `b - x`. A body that takes a step (`Zig.tick`) runs in the plain mode, so
  the invariant carries `plain`.

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
  /-- A sum that does not wrap (`Zig.add`: an overflow fails). -/
  | add (a b : Sym)
  /-- An unsigned `<`. -/
  | lt (a b : Sym)
  /-- A closed value: an exit constructor, `()`. -/
  | val (e : Expr)
  /-- Snapshot `k` of the locals (a `get`). -/
  | snap (k : Nat)
  deriving Inhabited, BEq

/-- `s` as a base and a constant summand. -/
partial def Sym.split : Sym → Sym × Nat
  | .add a (.lit n) | .add (.lit n) a => let (b, k) := a.split; (b, k + n)
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
  /-- The value of every `Zig.add` the path ran: each one fails on overflow, so the invariant
  must bound it, also when its result is not used. -/
  adds : Array Sym := #[]
  snaps : Array (Array Sym) := #[]
  ticks : Nat := 0
  cond : Array (Sym × Bool) := #[]

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
  if e.isAppOfArity `Zig.lt 4 then
    unless (e.getArg! 1).isConstOf ``Bool.false do throwError "a signed comparison: {e}"
    return .lt (← evalPure ctx st (e.getArg! 2)) (← evalPure ctx st (e.getArg! 3))
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
    unless args.size == 3 && args[2]!.isConstOf `Zig.tick do throwError "a call: {e}"
    return #[{ st := { st with ticks := st.ticks + 1 }, res := unitV }]
  | some ``ite =>
    unless args.size == 5 && args[1]!.isAppOfArity ``Eq 3 && args[1]!.appArg!.isConstOf ``Bool.true do
      throwError "a condition that is not a Bool test: {e}"
    -- The families test once per iteration: a second test on a path is outside them (and
    -- stopping here keeps the paths from doubling at every test).
    unless st.cond.isEmpty do throwError "a second test in one iteration"
    let c ← evalPure ctx st (args[1]!.getArg! 1)
    return (← exec ctx { st with cond := st.cond.push (c, true) } args[3]!) ++
      (← exec ctx { st with cond := st.cond.push (c, false) } args[4]!)
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
  if x.isAppOfArity `Zig.add 5 then
    unless args[1]!.isConstOf ``Bool.false do throwError "a signed add"
    let v := .add (← evalPure ctx st args[2]!) (← evalPure ctx st args[3]!)
    return { st := { st with adds := st.adds.push v }, res := v }
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

/-- A recognized counted loop. -/
structure Counted where
  counter : Nat
  /-- The bound: a local index or a loop parameter. -/
  bound : Sym
  /-- The cells the body writes, with their increments. -/
  cells : Array (Cell × Nat)
  plain : Bool

/-- Classify the paths of one iteration as a counted loop, or say why not. -/
def counted (ctx : Ctx) (again : Expr → MetaM Bool) (paths : Array Path) : MetaM Counted := do
  let mut cont := #[]
  let mut exits := #[]
  for p in paths do
    let .val e := p.res | throwError "an iteration whose exit is not a constructor"
    if ← again e then cont := cont.push p else exits := exits.push p
  let #[c] := cont | throwError "{cont.size} repeating paths, not one"
  if exits.isEmpty then throwError "no exit"
  let #[(.lt (.local x) b, true)] := c.st.cond | throwError "the repeating path is not guarded by one unsigned `x < b`"
  let some xi := ctx.fields.idxOf? x | throwError "a guard on an unknown local"
  match b with
  | .local y => unless y != x && ctx.fields.contains y do throwError "a bound that is not another local"
  | .param _ | .lit _ => pure ()
  | _ => throwError "a bound that is not a local, a parameter or a literal"
  for (v, f) in c.st.locals.zip ctx.fields do
    if f == x then
      unless v.split == (.local x, 1) do throwError "the counter `{x}` does not go up by 1"
    else unless v == .local f do throwError "the body writes the local `{f}`"
  let mut cells := #[]
  for cell in c.st.cells do
    unless cell.stored do throwError "a cell that is only read"
    let (base, k) := cell.val.split
    unless base == .cell cell.param do throwError "a cell that does not go up by a constant"
    cells := cells.push (cell, k)
  for p in exits do
    let #[(.lt (.local x') b', false)] := p.st.cond | throwError "an exit not guarded by `¬ x < b`"
    unless x' == x && b' == b do throwError "an exit guarded by another test"
    unless p.st.cells.isEmpty && p.st.adds.isEmpty &&
        (p.st.locals.zip ctx.fields).all (fun (v, f) => v == .local f) do
      throwError "an exit that accesses memory, adds or changes a local"
  -- Every add of the repeating path is a partial sum of the counter's or a cell's increment,
  -- so the bounds `x ≤ b` and the no-overflow facts cover it.
  for a in c.st.adds do
    let (base, k) := a.split
    unless (base == .local x && k ≤ 1) || cells.any (fun (cell, n) => base == .cell cell.param && k ≤ n) do
      throwError "an add that the counter's and the cells' bounds do not cover"
  let plain := paths.any (·.st.ticks > 0)
  return { counter := xi, bound := b, cells, plain }

/-- `n` without the namespace `ns`. -/
def relName (ns n : Name) : String :=
  (n.replacePrefix ns .anonymous).toString

/-- One generated loop: the source text of its definitions, or why there are none. -/
structure LoopOut where
  loop : Name
  text : Except String String

/-- Names the generated text binds next to the loop's parameters. -/
def reserved (n : Name) : Bool :=
  match n with
  | .str .anonymous s => s == "s" || s == "s0" || s == "v" ||
      (s.startsWith "v" && s.length > 1 && (s.toList.drop 1).all Char.isDigit)
  | _ => false

/-- The invariant `body.inv` and measure `body.meas` of the loop `body` (the definition run by
`Zig.loop`) with exit test `again`. -/
def genLoop (ns body again : Name) : MetaM LoopOut := do
  let res : Except String String ← try
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
      let x := fields[c.counter]!
      let (bound, boundName) ← match c.bound with
        | .local y => pure (s!"s.{y}.toNat", y.toString)
        | .param i => do
          unless (bitVecWidth? (← inferType xs[i]!)).isSome do throwError "a bound that is not a word"
          let p ← pname i
          pure (s!"{p}.toNat", p)
        | .lit n => pure (toString n, toString n)
        | _ => throwError "a bound"
      let scaled (k : Nat) (t : String) := if k == 1 then s!"({t})" else s!"{k} * ({t})"
      let mut facts := #[]
      for f in fields do
        if f != x then facts := facts.push s!"s.{f} = s0.{f}"
      facts := facts.push s!"s0.{x}.toNat ≤ s.{x}.toNat" |>.push s!"s.{x}.toNat ≤ {bound}"
      let mut entry := ""
      let mut owned := #[]
      let mut doc := #[]
      for h : k in [0:c.cells.size] do
        let (cell, inc) := c.cells[k]
        let p ← pname cell.param
        let ty ← ppExpr cell.ty
        entry := entry ++ s!"(v{k} : {ty}) "
        facts := facts.push s!"v{k}.toNat + {scaled inc s!"{bound} - s0.{x}.toNat"} < 2 ^ {cell.width}"
        owned := owned.push <|
          s!"(FAssn.ex fun v : {ty} => ⟪v.toNat = v{k}.toNat + " ++
          s!"{scaled inc s!"s.{x}.toNat - s0.{x}.toNat"}⟫ ⋆ up (pts {p} {cell.align} v))"
        doc := doc.push s!"\n`v{k}` is `*{p}` there, which goes up by {inc} per iteration."
      if c.plain then owned := owned.push "plain"
      let name := relName ns body
      let factText := " ∧\n      ".intercalate facts.toList
      let ownedText := " ⋆\n    ".intercalate owned.toList
      let bodyText := if owned.isEmpty then s!"⟪{factText}⟫" else s!"⟪{factText}⟫ ⋆\n    {ownedText}"
      return s!"/-- The invariant of `{name}`, a counted loop: `{x}` goes up by 1 while \
        `{x} < {boundName}`.\n`s0` holds the locals at loop entry.{String.join doc.toList} -/\n\
        def {name}.inv {binders}(s0 : {loc}) {entry}(s : {loc}) : FAssn :=\n  {bodyText}\n\n\
        /-- The measure of `{name}`: the iterations left. -/\n\
        def {name}.meas {binders}(s : {loc}) : Nat :=\n  {bound} - s.{x}.toNat\n"
    pure (.ok text)
  catch ex => pure (.error (← ex.toMessageData.toString))
  return { loop := body, text := res }

/-- The loops that `e` runs: each `Zig.loop (body …) again` as the body's definition and the
exit test, read off the term (no naming convention). -/
partial def loopApps (e : Expr) (acc : Array (Name × Name)) : Array (Name × Name) :=
  let acc :=
    if e.isAppOfArity `Zig.loop 7 then
      match e.getArg! 5 |>.getAppFn.constName?, e.getArg! 6 |>.constName? with
      | some b, some a => acc.push (b, a)
      | _, _ => acc
    else acc
  match e with
  | .app f x => loopApps x (loopApps f acc)
  | .lam _ t b _ | .forallE _ t b _ => loopApps b (loopApps t acc)
  | .letE _ t v b _ => loopApps b (loopApps v (loopApps t acc))
  | .mdata _ b | .proj _ _ b => loopApps b acc
  | _ => acc

/-- The loops of `module`, all with their bodies in the namespace `ns`, sorted. -/
def loopsOf (module ns : Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? module | throwError "module {module} is not imported"
  let mut out : Array (Name × Name) := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    if let some (.defnInfo d) := env.find? n then
      for l in loopApps d.value #[] do
        if !out.contains l then out := out.push l
  if out.isEmpty then throwError "module {module} runs no `Zig.loop`"
  if let some (b, _) := out.find? (!ns.isPrefixOf ·.1) then
    throwError "the loop body {b} is outside the namespace {ns}"
  return out.qsort (fun a b => a.1.toString < b.1.toString)

/-- The generated file for `module` (whose translated names are in `ns`), and the loops it has no
invariant for, with the reason. -/
def generate (module ns : Name) : MetaM (String × Array (String × String)) := do
  let outs ← (← loopsOf module ns).mapM fun (b, a) => genLoop ns b a
  let record := Json.mkObj [
    ("generator", "air2lean-invgen"), ("version", (1 : Nat)), ("module", module.toString),
    ("loops", Json.arr <| outs.map fun o => match o.text with
      | .ok _ => Json.mkObj [("loop", relName ns o.loop), ("family", "counted")]
      | .error why => Json.mkObj [("loop", relName ns o.loop), ("none", why)])]
  let defs := outs.filterMap fun o => match o.text with | .ok t => some t | .error _ => none
  let skipped := outs.filterMap fun o => match o.text with
    | .ok _ => none | .error why => some (relName ns o.loop, why)
  return (·, skipped) <| s!"-- air2lean-invgen: {record.compress}\n\
    import {module}\n\
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

end Air2Lean.InvGen
