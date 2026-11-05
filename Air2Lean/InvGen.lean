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
  a local the loop does not write or a loop parameter), and changes nothing; or it adds 1 to `x`,
  adds a constant `cₖ` to each cell `*pₖ` (`pₖ` a loop parameter, the cell an unsigned word),
  leaves every other local unchanged, and repeats. The invariant pins the other locals to their
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

/-- One cell the body accesses: its loop parameter, value type, width and alignment. -/
structure Cell where
  param : Nat
  ty : Expr
  width : Nat
  align : Nat

/-- The state of one path through the body. -/
structure St where
  /-- The current value of each local, in field order. -/
  locals : Array Sym
  /-- The current value of each accessed cell, by loop parameter. -/
  cells : Array (Nat × Sym) := #[]
  cellInfo : Array Cell := #[]
  stored : Array Nat := #[]
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
  if let some n := natLit? e then return .lit n
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

def St.cell? (st : St) (i : Nat) : Option Sym := (st.cells.find? (·.1 == i)).map (·.2)

def St.setCell (st : St) (i : Nat) (v : Sym) : St :=
  match st.cells.findIdx? (·.1 == i) with
  | some k => { st with cells := st.cells.set! k (i, v) }
  | none => { st with cells := st.cells.push (i, v) }

/-- Record the type and alignment of the cell at parameter `i` (the same at every access). -/
def St.access (st : St) (i : Nat) (ty : Expr) (align : Nat) : MetaM St := do
  let some w := bitVecWidth? ty | throwError "a cell that is not an unsigned word: {ty}"
  match st.cellInfo.find? (·.param == i) with
  | some c =>
    unless c.ty == ty && c.align == align do throwError "a cell accessed at two types or alignments"
    return st
  | none => return { st with cellInfo := st.cellInfo.push { param := i, ty, width := w, align } }

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
    return #[{ st := { st' with locals := new }, res := .val (.const ``Unit.unit []) }]
  | some `Zig.callM =>
    unless args.size == 3 && args[2]!.isConstOf `Zig.tick do throwError "a call: {e}"
    return #[{ st := { st with ticks := st.ticks + 1 }, res := .val (.const ``Unit.unit []) }]
  | some ``ite =>
    unless args.size == 5 && args[1]!.isAppOfArity ``Eq 3 && args[1]!.appArg!.isConstOf ``Bool.true do
      throwError "a condition that is not a Bool test: {e}"
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
    let st ← st.access i args[0]! al
    match st.cell? i with
    | some v => return { st, res := v }
    | none => return { st := st.setCell i (.cell i), res := .cell i }
  if x.isAppOfArity `Zig.store 5 then
    let some i := paramIdx? ctx args[3]! | throwError "a store through a pointer that is not a loop parameter"
    let some al := natLit? args[2]! | throwError "a store with an unknown alignment"
    let st ← st.access i args[0]! al
    let v ← evalPure ctx st args[4]!
    let st := st.setCell i v
    return { st := { st with stored := if st.stored.contains i then st.stored else st.stored.push i },
             res := .val (.const ``Unit.unit []) }
  if x.isAppOfArity `Zig.add 5 then
    unless args[1]!.isConstOf ``Bool.false do throwError "a signed add"
    return { st, res := .add (← evalPure ctx st args[2]!) (← evalPure ctx st args[3]!) }
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
  | .param _ => pure ()
  | _ => throwError "a bound that is neither a local nor a parameter"
  for (v, f) in c.st.locals.zip ctx.fields do
    if f == x then
      unless v.split == (.local x, 1) do throwError "the counter `{x}` does not go up by 1"
    else unless v == .local f do throwError "the body writes the local `{f}`"
  let mut cells := #[]
  for (i, v) in c.st.cells do
    let some cell := c.st.cellInfo.find? (·.param == i) | throwError "an untyped cell"
    unless c.st.stored.contains i do throwError "a cell that is only read"
    let (base, k) := v.split
    unless base == .cell i do throwError "a cell that does not go up by a constant"
    cells := cells.push (cell, k)
  for p in exits do
    let #[(.lt (.local x') b', false)] := p.st.cond | throwError "an exit not guarded by `¬ x < b`"
    unless x' == x && b' == b do throwError "an exit guarded by another test"
    unless p.st.stored.isEmpty && (p.st.locals.zip ctx.fields).all (fun (v, f) => v == .local f) do
      throwError "an exit that changes the state"
  let plain := paths.any (·.st.ticks > 0)
  return { counter := xi, bound := b, cells, plain }

/-- `n` without the namespace `ns`. -/
def relName (ns n : Name) : String :=
  (n.replacePrefix ns .anonymous).toString

/-- One generated loop: the source text of its definitions, or why there are none. -/
structure LoopOut where
  loop : Name
  text : Except String String

/-- The invariant and measure of the loop `body` (`F.loopN`) with exit test `again`. -/
def genLoop (ns body again : Name) : MetaM LoopOut := do
  let res : Except String String ← try
    let some (.defnInfo d) := (← getEnv).find? body | throwError "not a definition"
    let text ← lambdaTelescope d.value fun xs code => do
      let ty ← inferType code
      unless ty.isAppOfArity `Zig.MM 2 do throwError "not a loop body of `Zig.MM`"
      let some structName := (ty.getArg! 0).constName? | throwError "locals that are not a structure"
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
        entry := entry ++ s!"(v{k} : {← ppExpr cell.ty}) "
        facts := facts.push s!"v{k}.toNat + {scaled inc s!"{bound} - s0.{x}.toNat"} < 2 ^ {cell.width}"
        owned := owned.push <|
          s!"(FAssn.ex fun v : {← ppExpr cell.ty} => ⟪v.toNat = v{k}.toNat + " ++
          s!"{scaled inc s!"s.{x}.toNat - s0.{x}.toNat"}⟫ ⋆ up (pts {p} {cell.align} v))"
        doc := doc.push s!"\n`v{k}` is `*{p}` there, which goes up by {inc} per iteration."
      if c.plain then owned := owned.push "plain"
      let stem := relName ns body.getPrefix
      let suffix := match body with
        | .str _ s => String.ofList (s.toList.drop 4)
        | _ => ""
      let factText := " ∧\n      ".intercalate facts.toList
      let ownedText := " ⋆\n    ".intercalate owned.toList
      let bodyText := if owned.isEmpty then s!"⟪{factText}⟫" else s!"⟪{factText}⟫ ⋆\n    {ownedText}"
      return s!"/-- The invariant of `{relName ns body}`, a counted loop: `{x}` goes up by 1 while \
        `{x} < {boundName}`.\n`s0` holds the locals at loop entry.{String.join doc.toList} -/\n\
        def {stem}.inv{suffix} {binders}(s0 : {loc}) {entry}(s : {loc}) : FAssn :=\n  {bodyText}\n\n\
        /-- The measure of `{relName ns body}`: the iterations left. -/\n\
        def {stem}.meas{suffix} {binders}(s : {loc}) : Nat :=\n  {bound} - s.{x}.toNat\n"
    pure (.ok text)
  catch ex => pure (.error (← ex.toMessageData.toString))
  return { loop := body, text := res }

/-- The loops of `module` in namespace `ns`: each `F.loopN` with its `F.againN`, sorted. -/
def loopsOf (module ns : Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? module | throwError "module {module} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mut out := #[]
  for n in names do
    if let .str pre s := n then
      let digits := s.toList.drop 4
      if s.startsWith "loop" && !digits.isEmpty && digits.all Char.isDigit && ns.isPrefixOf n then
        let again := Name.str pre ("again" ++ String.ofList digits)
        if env.contains again then out := out.push (n, again)
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
