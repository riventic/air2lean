import Lean
import Air2Lean.Revision

/-!
# `air2lean-invgen`: generated loop invariants and measures (P09)

The offline, untrusted invariant generator of `docs/invariant-synthesis.md`. It reads the loops
of a translated module (the `Zig.loop` bodies `F.loopN` with their `F.againN`), as the elaborated
terms that `fsym` walks, and writes their invariants `F.loopN.inv`, measures `F.loopN.meas` and
exit posts `F.loopN.post` as `def`s into a Lean file (`Inv.lean`), registered with `@[fsym_inv]`:
at the loop, `fsym` applies its loop rule with them (P09-E4), so a proof of the function that runs
the loop names no loop lemma. It adds no tactic, judgment or command: the proofs that use the
definitions are `fsym` walks that the kernel checks, so a wrong or too weak invariant makes a
proof fail, never a wrong proof. A loop outside the families below gets no definition: the generator records why in
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
  iterations) that the checked adds need. The measure is the iterations left. The exit post is the
  exit's label, the other locals at their entry values, the counter at its exit value and each
  written cell at `vₖ + cₖ * n` (the invariant with no iteration left). A body that takes
  a step (`Zig.tick`) runs in the plain mode, so the invariant carries `plain`. The invariant
  holds at entry only for a counter that starts on the repeating side of its exit value (or at
  it): a client proves that, and a loop entered past it is not an instance.

  Widened (S2c′): a cell may be **an item of an array parameter** (`p` itself and
  `Zig.ptrProject p (·.elem size k)` with a literal `k`): the invariant owns the array as
  `up (arr p (x₀ :: … :: xₘ :: tₚ))`, its items up to the last one the body reaches (each a
  written item's value `wₖ` with its facts, or an item it only reads at its entry value `vₖ`) and
  the rest `tₚ` of any length. In a loop that counts up, a cell may go up by **a value `g u` of
  the counter's value `u`** at the iteration's start (and of the parameters, the locals the body
  does not write and the cells it only reads), not only a constant: with the library sum `tsum`,
  the cell plus the increments still to come stays at its entry value plus all of them,
  `v + (tsum e g - tsum x g) = vₖ + (tsum e g - tsum x₀ g)` (`e` the counter's exit value), with
  the no-overflow fact `vₖ + (tsum e g - tsum x₀ g) < 2 ^ w`. And the body may run **an inner
  counted loop** (`execInner`): it is read as its exit post (the inner counter at its exit value,
  each cell it writes up by its constant increment times the inner iterations), so a cell that
  the inner loop moves by a distance that depends on the outer counter is such a sum; the inner
  loop's counter is a **scratch local** (the body sets it before it reads it), which the
  invariant does not state. The walks of the outer step apply the inner loop's generated
  definitions, so the inner loop is generated first.

* **List walk** (`listWalk`, `listCand`; ledger #list-walk-step). One iteration tests an
  optional node pointer, the cursor (`cur.isSome`, a `while (cur) |n|` over `?*Node`): at `null`
  it exits and changes nothing; at a node it reads the node's `next` into the cursor and repeats.
  On the way it may read one item field of the node, add the item or a constant to word locals
  (accumulators), and point the node back to a local that it then sets to the node (a
  reversal). The invariant is stated over the library list family `listSeg`
  (`ZigLean/Sep/Full/ListSeg.lean`) at the node layout the body accesses (`F.loopN.node`: `next`,
  the item field if read, and the rest of each node as a parameter), with the nodes left as a
  ghost measure (`B.inv … s n`, `loop_ghost_ex`): the ghost lists `ys` (visited) and `zs` (left)
  with `xs = ys ++ zs` (a visit; `ys` the segment from the cursor's entry value) or
  `xs = ys.reverse ++ zs` (a reversal; `ys` the list at the reversal's local), each accumulator
  its entry value plus the items visited (with the no-overflow fact over `xs`, an entry
  obligation) and the other locals at their entry values. The exit post holds the whole list
  (reversed for a reversal) and the accumulators over `xs`.

  **With a call** (`readContract`): a visit may hand the cursor's node to one call
  (`a.destroy(n)`, a callback), after its own accesses to the node, if the generator was given a
  contract of the called function (`--contract RULE`, a theorem `∀ ys, T P (f as) fun _ => Q` of a
  specification module, `--spec`). The contract's precondition is read as the node (the atoms that
  name the node's pointer or the values of its fields: `name.node`, which must own the `next`
  field the body reads) and a frame (the other atoms), which the postcondition returns; what
  the postcondition holds besides is what the call leaves of a node (`name.done`). The invariant
  has the nodes passed as the segment at that layout told from its end (`listSegRev name.done
  s0.cur s.cur ys`, `xs = ys.reverse ++ zs`: a node joins it by the constructor, also when what
  the call leaves names neither the node's item nor its next pointer), the nodes left at the
  node's (`listSeg name.node s.cur none zs`), and the frame; its parameters are the loop's and
  the contract's variables that these name, and the contract's other variables (its hypotheses)
  are binders of the step's check only, which walks the call by the contract. A freeing walk is
  the instance whose contract leaves no field of the node.

A loop body is a program of `MM σ ε` (its step is checked as an `FTotalTriple`) or of `CM Tgt σ ε`
(a `CTriple`); its instance parameters are explicit parameters of the definitions (`inst0`).

**The credit mode** (`Cand.creditOutput`, `creditOf`). A loop body registers a second invariant for a
walk that pays its steps with credits (`@[fsym_inv]`'s `B.credits.inv … s n` and
`B.credits.post`; `fsym` takes them when the state at the loop holds credits and no plain mode,
with the counted loop rule `loop_exact`). It is derived from the plain-mode one, for every family:
the same facts and resources without the plain mode, at the exact count `n` of the body runs left
before the last one, which is the family's measure (a list walk's nodes left; a counted loop's
iterations left, as the fact `n = meas`). The rule adds the credits and the receipts
(`credits (n + 1)`, `spent (n + 1)`). The generator walks the rule's step with them (one credit
in, one receipt out, the count lowered by exactly one or zero at the exit); if that walk leaves
anything, the loop gets no credit-mode definitions, and the record says why.

Outside the families (each one recorded with its reason): a cell at an offset of a parameter
that is not an array item at a literal index, an increment that is not a constant in a loop that
counts down, an increment that depends on something the body writes, a bound of another width
(`@intCast`), a `>= 0` or `<= maxInt` test (it holds until the step wraps), an inner loop that is
not counted, whose increments are not constants or that runs a loop itself, a call without a
contract.

The body is read by a symbolic run over its monadic term (`bind`, `pure`, `get`, `modify`, `ite`,
the lifted `Zig.load`/`Zig.store`/`Zig.add`/`Zig.sub`/`Zig.intCast`, the unsigned comparisons
`Zig.lt`/`gt`/`le`/`ge`, `!=` (`bne`), a slice's `len`, `Zig.tick`, a `match` on a known exit,
an optional pointer's `isSome`, `some` and `Zig.optPayload`, and the loads and stores of a node's
fields through the payload, at offsets by `Zig.ptrProject`):
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

/-- A cell that a loop body reads or writes through a loop parameter: the word `*p` at parameter
`param`, or item `k` of the array at it (`item := some k`: `p` itself for `k = 0`, else
`Zig.ptrProject p (·.elem size k)`). -/
structure Loc where
  param : Nat
  item : Option Nat := none
  deriving Inhabited, BEq

/-- A symbolic value of one iteration, over the values at its start. -/
inductive Sym where
  /-- The local `f` at the start of the iteration. -/
  | local (f : Name)
  /-- The cell `l` at the start of the iteration. -/
  | cell (l : Loc)
  /-- The pointer to item `k` of the array at loop parameter `i`. -/
  | item (i k : Nat)
  /-- `k * a`: a cell's change over a whole inner loop (its summary), not a step of the body. -/
  | scale (k : Nat) (a : Sym)
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
  /-- `a.isSome` of an optional pointer. -/
  | isSome (a : Sym)
  /-- `some a`. -/
  | some (a : Sym)
  /-- The payload of the optional pointer `a` (`Zig.optPayload`). -/
  | payload (a : Sym)
  /-- The pointer `a` moved by `k` bytes (`Zig.ptrProject a (·.add k)`). -/
  | addr (a : Sym) (k : Nat)
  /-- The value at offset `k` of the node that the optional pointer `c` points to, as the
  iteration read it (`Zig.load` through `c`'s payload). -/
  | nload (c : Sym) (k : Nat)
  deriving Inhabited, BEq

/-- `s` as a base and a constant summand. -/
partial def Sym.split : Sym → Sym × Int
  | .add a (.lit n) | .add (.lit n) a => let (b, k) := a.split; (b, k + n)
  | .sub a (.lit n) => let (b, k) := a.split; (b, k - n)
  | s => (s, 0)

/-- The summands of `s` (the operands of its sums). -/
partial def Sym.summands : Sym → Array Sym
  | .add a b => a.summands ++ b.summands
  | s => #[s]

/-- The sums in `s` that contain the summand `leaf`: the partial sums of a value that adds terms to
`leaf`. -/
partial def Sym.partialSums (s leaf : Sym) : Array Sym :=
  match s with
  | .add a b =>
    (if s.summands.contains leaf then #[s] else #[]) ++ a.partialSums leaf ++ b.partialSums leaf
  | _ => #[]

/-- Whether `s` reads the start value of the local `f`. -/
partial def Sym.mentions (f : Name) : Sym → Bool
  | .local g => g == f
  | .add a b | .sub a b | .lt a b | .le a b | .ne a b => a.mentions f || b.mentions f
  | .widen a | .isSome a | .some a | .payload a | .addr a _ | .nload a _ | .scale _ a => a.mentions f
  | _ => false

/-- One cell the body accesses: where it is, its value type, width and alignment, its current
value, and whether the path stored to it. -/
structure Cell where
  loc : Loc
  ty : Expr
  width : Nat
  align : Nat
  val : Sym
  stored : Bool := false
  deriving Inhabited

/-- A memory access through a node pointer: the field at offset `off` of the node that the
optional pointer `node` points to, with its value type and alignment, and the value stored to it
(none: a load). -/
structure NodeOp where
  node : Sym
  off : Nat
  ty : Expr
  align : Nat
  store? : Option Sym := none
  deriving Inhabited

/-- The node field that the pointer `p` addresses: the optional pointer whose payload it is
offset, and the offset. -/
def Sym.nodeLoc? : Sym → Option (Sym × Nat)
  | .payload c => Option.some (c, 0)
  | .addr (.payload c) k => Option.some (c, k)
  | _ => none

/-- `()`, the result of a step that returns nothing. -/
def unitV : Sym := .val (.const ``Unit.unit [])

/-- The contract of a call that a list walk makes on the cursor's node, read off a rule
`∀ ys, T P (f as) (fun _ => Q)` of the contracts given to the generator (`--contract`): the
call takes the node's fields, the rest of the node and a frame, and returns the frame and what is
left of the node. All text is over the loop's parameters and the rule's variables. -/
structure Contract where
  /-- The rule. -/
  rule : Name
  /-- The call's argument that is the node's pointer, and the rule's variable for it. -/
  node : Sym
  ptr : String
  /-- The node's fields that the rule's precondition owns as `up (pts (p.add off) al y)`: the
  offset, the alignment, the variable `y` and its type. -/
  fields : Array (Nat × Nat × String × String)
  /-- The rule's variables that the call does not fix and that are not the node's, in order:
  the name, the type and whether it is a hypothesis (a proof). -/
  vars : Array (String × String × Bool)
  /-- The atoms of the precondition that name the node (its fields first to last, the rest of the
  node), those that do not (the frame), and the atoms of the postcondition besides the frame. -/
  nodeAtoms : Array String
  frame : Array String
  after : Array String
  /-- The loop's parameters and the rule's variables that each of the three names. -/
  nodeUses : Array String
  frameUses : Array String
  afterUses : Array String
  /-- The rule at the call's arguments as a function of the node's variables (the `fsym` rule of
  the step's check). -/
  use : String
  deriving Inhabited

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
  /-- The accesses through node pointers, in order (the list-walk family). -/
  nodeOps : Array NodeOp := #[]
  /-- The calls with a contract, in order, each with the number of node accesses before it. -/
  calls : Array (Contract × Nat) := #[]
  /-- Whether the path ran an inner loop that takes steps (`execInner`). -/
  innerSteps : Bool := false

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
  /-- The contracts given to the generator: the function a rule is about, and the rule. -/
  contracts : Array (Name × Name) := #[]
  /-- The loop parameters that the body indexes as arrays (`Zig.ptrProject p (·.elem size k)`),
  with their item size: every access through one is an item (`p` itself is item `0`). -/
  arrays : Array (Nat × Nat) := #[]

/-- `e` on one line. -/
def ppLine (e : Expr) : MetaM String :=
  return (← ppExpr e).pretty (width := 1000000)

/-- The precondition, the command and the postcondition of a triple of the full-state logic. -/
def tripleParts? (concl : Expr) : Option (Expr × Expr × Expr) :=
  if concl.isAppOfArity `Zig.Full.CTriple 5 then
    some (concl.getArg! 2, concl.getArg! 3, concl.getArg! 4)
  else [`Zig.Full.FTotalTriple, `Zig.Full.FTriple, `Zig.Full.FTTotalTriple, `Zig.Full.FTTriple].findSome?
    fun k => if concl.isAppOfArity k 4 then some (concl.getArg! 1, concl.getArg! 2, concl.getArg! 3)
      else none

/-- The function that the rule `rule` is about: the head of its triple's command. -/
def contractOf (rule : Name) : MetaM Name := do
  let some info := (← getEnv).find? rule | throwError "no contract `{rule}`"
  unless info.levelParams.isEmpty do throwError "a contract `{rule}` with universe parameters"
  forallTelescope info.type fun _ concl => do
    let some (_, cmd, _) := tripleParts? concl | throwError "a contract `{rule}` that is not a triple"
    let some f := cmd.getAppFn.constName? | throwError "a contract `{rule}` whose command is not a call"
    return f

/-- The atoms of the assertion `e`: the operands of its separating conjunctions, with the
reducible definitions on the way unfolded (a node written as its layout's name). -/
partial def sepAtoms (e : Expr) : MetaM (Array Expr) := do
  let w ← whnfR e
  if w.isAppOfArity `Zig.Full.FAssn.sep 2 then
    return (← sepAtoms (w.getArg! 0)) ++ (← sepAtoms (w.getArg! 1))
  -- An atom keeps the form the contract states it in (`I.fee φ`, not the projection it reduces
  -- to), unless it reduces to a cell.
  return #[if w.isAppOfArity `Zig.Full.FAssn.up 1 then w else e]

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
  -- an optional pointer: its test (a `while (cur) |n|` over `?*Node`) and a pointer as one
  if e.isAppOfArity ``Option.isSome 2 && (e.getArg! 0).isConstOf `Zig.Ptr then
    return .isSome (← evalPure ctx st e.appArg!)
  if e.isAppOfArity ``Option.some 2 && (e.getArg! 0).isConstOf `Zig.Ptr then
    return .some (← evalPure ctx st e.appArg!)
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

/-- Access the cell `l` with value type `ty` and alignment `align` (the same at every access; a new
cell holds its entry value): its index in `st.cells`. -/
def St.access (st : St) (l : Loc) (ty : Expr) (align : Nat) : MetaM (St × Nat) := do
  match st.cells.findIdx? (·.loc == l) with
  | some k =>
    let c := st.cells[k]!
    unless c.ty == ty && c.align == align do throwError "a cell accessed at two types or alignments"
    return (st, k)
  | none =>
    let some width := bitVecWidth? ty | throwError "a cell that is not an unsigned word: {ty}"
    return ({ st with cells := st.cells.push { loc := l, ty, width, align, val := .cell l } },
      st.cells.size)

/-- The item size and the index of a projection `(·.elem size k)` with literal `size` and `k`. -/
def elemProj? (f : Expr) : Option (Nat × Nat) :=
  match f.consumeMData with
  | .lam _ _ b _ =>
    if b.isAppOfArity `Zig.Ptr.elem 3 && (b.getArg! 0).consumeMData == .bvar 0 then
      match natLit? (b.getArg! 1), natLit? (b.getArg! 2) with
      | some sz, some k => some (sz, k)
      | _, _ => none
    else none
  | _ => none

/-- The cell that the pointer `p` addresses: a loop parameter (item `0` of an array parameter) or
an item of an array parameter (`Sym.item`). -/
def locOf? (ctx : Ctx) (st : St) (p : Expr) : MetaM (Option Loc) := do
  if let some i := paramIdx? ctx p then
    return some { param := i, item := if ctx.arrays.any (·.1 == i) then some 0 else none }
  match ← (try some <$> evalPure ctx st p catch _ => pure none) with
  | some (.item i k) => return some { param := i, item := some k }
  | _ => return none

/-- The contract `rule` at the call `call` (its function applied to the call's arguments), or why
it does not fit. The call fixes some of the rule's variables: one is the node's pointer (an
optional pointer's payload in the body), the others are terms over the loop's parameters, which
the text has in their place. The node's variables are the pointer and the values of the fields
that the precondition owns at offsets of it (`up (pts (p.add k) a y)`); the precondition's atoms
that name one are the node, the others the frame, which the postcondition must return atom for
atom. The call returns `()` and its postcondition does not read the result. -/
def readContract (ctx : Ctx) (st : St) (rule : Name) (call : Expr) : MetaM Contract := do
  let some info := (← getEnv).find? rule | throwError "no contract `{rule}`"
  let (ms, _, concl) ← forallMetaTelescope info.type
  let some (_, cmd, _) := tripleParts? concl | throwError "a contract `{rule}` that is not a triple"
  unless ← isDefEq cmd call do throwError "the contract `{rule}` is not about the call {call}"
  let vals ← ms.mapM (instantiateMVars ·)
  forallTelescope info.type fun ys concl => do
    let name (y : Expr) : MetaM String := do
      let n := (← y.fvarId!.getDecl).userName
      if n.hasMacroScopes then throwError "a variable of the contract `{rule}` without a name"
      return n.toString
    -- the variables that the call fixes: the node's pointer, or a term over the loop's parameters
    let mut fixed : Array (Expr × Expr) := #[]
    let mut node? : Option (Expr × Sym) := none
    for h : i in [0:ys.size] do
      let v := vals[i]!
      if v.isMVar then continue
      if v.hasExprMVar then throwError "a call that fixes a variable of the contract `{rule}` only in part"
      let local? := match v with | .fvar id => ctx.env[id]? | _ => none
      if let some sym := local? then
        let some (_, 0) := sym.nodeLoc? | throwError "a call argument that is not the loop's or the node's pointer"
        if node?.isSome then throwError "a call that takes two nodes"
        node? := some (ys[i], sym)
      else
        let outside := (collectFVars {} v).fvarIds.any (!ctx.params.contains ·)
        if outside then throwError "a call argument that is not over the loop's parameters"
        fixed := fixed.push (ys[i], v)
    let some (py, node) := node? | throwError "a call that does not take a node"
    let inst (e : Expr) : Expr := e.replaceFVars (fixed.map (·.1)) (fixed.map (·.2))
    let some (P, _, Q) := tripleParts? concl | throwError "a contract `{rule}` that is not a triple"
    let Q ← match (inst Q).consumeMData with
      | .lam _ _ b _ =>
        if b.hasLooseBVars then throwError "a contract `{rule}` whose postcondition reads the result"
        pure b
      | _ => throwError "a contract `{rule}` whose postcondition is not a function"
    let pre ← sepAtoms (inst P)
    let kept := ys.filter fun y => !fixed.any (·.1 == y)
    -- the node's fields and variables
    let mut fields := #[]
    let mut nodeVars := #[py]
    for a in pre do
      unless a.isAppOfArity `Zig.Full.FAssn.up 1 do continue
      let x := a.appArg!.consumeMData
      unless x.isAppOfArity `Zig.pts 5 do continue
      let (T, q, al, v) := (x.getArg! 0, x.getArg! 2, x.getArg! 3, x.getArg! 4)
      let off? : Option Nat :=
        if q == py then some 0
        else if q.isAppOfArity `Zig.Ptr.add 2 && q.getArg! 0 == py then natLit? (q.getArg! 1)
        else none
      let (some off, some al) := (off?, natLit? al) | continue
      unless v.isFVar && kept.contains v && !nodeVars.contains v do continue
      fields := fields.push (off, al, ← name v, ← ppLine T)
      nodeVars := nodeVars.push v
    let names (a : Expr) : Bool := nodeVars.any fun y => a.containsFVar y.fvarId!
    let nodeAtoms := pre.filter names
    let frame := pre.filter (!names ·)
    let mut after ← sepAtoms Q
    for f in frame do
      let some i := after.idxOf? f
        | throwError "the contract `{rule}` does not return its frame `{← ppLine f}`"
      after := after.extract 0 i ++ after.extract (i + 1) after.size
    -- the other variables
    let mut vars := #[]
    for y in kept do
      if nodeVars.contains y then continue
      let ty := inst (← inferType y)
      vars := vars.push (← name y, ← ppLine ty, ← isProp ty)
    let uses (atoms : Array Expr) : MetaM (Array String) := do
      let mut out := #[]
      for id in ctx.params ++ (kept.filter (!nodeVars.contains ·)).map (·.fvarId!) do
        if atoms.any (·.containsFVar id) then out := out.push (← id.getDecl).userName.toString
      return out
    let mut binders := ""
    let mut args := ""
    for h : i in [0:ys.size] do
      let y := ys[i]
      match fixed.find? (·.1 == y) with
      | some (_, v) => args := args ++ s!" ({← ppLine v})"
      | none =>
        args := args ++ s!" {← name y}"
        if nodeVars.contains y then binders := binders ++ s!"({← name y} : {← ppLine (inst (← inferType y))}) "
    return {
      rule, node, ptr := ← name py, fields, vars,
      nodeAtoms := ← nodeAtoms.mapM ppLine, frame := ← frame.mapM ppLine, after := ← after.mapM ppLine,
      nodeUses := ← uses nodeAtoms, frameUses := ← uses frame, afterUses := ← uses after,
      use := s!"(fun {binders}=> @{rule}{args})" }

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

/-- The exits' labels: the constructors that the exiting paths return (`none`: an exit with a
payload). -/
def exitLabels (exits : Array Path) : Option (Array Name) :=
  exits.foldl (init := some #[]) fun ls? p => do
    let l ← match p.res with | .val e => e.constName? | _ => none
    let ls ← ls?
    return if ls.contains l then ls else ls.push l

/-- What an iteration of a counted loop adds to a cell it writes: the constant `k` and the values
`terms`, each over the counter's value at the iteration's start, the loop's parameters, the locals
the body does not write and the cells it only reads. -/
structure Inc where
  k : Nat := 0
  terms : Array Sym := #[]
  deriving Inhabited

/-- `s` is built by sums, differences, widenings and summaries from the leaves that `ok` accepts. -/
partial def Sym.over (ok : Sym → Bool) : Sym → Bool
  | .add a b | .sub a b => a.over ok && b.over ok
  | .widen a | .scale _ a => a.over ok
  | s => ok s

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
  /-- The cells the body accesses, in order, with their increments (none for a cell it only
  reads). -/
  cells : Array (Cell × Inc)
  /-- The locals that the body writes but whose values at an iteration's start no path reads (an
  inner loop's counter, set before the inner loop runs): the invariant says nothing about them. -/
  scratch : Array Name
  /-- The exits' labels: the constructors of the exit type that an exiting iteration returns
  (`none`: an exit that returns a constructor with a payload). -/
  exits : Option (Array Name)
  plain : Bool
  /-- A path runs an inner loop that takes steps: a body run takes more than one step. -/
  innerSteps : Bool := false

/-- `R` includes the bound: the counter passes it by one before the loop exits. -/
def Counted.incl (c : Counted) : Bool := c.rel == .le || c.rel == .ge

/-- The one repeating path of an iteration and its exiting paths (each family's first test). -/
def splitPaths (again : Expr → MetaM Bool) (paths : Array Path) : MetaM (Path × Array Path) := do
  let mut cont := #[]
  let mut exits := #[]
  for p in paths do
    let .val e := p.res | throwError "an iteration whose exit is not a constructor"
    if ← again e then cont := cont.push p else exits := exits.push p
  let #[c] := cont | throwError "{cont.size} repeating paths, not one"
  if exits.isEmpty then throwError "no exit"
  return (c, exits)

/-- Classify the paths of one iteration as a counted loop, or say why not. -/
def counted (ctx : Ctx) (again : Expr → MetaM Bool) (paths : Array Path) : MetaM Counted := do
  let (c, exits) ← splitPaths again paths
  -- A local that a path reads: its start value occurs in a value of the path (not counting the
  -- local itself left unchanged).
  let reads (f : Name) : Bool := paths.any fun p =>
    (p.st.locals.zip ctx.fields).any (fun (v, g) => v.mentions f && !(g == f && v == .local f)) ||
      p.st.cells.any (·.val.mentions f) || p.st.checked.any (·.mentions f) ||
      p.st.cond.any (·.1.mentions f) || p.res.mentions f
  let changed := (c.st.locals.zip ctx.fields).filter fun (v, f) => v != .local f
  let scratch := (changed.filter fun (_, f) => !reads f).map (·.2)
  -- The counter: the one local the iteration changes and reads, by 1 up or down.
  let counters := changed.filter fun (_, f) => !scratch.contains f
  let #[(v, x)] := counters | throwError "the body writes {counters.size} locals that it reads, not one counter"
  let (base, step) := v.split
  unless base == .local x && step.natAbs == 1 do throwError "the counter `{x}` does not step by 1"
  let down := step == -1
  let some (cnd, o) := c.st.cond | throwError "the repeating path is not guarded by a test"
  let some (rel, b) := relOf x cnd o | throwError "the repeating path is not guarded by a test of `{x}`"
  unless (if down then rel != .lt && rel != .le else rel != .gt && rel != .ge) do
    throwError "the counter `{x}` steps away from its bound (`{x} {rel.text} …`)"
  let unchanged (f : Name) : Bool :=
    (c.st.locals.zip ctx.fields).any fun (v, g) => g == f && v == .local f
  let readOnly (l : Loc) : Bool := c.st.cells.any fun cell => cell.loc == l && !cell.stored
  -- what a cell may go up by besides a constant: values over the counter, the parameters, the
  -- locals the body does not write and the cells it only reads
  let leafOk (s : Sym) : Bool := match s with
    | .local f => f == x || unchanged f
    | .param _ | .slen _ | .lit _ => true
    | .cell l => readOnly l
    | _ => false
  let mut cells := #[]
  for cell in c.st.cells do
    if !cell.stored then cells := cells.push (cell, {}); continue
    let leaves := cell.val.summands
    unless (leaves.filter (· == .cell cell.loc)).size == 1 do
      throwError "a cell that does not go up from its value (the body overwrites it)"
    let mut inc : Inc := {}
    for t in leaves do
      if t == .cell cell.loc then continue
      if let .lit n := t then inc := { inc with k := inc.k + n }; continue
      unless t.over leafOk do throwError "a cell that goes up by a value of something the body writes"
      inc := { inc with terms := inc.terms.push t }
    if down && !inc.terms.isEmpty then
      throwError "a cell that goes up by a value that is not a constant, in a loop that counts down"
    cells := cells.push (cell, inc)
  match b with
  | .local y =>
    if y == x then throwError "a bound that is the counter"
    unless unchanged y do throwError "a bound in a local the body writes"
  | .param _ | .lit _ | .slen _ => pure ()
  | .cell l => unless readOnly l do throwError "a bound in a cell the body writes"
  | _ => throwError "a bound that is not a local, a parameter, a literal, a slice length or a cell"
  for p in exits do
    unless p.st.cond == some (cnd, !o) do throwError "an exit guarded by another test"
    unless p.st.checked.isEmpty && (p.st.locals.zip ctx.fields).all (fun (v, f) => v == .local f) do
      throwError "an exit that adds, subtracts or changes a local"
    for cell in p.st.cells do
      unless !cell.stored && cells.any (fun (k, _) => k.loc == cell.loc && k.ty == cell.ty && k.align == cell.align) do
        throwError "an exit that writes memory or reads a cell the repeating path does not"
  -- Every add and subtraction of the repeating path is a step of the counter or a partial sum of a
  -- cell's new value, so the counter's bounds and the no-overflow facts cover it.
  for a in c.st.checked do
    let (base, k) := a.split
    unless (base == .local x && (k == 0 || k == step)) ||
        cells.any (fun (cell, _) => cell.stored && (cell.val.partialSums (.cell cell.loc)).contains a) do
      throwError "an add or subtraction that the counter's and the cells' bounds do not cover"
  -- (an exit with a payload has no label: the post then states only that it exits)
  return { counter := x, rel, bound := b, down, cells, scratch, exits := exitLabels exits,
           plain := paths.any (·.st.tick), innerSteps := paths.any (·.st.innerSteps) }

/-- A definition's value with its leading instance binders named (`inst0`, by position): the
generated definitions take them as explicit parameters. -/
partial def nameInsts (i : Nat) : Expr → Expr
  | .lam n ty b bi =>
    .lam (if bi.isInstImplicit then Name.mkSimple s!"inst{i}" else n) ty (nameInsts (i + 1) b) bi
  | e => e

/-- The loop parameters (`params`) that the body `code` indexes as arrays, with their item size
(`Zig.ptrProject p (·.elem size k)`). -/
def arraysOf (params : Array Expr) (code : Expr) : MetaM (Array (Nat × Nat)) := do
  let out ← IO.mkRef (#[] : Array (Nat × Nat))
  code.forEachWhere (·.isAppOfArity `Zig.ptrProject 2) fun e => do
    let some i := params.idxOf? (e.getArg! 0).consumeMData | return
    let some (sz, _) := elemProj? (e.getArg! 1) | return
    let arrs ← out.get
    if arrs.any (fun (j, s) => j == i && s != sz) then throwError "an array indexed at two item sizes"
    unless arrs.contains (i, sz) do out.set (arrs.push (i, sz))
  out.get

/-- `s` with each leaf (a value that is not a sum, difference, widening or summary) replaced by
`leaf`. -/
partial def Sym.substM (leaf : Sym → MetaM Sym) : Sym → MetaM Sym
  | .add a b => return .add (← a.substM leaf) (← b.substM leaf)
  | .sub a b => return .sub (← a.substM leaf) (← b.substM leaf)
  | .widen a => return .widen (← a.substM leaf)
  | .scale k a => return .scale k (← a.substM leaf)
  | s => leaf s

/-- `d` times `k`. -/
def scaleBy (k : Nat) (d : Sym) : Sym := if k == 1 then d else .scale k d

/-- `a - b`, `a` itself for `b = 0`. -/
def subSym (a b : Sym) : Sym := if b == .lit 0 then a else .sub a b

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
  | some n@`Zig.callM | some n@`Zig.callMC | some n@`Zig.callC =>
    -- (`callM r : MM σ α` and `callMC r : CM Tgt σ α` lift the memory command `r`, `callC r` the
    -- concurrent function `r`)
    let callee := (args.back?.getD default).consumeMData
    unless args.size == (if n == `Zig.callM then 3 else 4) do throwError "a partial lift: {e}"
    -- a call with a contract (`--contract`): the first rule about the function that fits
    let rules : Array (Name × Name) := match callee.getAppFn.constName? with
      | some f => ctx.contracts.filter (·.1 == f)
      | none => #[]
    if !rules.isEmpty then
      unless (← inferType callee).getAppArgs.back?.any (·.isConstOf ``Unit) do
        throwError "a call with a contract that returns a value"
      let mut why := #[]
      for (_, rule) in rules do
        try
          let k ← readContract ctx st rule callee
          return #[{ st := { st with calls := st.calls.push (k, st.nodeOps.size) }, res := unitV }]
        catch ex => why := why.push (← ex.toMessageData.toString)
      throwError "a call that no given contract fits: {"; ".intercalate why.toList}"
    if callee.isAppOfArity `Zig.ptrProject 2 then
      let base ← evalPure ctx st (callee.getArg! 0)
      -- an item of an array parameter (`(·.elem size k)`, `k` a literal)
      if let .param i := base then
        let some (sz, k) := elemProj? (callee.getArg! 1)
          | throwError "a pointer projection of a parameter that is not an item at a literal index"
        unless ctx.arrays.contains (i, sz) do
          throwError "an item of a parameter that the body does not index directly (`arraysOf`)"
        return #[{ st, res := .item i k }]
      -- else a field of a node (`(·.add k)` of an optional pointer's payload)
      let .payload _ := base | throwError "a pointer projection of a value that is not a parameter or a node"
      let k? : Option Nat := match (callee.getArg! 1).consumeMData with
        | .lam _ _ b _ =>
          if b.isAppOfArity `Zig.Ptr.add 2 && (b.getArg! 0).consumeMData == .bvar 0 then
            natLit? (b.getArg! 1) else none
        | _ => none
      let some k := k? | throwError "a pointer projection that is not by a constant: {callee}"
      return #[{ st, res := .addr base k }]
    unless callee.isConstOf `Zig.tick do throwError "a call: {e}"
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
    if n == `Zig.loop then
      unless args.size == 7 do throwError "a partial nested loop: {e}"
      return #[← execInner ctx st args[5]! args[6]!]
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
  -- (a field of a node: through an optional pointer's payload, `Sym.nodeLoc?`)
  let nodeLoc? (p : Expr) : MetaM (Option (Sym × Nat)) := do
    if (paramIdx? ctx p).isSome then return none
    try return (← evalPure ctx st p).nodeLoc? catch _ => return none
  if x.isAppOfArity `Zig.load 4 then
    let some al := natLit? args[2]! | throwError "a load with an unknown alignment"
    if let some (c, off) ← nodeLoc? args[3]! then
      -- the value the path stored there last, else the field's value at the iteration's start
      let last := st.nodeOps.findSomeRev? fun o =>
        if o.node == c && o.off == off then o.store? else none
      let op := { node := c, off, ty := args[0]!, align := al }
      return { st := { st with nodeOps := st.nodeOps.push op }, res := last.getD (.nload c off) }
    let some l ← locOf? ctx st args[3]! | throwError "a load through a pointer that is not a loop parameter"
    let (st, k) ← st.access l args[0]! al
    return { st, res := st.cells[k]!.val }
  if x.isAppOfArity `Zig.store 5 then
    let some al := natLit? args[2]! | throwError "a store with an unknown alignment"
    let v ← evalPure ctx st args[4]!
    if let some (c, off) ← nodeLoc? args[3]! then
      let op := { node := c, off, ty := args[0]!, align := al, store? := some v }
      return { st := { st with nodeOps := st.nodeOps.push op }, res := unitV }
    let some l ← locOf? ctx st args[3]! | throwError "a store through a pointer that is not a loop parameter"
    let (st, k) ← st.access l args[0]! al
    return { st := { st with cells := st.cells.modify k ({ · with val := v, stored := true }) },
             res := unitV }
  if x.isAppOfArity `Zig.optPayload 2 then
    return { st, res := .payload (← evalPure ctx st args[1]!) }
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

/-- An inner loop `Zig.loop body again` that the body runs, read as its summary: the inner body is
read as a counted loop (over the same locals), and the path continues after its exit. The inner
counter is at its exit value (the bound, or one past it for `<=`/`>=`), each cell it writes has
gone up by its constant increment times the iterations (the distance from the counter's value at
the inner loop's entry to its exit value), and the result is the inner loop's one exit. This is
the inner loop's generated exit post (`B.post`, which `fsym` applies at the inner loop) read as
values: the outer loop's candidates come from it, and the walks of the outer step, which run the
inner loop by its registered invariant, decide. An inner loop with no counted reading, with an
increment that is not a constant, with another loop inside or with several exits is outside. -/
partial def execInner (ctx : Ctx) (st : St) (body again : Expr) : MetaM Path := do
  let some bodyName := body.getAppFn.constName? | throwError "a nested loop whose body is not a definition"
  let some againName := again.consumeMData.constName? | throwError "a nested loop whose test is not a definition"
  let some (.defnInfo d) := (← getEnv).find? bodyName | throwError "a nested loop whose body is not a definition"
  let bargs := body.getAppArgs
  lambdaTelescope (nameInsts 0 d.value) fun ys code => do
    unless ys.size == bargs.size do throwError "a nested loop whose body is applied in part"
    let ty ← inferType code
    unless ty.isAppOfArity `Zig.MM 2 && (ty.getArg! 0).isConstOf ctx.structName do
      throwError "a nested loop that is not a body of `Zig.MM` over the same locals"
    let ictx : Ctx := { structName := ctx.structName, fields := ctx.fields,
                        params := ys.map (·.fvarId!), arrays := ← arraysOf ys code }
    let paths ← exec ictx { locals := ctx.fields.map .local } code
    let isAgain (e : Expr) : MetaM Bool := do
      return (← whnf (mkApp (.const againName []) e)).isConstOf ``Bool.true
    let c ← try counted ictx isAgain paths
      catch ex => throwError "a nested loop outside the counted family: {ex.toMessageData}"
    unless c.scratch.isEmpty do throwError "a nested loop that runs a nested loop"
    let some #[label] := c.exits | throwError "a nested loop without exactly one exit label"
    -- the inner loop's parameters, at the outer loop's values
    let argSyms ← bargs.mapM (evalPure ctx st)
    let idx (f : Name) : Nat := (ctx.fields.idxOf? f).getD 0
    -- the cell `l` of the inner loop, as the outer loop reaches it
    let outerLoc (l : Loc) : MetaM Loc := do
      let some (.param j) := argSyms[l.param]? | throwError "a nested loop that accesses a cell through a value that is not a parameter"
      unless (ctx.arrays.any (·.1 == j)) == l.item.isSome do
        throwError "a nested loop that indexes a parameter as an array differently"
      return { param := j, item := l.item }
    -- (the cells that the substitution reads are accessed first, so `subst` is pure)
    let mut st := st
    for (cell, _) in c.cells do
      st := (← st.access (← outerLoc cell.loc) cell.ty cell.align).1
    let st0 := st
    let cellVal (l : Loc) : MetaM Sym := do
      let l' ← outerLoc l
      let some cell := st0.cells.find? (·.loc == l') | throwError "a nested loop's cell"
      return cell.val
    -- an inner value at the inner loop's entry, over the outer iteration's start
    let subst := Sym.substM fun s => match s with
      | .local f => return st0.locals[idx f]!
      | .param i => return argSyms[i]!
      | .slen i => match argSyms[i]! with
        | .param j => return .slen j
        | _ => throwError "a nested loop's bound of a slice that is not a parameter"
      | .cell l => cellVal l
      | .lit n => return .lit n
      | _ => throwError "a nested loop's value that the summary does not read"
    let b ← subst c.bound
    let x0 := st0.locals[idx c.counter]!
    let exitV := if c.down then (if c.incl then .sub b (.lit 1) else b)
      else if c.incl then .add b (.lit 1) else b
    let dist := if c.down then subSym x0 exitV else subSym exitV x0
    for (cell, inc) in c.cells do
      if !cell.stored then continue
      unless inc.terms.isEmpty do throwError "a nested loop whose cell goes up by a value that is not a constant"
      let (st', k) ← st.access (← outerLoc cell.loc) cell.ty cell.align
      let v := Sym.add st'.cells[k]!.val (scaleBy inc.k dist)
      st := { st' with cells := st'.cells.modify k ({ · with val := v, stored := true }),
                       checked := st'.checked.push v }
    st := { st with locals := st.locals.set! (idx c.counter) exitV, tick := st.tick || c.plain,
                    innerSteps := st.innerSteps || c.plain }
    return { st, res := .val (.const label []) }

end

/-- What an accumulator of a list walk adds per node: the item, or a constant. -/
inductive Acc where
  | item
  | count (k : Nat)

/-- A recognized list walk (the list-walk family over the library list family `listSeg`). -/
structure Walk where
  /-- The cursor, an optional node pointer (a local). -/
  cursor : Name
  /-- The offset and alignment of the node's `next` field. -/
  next : Nat × Nat
  /-- The node's item field the body reads: its offset, value type and alignment. -/
  item? : Option (Nat × Expr × Nat)
  /-- The reversal: the local that holds the reversed prefix (the body points each node it passes
  back to it); none: a visit, which leaves the nodes unchanged. -/
  rev? : Option Name
  /-- The accumulators: each a word local that the body adds the item or a constant to. -/
  accs : Array (Name × Nat × Acc)
  /-- The locals that the body leaves unchanged. -/
  pinned : Array Name
  exits : Option (Array Name)
  plain : Bool
  /-- The call that the body hands each node to, by its contract (a consuming walk): the nodes
  passed are then what the contract leaves of them. -/
  call? : Option Contract := none

/-- An optional pointer (`?*T`). -/
def isOptPtr (ty : Expr) : Bool :=
  ty.isAppOfArity ``Option 1 && ty.appArg!.isConstOf `Zig.Ptr

/-- Classify the paths of one iteration as a list walk, or say why not: the iteration tests the
cursor `c` (`c.isSome`); at `null` it exits and changes nothing; at a node it reads the node's
`next` into the cursor and repeats. On the way it may add the node's item or a constant to word
locals (accumulators), and it may point the node back to the reversed prefix, a local that it then
sets to the node (a reversal). It accesses no other node, field or memory. `fieldTy f` is the type
of the local `f`. -/
def listWalk (ctx : Ctx) (again : Expr → MetaM Bool) (fieldTy : Name → MetaM Expr)
    (paths : Array Path) : MetaM Walk := do
  let (c, exits) ← splitPaths again paths
  let some (.isSome (.local cur), true) := c.st.cond
    | throwError "the repeating path is not guarded by a test of an optional pointer local"
  unless isOptPtr (← fieldTy cur) do throwError "a cursor `{cur}` that is not an optional pointer"
  for p in exits do
    unless p.st.cond == some (.isSome (.local cur), false) do throwError "an exit guarded by another test"
    unless p.st.checked.isEmpty && p.st.cells.isEmpty && p.st.nodeOps.isEmpty && p.st.calls.isEmpty &&
        (p.st.locals.zip ctx.fields).all (fun (v, f) => v == .local f) do
      throwError "an exit that adds, accesses memory, calls or changes a local"
  unless c.st.cells.isEmpty do throwError "a list walk that accesses a cell of a parameter"
  let ops := c.st.nodeOps
  unless ops.all (·.node == .local cur) do throwError "an access to a node other than the cursor's"
  -- the cursor moves to the node's `next`
  let some cv := (c.st.locals.zip ctx.fields).findSome? fun (v, f) => if f == cur then some v else none
    | throwError "no cursor"
  let .nload (.local c0) nextOff := cv | throwError "the cursor `{cur}` does not move to a field of its node"
  unless c0 == cur do throwError "the cursor `{cur}` moves to a field of another node"
  let some nextOp := ops.find? fun o => o.off == nextOff && o.store?.isNone
    | throwError "no load of the node's next pointer"
  unless ops.all (fun o => o.off != nextOff || (isOptPtr o.ty && o.align == nextOp.align)) do
    throwError "a next field that is not an optional pointer at one alignment"
  -- the item: the one other field it reads
  let reads := ops.filter fun o => o.off != nextOff && o.store?.isNone
  let item? ← match reads[0]? with
    | none => pure none
    | some o =>
      unless reads.all (fun o' => o'.off == o.off && o'.ty == o.ty && o'.align == o.align) do
        throwError "a list walk that reads two fields of a node"
      pure (some (o.off, o.ty, o.align))
  -- a reversal points the node back to the prefix, which then starts at the node
  let stores := ops.filter (·.store?.isSome)
  let changed := (c.st.locals.zip ctx.fields).filter fun (v, f) => v != .local f && f != cur
  let rev? ← match stores.toList with
    | [] => pure none
    | [o] =>
      let some (.local r) := o.store? | throwError "a node store outside the reversal"
      unless o.off == nextOff && r != cur do throwError "a node store outside the reversal"
      unless changed.any (fun (v, f) => f == r && v == .some (.payload (.local cur))) do
        throwError "a node store whose local does not move to the node"
      pure (some r)
    | _ => throwError "a node store outside the reversal"
  -- every other change: an accumulator `a := a + item` (widened) or `a := a + k`
  let mut accs := #[]
  for (v, f) in changed do
    if rev? == some f then continue
    let some w := bitVecWidth? (← fieldTy f) | throwError "a local `{f}` that is not a word changes"
    let .add (.local f') t := v | throwError "a local `{f}` that does not go up by the item or a constant"
    unless f' == f do throwError "a local `{f}` that does not go up by the item or a constant"
    let itemV : Bool := match item? with
      | some (k, _, _) => t == .nload (.local cur) k || t == .widen (.nload (.local cur) k)
      | none => false
    let acc ← if itemV then
        unless (item?.bind fun (_, ty, _) => bitVecWidth? ty).isSome do throwError "an item that is not a word"
        pure Acc.item
      else match t with
        | .lit k => if k == 0 then throwError "a local `{f}` that goes up by 0" else pure (Acc.count k)
        | _ => throwError "a local `{f}` that does not go up by the item or a constant"
    accs := accs.push (f, w, acc)
  -- every add the path ran is an accumulator's
  for a in c.st.checked do
    unless changed.any (fun (v, f) => v == a && accs.any (·.1 == f)) do
      throwError "an add or subtraction outside the accumulators"
  let pinned := ctx.fields.filter fun f => f != cur && rev? != some f && !accs.any (·.1 == f)
  -- a call with a contract takes the cursor's node, after the body's accesses to it: the
  -- contract owns the `next` field and the item's (and at most that one value besides `next`)
  let call? ← match c.st.calls with
    | #[] => pure none
    | #[(k, before)] =>
      unless k.node == .payload (.local cur) do throwError "a call on a node other than the cursor's"
      unless before == ops.size do throwError "an access to a node after the call that takes it"
      unless stores.isEmpty do throwError "a store to a node that a call takes"
      unless k.fields.any (fun (off, al, _, _) => off == nextOff && al == nextOp.align) do
        throwError "the contract `{k.rule}` does not own the node's next field"
      if let some (off, _, al) := item? then
        unless k.fields.any (fun (off', al', _, _) => off' == off && al' == al) do
          throwError "the contract `{k.rule}` does not own the node's item field"
      if k.fields.size > 2 then
        throwError "the contract `{k.rule}` owns {k.fields.size - 1} values of a node besides `next`, not at most one"
      pure (some k)
    | _ => throwError "a list walk with two calls"
  return { cursor := cur, next := (nextOff, nextOp.align), item?, rev?, accs, pinned,
           exits := exitLabels exits, plain := paths.any (·.st.tick), call? }

/-- `n` without the namespace `ns`. -/
def relName (ns n : Name) : String :=
  (n.replacePrefix ns .anonymous).toString

/-- Names the generated text binds next to the loop's parameters (`r`: the step's result in the
check of `walk`). -/
def reserved (n : Name) : Bool :=
  match n with
  | .str .anonymous s => ["s", "s0", "v", "r", "n", "u", "xs", "ys", "zs", "X", "D", "V", "up", "pts",
      "arr", "tsum", "plain", "listSeg", "FAssn", "Zig", "BitVec", "List"].contains s ||
      -- (the cells' entry values `vₖ`, an array's items `wₖ` and its rest `tᵢ`)
      (["v", "w", "t"].any (fun c : String => s.startsWith c) && s.length > 1 && (s.toList.drop 1).all Char.isDigit)
  | _ => false

/-- `s` in parentheses if it has a space. -/
def paren (s : String) : String := if s.contains ' ' then s!"({s})" else s

/-- The cell `l` as Zig writes it, `p` its parameter's name: `*p` or `p[k]`. -/
def cellName (p : String) (l : Loc) : String :=
  match l.item with
  | some k => s!"{p}[{k}]"
  | none => s!"*{p}"

/-- The value `s` as `Nat` source text, with its leaves written by `leaf` (a difference does not
wrap: each one in a body is checked, and a summary's is the distance its counter goes). -/
partial def Sym.natText (leaf : Sym → MetaM String) : Sym → MetaM String
  | .add a b => return s!"({← a.natText leaf} + {← b.natText leaf})"
  | .sub a b => return s!"({← a.natText leaf} - {← b.natText leaf})"
  | .widen a => a.natText leaf
  | .scale k a => return s!"{k} * {← a.natText leaf}"
  | .lit n => return toString n
  | s => leaf s

/-- A candidate fact of a loop invariant, as source text over the loop's parameters, the entry
locals `s0`, the cells' entry values `vₖ` and the locals `s`. -/
structure Fact where
  text : String
  /-- The written cell `k` (with its value type) whose current value the fact states: the fact
  stands inside that cell's existential, whose variable is `var`. -/
  cell? : Option (Nat × String) := none
  var : String := "v"
  deriving Inhabited

/-- A resource of the invariant, in order. -/
inductive Owned where
  /-- A cell the loop only reads, owned at its entry value. -/
  | read (atom : String)
  /-- The written cell `k`, owned at a value `v : ty` that its facts state. -/
  | written (k : Nat) (ty atom : String)
  /-- Another atom (a list walk's lists). -/
  | atom (text : String)
  /-- The array at `p`: its items `0, 1, …` as the cells `k` (a written one at a value `wₖ : ty`
  that its facts state, one the loop only reads at its entry value `vₖ`), then the rest `tail`. -/
  | arr (p : String) (items : Array (Nat × Option String)) (tail : String)
  | plain

/-- The candidate invariant `name.inv` of a loop, its measure `name.meas` and its exit post
`name.post`, as source text: the invariant's facts are candidates, which `houdini` prunes. -/
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
  /-- The exit type, and the exit post's facts over the exit `r` and its value fact of each
  written cell `k` (not candidates: the output's walk with the post checks them, `genLoop`). -/
  exit : String
  postFacts : Array String
  postCells : Array (Nat × String)
  /-- A list walk's: the invariant's last parameter is a ghost measure `n` (no `name.meas`), and
  its facts and resources stand under the existentials `exs` (name, type) of the ghost lists. -/
  ghost : Bool := false
  exs : Array (String × String) := #[]
  /-- The exit post's resources, if not `owned`. -/
  postOwned? : Option (Array Owned) := none
  /-- Definitions the others use (a list walk's node layout), as text. -/
  pre : String := ""
  /-- The arguments of the check's `fsym` (` [update]`). -/
  fsymArgs : String := ""
  /-- The body at the loop's parameters (`@B xs`), as the check runs it. -/
  run : String
  /-- The binders of the check's theorem: `binders` with the instance parameters as instances,
  and the variables of a contract that the definitions do not take (its hypotheses). -/
  tbinders : String
  /-- The judgment of the step's check: `FTotalTriple` (a body of `MM`), `CTriple` (of `CM`). -/
  triple : String := "FTotalTriple"
  /-- The contracts that the candidate uses. -/
  rules : Array Name := #[]
  /-- The generated definitions of the inner loops that the body runs, which the walks of its step
  apply (not part of the output: they are the inner loops' own). -/
  deps : String := ""
  /-- The library modules that the definitions name besides the ones every generated file
  imports (the array assertion `arr`, the sum `tsum`). -/
  imports : Array Name := #[]
  /-- The body runs an inner loop that takes steps (no credit mode: a run takes several steps). -/
  innerSteps : Bool := false

/-- An assertion over the resources `owned`: the facts `top`, and each written cell `k` at a
value `v` with the facts `cell k`. -/
def Cand.assn (c : Cand) (top : List String) (cell : Nat → List String) (owned := c.owned) :
    String := Id.run do
  let mut atoms := #[]
  if !top.isEmpty then atoms := atoms.push s!"⟪{" ∧\n      ".intercalate top}⟫"
  for o in owned do
    match o with
    | .read atom | .atom atom => atoms := atoms.push atom
    | .plain => atoms := atoms.push "plain"
    | .written k ty atom =>
      let fs := cell k
      atoms := atoms.push <| if fs.isEmpty then s!"(FAssn.ex fun v : {ty} => {atom})"
        else s!"(FAssn.ex fun v : {ty} => ⟪{" ∧ ".intercalate fs}⟫ ⋆ {atom})"
    | .arr p items tail =>
      let fs := items.toList.flatMap fun (k, ty?) => if ty?.isSome then cell k else []
      let list := String.join (items.toList.map fun (k, ty?) => if ty?.isSome then s!"w{k} :: " else s!"v{k} :: ")
      let atom := s!"up (arr {p} ({list}{tail}))"
      let exs := String.join (items.toList.filterMap fun (k, ty?) => ty?.map (s!"FAssn.ex fun w{k} : {·} => "))
      atoms := atoms.push <| if fs.isEmpty then s!"({exs}{atom})"
        else s!"({exs}⟪{" ∧ ".intercalate fs}⟫ ⋆ {atom})"
  return if atoms.isEmpty then "⟪True⟫" else " ⋆\n    ".intercalate atoms.toList

/-- The invariant's body with the kept facts (`keep`), each written by `fact`. -/
def Cand.body (c : Cand) (keep : Array Bool) (fact : Nat → String) : String :=
  let kept := (List.range c.facts.size).filter (keep[·]!)
  (if c.exs.isEmpty then "" else
    " ".intercalate (c.exs.toList.map fun (y, ty) => s!"FAssn.ex fun {y} : {ty} =>") ++ "\n    ") ++
  c.assn ((kept.filter (c.facts[·]!.cell?.isNone)).map fact)
    fun k => (kept.filter fun i => (c.facts[i]!.cell?.map (·.1)) == some k).map fact

/-- The exit post's body. -/
def Cand.post (c : Cand) : String :=
  c.assn c.postFacts.toList (owned := c.postOwned?.getD c.owned)
    fun k => (c.postCells.filter (·.1 == k)).toList.map (·.2)

/-- The family, as the file's record names it (a ghost measure is a list walk's). -/
def Cand.family (c : Cand) : String := if c.ghost then "list-walk" else "counted"

/-- The ghost measure's binder of the invariant, if it has one. -/
def Cand.nBinder (c : Cand) : String := if c.ghost then "(n : Nat) " else ""

/-- The definitions `name.inv` and `name.meas` (none with a ghost measure) with the kept facts,
each written by `fact`, each prefixed with `attr` (`Cand.output`: `@[fsym_inv]`). -/
def Cand.defs (c : Cand) (keep : Array Bool) (fact : Nat → String) (attr := "") : String :=
  s!"{c.doc}{attr}def {c.name}.inv {c.binders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) {c.nBinder}: \
    FAssn :=\n  {c.body keep fact}\n" ++
  if c.ghost then "" else s!"\n/-- The measure of `{c.name}`: the iterations left. -/\n\
    {attr}def {c.name}.meas {c.binders}{c.measEntry}(s : {c.loc}) : Nat :=\n  {c.meas}\n"

/-- The exit post `name.post`, prefixed with `attr`. -/
def Cand.postDef (c : Cand) (attr := "") : String :=
  s!"/-- The exit post of `{c.name}`: the loop exits with `r`, after all iterations. -/\n\
    {attr}def {c.name}.post {c.binders}(s0 : {c.loc}) {c.entry}(r : {c.exit} × {c.loc}) : \
    FAssn :=\n  {c.post}\n"

/-- The generated definitions with the kept facts and the exit post `name.post`, registered for
`fsym`'s loop rule (`@[fsym_inv]`). -/
def Cand.output (c : Cand) (keep : Array Bool) : String :=
  s!"{c.pre}{c.defs keep (c.facts[·]!.text) "@[fsym_inv] "}\n{c.postDef "@[fsym_inv] "}"

/-- The body takes a step (`Zig.tick`) in every run: its invariant holds the plain mode, and a
walk that counts its steps pays each run with a credit. -/
def Cand.ticks (c : Cand) : Bool := c.owned.any (· matches .plain)

/-- **The credit-mode candidate** of `c` (`@[fsym_inv]`'s second invariant of a loop body, for a
walk that pays its steps with credits; `name.credits.inv`, `name.credits.post`): derived from the
plain-mode one, for every family alike. The resources are `c`'s without the plain mode; the last
parameter `n` is the **exact count**, the body runs left before the last one, as a function of
the family's measure: a list walk's ghost measure is that count already (`zs.length = n`, the
nodes left), and a counted loop's measure `name.meas` (the iterations left) becomes the fact
`n = meas`. Neither credits nor receipts are named: the counted loop rule (`loop_exact`) adds
`credits (n + 1)` and returns `spent (n + 1)`, one per body run, the last being the exit's.
Its definitions as source text, given `c`'s kept facts `keep` (with the count's fact of a counted
loop, kept). -/
def Cand.creditOutput (c : Cand) (keep : Array Bool) : String :=
  let metered (owned : Array Owned) := owned.filter fun o => !(o matches .plain)
  let cc := { c with
    name := s!"{c.name}.credits"
    owned := metered c.owned
    postOwned? := c.postOwned?.map metered
    facts := if c.ghost then c.facts else c.facts.push { text := s!"n = {c.meas}" }
    ghost := true
    pre := ""
    doc := s!"/-- The credit-mode invariant of `{c.name}` (a walk that counts its steps, \
      `loop_exact`): `{c.name}.inv` without the plain mode, at the exact count `n` of the body \
      runs left before the last one.\n`s0` holds the locals at loop entry. -/\n" }
  cc.output (if c.ghost then keep else keep.push true)

/-- The check of the credit-mode definitions `out` (`Cand.creditOutput`, as they are written out):
the step of the counted loop rule (`FTotalTriple.loop_exact`, `CTriple.loop_exact`), walked by
`fsym` with its report on. From the invariant at the count `n` and one credit, a body run returns
the receipt and either repeats with the invariant at exactly `n - 1` or exits at `n = 0` with the
exit post (`floopExact`). -/
def Cand.creditCheck (ns : Name) (c : Cand) (out : String) : String :=
  let cn := s!"{c.name}.credits"
  let q (n : String) := s!"_root_.{ns}.{n}"
  let inv (s : String) := s!"{q cn}.inv {c.args}s0 {c.vargs}{s}"
  s!"{c.pre}{out}\n\
    set_option fsym.report true in\n\
    theorem {cn}.houdini {c.tbinders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) (n : Nat) :\n    \
      {c.triple} ({inv "s n"} ⋆ credits 1) (({c.run}).run s)\n      \
      (fun r => floopExact {q c.again} ({inv ""}) ({q cn}.post {c.args}s0 {c.vargs}) n r ⋆ \
      spent 1) := by\n  \
      unfold {q c.name} {q cn}.inv {q cn}.post\n  fsym{c.fsymArgs}\n"

/-- The check of the kept facts: each one a definition `name.candᵢ` (so that a residual goal
names it), the invariant over them, the measure, and the step triple of one iteration, walked by
`fsym` with its report on: from the invariant, a repeating iteration ends in it with a smaller
measure, an exiting one in it (in the counted family an exit changes no local and no memory).
`final`: the check of the output instead (`Cand.output`, the kept facts written out), where an
exiting iteration ends in the exit post `name.post`, as the loop rule's step requires. -/
def Cand.check (ns : Name) (c : Cand) (keep : Array Bool) (final := false) : String := Id.run do
  let mut defs := ""
  -- (a list walk's facts are over its ghost lists and measure too)
  let exB := String.join (c.exs.toList.map fun (y, ty) => s!"({y} : {ty}) ") ++ c.nBinder
  let exA := String.join (c.exs.toList.map (s!" {·.1}")) ++ if c.ghost then " n" else ""
  for h : i in [0:c.facts.size] do
    if !keep[i]! then continue
    let v := match c.facts[i].cell? with | some (_, ty) => s!"({c.facts[i].var} : {ty}) " | none => ""
    defs := defs ++ s!"def {c.name}.cand{i} {c.binders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) {exB}{v}: Prop :=\n  \
      {c.facts[i].text}\n\n"
  -- The uses are qualified from the root: under the parameters' binders, a parameter named like
  -- the body's first component (`p0.loop5 (p0 : …)`) would capture a relative name.
  let q (n : String) := s!"_root_.{ns}.{n}"
  let use (i : Nat) := s!"{q c.name}.cand{i} {c.args}s0 {c.vargs}s{exA}" ++ if c.facts[i]!.cell?.isSome then s!" {c.facts[i]!.var}" else ""
  let inv (s : String) := s!"{q c.name}.inv {c.args}s0 {c.vargs}{s}"
  let meas (s : String) := s!"{q c.name}.meas {c.args}{c.measArgs}{s}"
  -- A list walk (ghost measure): the step of `loop_ghost_ex`, which ends in the exit post at an
  -- exit, also while pruning (its exit moves to the post's lists).
  if c.ghost then
    let text := if final then c.output keep else c.pre ++ defs ++ c.defs keep use ++ "\n" ++ c.postDef
    return s!"{text}\n\
      set_option fsym.report true in\n\
      theorem {c.name}.houdini {c.tbinders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) (n : Nat) :\n    \
        {c.triple} ({inv "s n"}) (({c.run}).run s)\n      \
        (floopNext {q c.again} ({inv ""}) ({q c.name}.post {c.args}s0 {c.vargs}) n) := by\n  \
        unfold {q c.name} {q c.name}.inv {q c.name}.post\n  fsym{c.fsymArgs}\n"
  -- the definitions, the assertion at the exit and the extra definition to unfold
  let (text, atExit, unfoldPost) := if final then
      (c.output keep, s!"{q c.name}.post {c.args}s0 {c.vargs}r", s!" {q c.name}.post")
    else (defs ++ c.defs keep use, inv "r.2", "")
  return s!"{text}\n\
    set_option fsym.report true in\n\
    theorem {c.name}.houdini {c.tbinders}(s0 : {c.loc}) {c.entry}(s : {c.loc}) :\n    \
      {c.triple} ({inv "s"}) (({c.run}).run s)\n      \
      (fun r => if {q c.again} r.1 then ⟪{meas "r.2"} < {meas "s"}⟫ ⋆ {inv "r.2"}\n        \
        else {atExit}) := by\n  \
      unfold {q c.name} {q c.name}.inv {q c.name}.meas{unfoldPost}\n  fsym\n"

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
trusted: the generated definitions are checked by the proofs that use them. `final`
(`Cand.check`'s): any residual is an error. `credits?`: the credit-mode definitions, whose step
is walked instead (`Cand.creditCheck`), where any residual is an error too. -/
def walk (ns : Name) (c : Cand) (keep : Array Bool) (final := false)
    (credits? : Option String := none) : MetaM (Array (Nat × String)) := do
  let check := match credits? with
    | some out => c.creditCheck ns out
    | none => c.check ns keep final
  let text := s!"namespace {ns}\n{opens}\n\
    set_option linter.unusedVariables false\n\n{c.deps}{check}\nend {ns}\n"
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
  let field (j : Json) (k : String) := (j.getObjValAs? String k).toOption.getD ""
  -- (the output has no candidates: a residual there is fatal, and this says why)
  if credits?.isSome then
    if let some res := residuals[0]? then
      throwError "the step does not keep the count (each body run one step, the measure lowered \
        by exactly one, zero at the exit): `{field (res.getObjValD "goal") "text"}` \
        ({field (res.getObjValD "origin") "reason"})"
    return #[]
  if final then
    if let some res := residuals[0]? then
      throwError "the kept facts do not establish the exit post `{c.name}.post`: \
        `{field (res.getObjValD "goal") "text"}`"
  let pre := s!"{ns}.{c.name}.cand"
  let mut drop := #[]
  for res in residuals do
    let goal := res.getObjValD "goal"
    let origin := res.getObjValD "origin"
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

/-- The candidate invariant and exit post of the list walk `w`, the loop `name` (exit test
`again`, the body's parameters `binders`/`args`, its locals `loc`, its exit type `exit`), over the
library list family `listSeg` (`ZigLean/Sep/Full/ListSeg.lean`) with a ghost measure `n`, the
nodes left (`loop_ghost_ex`). The node layout `name.node` is read off the body: `next` at its
offset, the item's field if the body reads one (the item then is that field's value and the rest
of a node `X p`), else an abstract rest `D p v` of an item type `V` (the walk holds for every
node that has the `next` field). The lists are `xs = ys ++ zs` for a visit (the visited segment
`ys` from the cursor's entry value, the nodes left `zs` at the cursor) or `xs = ys.reverse ++ zs`
for a reversal (the prefix `ys` reversed at the prefix's local); each accumulator is its entry
value plus the sum of the visited items (or `k` per node), with the no-overflow fact over all of
`xs` (an entry obligation, as in the counted family); the other locals keep their entry values.
These facts are Houdini's candidates; the walk of the step with the exit post decides. -/
def listCand (ns : Name) (name again binders tbinders args run triple loc exit : String)
    (params : Array (String × String)) (w : Walk) : MetaM Cand := do
  let ptr (k : Nat) := if k == 0 then "p" else s!"(p.add {k})"
  let (nextOff, nextAl) := w.next
  let cur := w.cursor
  -- The node layout and the item type. Without a call they are read off the body's accesses;
  -- with one, off its contract: the node is the contract's precondition without its frame, and a
  -- node passed is the contract's postcondition without it (`name.done`). `layout`: the
  -- parameters of the definitions for them, `hyps`: those of the check besides.
  let (T, layout, layoutArgs, hyps, N, M, frame, pre) ← match w.call? with
    | none => do
      let (T, layout, layoutArgs, rest) ← match w.item? with
        | some (k, ty, al) => do
          let t := toString (← ppExpr ty)
          pure (t, "(X : Zig.Ptr → FAssn) ", "X", s!"up (pts {ptr k} {al} v) ⋆ X p")
        | none => pure ("V", "(V : Type) (D : Zig.Ptr → V → FAssn) ", "V D", "D p v")
      -- (qualified: a parameter named like the body's first component would capture it)
      let N := s!"({ns}.{name}.node {layoutArgs})"
      let pre := s!"/-- The node layout of `{name}`: `next` at offset {nextOff}{if w.item?.isSome then ", the item" else ""}, \
        the rest. -/\nabbrev {name}.node {layout}(p : Zig.Ptr) (v : {T}) (q : Option Zig.Ptr) : FAssn :=\n  \
        up (pts {ptr nextOff} {nextAl} q) ⋆ {rest}\n\n"
      pure (T, layout, layoutArgs, "", N, N, (#[] : Array String), pre)
    | some k => do
      -- the node's variables: the pointer, `next`'s value and the item (the other value field)
      let some (_, _, q, qT) := k.fields.find? (·.1 == nextOff) | throwError "no next field"
      let (v, T) := match k.fields.find? (·.1 != nextOff) with
        | some (_, _, v, T) => (v, T)
        | none => ("v", "Unit")
      let bound := ["s", "s0", "r", "n", "xs", "ys", "zs", "plain", "listSeg", "listSegRev", "FAssn", "Zig"]
      let taken := params.map (·.1) ++ k.vars.map (·.1)
      for x in #[k.ptr, q, v] ++ k.vars.map (·.1) do
        if bound.contains x then throwError "a variable of the contract `{k.rule}` named {x}"
      for x in #[k.ptr, q, v] do
        if taken.contains x then throwError "the contract `{k.rule}` names a variable and the node's {x}"
      if k.ptr == q || k.ptr == v || q == v then throwError "the contract `{k.rule}` names two of the node's variables {v}"
      if let some (x, _, _) := k.vars.find? fun (x, _, _) => params.any (·.1 == x) then
        throwError "the contract `{k.rule}` and the loop both name {x}"
      -- a definition's parameters: the loop's parameters and the contract's variables it names
      let all := params ++ k.vars.filterMap fun (x, ty, hyp) => if hyp then none else some (x, ty)
      let pick (uses : Array String) : String × String :=
        let ps := all.filter (uses.contains ·.1)
        (String.join (ps.toList.map fun (x, ty) => s!"({x} : {ty}) "), " ".intercalate (ps.toList.map (·.1)))
      let join (atoms : Array String) := if atoms.isEmpty then "FAssn.emp" else " ⋆ ".intercalate atoms.toList
      let nodeB := s!"({k.ptr} : Zig.Ptr) ({v} : {T}) ({q} : {qT}) : FAssn"
      let (nb, na) := pick k.nodeUses
      let (db, da) := pick k.afterUses
      let app (f a : String) := if a.isEmpty then s!"{ns}.{name}.{f}" else s!"({ns}.{name}.{f} {a})"
      let pre := s!"/-- The node layout of `{name}`: a node as the contract `{k.rule}` of the call that takes \
        it owns it. -/\nabbrev {name}.node {nb}{nodeB} :=\n  {join k.nodeAtoms}\n\n\
        /-- A node that `{name}` has passed: what the contract `{k.rule}` leaves of it. -/\n\
        abbrev {name}.done {db}{nodeB} :=\n  {join k.after}\n\n"
      -- the invariant's parameters: every variable that the node, the frame or a node passed
      -- names; one that only a node passed names is not determined at the loop's entry
      let known := params.map (·.1) ++ k.nodeUses ++ k.frameUses
      if let some x := k.afterUses.find? (!known.contains ·) then
        throwError "the contract `{k.rule}` leaves `{x}` in a node, which its precondition does not name"
      let used := k.vars.filter fun (x, _, hyp) => !hyp && known.contains x
      let rest := k.vars.filter fun (x, _, hyp) => hyp || !known.contains x
      let bindersOf (vs : Array (String × String × Bool)) :=
        String.join (vs.toList.map fun (x, ty, _) => s!"({x} : {ty}) ")
      let frame := k.frame.map paren
      pure (T, bindersOf used, " ".intercalate (used.toList.map (·.1)), bindersOf rest, app "node" na,
        app "done" da, frame, pre)
  let LT := s!"List {paren T}"
  -- The nodes passed. A visit's are a segment to the cursor, which a node joins at its end (the
  -- update `listSeg_snoc_upd`: the node's atoms give the update the item and the next pointer).
  -- What a call leaves of a node need not name either, so the nodes that a call has taken are
  -- the segment told from its end (`listSegRev`, the last node passed first): a node joins it
  -- by the constructor, as a reversal's prefix, and the list's equation gives its item.
  let (rel, prefixAt, postList) := match w.rev?, w.call? with
    | some r, _ => ("ys.reverse ++ zs", s!"listSeg {N} s.{r} none ys", s!"listSeg {N} r.2.{r} none xs.reverse")
    | none, some _ => ("ys.reverse ++ zs", s!"listSegRev {M} s0.{cur} s.{cur} ys",
        s!"listSegRev {M} s0.{cur} none xs.reverse")
    | none, none => ("ys ++ zs", s!"listSeg {N} s0.{cur} s.{cur} ys", s!"listSeg {N} s0.{cur} none xs")
  -- an accumulator's increment over the items `l`
  let inc (a : Acc) (l : String) := match a with
    | .item => s!"({l}.map BitVec.toNat).sum"
    | .count 1 => s!"{l}.length"
    | .count k => s!"{k} * {l}.length"
  let mut facts : Array Fact := #[{ text := s!"xs = {rel}" }, { text := "zs.length = n" }]
  facts := facts ++ w.pinned.map fun f => { text := s!"s.{f} = s0.{f}" }
  let mut post := #[match w.exits with
    | some #[l] => s!"r.1 = {relName ns l}"
    | some ls => s!"({" ∨ ".intercalate (ls.map (s!"r.1 = {relName ns ·}")).toList})"
    | none => s!"{again} r.1 = false"] ++ w.pinned.map fun f => s!"r.2.{f} = s0.{f}"
  for (a, width, acc) in w.accs do
    facts := facts ++ #[{ text := s!"s.{a}.toNat = s0.{a}.toNat + {inc acc "ys"}" },
      { text := s!"s0.{a}.toNat + {inc acc "xs"} < 2 ^ {width}" }]
    post := post.push s!"r.2.{a}.toNat = s0.{a}.toNat + {inc acc "xs"}"
  -- (the frame of a call's contract stays with the loop, after the lists)
  let rest := frame.map Owned.atom ++ if w.plain then #[Owned.plain] else #[]
  let kind := match w.rev?, w.call? with
    | some _, _ => "reverses the list"
    | _, some k => s!"hands to the call of `{k.rule}` each node of the list"
    | _, _ => "visits the list"
  let rules := match w.call? with
    | some k => #[k.use]
    | none => #[]
  let upds := (if w.rev?.isSome || w.call?.isSome then #[] else #["Zig.Full.listSeg_snoc_upd"]) ++ rules
  return {
    name, again, binders := binders ++ layout ++ s!"(xs : {LT}) ",
    tbinders := tbinders ++ layout ++ hyps ++ s!"(xs : {LT}) ", args := args ++ layoutArgs ++ " xs ",
    run, triple, rules := w.call?.toArray.map (·.rule),
    loc, entry := "", vargs := "", measEntry := "", measArgs := "", facts,
    owned := #[.atom prefixAt, .atom s!"listSeg {N} s.{cur} none zs"] ++ rest,
    meas := "", exit, postFacts := post, postCells := #[], ghost := true,
    exs := #[("ys", LT), ("zs", LT)], postOwned? := some (#[.atom postList] ++ rest), pre,
    fsymArgs := if upds.isEmpty then "" else s!" [{", ".intercalate upds.toList}]",
    doc := s!"/-- The invariant of `{name}`, a list walk that {kind} `xs` at `{cur}` \
      (`{name}.node`): `zs` are the `n` nodes left.\n`s0` holds the locals at loop entry. -/\n" }

/-- The candidate invariant, measure and exit post of the loop `body` (the definition run by
`Zig.loop`) with exit test `again`, with the contracts `contracts` (the function, the rule) for
its calls; throws why there are none. -/
def candLoop (ns body again : Name) (contracts : Array (Name × Name) := #[]) : MetaM Cand := do
    let some (.defnInfo d) := (← getEnv).find? body | throwError "not a definition"
    lambdaTelescope (nameInsts 0 d.value) fun xs code => do
      let ty ← inferType code
      -- a body of `MM σ ε` (checked in `FTotalTriple`) or of `CM Tgt σ ε` (in `CTriple`)
      let (σ, ε, triple) ←
        if ty.isAppOfArity `Zig.MM 2 then pure (ty.getArg! 0, ty.getArg! 1, "FTotalTriple")
        else if ty.isAppOfArity `Zig.CM 3 then pure (ty.getArg! 1, ty.getArg! 2, "CTriple")
        else throwError "not a loop body of `Zig.MM` or `Zig.CM`"
      let some structName := σ.constName? | throwError "locals that are not a structure"
      let exit ← match ε.constName? with
        | some n => pure (relName ns n)
        | none => toString <$> ppExpr ε
      unless isStructure (← getEnv) structName do throwError "locals that are not a structure"
      for x in xs do
        let n := (← x.fvarId!.getDecl).userName
        if n.hasMacroScopes || reserved n then throwError "a parameter named {n}"
      let fields := getStructureFields (← getEnv) structName
      let ctx : Ctx := { structName, fields, params := xs.map (·.fvarId!), contracts,
                         arrays := ← arraysOf xs code }
      let st : St := { locals := fields.map .local }
      let paths ← exec ctx st code
      let isAgain (e : Expr) : MetaM Bool := do
        return (← whnf (mkApp (.const again []) e)).isConstOf ``Bool.true
      -- The text.
      -- (`binders`: of the definitions, all explicit, as `@[fsym_inv]` wants them; `tbinders`: of
      -- the check's theorem, where an instance parameter is an instance)
      let mut binders := ""
      let mut tbinders := ""
      let mut args := ""
      let mut params := #[]
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let ty ← ppLine decl.type
        binders := binders ++ s!"({decl.userName} : {ty}) "
        tbinders := tbinders ++ (if decl.binderInfo.isInstImplicit then s!"[{decl.userName} : {ty}] "
          else s!"({decl.userName} : {ty}) ")
        args := args ++ s!"{decl.userName} "
        params := params.push (decl.userName.toString, ty)
      -- (qualified from the root, as in `Cand.check`; all of the parameters given)
      let run := s!"@_root_.{body} {args}"
      let loc := relName ns structName
      -- a loop that tests an optional pointer is a list walk, any other a counted loop
      if paths.any (·.st.cond.any (· matches (.isSome _, _))) then
        let fieldTy (f : Name) : MetaM Expr := withLocalDeclD `s (.const structName []) fun s =>
          inferType (mkApp (.const (structName ++ f) []) s)
        let w ← listWalk ctx isAgain fieldTy paths
        return ← listCand ns (relName ns body) (relName ns again) binders tbinders args run triple loc
          exit params w
      let c ← counted ctx isAgain paths
      let pname (i : Nat) : MetaM String := return (← xs[i]!.fvarId!.getDecl).userName.toString
      let x := c.counter
      -- The cells: each one the body accesses, and each item of an array up to the last one it
      -- accesses (an item it does not access is one it only reads).
      let mut cells := c.cells
      for (j, sz) in ctx.arrays do
        let items := cells.filter (·.1.loc.param == j)
        let some (first, _) := items[0]? | continue
        unless items.all (fun (cell, _) => cell.ty == first.ty && cell.align == first.align) do
          throwError "an array whose items are accessed at two types or alignments"
        unless first.width == 8 * sz do throwError "an array whose item size is not its word's"
        let last := items.foldl (fun m (cell, _) => max m (cell.loc.item.getD 0)) 0
        for i in [0:last + 1] do
          unless items.any (·.1.loc.item == some i) do
            let loc : Loc := { param := j, item := some i }
            cells := cells.push ({ first with loc, val := .cell loc, stored := false }, {})
      -- Each cell's type, and its entry value `vₖ` as a binder (the measure binds the bound's);
      -- then the rest `tⱼ` of each array `j` after the items the body reaches.
      let tys ← cells.mapM fun (cell, _) => return toString (← ppExpr cell.ty)
      let binder (k : Nat) := s!"(v{k} : {tys[k]!}) "
      let arrs := (ctx.arrays.filterMap fun (j, _) => (cells.findIdx? (·.1.loc.param == j)).map (j, ·))
      let entry := String.join ((List.range tys.size).map binder) ++
        String.join (arrs.toList.map fun (j, k) => s!"(t{j} : List {paren tys[k]!}) ")
      let vargs := String.join ((List.range tys.size).map (s!"v{·} ")) ++
        String.join (arrs.toList.map (s!"t{·.1} "))
      let boundCell? := cells.findIdx? fun (cell, _) => c.bound == .cell cell.loc
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
        | .cell l => do
          let some k := boundCell? | throwError "a bound cell"
          pure (s!"v{k}.toNat", cellName (← pname l.param) l)
        | _ => throwError "a bound"
      -- the bound at the locals `sv` (`bound` is at `s`)
      let boundAt (sv : String) := match c.bound with
        | .local y => s!"{sv}.{y}.toNat"
        | _ => bound
      -- `X` the counter, `X0` its entry value: the loop counts `total` iterations in all, and its
      -- measure is `left`.
      let X := s!"s.{x}.toNat"
      let X0 := s!"s0.{x}.toNat"
      -- the other locals at their entry values, at the locals `sv`
      -- (not the scratch locals: the body sets them before it reads them)
      let pinned (sv : String) := (fields.filter fun f => f != x && !c.scratch.contains f).map
        fun f => s!"{sv}.{f} = s0.{f}"
      let mut facts : Array Fact := (pinned "s").map ({ text := · })
      -- The counter runs from `X0` to the value it exits at: the bound, or one past it for
      -- `<=`/`>=` (`one`), where the counter's last step must not wrap (`noWrap`; a literal bound
      -- that makes it false is outside the family). Which side of `X0` it stays on is left to
      -- Houdini: both are candidates (true at entry), and the step keeps one.
      let one := if c.incl then " + 1" else ""
      -- the iterations in all, with the bound `b`
      let totalOf (b : String) := if c.down then s!"{X0}{one} - {b}" else s!"{b}{one} - {X0}"
      let total := totalOf bound
      let (left, toExit) := if c.down then (s!"{X}{one} - {bound}", s!"{bound} ≤ {X}{one}")
        else (s!"{bound}{one} - {X}", s!"{X} ≤ {bound}{one}")
      facts := facts ++ #[{ text := s!"{X0} ≤ {X}" }, { text := s!"{X} ≤ {X0}" }, { text := toExit }]
      -- `total` at the exit's locals `r.2`
      let totalPost := totalOf (boundAt "r.2")
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
      -- The exit post: the exit's label, the other locals at their entry values, the counter at
      -- its exit value and each written cell after all `total` iterations.
      let XR := s!"r.2.{x}.toNat"
      let label := match c.exits with
        | some #[l] => s!"r.1 = {relName ns l}"
        | some ls => s!"({" ∨ ".intercalate (ls.map (s!"r.1 = {relName ns ·}")).toList})"
        | none => s!"{relName ns again} r.1 = false"
      let post := #[label] ++ pinned "r.2" ++
        #[if c.down then s!"{XR}{one} = {boundAt "r.2"}" else s!"{XR} = {boundAt "r.2"}{one}"]
      let mut owned := #[]
      let mut postCells : Array (Nat × String) := #[]
      let mut doc := #[]
      -- a value over the counter's value `u` at an iteration's start, as `Nat` text
      let leaf (s : Sym) : MetaM String := match s with
        | .local f => return if f == x then "u" else s!"s0.{f}.toNat"
        | .param i => return s!"{← pname i}.toNat"
        | .slen i => return s!"{← pname i}.len.toNat"
        | .cell l => match cells.findIdx? (·.1.loc == l) with
          | some k => return s!"v{k}.toNat"
          | none => throwError "an increment that reads a cell"
        | _ => throwError "an increment that is not a value of the counter"
      for h : k in [0:cells.size] do
        let (cell, inc) := cells[k]
        let p ← pname cell.loc.param
        let ty := tys[k]!
        let name := cellName p cell.loc
        -- an array: one resource, at its first cell, with its items in order
        if cell.loc.item.isSome && !(cells.extract 0 k).any (·.1.loc.param == cell.loc.param) then
          let items := ((List.range cells.size).filterMap fun k' =>
            let c' := cells[k']!.1
            if c'.loc.param == cell.loc.param then some (c'.loc.item.getD 0, k', c'.stored) else none).toArray
          let items := items.qsort (·.1 < ·.1)
          owned := owned.push (.arr p (items.map fun (_, k', w) => (k', if w then some tys[k']! else none))
            s!"t{cell.loc.param}")
        if !cell.stored then
          if cell.loc.item.isNone then owned := owned.push (.read s!"up (pts {p} {cell.align} v{k})")
          doc := doc.push s!"\n`v{k}` is `{name}`, which the loop only reads."
          continue
        -- (the existential's variable of a written cell: `v` for `*p`, `wₖ` for an item)
        let var := if cell.loc.item.isSome then s!"w{k}" else "v"
        if inc.terms.isEmpty then
          let n := inc.k
          facts := facts.push { text := s!"v{k}.toNat + {scaled n total} < 2 ^ {cell.width}" }
          -- The cell's value after the iterations so far, counted up or down from `X0`: both are
          -- candidates (true at entry), Houdini keeps the one of the counter's direction (a cell
          -- that goes up by 0 keeps both, so it gets the one of the reading's direction only).
          let up := s!"{X} - {X0}"
          let down := s!"{X0} - {X}"
          for d in (if n != 0 then #[up, down] else if c.down then #[down] else #[up]) do
            facts := facts.push { text := s!"{var}.toNat = v{k}.toNat + {scaled n d}", cell? := some (k, ty), var }
          postCells := postCells.push (k, s!"{var}.toNat = v{k}.toNat + {scaled n totalPost}")
          doc := doc.push s!"\n`v{k}` is `{name}` there, which goes up by {n} per iteration."
        else
          -- An increment `g u` over the counter's value `u` (a loop that counts up, `counted`):
          -- with the library sum `tsum` (`ZigLean/Sep/Full/TSum.lean`), the increments still to
          -- come are `tsum e g - tsum x g` (`e` the counter's exit value), and the cell plus
          -- them stays at its entry value plus all of them: a linear fact for `fsym_arith`.
          let ts ← inc.terms.mapM (·.natText leaf)
          let g := s!"(fun u => {" + ".intercalate (ts.toList ++ if inc.k == 0 then [] else [toString inc.k])})"
          let rest (e y : String) := s!"(tsum {paren e} {g} - tsum {paren y} {g})"
          let e := s!"{bound}{one}"
          let ePost := s!"{boundAt "r.2"}{one}"
          facts := facts.push { text := s!"v{k}.toNat + {rest e X0} < 2 ^ {cell.width}" }
          facts := facts.push { text := s!"{var}.toNat + {rest e X} = v{k}.toNat + {rest e X0}",
                                cell? := some (k, ty), var }
          postCells := postCells.push (k, s!"{var}.toNat = v{k}.toNat + {rest ePost X0}")
          doc := doc.push s!"\n`v{k}` is `{name}` there, which goes up by `{g} {x}` per iteration."
        if cell.loc.item.isNone then owned := owned.push (.written k ty s!"up (pts {p} {cell.align} {var})")
      if c.plain then owned := owned.push .plain
      for f in c.scratch do
        doc := doc.push s!"\n`{f}` is not stated: the body sets it before it reads it."
      let name := relName ns body
      return {
        name, again := relName ns again, binders, tbinders, args, run, triple, loc, entry,
        vargs, measEntry, measArgs,
        facts, owned, meas := left, exit, postFacts := post, postCells, innerSteps := c.innerSteps,
        imports := (if arrs.isEmpty then #[] else #[`ZigLean.Sep.Full.Arr]) ++
          if cells.any (fun (cell, inc) => cell.stored && !inc.terms.isEmpty) then #[`ZigLean.Sep.Full.TSum] else #[],
        doc := s!"/-- The invariant of `{name}`, a counted loop: `{x}` goes {if c.down then "down" else "up"} \
          by 1 while `{x} {c.rel.text} {boundName}`.\n`s0` holds the locals at loop entry.{String.join doc.toList} -/\n" }

/-- The credit-mode definitions of the loop of `c` with the kept facts `keep` (`Cand.creditOutput`:
the text after the plain-mode definitions, and the record's entry `{"count": …}`), if the walk of
the counted rule's step proves them (`walk … (credits? := …)`); else no definition and the entry
`{"none": why}`. A proof that counts the loop's steps then does not build: `fsym` does not take
the plain-mode invariant for it (fail closed). -/
def creditOf (ns : Name) (c : Cand) (keep : Array Bool) : MetaM (String × Json) := do
  unless c.ticks do
    return ("", Json.mkObj [("none", "the body takes no step (`Zig.tick`): there is nothing to count")])
  if c.innerSteps then
    return ("", Json.mkObj [("none", "the body runs an inner loop that takes steps: a body run takes \
      more than the one step that the counted loop rule pays with one credit")])
  withCurrHeartbeats <| tryCatchRuntimeEx
    (do
      let out := c.creditOutput keep
      discard <| walk ns c keep (credits? := some out)
      let count := if c.ghost then "zs.length" else c.meas
      return (s!"\n{out}", Json.mkObj [("count", count)]))
    fun ex => return ("", Json.mkObj [("none", ← ex.toMessageData.toString)])

/-- A loop's generated definitions (plain and credit mode) as text, its family, the pruning
decisions and the credit mode's record entry, and the library modules they name. -/
structure LoopOut where
  family : String
  text : String
  pruned : Array Json
  credits : Json
  imports : Array Name

/-- The invariant `body.inv`, measure `body.meas` and exit post `body.post` of the loop `body`
with exit test `again` (`candLoop`, pruned by `houdini`, the output walked once more with its exit
post) as source text with the pruning decisions, or why there are none; then its credit-mode
definitions `body.credits.inv` and `body.credits.post` with the record's entry for them
(`creditOf`). Each loop has its own heartbeat budget: the walks of the loops before it do not
count. `deps`: the generated definitions of the inner loops that the body runs (`Cand.deps`). -/
def genLoop (ns body again : Name) (contracts : Array (Name × Name) := #[]) (deps := "") :
    MetaM (Except String LoopOut) :=
  -- (a heartbeat or recursion limit, too, only costs this loop its invariant)
  withCurrHeartbeats <| tryCatchRuntimeEx
    (do
      let c := { ← candLoop ns body again contracts with deps }
      -- a file generated with contracts holds the loops that call by them; the others are in
      -- the module's file generated without contracts
      if !contracts.isEmpty && c.rules.isEmpty then
        throwError "no call by one of the given contracts (a loop of the file generated without them)"
      let (keep, pruned) ← houdini ns c
      -- the output itself, with its exit post: a walk with no residual (else no invariant)
      discard <| walk ns c keep (final := true)
      -- the second invariant of the body, for the credit mode
      let (creditText, credits) ← creditOf ns c keep
      return .ok { family := c.family, text := c.output keep ++ creditText, pruned, credits,
                   imports := c.imports })
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
invariant (`none`), and the function that runs the loop with its fingerprint (`function`,
`fingerprint`, from `fingerprints`: `[definition, fingerprint]` of the translated functions,
`docs/stable-generation.md`), so that a stale file says which loops' functions changed. The
current environment must import `ZigLean.Sep.Full.AutoAll`: the pruning walks run `fsym`. -/
def generate (module ns : Name) (generator inputs : Json) (specs contracts : Array Name := #[])
    (fingerprints : Array (String × String)) :
    MetaM (String × Array (String × String)) := do
  let rules ← contracts.mapM fun r => return (← contractOf r, r)
  let all ← loopsOf module ns
  -- The inner loops that each body runs. A loop is generated after them: the walks of its step
  -- apply their generated definitions (`Cand.deps`), and without them it gets none.
  let inner ← all.mapM fun (b, _) => do
    let some (.defnInfo d) := (← getEnv).find? b | return #[]
    return (← loopApps d.value).map (·.1)
  let mut results : Std.HashMap Name (Except String LoopOut) := {}
  let mut pending := (List.range all.size).toArray
  while !pending.isEmpty do
    let (ready, wait) := pending.partition fun i => inner[i]!.all results.contains
    if ready.isEmpty then throwError "loops that run each other: {pending.map fun i => all[i]!.1}"
    for i in ready do
      let (b, a) := all[i]!
      let deps := inner[i]!.filterMap fun ib => match (results[ib]? : Option (Except String LoopOut)) with
        | some (Except.ok o) => some o.text
        | _ => none
      let r ← if deps.size < inner[i]!.size then
          pure (.error s!"a nested loop without generated definitions: \
            {(inner[i]!.filter fun ib => !(results[ib]?.any (· matches .ok _))).map (relName ns ·)}")
        else genLoop ns b a rules (String.join deps.toList)
      results := results.insert b r
    pending := wait
  -- (in the order of `loopsOf`; `libs`: the library modules the definitions name besides the
  -- ones every file imports)
  let mut libs : Array Name := #[]
  let mut loops := #[]
  let mut defs := #[]
  let mut skipped := #[]
  for (b, _) in all do
    let loop := relName ns b
    -- the function that runs the loop (the longest translated definition that names it, `F` of
    -- `F.loopN`) and its semantic fingerprint
    let owners := fingerprints.filter fun (d, _) => loop.startsWith (d ++ ".")
    let some (d, fp) := owners.foldl (init := (none : Option (String × String)))
        fun best (d, fp) => if best.all (·.1.length < d.length) then some (d, fp) else best
      | throwError "no fingerprint of the function that runs the loop {loop}"
    let head : List (String × Json) :=
      [("loop", Json.str loop), ("function", Json.str d), ("fingerprint", Json.str fp)]
    match results[b]! with
    | .ok o =>
      loops := loops.push (Json.mkObj (head ++ [("family", Json.str o.family),
        ("pruned", Json.arr o.pruned), ("credits", o.credits)]))
      defs := defs.push o.text
      for m in o.imports do
        unless libs.contains m do libs := libs.push m
    | .error why =>
      loops := loops.push (Json.mkObj (head ++ [("none", Json.str why)]))
      skipped := skipped.push (loop, why)
  let body := s!"import {module}\n\
    {String.join (specs.toList.map (s!"import {·}\n"))}\
    {String.join ((libs.qsort (·.toString < ·.toString)).toList.map (s!"import {·}\n"))}\
    import ZigLean.Sep.Full.Ghost\n\
    import ZigLean.Sep.Full.AutoAttr\n\
    import ZigLean.Sep.Full.ListSeg\n\n\
    /-!\n\
    Generated by `air2lean-invgen` (`docs/invariant-synthesis.md`) from `{module}`: do not edit.\n\
    Untrusted: the proofs that use these definitions are checked by the kernel.\n\
    -/\n\n\
    set_option linter.unusedVariables false\n\n\
    namespace {ns}\n\
    {opens}\n\n\
    {"\n".intercalate defs.toList}\n\
    end {ns}\n"
  -- (a file generated with contracts: the modules that state them, and the rules)
  let extra : List (String × Json) := if contracts.isEmpty then [] else [
    ("specs", Json.arr (specs.map (Json.str ·.toString))),
    ("contracts", Json.arr (contracts.map (Json.str ·.toString)))]
  let fields : List (String × Json) := [
    ("version", (3 : Nat)), ("generator", generator), ("inputs", inputs),
    ("module", module.toString), ("namespace", ns.toString), ("loops", Json.arr loops),
    ("output", Air2Lean.Revision.sha256 body.toUTF8)]
  let record := Json.mkObj (fields ++ extra)
  return (s!"-- air2lean-invgen: {record.compress}\n" ++ body, skipped)

end Air2Lean.InvGen
