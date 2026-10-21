import ZigLean.Sep.Full.Auto

/-!
# `fsym [u]`: the caller's updates at returns (`docs/proof-automation.md` §Updates)

A module states the step its invariant takes at a return as an update `EUpd P Q` over its own
variables (the arena's `free_last_upd`, `free_other_upd`: `tests/roadmap/alloc-arena`); `fsym`
applies it where the planner alone does not reach the postcondition: `P` is planned out of the
state, `Q` into the postcondition, the update's hypotheses are side goals. The variables may be
bundled in a structure (`v : FV`, here `W`): the planner unifies its fields. Facts of a user
structure (`Small x`) give their fields, and two owned regions of one block have its labels
(`facts_regions_labels`).
-/

namespace SepAuto.Updates

open Zig Zig.Full Zig.Full.FAssn

/-- The variables of a two-word state, bundled. -/
structure W where
  p : Ptr
  v : BitVec 64
  q : Ptr

/-- The state over its variables. -/
def W.L (w : W) : FAssn := apts w.p w.v ⋆ apts w.q 0#64

/-- A published state: a raw predicate, which the planner does not unfold. -/
def Pub (p q : Ptr) : FAssn := fun r => (FAssn.ex fun v => apts p v ⋆ apts q 0#64) r

/-- The module's update: a small value publishes the state. -/
theorem pub_upd {w : W} (_h : w.v.toNat < 10) : EUpd w.L (Pub w.p w.q) :=
  EUpd.of_imp fun _ hr => ⟨w.v, hr⟩

/-- A fact of a user structure. -/
structure Small (x : BitVec 64) : Prop where
  lt : x.toNat < 5

/-- The return is closed by the update (its variables from the state, its hypothesis by
arithmetic from the fields of `Small x`). -/
theorem ret_by_update (p q : Ptr) (x : BitVec 64) :
    FTotalTriple (⟪Small x⟫ ⋆ apts q 0#64 ⋆ apts p x) (pure ()) (fun _ => Pub p q) := by
  fsym [pub_upd]

set_option linter.unusedVariables false in
/-- Rejected: the update's hypothesis does not hold. -/
example (p q : Ptr) (x : BitVec 64) (hx : x.toNat = 12) : True := by
  fail_if_success
    have : FTotalTriple (apts q 0#64 ⋆ apts p x) (pure ()) (fun _ => Pub p q) := by
      fsym [pub_upd]
  trivial

/-- Two owned nonempty regions of one block: the same address and kind labels. -/
theorem region_labels (p q : Ptr) (b : BlockId) (A S A' S' : Nat) (K K' : BlockKind) (bs cs : Array Byte)
    (hp : p.block = some b) (hq : q.block = some b) (hb : 0 < bs.size) (hc : 0 < cs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs)) (pure ())
      (fun _ => ⟪A = A' ∧ K.norm = K'.norm⟫ ⋆ up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 cs)) := by
  fsym

/-! ## The caller's terms across substitutions -/

/-- A command over a typed value (a stand-in that keeps it). -/
@[irreducible] def keep (_p : Ptr) : MemM Unit := pure ()

theorem keep_spec (q : Ptr) (v : BitVec 64) (_hv : v.toNat < 10) :
    FTotalTriple (up (pts q 8 v)) (keep q) (fun _ => up (pts q 8 v)) := by
  unfold keep; exact FTotalTriple.ret (Q := fun _ => _) ()

/-- The caller's rule names `q`, which the fact `p = q` substitutes away: the term's `q` becomes
an argument again (`refreshUser`), here `p` by unification. -/
theorem stale_local (p q : Ptr) (v : BitVec 64) (hv : v.toNat < 10) :
    FTotalTriple (⟪p = q⟫ ⋆ up (pts q 8 v)) (keep q) (fun _ => up (pts p 8 v)) := by
  fsym [keep_spec q v hv]

/-! ## Definitions of a state and of an update's result (ledger #43) -/

/-- An invariant whose unfolding opens a witness the planner cannot choose (the arena's `own`:
`∃ w : OV, …` over projections of `w`): its update says how to reach it. -/
def Inv (p q : Ptr) : FAssn := FAssn.ex fun w : W => ⟪w.p = p ∧ w.q = q ∧ w.v.toNat < 10⟫ ⋆ w.L

theorem inv_upd {p q : Ptr} {x : BitVec 64} (_h : x.toNat < 10) : EUpd (apts p x ⋆ apts q 0#64) (Inv p q) :=
  EUpd.of_imp fun _ hr => ⟨⟨p, x, q⟩, sep_lift.mpr ⟨⟨rfl, rfl, ‹_›⟩, hr⟩⟩

/-- The postcondition's `Inv` is the update's to close, not unfolded (its witness `w` would be
planned from the atoms' projections `?w.p`). -/
theorem upd_atom (p q : Ptr) (x : BitVec 64) (hx : x.toNat < 5) :
    FTotalTriple (apts q 0#64 ⋆ apts p x) (pure ()) (fun _ => Inv p q) := by
  fsym [inv_upd]

/-- A state of the module's definitions (`W.L`), in an entailment: unfolded, as a walk's
precondition. -/
theorem entail_def (w : W) : EUpd w.L (apts w.q 0#64 ⋆ apts w.p w.v) := by
  fsym_entail

/-! ## An update's precondition through views (ledger #update-plan-views)

An invariant holds a word as a `wpts` (any tag constraint: the arena's node headers); an atomic op
leaves an `apts`. The plan of an update's precondition views the state's atom as the one that
plan did not find (`apts_wpts_view`), as a step's plan does, not as what other plans of the
return missed. -/

/-- A published word at `p`: with any tag constraint, or 16 bytes of a region (a raw predicate,
which the planner does not unfold). -/
def PubW (p : Ptr) : FAssn := fun r =>
  (FAssn.ex fun v => wpts p v) r ∨ ∃ A S K bs, bs.size = 16 ∧ up (regionIn p A S K 8 bs) r

/-- An update that this state does not meet: 16 bytes at `p`. -/
theorem pubR_upd (p : Ptr) {A S : Nat} {K : BlockKind} {bs : Array Byte} (h : bs.size = 16) :
    EUpd (up (regionIn p A S K 8 bs)) (PubW p) :=
  EUpd.of_imp fun _ hr => .inr ⟨A, S, K, bs, h, hr⟩

theorem pubW_upd (p : Ptr) {v : BitVec 64} : EUpd (wpts p v) (PubW p) :=
  EUpd.of_imp fun _ hr => .inl ⟨v, hr⟩

/-- The second update names a `wpts`, the state has the `apts`: viewed as it (`closePre`). The
first one's plan, which views the word as the bytes of a region and fails, leaves the state as it
was: each update's plan views only what that plan misses. -/
theorem upd_view (p : Ptr) (x : BitVec 64) :
    FTotalTriple (apts p x) (pure ()) (fun _ => PubW p) := by
  fsym [pubR_upd p, pubW_upd p]

/- An update proof can have an assigned proposition metavariable as its raw type.
This checks that representation and the completed proof. Absence of the previously recovered
PANIC must also be checked in captured output from a fresh actual Full elaboration. -/
open Lean Meta Elab Tactic Zig.Full.Auto in
example (P Q : FAssn) (h : EUpd P Q) : True := by
  run_tac do
    let value := (← getLocalDeclFromUserName `h).toExpr
    let rawType ← mkFreshExprMVar (mkSort Level.zero)
    rawType.mvarId!.assign (← inferType value)
    let update ← mkFreshExprSyntheticOpaqueMVar rawType
    update.mvarId!.assign value
    let observed ← inferType update
    unless observed.isMVar do throwError "control lost its raw type metavariable"
    unless ← observed.mvarId!.isAssigned do throwError "control type metavariable is not assigned"
    unless ← isUpd update do throwError "valid assigned-type update was not classified"
    let goalType ← elabTerm
      (← `(FTotalTriple $(mkIdent `P) (pure ()) (fun _ => $(mkIdent `Q)))) none
    let goal ← mkFreshExprSyntheticOpaqueMVar goalType
    let left ← run goal.mvarId! #[update]
    unless left.isEmpty do throwError "assigned-type update did not close the full-state goal"
    if (← instantiateMVars goal).hasExprMVar then
      throwError "assigned-type update left proof unknowns"
  trivial

/-! ## Several inferred frames (a caller contract's frame plus the walk's outer frame)

Only the first hole takes unconsumed resources; independent later holes are empty.
Shared holes and explicit spatial atoms retain their ordinary multiplicity. -/

example {α : Type} {φ : Prop} (hφ : φ) (x : MemM α) (X R : FAssn)
    (h : ∀ F, FTotalTriple ((⟪φ⟫ ⋆ X) ⋆ F) x (fun _ => F)) :
    FTotalTriple (X ⋆ R) x (fun _ => R) := by
  fsym [h]

open Lean Meta Elab Tactic Zig.Full.Auto in
example {φ : Prop} (hφ : φ) (X R : FAssn) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let φ := (← getLocalDeclFromUserName `φ).toExpr
    for count in [2, 3] do
      let frames ← (List.range count).toArray.mapM fun _ => mkFreshExprMVar (mkConst ``FAssn)
      let target := sepOf (#[mkSep (mkApp (mkConst ``FAssn.lift) φ) X] ++ frames)
      let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[mkSep X R, target])
      unless (← closeEntail g.mvarId!).isEmpty do
        throwError "independent frame holes did not close"
      unless (← instantiateMVars frames[0]!) == R do
        throwError "first frame did not retain the exact remainder"
      for frame in frames.extract 1 frames.size do
        unless (← instantiateMVars frame).isConstOf ``FAssn.emp do
          throwError "later independent frame is not empty"
      if (← instantiateMVars g).hasExprMVar then
        throwError "independent frame proof has unknowns"
  trivial

open Lean Meta Elab Tactic Zig.Full.Auto in
example (X R : FAssn) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let frame ← mkFreshExprMVar (mkConst ``FAssn)
    let g ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, frame, frame]])
    let left ← closeEntail g.mvarId!
    unless left == [g.mvarId!] && !(← g.mvarId!.isAssigned) &&
        !(← frame.mvarId!.isAssigned) do
      throwError "shared frame duplicated resources or leaked its rejected choice"
    let later ← mkFreshExprMVar (mkConst ``FAssn)
    let good ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, frame, later]])
    unless (← closeEntail good.mvarId!).isEmpty do
      throwError "a rejected shared frame spoiled a later independent choice"
    if (← instantiateMVars good).hasExprMVar then
      throwError "later frame proof has unknowns"
    let source ← mkFreshExprMVar (mkConst ``FAssn)
    let shared ← mkFreshExprMVar (mkConst ``FAssn)
    let alias ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X source, sepOf #[X, shared, shared]])
    unless (← closeEntail alias.mvarId!) == [alias.mvarId!] &&
        !(← source.mvarId!.isAssigned) && !(← shared.mvarId!.isAssigned) do
      throwError "a shared frame forced its source remainder to empty"
  trivial

open Lean Meta Elab Tactic Zig.Full.Auto in
example (X : FAssn) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let frame ← mkFreshExprMVar (mkConst ``FAssn)
    let later ← mkFreshExprMVar (mkConst ``FAssn)
    let g ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[X, sepOf #[X, frame, frame, later]])
    unless (← closeEntail g.mvarId!).isEmpty do
      throwError "empty shared and independent frames did not close"
    unless (← instantiateMVars frame).isConstOf ``FAssn.emp &&
        (← instantiateMVars later).isConstOf ``FAssn.emp do
      throwError "an empty remainder acquired resources"
    if (← instantiateMVars g).hasExprMVar then throwError "empty frame proof has unknowns"
  trivial

open Lean Meta Elab Tactic Zig.Full.Auto in
example (X R : FAssn) (a b : Nat) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let a := (← getLocalDeclFromUserName `a).toExpr
    let b := (← getLocalDeclFromUserName `b).toExpr
    let fnType ← mkArrow (mkConst ``Nat) (mkConst ``FAssn)
    let first ← mkFreshExprMVar fnType
    let later ← mkFreshExprMVar fnType
    let g ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, mkApp first a, mkApp later b]])
    unless (← closeEntail g.mvarId!).isEmpty do
      throwError "independent applied frames did not close"
    unless ← withNewMCtxDepth (isDefEq (← instantiateMVars (mkApp first a)) R) do
      throwError "applied first frame lost its remainder"
    unless ← withNewMCtxDepth
        (isDefEq (← instantiateMVars (mkApp later b)) (mkConst ``FAssn.emp)) do
      throwError "applied later frame is not empty"
    if (← instantiateMVars g).hasExprMVar then throwError "applied frame proof has unknowns"
    let dependent ← mkFreshExprMVar
      (← mkArrow (mkConst ``FAssn) (mkConst ``FAssn))
    let root ← mkFreshExprMVar (mkConst ``FAssn)
    let dep ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, root, mkApp dependent root]])
    unless (← closeEntail dep.mvarId!).isEmpty do
      throwError "a dependent independent-head frame did not close"
    unless (← instantiateMVars root) == R do
      throwError "a dependent frame changed its input remainder"
    if (← instantiateMVars dep).hasExprMVar then
      throwError "dependent frame proof has unknowns"
    let shared ← mkFreshExprMVar fnType
    let bad ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, mkApp shared a, mkApp shared b]])
    unless (← closeEntail bad.mvarId!) == [bad.mvarId!] &&
        !(← bad.mvarId!.isAssigned) && !(← shared.mvarId!.isAssigned) do
      throwError "a shared application head duplicated resources or leaked assignments"
  trivial

open Lean Meta Elab Tactic Zig.Full.Auto in
example (X R : FAssn) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let frame ← mkFreshExprMVar (mkConst ``FAssn)
    let g ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, R, frame]])
    unless (← closeEntail g.mvarId!).isEmpty do
      throwError "a determined explicit frame was not preserved"
    unless (← instantiateMVars frame).isConstOf ``FAssn.emp do
      throwError "a determined frame was overwritten"
    let extra ← mkFreshExprMVar (mkConst ``FAssn)
    let bad ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, R, R, extra]])
    unless (← closeEntail bad.mvarId!) == [bad.mvarId!] &&
        !(← bad.mvarId!.isAssigned) && !(← extra.mvarId!.isAssigned) do
      throwError "an explicit spatial atom was duplicated or dropped"
    if (← instantiateMVars g).hasExprMVar then throwError "explicit frame proof has unknowns"
  trivial

open Lean Meta Elab Tactic Zig.Full.Auto in
example (X R : FAssn) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let first ← mkFreshExprMVar (mkConst ``FAssn)
    let later ← mkFreshExprMVar (mkConst ``FAssn)
    let target := sepOf #[mkSep (mkApp (mkConst ``FAssn.lift) (mkConst ``False)) X,
      first, later]
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[mkSep X R, target])
    let left ← closeEntail g.mvarId!
    unless ← left.anyM fun m => return (← instantiateMVars (← m.getType)).isFalse do
      throwError "a false pure fact was not retained as an actual False obligation"
    unless (← instantiateMVars first) == R &&
        (← instantiateMVars later).isConstOf ``FAssn.emp do
      throwError "the false-fact residual changed the frame allocation"
  trivial

end SepAuto.Updates

namespace SepAuto.Updates

open Zig Zig.Full Zig.Full.FAssn Lean Meta Elab Tactic Zig.Full.Auto

/-- Matching a structured atom can introduce a live alias into a still-raw source atom. -/
example (U : FAssn → FAssn) (a : Nat) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let U := (← getLocalDeclFromUserName `U).toExpr
    let a := (← getLocalDeclFromUserName `a).toExpr
    let source ← mkFreshExprMVar (mkConst ``FAssn)
    let first ← mkFreshExprMVar (mkConst ``FAssn)
    let shared ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkConst ``FAssn))
    let value := mkApp shared a
    let g ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep (mkApp U source) source,
        sepOf #[mkApp U value, first, value]])
    unless (← closeEntail g.mvarId!) == [g.mvarId!] && !(← g.mvarId!.isAssigned) &&
        !(← source.mvarId!.isAssigned) && !(← first.mvarId!.isAssigned) &&
        !(← shared.mvarId!.isAssigned) do
      throwError "matching an atom forced its aliased source remainder to empty"
  trivial

/-- Positive direct API controls check their completed intermediate proofs with the kernel,
in addition to the public caller-contract theorem and Meta-level allocation/refusal checks. -/
example {φ : Prop} (hφ : φ) (X R : FAssn) (a b : Nat) : True := by
  run_tac withRunCaches do
    discard arithSimpCtx
    let X := (← getLocalDeclFromUserName `X).toExpr
    let R := (← getLocalDeclFromUserName `R).toExpr
    let φ := (← getLocalDeclFromUserName `φ).toExpr
    for count in [2, 3] do
      let frames ← (List.range count).toArray.mapM fun _ => mkFreshExprMVar (mkConst ``FAssn)
      let g ← mkFreshExprSyntheticOpaqueMVar
        (← mkAppM ``EUpd #[mkSep X R,
          sepOf (#[mkSep (mkApp (mkConst ``FAssn.lift) φ) X] ++ frames)])
      unless (← closeEntail g.mvarId!).isEmpty do
        throwError "independent frame proof did not close for kernel checking"
      checkWithKernel (← mkExpectedTypeHint (← instantiateMVars g)
        (← instantiateMVars (← g.mvarId!.getType)))
    let shared ← mkFreshExprMVar (mkConst ``FAssn)
    let later ← mkFreshExprMVar (mkConst ``FAssn)
    let empty ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[X, sepOf #[X, shared, shared, later]])
    unless (← closeEntail empty.mvarId!).isEmpty do
      throwError "empty shared frame proof did not close for kernel checking"
    checkWithKernel (← mkExpectedTypeHint (← instantiateMVars empty)
      (← instantiateMVars (← empty.mvarId!.getType)))
    let a := (← getLocalDeclFromUserName `a).toExpr
    let b := (← getLocalDeclFromUserName `b).toExpr
    let fnType ← mkArrow (mkConst ``Nat) (mkConst ``FAssn)
    let first ← mkFreshExprMVar fnType
    let second ← mkFreshExprMVar fnType
    let applied ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, mkApp first a, mkApp second b]])
    unless (← closeEntail applied.mvarId!).isEmpty do
      throwError "applied frame proof did not close for kernel checking"
    checkWithKernel (← mkExpectedTypeHint (← instantiateMVars applied)
      (← instantiateMVars (← applied.mvarId!.getType)))
    let root ← mkFreshExprMVar (mkConst ``FAssn)
    let dependent ← mkFreshExprMVar (← mkArrow (mkConst ``FAssn) (mkConst ``FAssn))
    let dep ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, root, mkApp dependent root]])
    unless (← closeEntail dep.mvarId!).isEmpty do
      throwError "dependent frame proof did not close for kernel checking"
    checkWithKernel (← mkExpectedTypeHint (← instantiateMVars dep)
      (← instantiateMVars (← dep.mvarId!.getType)))
    let explicit ← mkFreshExprMVar (mkConst ``FAssn)
    let determined ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``EUpd #[mkSep X R, sepOf #[X, R, explicit]])
    unless (← closeEntail determined.mvarId!).isEmpty do
      throwError "explicit frame proof did not close for kernel checking"
    checkWithKernel (← mkExpectedTypeHint (← instantiateMVars determined)
      (← instantiateMVars (← determined.mvarId!.getType)))
  trivial

end SepAuto.Updates
