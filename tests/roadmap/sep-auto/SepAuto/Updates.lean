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

end SepAuto.Updates
