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

end SepAuto.Updates
