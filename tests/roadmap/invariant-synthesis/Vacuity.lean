import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Witness

/-!
# P09 spike: a kernel-checked invariant can be vacuous

Design question (docs/invariant-synthesis.md, "Non-vacuity"): is "the kernel checks the generated
invariant" enough to make an untrusted invariant generator harmless? It is not.

* `vacuous_spec`: **every** program, whatever its vtable does, meets `FAllocSpec` (total logic
  included) for the invariant whose state no resource satisfies (`falseInv`). The precondition of
  each entry starts with `I.own`, so the triples hold vacuously. A generator that proposes
  `own := ⟪False⟫` (or any unsatisfiable invariant) passes the kernel.
* `creation_admits`: a total creation triple from an admissible precondition (`FAdmit`,
  `docs/claim-strength.md`) ends in an admissible state, so it reaches the invariant.
* `no_creation_falseInv`: no creation triple from an admissible precondition reaches `falseInv`.

So the anchor that rules out a vacuous generated invariant is a hand-stated creation triple from
spec-level resources (the allocator's `init` from its raw buffer), proved by `fsym`, with an
`FAdmit` companion for its precondition. P09 makes that pair a required part of every specification
instance. Nothing here is a judgment or a tactic; this file is not part of CI.
-/

namespace InvariantSynthesis.Vacuity

open Zig Zig.Full Zig.Full.FAssn Zig.Witness

/-- An allocator invariant that no resource satisfies. -/
def falseInv : FAllocInv where
  own := ⟪False⟫
  tok _ _ _ _ _ _ _ _ := FAssn.emp

/-- **Vacuity**: every vtable meets the full-state allocator contract for `falseInv`, in every
logic (`FLogic.total` too). -/
theorem vacuous_spec (L : FLogic) (vt : RawVTable) (ctx : Ptr) : FAllocSpec L vt ctx falseInv where
  alloc _ _ _ _ _ _ _ := L.lift False.elim
  resize _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := L.lift False.elim
  remap _ _ _ _ _ _ _ _ _ _ _ := L.lift False.elim
  free _ _ _ _ _ _ _ _ := L.lift False.elim

/-- **The anchor**: a total triple from an admissible precondition ends in an admissible state. -/
theorem creation_admits {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTotalTriple P c Q) (h : FAdmit P) : ∃ v, FAdmit (Q v) :=
  FAdmit.of_total ht h

/-- No state holds `falseInv.own`. -/
theorem not_admit_falseInv (R : FAssn) : ¬ FAdmit (falseInv.own ⋆ R) := by
  rintro ⟨_, r, _, _, hp, _, _⟩
  exact (sep_lift.mp hp).1

/-- **No creation reaches `falseInv`**: a hand-stated creation triple whose precondition is
admissible rules the vacuous invariant out. -/
theorem no_creation_falseInv {α : Type} {P : FAssn} {c : MemM α} {R : α → FAssn}
    (ht : FTotalTriple P c (fun v => falseInv.own ⋆ R v)) (h : FAdmit P) : False :=
  have ⟨v, hv⟩ := creation_admits ht h
  not_admit_falseInv (R v) hv

end InvariantSynthesis.Vacuity

#print axioms InvariantSynthesis.Vacuity.vacuous_spec
#print axioms InvariantSynthesis.Vacuity.no_creation_falseInv
