import ZigLean.Sep.Base.Pts

/-!
# Triples (legacy logic)

`Triple P c Q` is partial correctness without a panic: if `P` holds of a part of
the memory, `c` does not throw; if it returns `v`, `Q v` holds of that part after it, and the
rest of the memory (the frame) is unchanged. A program that does not terminate satisfies every
triple. The frame is in the definition, so the frame rule (`Triple.frame`) holds for every
program.

The assertions `pts`/`arr` and the `*_run` lemmas of one memory operation are vocabulary of
both logics (`ZigLean/Sep/Base/Pts.lean`). This module is the legacy judgment, deleted with the
legacy layer (`docs/proof-framework.md`).
-/

namespace Zig

open Assn

/-- `Triple P c Q` (module doc). `m.Seq` is a precondition and, on a return, a guarantee
about the result memory: every rule below carries it through, so a caller that never spawns a
thread (all `M17`/`M22`-example proofs before `Threads`) never re-derives it, and every `NoRace`
obligation a memory-operation lemma needs is `noRace_of_singleThread hst.single` for free. -/
def Triple {α : Type} (P : Assn) (c : MemM α) (Q : α → Assn) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
    match (c.run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq


namespace Triple

variable {α β : Type} {P P' R : Assn} {Q Q' : α → Assn} {c : MemM α}

/-- A triple from the run: `c` returns, and the post-condition holds. -/
theorem of_run
    (h : ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
      ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧
        m'.Seq) :
    Triple P c Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := h m hP hF hd hm hp hs
  rw [hr]; exact ⟨hQ, hd', hm', hq, hs'⟩

theorem conseq (ht : Triple P c Q) (hp : ∀ h, P' h → P h) (hq : ∀ v h, Q v h → Q' v h) :
    Triple P' c Q' := by
  intro m hP hF hd hm hp' hs
  have := ht m hP hF hd hm (hp _ hp') hs
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, a, b, c, s⟩ := this; exact ⟨hQ, a, b, hq _ _ c, s⟩

/-- The frame rule: a part of the memory that `c` does not own stays unchanged. -/
theorem frame (ht : Triple P c Q) : Triple (P ∗ R) c (fun v => Q v ∗ R) := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩ hs
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' : Heap.Disjoint hP (hR ∪ hF) := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  have := ht m hP (hR ∪ hF) hd' hm' hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨hQ, hQd, hmQ, hq, hs'⟩ := this
    obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
    exact ⟨hQ ∪ hR, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩, by rw [hmQ, Heap.union_assoc],
      ⟨hQ, hR, hQR, rfl, hq, hr⟩, hs'⟩

theorem ret (v : α) : Triple (Q v) (pure v : MemM α) (Q) :=
  of_run fun m hP _ hd hm hq hs => ⟨v, m, hP, rfl, hd, hm, hq, hs⟩

theorem bind {R : β → Assn} {f : α → MemM β} (hc : Triple P c Q) (hf : ∀ v, Triple (Q v) (f v) R) :
    Triple (P) (c >>= f) (R) := by
  intro m hP hF hd hm hp hs
  have h1 := hc m hP hF hd hm hp hs
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some r =>
    cases r with
    | error e => intro h1; exact h1
    | ok r =>
      obtain ⟨v, m'⟩ := r
      rintro ⟨hQ, hd', hm', hq, hs'⟩
      exact hf v m' hQ hF hd' hm' hq hs'

theorem ex {γ : Type} {P : γ → Assn} (h : ∀ x, Triple (P x) c Q) : Triple (Assn.ex P) c Q := by
  intro m hP hF hd hm ⟨x, hp⟩ hs
  exact h x m hP hF hd hm hp hs

theorem lift {φ : Prop} (h : φ → Triple P c Q) : Triple (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m hP hF hd hm hp hs

end Triple

section Rules

variable {T : Type} [Enc T]

theorem Triple.load {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    Triple (pts p a v) (load T a p) (fun r => ⌜r = v⌝ ∗ pts p a v) :=
  Triple.of_run fun _ hP _ hd hm hp hs => by
    obtain ⟨m', hr, hheap, hst'⟩ := pts_load_run hp hm hn hs
    exact ⟨v, m', hP, hr, hd, hheap, sep_lift.mpr ⟨rfl, hp⟩, hst'⟩

theorem Triple.store [LawfulEnc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    Triple (pts p a v) (store a p w) (fun _ => pts p a w) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', hr, hst', h', hd', hm', hp'⟩ := pts_store_run hp hm hd hn hs w
    exact ⟨(), m', h', hr, hd', hm', hp', hst'⟩

/-- `&xs[i]` of an owned array, `i ≤ len` (`ptrProject`, MM-3). -/
theorem Triple.arr_ptrProject {p : Ptr} {xs : List T} {i : BitVec 64} (hi : i.toNat ≤ xs.length) :
    Triple (arr p xs) (ptrProject p (·.elem (Enc.size T) i))
      (fun q => ⌜q = p.elem (Enc.size T) i⌝ ∗ arr p xs) :=
  Triple.of_run fun m hP _ hd hm hp hs =>
    ⟨_, m, hP, arr_ptrProject_run hp hm hi, hd, hm, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

end Rules

end Zig
