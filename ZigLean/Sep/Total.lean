import ZigLean.Sep.Loop

/-!
# Total separation triples

`Triple` deliberately permits divergence. `TotalTriple` requires an actual successful
result for every sequential memory satisfying its precondition, including every disjoint
frame. The witness is an equality with `pure`; neither `none` nor a safety error can satisfy
it. Zig error-union values remain ordinary return values.

These rules reuse the existing run lemmas and decreasing-measure loop theorem. They do not
turn an arbitrary partial-correctness proof into a termination proof.
-/

namespace Zig

open Assn

/-- Successful termination, ownership of the postcondition, and preservation of the frame. -/
def TotalTriple {α : Type} (P : Assn) (c : MemM α) (Q : α → Assn) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
    ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq

/-- A successful result exists under the same framed precondition as a triple. -/
def Returns {α : Type} (P : Assn) (c : MemM α) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
    ∃ v m', c.run m = pure (v, m')

namespace TotalTriple

variable {α β : Type} {P P' R : Assn} {Q Q' : α → Assn} {c : MemM α}

theorem of_run
    (h : ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
      ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq) :
    TotalTriple P c Q := h

theorem toPartial (ht : TotalTriple P c Q) : Triple P c Q := Triple.of_run ht

theorem returns (ht : TotalTriple P c Q) : Returns P c := by
  intro m hP hF hd hm hp hs
  obtain ⟨v, m', _, hr, _⟩ := ht m hP hF hd hm hp hs
  exact ⟨v, m', hr⟩

/-- A partial proof needs a separate return witness before it yields a total proof. -/
theorem of_partial (ht : Triple P c Q) (hr : Returns P c) : TotalTriple P c Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨v, m', hrun⟩ := hr m hP hF hd hm hp hs
  have hpost := ht m hP hF hd hm hp hs
  rw [hrun] at hpost
  obtain ⟨hQ, hd', hm', hq, hs'⟩ := hpost
  exact ⟨v, m', hQ, hrun, hd', hm', hq, hs'⟩

theorem iff_partial_returns : TotalTriple P c Q ↔ Triple P c Q ∧ Returns P c :=
  ⟨fun ht => ⟨ht.toPartial, ht.returns⟩, fun ⟨ht, hr⟩ => of_partial ht hr⟩

theorem conseq (ht : TotalTriple P c Q) (hp : ∀ h, P' h → P h)
    (hq : ∀ v h, Q v h → Q' v h) : TotalTriple P' c Q' := by
  intro m hP hF hd hm hp' hs
  obtain ⟨v, m', hQ, hr, hd', hm', hq', hs'⟩ := ht m hP hF hd hm (hp _ hp') hs
  exact ⟨v, m', hQ, hr, hd', hm', hq _ _ hq', hs'⟩

theorem frame (ht : TotalTriple P c Q) :
    TotalTriple (P ∗ R) c (fun v => Q v ∗ R) := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩ hs
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨v, m', hQ, hrun, hQd, hmQ, hq, hs'⟩ := ht m hP (hR ∪ hF) hd' hm' hp hs
  obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
  exact ⟨v, m', hQ ∪ hR, hrun, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩,
    by rw [hmQ, Heap.union_assoc], ⟨hQ, hR, hQR, rfl, hq, hr⟩, hs'⟩

theorem ret (v : α) : TotalTriple (Q v) (pure v : MemM α) Q :=
  fun m hP _ hd hm hq hs => ⟨v, m, hP, rfl, hd, hm, hq, hs⟩

theorem bind {S : β → Assn} {f : α → MemM β}
    (hc : TotalTriple P c Q) (hf : ∀ v, TotalTriple (Q v) (f v) S) :
    TotalTriple P (c >>= f) S := by
  intro m hP hF hd hm hp hs
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := hc m hP hF hd hm hp hs
  obtain ⟨w, m'', hS, hr', hd'', hm'', hS', hs''⟩ := hf v m' hQ hF hd' hm' hq hs'
  refine ⟨w, m'', hS, ?_, hd'', hm'', hS', hs''⟩
  simpa only [StateT.run_bind, hr, pure_bind] using hr'

theorem ex {γ : Type} {P : γ → Assn} (ht : ∀ x, TotalTriple (P x) c Q) :
    TotalTriple (Assn.ex P) c Q := by
  intro m hP hF hd hm ⟨x, hp⟩ hs
  exact ht x m hP hF hd hm hp hs

theorem lift {φ : Prop} (ht : φ → TotalTriple P c Q) : TotalTriple (⌜φ⌝ ∗ P) c Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact ht hφ m hP hF hd hm hp hs

theorem load {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    TotalTriple (pts p a v) (Zig.load T a p) (fun r => ⌜r = v⌝ ∗ pts p a v) := by
  intro m hP hF hd hm hp hs
  obtain ⟨m', hr, hheap, hs'⟩ := pts_load_run hp hm hn hs
  exact ⟨v, m', hP, hr, hd, hheap, sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

theorem store {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) (w : T) :
    TotalTriple (pts p a v) (Zig.store a p w) (fun _ => pts p a w) := by
  intro m hP hF hd hm hp hs
  obtain ⟨m', hr, hs', h', hd', hm', hp'⟩ := pts_store_run hp hm hd hn hs w
  exact ⟨(), m', h', hr, hd', hm', hp', hs'⟩

theorem arr_store {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {vs : List T}
    {a : Nat} {i : BitVec 64} (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) (w : T) :
    TotalTriple (arr p vs) (Zig.store a (p.elem (Enc.size T) i) w)
      (fun _ => arr p (vs.set i.toNat w)) := by
  intro m hP hF hd hm hp hseq
  obtain ⟨m', hr, hs', h', hd', hm', hp'⟩ := arr_store_run hp hm hd hn ha hs hi hseq w
  exact ⟨(), m', h', hr, hd', hm', hp', hs'⟩

/-- Total loop correctness from a natural-number measure carried by the invariant. -/
theorem loop_ghost {σ ε : Type} (body : MM σ ε) (again : ε → Bool)
    (I : σ → Nat → Assn) (post : ε → σ → Assn)
    (step : ∀ hF s n m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s n h → m.Seq →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ m'.Seq ∧
        (if again e then ∃ n' < n, I s' n' h' else post e s' h')) (s : σ) (n : Nat) :
    TotalTriple (I s n) ((Zig.loop body again).run s) (fun r => post r.1 r.2) := by
  intro m hP hF hd hm hi hs
  obtain ⟨e, s', m', h', hr, hd', hm', hp, hs'⟩ :=
    loop_sep_ghost body again I post hF (step hF) s n m hP hd hm hi hs
  exact ⟨(e, s'), m', h', hr, hd', hm', hp, hs'⟩

end TotalTriple

end Zig
