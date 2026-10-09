import ZigLean.Sep.Total
import ZigLean.Sep.Cost

/-!
# Resource-bounded total triples

`TotalTripleWithin B P body again s Q` is a total triple for the loop `loop body again` from the
locals `s`, together with a bound: from every framed precondition the loop exits after at most
`B` body runs. The count is P06's `LoopRuns` (`ZigLean/Sep/Cost.lean`): every repeat and the
final exit, and nothing else. Since the body is deterministic (`LoopRuns.unique`), the bound
holds for *the* run of the loop, not merely for some counted run (`count_le`).

* `toTotal`: a bounded triple is a total triple; the bound is extra information.
* `mono`, `conseq`, `frame`: the usual structural rules; a larger bound is weaker.
* `step` / `exit`: one body run (a `TotalTriple` of the body) composed with a bounded rest adds
  one to the bound. `then_total`: a bounded loop followed by a total continuation is total.
* `of_ghost`: `TotalTriple.loop_ghost`'s decreasing ghost number `n` bounds the count by `n + 1`.
* `not_within_of_count`, `not_within_of_stuck`: a run with more body runs than `B`, or a loop
  that never exits, from an admissible input refutes the bounded triple. Divergence cannot
  satisfy it vacuously.

The unit is the loop-body run of the model, as in P06. It is not CPU time, and no step of
straight-line code outside the counted loop is counted.
-/

namespace Zig

open Assn

/-- The loop `loop body again` from the locals `s` exits after at most `B` body runs, with the
postcondition owned and the frame preserved. -/
def TotalTripleWithin {σ ε : Type} (B : Nat) (P : Assn) (body : MM σ ε) (again : ε → Bool)
    (s : σ) (Q : ε → σ → Assn) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
    ∃ k e s' m' hQ, k ≤ B ∧ LoopRuns body again s m k e s' m' ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ Q e s' hQ ∧ m'.Seq

namespace TotalTripleWithin

variable {σ ε : Type} {B B' : Nat} {P P' R : Assn} {body : MM σ ε} {again : ε → Bool} {s : σ}
  {Q Q' : ε → σ → Assn}

/-- Bounded implies total. -/
theorem toTotal (h : TotalTripleWithin B P body again s Q) :
    TotalTriple P ((loop body again).run s) (fun r => Q r.1 r.2) := by
  intro m hP hF hd hm hp hs
  obtain ⟨_, e, s', m', hQ, _, hl, hd', hm', hq, hs'⟩ := h m hP hF hd hm hp hs
  exact ⟨(e, s'), m', hQ, hl.run, hd', hm', hq, hs'⟩

theorem returns (h : TotalTripleWithin B P body again s Q) :
    Returns P ((loop body again).run s) := h.toTotal.returns

theorem toPartial (h : TotalTripleWithin B P body again s Q) :
    Triple P ((loop body again).run s) (fun r => Q r.1 r.2) := h.toTotal.toPartial

/-- The bound applies to the loop's one run: any counted run from an admissible input has at
most `B` body runs. -/
theorem count_le (h : TotalTripleWithin B P body again s Q) {m : Mem} {hP hF : Heap}
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    {k : Nat} {e : ε} {s' : σ} {m' : Mem} (hk : LoopRuns body again s m k e s' m') : k ≤ B := by
  obtain ⟨k₀, _, _, _, _, hle, hl, _⟩ := h m hP hF hd hm hp hs
  rw [(hk.unique hl).1]; exact hle

/-- A run with more than `B` body runs from an admissible input refutes the bound. -/
theorem not_within_of_count {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) {k : Nat} {e : ε} {s' : σ} {m' : Mem}
    (hk : LoopRuns body again s m k e s' m') (hB : B < k) :
    ¬ TotalTripleWithin B P body again s Q := fun h => by
  have := h.count_le hd hm hp hs hk; omega

/-- A loop without any counted run from an admissible input (it diverges or fails) has no
bounded triple, for any bound. -/
theorem not_within_of_stuck {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    (hno : ∀ k e s' m', ¬ LoopRuns body again s m k e s' m') :
    ¬ TotalTripleWithin B P body again s Q := fun h => by
  obtain ⟨k, e, s', m', _, _, hl, _⟩ := h m hP hF hd hm hp hs
  exact hno k e s' m' hl

theorem mono (h : TotalTripleWithin B P body again s Q) (hB : B ≤ B') :
    TotalTripleWithin B' P body again s Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨k, e, s', m', hQ, hk, rest⟩ := h m hP hF hd hm hp hs
  exact ⟨k, e, s', m', hQ, Nat.le_trans hk hB, rest⟩

theorem conseq (h : TotalTripleWithin B P body again s Q) (hp : ∀ h, P' h → P h)
    (hq : ∀ e s' h, Q e s' h → Q' e s' h) : TotalTripleWithin B P' body again s Q' := by
  intro m hP hF hd hm hp' hs
  obtain ⟨k, e, s', m', hQ, hk, hl, hd', hm', hq', hs'⟩ := h m hP hF hd hm (hp _ hp') hs
  exact ⟨k, e, s', m', hQ, hk, hl, hd', hm', hq _ _ _ hq', hs'⟩

theorem frame (h : TotalTripleWithin B P body again s Q) :
    TotalTripleWithin B (P ∗ R) body again s (fun e s' => Q e s' ∗ R) := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩ hs
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨k, e, s', m', hQ, hk, hl, hQd, hmQ, hq, hs'⟩ := h m hP (hR ∪ hF) hd' hm' hp hs
  obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
  exact ⟨k, e, s', m', hQ ∪ hR, hk, hl, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩,
    by rw [hmQ, Heap.union_assoc], ⟨hQ, hR, hQR, rfl, hq, hr⟩, hs'⟩

/-- One body run, then either the exit or a rest bounded by `B`: the loop is bounded by
`B + 1`. The body step is an ordinary total triple. -/
theorem step {Rs : σ → Assn}
    (hb : TotalTriple P (body.run s) (fun r => if again r.1 then Rs r.2 else Q r.1 r.2))
    (hrest : ∀ s', TotalTripleWithin B (Rs s') body again s' Q) :
    TotalTripleWithin (B + 1) P body again s Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨⟨e, s₁⟩, m₁, h₁, hr, hd₁, hm₁, hq₁, hs₁⟩ := hb m hP hF hd hm hp hs
  cases ha : again e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hq₁
    exact ⟨1, e, s₁, m₁, h₁, by omega, .exit hr ha, hd₁, hm₁, hq₁, hs₁⟩
  · simp only [ha, ↓reduceIte] at hq₁
    obtain ⟨k, e₂, s₂, m₂, h₂, hk, hl, rest⟩ := hrest s₁ m₁ h₁ hF hd₁ hm₁ hq₁ hs₁
    exact ⟨k + 1, e₂, s₂, m₂, h₂, by omega, .next hr ha hl, rest⟩

/-- A body run that exits: the loop runs its body once. -/
theorem exit (hb : TotalTriple P (body.run s) (fun r => ⌜again r.1 = false⌝ ∗ Q r.1 r.2)) :
    TotalTripleWithin 1 P body again s Q := by
  intro m hP hF hd hm hp hs
  obtain ⟨⟨e, s₁⟩, m₁, h₁, hr, hd₁, hm₁, hq₁, hs₁⟩ := hb m hP hF hd hm hp hs
  obtain ⟨ha, hq⟩ := sep_lift.mp hq₁
  exact ⟨1, e, s₁, m₁, h₁, Nat.le_refl _, .exit hr ha, hd₁, hm₁, hq, hs₁⟩

/-- A bounded loop followed by a total continuation is total. -/
theorem then_total {β : Type} {S : β → Assn} {f : ε × σ → MemM β}
    (h : TotalTripleWithin B P body again s Q) (hf : ∀ r, TotalTriple (Q r.1 r.2) (f r) S) :
    TotalTriple P (((loop body again).run s) >>= f) S :=
  h.toTotal.bind hf

/-- `TotalTriple.loop_ghost` with its bound: a ghost number `n` that each repeat lowers bounds
the count by `n + 1`. -/
theorem of_ghost (body : MM σ ε) (again : ε → Bool) (I : σ → Nat → Assn) (post : ε → σ → Assn)
    (step : ∀ hF s n m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s n h → m.Seq →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ m'.Seq ∧
        (if again e then ∃ n' < n, I s' n' h' else post e s' h')) (s : σ) (n : Nat) :
    TotalTripleWithin (n + 1) (I s n) body again s post := by
  intro m hP hF hd hm hi hs
  let inv : σ → Mem → Nat → Prop := fun s m n =>
    ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ I s n h ∧ m.Seq
  let fin : ε → σ → Mem → Prop := fun e s m =>
    ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ post e s h ∧ m.Seq
  have hstep : ∀ s m n, inv s m n → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      (if again e then ∃ n' < n, inv s' m' n' else fin e s' m') := by
    rintro s m n ⟨h, hd, hm, hi, hs⟩
    obtain ⟨e, s', m', h', hr, hd', hm', hs', hn⟩ := step hF s n m h hd hm hi hs
    refine ⟨e, s', m', hr, ?_⟩
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn ⊢
      exact ⟨h', hd', hm', hn, hs'⟩
    · simp only [ha, ↓reduceIte] at hn ⊢
      obtain ⟨n', hlt, hi'⟩ := hn
      exact ⟨n', hlt, h', hd', hm', hi', hs'⟩
  obtain ⟨k, e, s', m', hk, hl, h', hd', hm', hp, hs'⟩ :=
    loopRuns_bound body again inv fin hstep s m n ⟨hP, hd, hm, hi, hs⟩
  exact ⟨k, e, s', m', h', hk, hl, hd', hm', hp, hs'⟩

end TotalTripleWithin

end Zig
