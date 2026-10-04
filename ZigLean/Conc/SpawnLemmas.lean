import ZigLean.Conc.Spawn
import ZigLean.Conc.Lemmas

/-! WP rules require every oracle outcome. A failed assignment does not require
`P.init` and cannot use the historical successful-spawn rule. Interference is
accounted for at the choice: preservation is relative to the resumed memory. -/

namespace Zig.Conc.Proto

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n : Nat}

/-- A resource choice followed by a body in the same caller. The invariant is
re-established before the choice; the branch proof sees arbitrary legal interference. -/
theorem WP.assignmentChoice {count : Mem → Nat} {body : Nat → CM Tgt σ α} {s : σ}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, (c < count { m₁ with current := t } ∨ count { m₁ with current := t } = 0 ∧ c = 0) →
        P.WP t ((body c).run s) Q G₁ { m₁ with current := t } k) :
    P.WP t ((do let c ← pickC count; body c : CM Tgt σ α).run s) Q G m n := by
  simp only [StateT.run_bind]
  apply WP.bind
  exact WP.pickC h

theorem WP.spawnFallibleC {target : Tgt} {s : σ}
    {Q : Except ErrName ThreadId × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, c < spawnErrors.size + 1 →
        P.WP t ((spawnOutcomeC c target : CM Tgt σ _).run s)
          Q G₁ { m₁ with current := t } k) :
    P.WP t ((spawnWithPolicyC .fallible target : CM Tgt σ _).run s) Q G m n := by
  unfold spawnWithPolicyC
  apply WP.assignmentChoice
  intro k hk
  obtain ⟨g, hi, hb⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hc => hb G₁ m₁ hg hi₁ c ?_⟩
  rcases hc with hc | hc
  · exact hc
  · simp [spawnErrors] at hc

theorem WP.groupAsyncFallibleC {group : Ptr} {io : Io} {target : Tgt}
    {fallback : ConcM Tgt Unit} {s : σ}
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, c < 2 → P.WP t ((groupAsyncOutcomeC c group io target fallback : CM Tgt σ _).run s)
        Q G₁ { m₁ with current := t } k) :
    P.WP t ((groupAsyncWithPolicyC .fallible group io target fallback : CM Tgt σ _).run s)
      Q G m n := by
  unfold groupAsyncWithPolicyC
  apply WP.assignmentChoice
  intro k hk
  obtain ⟨g, hi, hb⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hc => hb G₁ m₁ hg hi₁ c ?_⟩
  rcases hc with hc | hc
  · exact hc
  · omega

theorem WP.groupConcurrentFallibleC {group : Ptr} {io : Io} {target : Tgt} {s : σ}
    {Q : Except ErrName Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, c < 2 → P.WP t ((groupConcurrentOutcomeC c group io target : CM Tgt σ _).run s)
        Q G₁ { m₁ with current := t } k) :
    P.WP t ((groupConcurrentWithPolicyC .fallible group io target : CM Tgt σ _).run s)
      Q G m n := by
  unfold groupConcurrentWithPolicyC
  apply WP.assignmentChoice
  intro k hk
  obtain ⟨g, hi, hb⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hc => hb G₁ m₁ hg hi₁ c ?_⟩
  rcases hc with hc | hc
  · exact hc
  · omega

/-- The frame may include ownership of every captured object and a pending cleanup
list. A failed spawn preserves it at the resumed memory, with no child ghost update. -/
theorem WP.spawnFailureFrame {target : Tgt} {c : Nat} (hc : c ≠ 0) {s : σ}
    {frame : (ThreadId → γ) → Mem → Prop} (hf : frame G m) :
    P.WP t ((spawnOutcomeC c target : CM Tgt σ _).run s)
      (fun result G' m' _ => result = (.error (spawnErrorAt (c - 1)), s) ∧ frame G' m') G m n := by
  simp only [spawnOutcomeC, if_neg hc]
  exact WP.pure' ⟨rfl, hf⟩

/-- A failed second assignment executes the caller's cleanup continuation. In
particular, an outstanding first-child join must be proved with WP.joinC; failure
adds neither a new child obligation nor a substitute join. -/
theorem WP.failedSpawnCleanup {target : Tgt} {c : Nat} (hc : c ≠ 0) {s : σ}
    {cleanup : Except ErrName ThreadId → CM Tgt σ α}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : P.WP t ((cleanup (.error (spawnErrorAt (c - 1)))).run s) Q G m n) :
    P.WP t ((do
      let result ← spawnOutcomeC c target
      cleanup result : CM Tgt σ α).run s) Q G m n := by
  simpa only [spawnOutcomeC, if_neg hc, StateT.run_bind, StateT.run_pure, pure_bind] using h

end Zig.Conc.Proto
