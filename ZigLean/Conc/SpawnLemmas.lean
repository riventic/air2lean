import ZigLean.Conc.Spawn
import ZigLean.Conc.Lemmas
import ZigLean.Conc.Transfer

/-! WP rules require every oracle outcome. A failed assignment does not require
`P.init` and cannot use the historical successful-spawn rule. Interference is
accounted for at the choice: preservation is relative to the resumed memory. The
assignment outcome is only required where the caller's budget (`Mem.spawnLimit`) admits
it; every failure outcome is required regardless of the budget. -/

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
    P.WP t ((do let c ← Zig.pickC count; body c : CM Tgt σ α).run s) Q G m n := by
  simp only [StateT.run_bind]
  apply WP.bind
  exact WP.pickC h

/-- A budgeted resource choice among `total ≥ 2` outcomes. The branch proof receives every
outcome `o < total`; the assignment outcome `0` only when the caller's budget admits a child. -/
theorem WP.assignmentChoiceC {total : Nat} (htot : 2 ≤ total) {body : Nat → CM Tgt σ α} {s : σ}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ o, o < total → (o = 0 → ({ m₁ with current := t } : Mem).spawnAdmits = true) →
        P.WP t ((body o).run s) Q G₁ { m₁ with current := t } k) :
    P.WP t ((do let c ← Zig.assignmentChoiceC total; body c : CM Tgt σ α).run s) Q G m n := by
  unfold Zig.assignmentChoiceC
  simp only [bind_assoc, StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ?_)
  obtain ⟨g, hi, hb⟩ := h k hk
  refine ⟨g, hi, fun G₁ m₁ hg hi₁ c hc => ?_⟩
  refine WP.bind (WP.callMC (fun e he => by cases he) fun a m' hr => ?_)
  cases hr
  refine ⟨rfl, ?_⟩
  simp only [StateT.run_pure, pure_bind]
  refine hb G₁ m₁ hg hi₁ _ ?_ ?_
  · unfold assignmentOutcome
    unfold assignmentCount at hc
    split <;> rename_i ha <;> simp only [ha, if_true, if_false, Bool.false_eq_true] at hc <;> omega
  · intro h0
    unfold assignmentOutcome at h0
    split at h0
    · assumption
    · omega

theorem WP.spawnFallibleC {target : Tgt} {s : σ}
    {Q : Except ErrName ThreadId × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, c < spawnErrors.size + 1 →
        (c = 0 → ({ m₁ with current := t } : Mem).spawnAdmits = true) →
        P.WP t ((spawnOutcomeC c target : CM Tgt σ _).run s)
          Q G₁ { m₁ with current := t } k) :
    P.WP t ((spawnWithPolicyC .fallible target : CM Tgt σ _).run s) Q G m n := by
  unfold spawnWithPolicyC
  exact WP.assignmentChoiceC (by decide) h

theorem WP.groupAsyncFallibleC {group : Ptr} {io : Io} {target : Tgt}
    {fallback : ConcM Tgt Unit} {s : σ}
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, c < 2 → (c = 0 → ({ m₁ with current := t } : Mem).spawnAdmits = true) →
        P.WP t ((groupAsyncOutcomeC c group io target fallback : CM Tgt σ _).run s)
          Q G₁ { m₁ with current := t } k) :
    P.WP t ((groupAsyncWithPolicyC .fallible group io target fallback : CM Tgt σ _).run s)
      Q G m n := by
  unfold groupAsyncWithPolicyC
  exact WP.assignmentChoiceC (by decide) h

theorem WP.groupConcurrentFallibleC {group : Ptr} {io : Io} {target : Tgt} {s : σ}
    {Q : Except ErrName Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
      ∀ c, c < 2 → (c = 0 → ({ m₁ with current := t } : Mem).spawnAdmits = true) →
        P.WP t ((groupConcurrentOutcomeC c group io target : CM Tgt σ _).run s)
          Q G₁ { m₁ with current := t } k) :
    P.WP t ((groupConcurrentWithPolicyC .fallible group io target : CM Tgt σ _).run s)
      Q G m n := by
  unfold groupConcurrentWithPolicyC
  exact WP.assignmentChoiceC (by decide) h

/-- The frame may include ownership of every captured object and a pending cleanup
list. A failed spawn preserves it at the resumed memory, with no child ghost update. -/
theorem WP.spawnFailureFrame {target : Tgt} {c : Nat} (hc : c ≠ 0) {s : σ}
    {frame : (ThreadId → γ) → Mem → Prop} (hf : frame G m) :
    P.WP t ((spawnOutcomeC c target : CM Tgt σ _).run s)
      (fun result G' m' _ => result = (.error (spawnErrorAt (c - 1)), s) ∧ frame G' m') G m n := by
  simp only [spawnOutcomeC, if_neg hc]
  exact WP.pure' ⟨rfl, hf⟩

/-- **Failure leaves ownership with the caller.** Suppose the caller split its part into `keep`
and the `child` cells of the grant it prepared for the captured fields (`Capture.grant`,
`ZigLean/Conc/Transfer.lean`). On a failed assignment the split, the grant, the ghost state and
the memory at the resumed choice are all unchanged: no thread is created and no captured
region moves. Contrast `Capture.fork_grant`, which hands `child` to the new thread. -/
theorem WP.spawnFailureRetains {target : Tgt} {c : Nat} (hc : c ≠ 0) {s : σ}
    {own : ThreadId → Heap} {keep child : Heap} {mode : Ptr → Transfer} {cs : List Capture}
    (ho : Owned own m) (hsplit : own t = keep ∪ child) (hg : Capture.grant mode cs child) :
    P.WP t ((spawnOutcomeC c target : CM Tgt σ _).run s)
      (fun r G' m' _ => r = (.error (spawnErrorAt (c - 1)), s) ∧ G' = G ∧ m' = m ∧
        Owned own m' ∧ own t = keep ∪ child ∧ Capture.grant mode cs child) G m n :=
  WP.spawnFailureFrame hc (frame := fun G' m' => G' = G ∧ m' = m ∧ Owned own m' ∧
    own t = keep ∪ child ∧ Capture.grant mode cs child) ⟨rfl, rfl, ho, hsplit, hg⟩

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
