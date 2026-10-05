import ZigLean.Conc.Lemmas

/-! Weak CAS proof interfaces. Successful weak operations use the strong RMW transition;
a matching-value failure is a failure-order read. These are safety rules, allowing arbitrary
repeated failure and no completed result. -/

namespace Zig
namespace Conc
namespace Proto

theorem weakCasPrep_ok {n align : Nat} {p : Ptr} {expected : BitVec n} {m m' : Mem} {li : Nat}
    {opts : Array (Nat × Bool)}
    (h : ((weakCasPrep n align p expected).run m).run = some (.ok ((li, opts), m'))) :
    ∃ b blk o, m.accessW p (intSize n) align = pure (b, blk, o) ∧
      NoRace m b o (intSize n) .atomicRead ∧
      ((locIdx b o (intSize n)).run (m.recordAt b o (intSize n) .atomicRead)).run =
        some (.ok (li, m')) ∧
      opts = weakCasOpts m' li expected (casOpts m' li expected) := by
  unfold weakCasPrep at h
  obtain ⟨⟨li₁, readable⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := casReadPrep_ok hp
  obtain ⟨a, m₂, hg, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨he, rfl⟩ := MemM.pure_ok h₂
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨b, blk, o, ha, hnr, hl, rfl⟩

/-- A weak failure includes both unequal reads and matching-value spurious failures.
Its memory transition is exactly `loadM` with the failure order. -/
theorem cmpxchgWeakAt_ok {n c : Nat} {succ fail : AtomicOrder} {align : Nat} {p : Ptr}
    {expected new : BitVec n} {r : Option (BitVec n)} {m m' : Mem}
    (h : ((cmpxchgWeakAt c succ fail align p expected new).run m).run = some (.ok (r, m'))) :
    ∃ b blk o li m₁ pos spurious old, m.accessW p (intSize n) align = pure (b, blk, o) ∧
      NoRace m b o (intSize n) .atomicRead ∧
      ((locIdx b o (intSize n)).run (m.recordAt b o (intSize n) .atomicRead)).run =
        some (.ok (li, m₁)) ∧
      (weakCasOpts m₁ li expected (casOpts m₁ li expected))[c]? = some (pos, spurious) ∧
      (intOfBytes n ((m₁.atomics[li]!).msgs[pos]!).bytes).run = some (.ok old) ∧
      ((old = expected ∧ spurious = false ∧ r = none ∧ NoRace m₁ b o (intSize n) .atomicWrite ∧
          m' = rmwM (m₁.recordAt b o (intSize n) .atomicWrite) li pos succ
            ((m₁.atomics[li]!).msgs[pos]!) new) ∨
       (¬ (old = expected ∧ spurious = false) ∧ r = some old ∧ m' = loadM m₁ li fail ((m₁.atomics[li]!).msgs[pos]!))) := by
  unfold cmpxchgWeakAt at h
  obtain ⟨⟨li, opts⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, hnr, hl, rfl⟩ := weakCasPrep_ok hp
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i pos spurious hpos
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨old, m₃, hd, h₃⟩ := MemM.bind_ok h₂
    obtain ⟨hd, rfl⟩ := MemM.lift_ok hd
    refine ⟨pos, spurious, old, ha, hnr, hl, hpos, hd, ?_⟩
    split at h₃
    · rename_i he
      obtain ⟨_, m₄, hm, h₄⟩ := MemM.bind_ok h₃
      obtain ⟨hnw, rfl⟩ := casMarkWrite_ok ha hl hm
      obtain ⟨_, m₅, hw, h₅⟩ := MemM.bind_ok h₄
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₅
      exact .inl ⟨he.1, he.2, rfl, hnw, rmwWrite_ok hw⟩
    · rename_i he
      obtain ⟨_, m₄, ho, h₄⟩ := MemM.bind_ok h₃
      have := modify_ok ho
      subst this
      refine .inr ⟨he, ?_⟩
      unfold loadM
      cases hq : fail.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h₄ ⊢
      · obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₄
        exact ⟨rfl, rfl⟩
      · obtain ⟨_, m₅, hc, h₅⟩ := MemM.bind_ok h₄
        have := modify_ok hc
        subst this
        obtain ⟨rfl, rfl⟩ := MemM.pure_ok h₅
        exact ⟨rfl, rfl⟩
  · exact (MemM.throw_ok h₁).elim

/-- The postcondition must hold for every weak-CAS choice, including matching failure. -/
theorem WP.cmpxchgWeakC {Tgt γ σ : Type} {P : Proto Tgt γ} {t : ThreadId}
    {G : ThreadId → γ} {m : Mem} {n bits align : Nat} {p : Ptr}
    {succ fail : AtomicOrder} {expected new : BitVec bits} {s : σ}
    {Q : Option (BitVec bits) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → ∀ c,
        (c < weakCasCount bits succ align p expected { m₁ with current := t } ∨
         weakCasCount bits succ align p expected { m₁ with current := t } = 0 ∧ c = 0) →
        P.WP t ((Zig.callMC (cmpxchgWeakAt c succ fail align p expected new) :
          CM Tgt σ (Option (BitVec bits))).run s) Q G₁ { m₁ with current := t } k) :
    P.WP t ((Zig.cmpxchgWeakC succ fail align p expected new :
      CM Tgt σ (Option (BitVec bits))).run s) Q G m n := by
  show P.WP t (((Zig.pickC (weakCasCount bits succ align p expected) : CM Tgt σ Nat).run s) >>=
    fun r => (Zig.callMC (cmpxchgWeakAt r.1 succ fail align p expected new) :
      CM Tgt σ (Option (BitVec bits))).run r.2) Q G m n
  exact WP.bind (WP.pickC h)

/-- A retry client is safe when all permitted failures preserve its invariant and successful
writes establish its postcondition. Every repetition passes the CAS scheduler choice, so depth
is the safety induction measure; repeated spurious failures need not ever return. -/
theorem WP.weakCasRetry {Tgt γ σ : Type} {P : Proto Tgt γ} {t : ThreadId}
    {bits align : Nat} {p : Ptr} {succ fail : AtomicOrder} {expected new : BitVec bits}
    (inv : σ → (ThreadId → γ) → Mem → Nat → Prop)
    (post : Option (BitVec bits) × σ → (ThreadId → γ) → Mem → Nat → Prop)
    (step : ∀ s G m n, inv s G m n → P.WP t
      ((Zig.cmpxchgWeakC succ fail align p expected new : CM Tgt σ (Option (BitVec bits))).run s)
      (fun r G' m' d => if r.1.isSome then inv r.2 G' m' d ∧ d < n
        else post r G' m' d) G m n) :
    ∀ s G m n, inv s G m n → P.WP t
      ((Zig.loop (Zig.cmpxchgWeakC succ fail align p expected new :
        CM Tgt σ (Option (BitVec bits))) Option.isSome).run s) post G m n := by
  apply WP.loop _ _ inv (fun _ => 0) post
  intro s G m n hi
  apply WP.mono _ (step s G m n hi)
  intro r G' m' d hr
  cases ha : r.1.isSome
  · simpa only [ha, Bool.false_eq_true, ↓reduceIte] using hr
  · simp only [ha, ↓reduceIte] at hr ⊢
    exact ⟨hr.1, Or.inl hr.2⟩

end Proto
end Conc
end Zig
