import ZigLean.Conc.Own

/-!
# Concurrent separation logic

Each thread owns a part of the heap (`ZigLean/Conc/Own.lean`), and the parts move between the
threads at the sync ops. A proof over all schedules (`ZigLean/Conc/Logic.lean`) keeps them in its
invariant:

- **The parts** (`Owned own m`). `own u` is thread `u`'s part: each part is in `m.heap` with the
  same cells, two parts are disjoint, and each thread owns its part (`Mem.Owns`). A thread that
  does not exist has no part. A proof puts a thread's part in its ghost value: after a stop the
  thread knows only the invariant and its own ghost value, and `Owned` then tells it that its
  part is unchanged.
- **A step of a thread** (`Owned.step`, `WP.liftM_owned`). A `MemM` step with a thread triple
  (`TTriple`) on the thread's part changes only that part; the other parts stay.
- **Spawn** (`Owned.fork`). The parent gives a part of its heap to the new thread: the new
  thread's clock is the parent's.
- **Join** (`Owned.join`). The parent takes the joined thread's part: the join merges that
  thread's clock into the parent's.
- **Other steps** (`Owned.keep`). A step that changes no byte of a part, whose new footprint
  entries touch no part, and that makes no clock smaller keeps `Owned`: an atomic op on a
  location that no thread owns, a futex op, a stop.
-/

namespace Zig

open Assn

/-- Every cell of `h₁` is in `h`. -/
def Heap.Sub (h₁ h : Heap) : Prop := ∀ l c, h₁ l = some c → h l = some c

/-- The cells of `h` that `h₁` does not have. -/
def Heap.diff (h h₁ : Heap) : Heap := fun l => if h₁ l = none then h l else none

namespace Heap

variable {h h₁ h₂ : Heap}

theorem Sub.ne {l : Loc} (hs : h₁.Sub h) (hl : h₁ l ≠ none) : h l ≠ none := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hl
  rw [hs l c hc]; simp

theorem sub_union_left : h₁.Sub (h₁ ∪ h₂) := fun l c hc => by simp [hc]

theorem sub_union_right (hd : Disjoint h₁ h₂) : h₂.Sub (h₁ ∪ h₂) := fun l c hc => by
  rcases hd l with e | e
  · simp [e, hc]
  · rw [e] at hc; cases hc

theorem Sub.trans {h₃ : Heap} (h12 : h₁.Sub h₂) (h23 : h₂.Sub h₃) : h₁.Sub h₃ :=
  fun l c hc => h23 l c (h12 l c hc)

theorem union_sub {h₃ : Heap} (h1 : h₁.Sub h₃) (h2 : h₂.Sub h₃) : (h₁ ∪ h₂).Sub h₃ := by
  intro l c hc
  simp only [union_apply] at hc
  cases e : h₁ l with
  | none => rw [e] at hc; exact h2 l c (by simpa using hc)
  | some c' => rw [e] at hc; simp only [Option.some_or, Option.some.injEq] at hc; subst hc; exact h1 l _ e

/-- `h` is `h₁` and the rest. -/
theorem diff_split (hs : h₁.Sub h) : h = h₁ ∪ h.diff h₁ ∧ Disjoint h₁ (h.diff h₁) := by
  refine ⟨funext fun l => ?_, fun l => ?_⟩
  · cases e : h₁ l with
    | none => simp [diff, e]
    | some c => rw [Heap.union_apply, e, hs l c e]; rfl
  · cases e : h₁ l <;> simp [diff, e]

/-- A part disjoint from `h₁` is a part of the rest. -/
theorem sub_diff {h₃ : Heap} (hs : h₃.Sub h) (hd : Disjoint h₃ h₁) : h₃.Sub (h.diff h₁) := by
  intro l c hc
  rcases hd l with e | e
  · rw [e] at hc; cases hc
  · simp [diff, e, hs l c hc]

theorem disjoint_sub {h₃ : Heap} (hd : Disjoint h₁ h₂) (hs : h₃.Sub h₂) : Disjoint h₁ h₃ := by
  intro l
  rcases hd l with e | e
  · exact .inl e
  · right; cases e' : h₃ l with
    | none => rfl
    | some c => rw [hs l c e'] at e; cases e

end Heap

open Conc

/-- The threads' parts of the heap in `m` (module doc). -/
structure Owned (own : ThreadId → Heap) (m : Mem) : Prop where
  sub : ∀ u, (own u).Sub m.heap
  disj : ∀ u v, u ≠ v → Heap.Disjoint (own u) (own v)
  owns : ∀ u < m.threads.size, m.Owns u (own u)
  outside : ∀ u, m.threads.size ≤ u → own u = Heap.empty
  csize : m.clocks.size = m.threads.size

namespace Owned

variable {own : ThreadId → Heap} {m m' : Mem} {t : ThreadId}

theorem hne {u : ThreadId} {l : Loc} (ho : Owned own m) (hut : u ≠ t) (hl : own u l ≠ none) :
    own t l = none :=
  ((ho.disj u t hut l).resolve_left hl)

/-- The parts of the other threads are in the rest of the heap. -/
theorem sub_rest {u : ThreadId} (ho : Owned own m) (hut : u ≠ t) :
    (own u).Sub (m.heap.diff (own t)) :=
  Heap.sub_diff (ho.sub u) (ho.disj u t hut)

/-- A step of the current thread `t` with a thread triple (`StepIn` of the rest of the heap):
its part is the new one, `hQ`. -/
theorem step {hQ : Heap} (ho : Owned own m) (hc : m.current = t) (ht : t < m.threads.size)
    (hs : StepIn (m.heap.diff (own t)) m m') (hm' : m'.heap = hQ ∪ m.heap.diff (own t))
    (hd : Heap.Disjoint hQ (m.heap.diff (own t))) (howt : m'.Owns t hQ) :
    Owned (upd own t hQ) m' where
  sub u := by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hm']; exact Heap.sub_union_left
    · rw [upd_ne _ _ hu, hm']
      exact (ho.sub_rest hu).trans (Heap.sub_union_right hd)
  disj u v huv := by
    by_cases hu : u = t
    · subst hu; rw [upd_self, upd_ne _ _ (Ne.symm huv)]
      exact Heap.disjoint_sub hd (ho.sub_rest (Ne.symm huv))
    · by_cases hv : v = t
      · subst hv; rw [upd_self, upd_ne _ _ hu]
        exact (Heap.disjoint_sub hd (ho.sub_rest hu)).symm
      · rw [upd_ne _ _ hu, upd_ne _ _ hv]; exact ho.disj u v huv
  owns u hu := by
    by_cases hut : u = t
    · subst hut; rw [upd_self]; exact howt
    · rw [upd_ne _ _ hut]
      rw [hs.threads] at hu
      exact Mem.Owns.frame hs (hc ▸ hut) (ho.owns u hu) fun l hl => (ho.sub_rest hut).ne hl
  outside u hu := by
    rw [hs.threads] at hu
    rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact ho.outside u hu
  csize := by rw [hs.size, hs.threads]; exact ho.csize

/-- A step that changes no byte of a part, adds no footprint entry that touches a part (or a
block that does not exist), and makes no clock smaller. -/
theorem keep (ho : Owned own m) (hth : m'.threads.size = m.threads.size)
    (hcs : m'.clocks.size = m.clocks.size) (hheap : ∀ u, (own u).Sub m'.heap)
    (hblk : m.blocks.size ≤ m'.blocks.size)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
      (e.block < m'.blocks.size ∧ ∀ u, ¬ e.Touches (own u))) :
    Owned own m' where
  sub := hheap
  disj := ho.disj
  owns u hu := by
    rw [hth] at hu
    intro e he htc
    rcases hfp e he with he' | ⟨hb, hnt⟩
    · exact VClock.le_trans (ho.owns u hu e he' (htc.imp id fun h => Nat.le_trans hblk h)) (hcl u hu)
    · rcases htc with htc | hb'
      · exact absurd htc (hnt u)
      · exact absurd hb' (Nat.not_le.mpr hb)
  outside u hu := ho.outside u (hth ▸ hu)
  csize := by rw [hcs, hth]; exact ho.csize

/-- A stop: only `current` changes. -/
theorem current (ho : Owned own m) (t : ThreadId) : Owned own { m with current := t } :=
  ⟨ho.sub, ho.disj, ho.owns, ho.outside, ho.csize⟩

/-- Spawn: the parent `t` gives `h₂` of its part `h₁ ∪ h₂` to the new thread. -/
theorem fork {h₁ h₂ : Heap} {c : ThreadId} (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = h₁ ∪ h₂) (hd12 : Heap.Disjoint h₁ h₂)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t h₁) c h₂) m' := by
  rw [Proto.fork_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have hcs := ho.csize
  have hne : m.threads.size ≠ t := by unfold ThreadId at *; omega
  have hsub1 : h₁.Sub (own t) := by rw [hsplit]; exact Heap.sub_union_left
  have hsub2 : h₂.Sub (own t) := by rw [hsplit]; exact Heap.sub_union_right hd12
  -- The clocks after the fork.
  have hclk : ∀ u, ((m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push
      (VClock.bump (m.clocks[t]!) t))[u]! =
      if u = m.threads.size then VClock.bump (m.clocks[t]!) t
      else if u = t then VClock.bump (m.clocks[t]!) t else m.clocks[u]! := by
    intro u
    have htc : t < m.clocks.size := hcs ▸ ht
    by_cases hu : u < m.clocks.size
    · rw [getElem!_pos _ u (by simp only [Array.size_push, Array.size_set!]; omega),
        Array.getElem_push_lt (by simpa using hu), ← getElem!_pos, Proto.getElem!_set!_ite]
      have hu' : u ≠ m.threads.size := by rw [← hcs]; omega
      by_cases hut : u = t
      · subst hut; simp [hu', htc]
      · simp [hu', hut]
    · by_cases he : u = m.clocks.size
      · subst he
        rw [getElem!_pos _ _ (by simp only [Array.size_push, Array.size_set!]; omega)]
        simp [Array.getElem_push, hcs]
      · rw [getElem!_neg _ u (by simp only [Array.size_push, Array.size_set!]; omega),
          getElem!_neg _ u hu]
        have h1 : u ≠ m.threads.size := by rw [← hcs]; exact he
        have h2 : u ≠ t := by intro h; subst h; exact hu htc
        simp [h1, h2]
  refine ⟨fun u => ?_, fun u v huv => ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · by_cases hc : u = m.threads.size
    · subst hc; rw [upd_self]; exact hsub2.trans (ho.sub t)
    · rw [upd_ne _ _ hc]
      by_cases hu : u = t
      · subst hu; rw [upd_self]; exact hsub1.trans (ho.sub u)
      · rw [upd_ne _ _ hu]; exact ho.sub u
  · -- The parts after the spawn: `h₁` and `h₂` come from `t`'s part.
    have hpart : ∀ w, (upd (upd own t h₁) m.threads.size h₂ w).Sub
        (if w = t ∨ w = m.threads.size then own t else own w) := by
      intro w
      by_cases hc : w = m.threads.size
      · subst hc; rw [upd_self]; simp only [or_true, ↓reduceIte]; exact hsub2
      · rw [upd_ne _ _ hc]
        by_cases hw : w = t
        · subst hw; rw [upd_self]; simp; exact hsub1
        · rw [upd_ne _ _ hw]; simp [hw, hc]; exact fun _ _ h => h
    by_cases hut : (u = t ∨ u = m.threads.size) ∧ (v = t ∨ v = m.threads.size)
    · -- `t` and the new thread: `h₁` and `h₂`.
      rcases hut with ⟨rfl | rfl, rfl | rfl⟩
      · exact absurd rfl huv
      · rw [upd_self, upd_ne _ _ huv, upd_self]; exact hd12
      · rw [upd_self, upd_ne _ _ (Ne.symm huv), upd_self]; exact hd12.symm
      · exact absurd rfl huv
    · have hu' := hpart u
      have hv' := hpart v
      have base : Heap.Disjoint (if u = t ∨ u = m.threads.size then own t else own u)
          (if v = t ∨ v = m.threads.size then own t else own v) := by
        by_cases hu : u = t ∨ u = m.threads.size
        · have hv : ¬ (v = t ∨ v = m.threads.size) := fun hv => hut ⟨hu, hv⟩
          simp only [hu, hv, ↓reduceIte]
          by_cases hvs : m.threads.size ≤ v
          · rw [ho.outside v hvs]; exact Heap.disjoint_empty _
          · exact ho.disj t v fun h => hv (.inl h.symm)
        · simp only [hu, ↓reduceIte]
          by_cases hv : v = t ∨ v = m.threads.size
          · simp only [hv, ↓reduceIte]
            by_cases hus : m.threads.size ≤ u
            · rw [ho.outside u hus]; exact (Heap.disjoint_empty _).symm
            · exact ho.disj u t fun h => hu (.inl h)
          · simp only [hv, ↓reduceIte]; exact ho.disj u v huv
      exact Heap.disjoint_sub (Heap.disjoint_sub base.symm hu').symm hv'
  · -- Ownership: the footprint and the blocks are the same; no clock is smaller.
    simp only [Array.size_push] at hu
    show Mem.OwnsC _ _ _
    rw [hclk]
    by_cases hc : u = m.threads.size
    · subst hc; rw [upd_self]; simp only [↓reduceIte]
      exact ((ho.owns t ht).sub fun l hl => hsub2.ne hl).mono (VClock.le_bump _ _)
    · rw [upd_ne _ _ hc]
      simp only [hc, ↓reduceIte]
      by_cases hu' : u = t
      · subst hu'; rw [upd_self]; simp only [↓reduceIte]
        exact ((ho.owns u ht).sub fun l hl => hsub1.ne hl).mono (VClock.le_bump _ _)
      · rw [upd_ne _ _ hu']; simp only [hu', ↓reduceIte]
        exact ho.owns u (by omega)
  · simp only [Array.size_push] at hu
    rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
    exact ho.outside u (by omega)
  · simp [hcs]

/-- Join: the parent `t` takes the part of thread `u`, which has ended. -/
theorem join {u : ThreadId} (ho : Owned own m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    Owned (upd (upd own t (own t ∪ own u)) u Heap.empty) m' := by
  unfold Thread.join at hj
  cases hr : m.threads[u]? with
  | none =>
    simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift]
  | some rec =>
    by_cases hc : (rec.spawner != t || rec.joined) = true
    · simp_all [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, throw, throwThe,
        MonadExceptOf.throw, StateT.lift]
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      simp [hr, hc1, hc2, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.set, set,
        MonadStateOf.set, pure, ExceptT.pure] at hj
      subst hj
      have hul : u < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
      have hcs := ho.csize
      have hdtu := ho.disj t u (Ne.symm hut)
      have hclk : ∀ w, (m.clocks.setIfInBounds t (VClock.merge (VClock.bump (m.clocks[t]!) t)
          (m.clocks[u]!)))[w]! = if w = t then VClock.merge (VClock.bump (m.clocks[t]!) t)
          (m.clocks[u]!) else m.clocks[w]! := by
        intro w
        rw [← Array.set!_eq_setIfInBounds, Proto.getElem!_set!_ite]
        by_cases hw : w = t
        · simp [hw, show t < m.clocks.size from hcs ▸ ht]
        · simp [hw]
      refine ⟨fun w => ?_, fun w v hwv => ?_, fun w hw => ?_, fun w hw => ?_, by simp [hcs]⟩
      · by_cases hw : w = u
        · subst hw; rw [upd_self]; intro l c hc; cases hc
        · rw [upd_ne _ _ hw]
          by_cases hwt : w = t
          · subst hwt; rw [upd_self]; exact Heap.union_sub (ho.sub w) (ho.sub u)
          · rw [upd_ne _ _ hwt]; exact ho.sub w
      · -- The part of `u` is now `t`'s; `u` has none.
        have part : ∀ x, x ≠ u → (upd (upd own t (own t ∪ own u)) u Heap.empty x) =
            if x = t then own t ∪ own u else own x := by
          intro x hx; rw [upd_ne _ _ hx]
          by_cases hxt : x = t
          · subst hxt; simp
          · rw [upd_ne _ _ hxt]; simp [hxt]
        by_cases hw : w = u
        · subst hw; rw [upd_self]; intro l; exact .inl rfl
        by_cases hv : v = u
        · subst hv; rw [upd_self]; exact Heap.disjoint_empty _
        rw [part w hw, part v hv]
        have hdU : ∀ x, x ≠ t → x ≠ u → Heap.Disjoint (own t ∪ own u) (own x) := fun x hxt hxu =>
          fun l => by
            rcases ho.disj t x (Ne.symm hxt) l with e | e
            · rcases ho.disj u x (Ne.symm hxu) l with e' | e'
              · left; simp [e, e']
              · exact .inr e'
            · exact .inr e
        by_cases hwt : w = t
        · subst hwt; simp only [↓reduceIte, Ne.symm hwv]
          exact hdU v (Ne.symm hwv) hv
        · by_cases hvt : v = t
          · subst hvt; simp only [hwt, ↓reduceIte]; exact (hdU w hwt hw).symm
          · simp only [hwt, hvt, ↓reduceIte]; exact ho.disj w v hwv
      · simp only [Array.size_setIfInBounds] at hw
        show Mem.OwnsC _ _ _
        dsimp only
        rw [hclk]
        by_cases hwu : w = u
        · subst hwu; rw [upd_self]
          simp only [hut, ↓reduceIte]
          exact (ho.owns w hul).sub fun l hl => absurd rfl hl
        · rw [upd_ne _ _ hwu]
          by_cases hwt : w = t
          · subst hwt; rw [upd_self]; simp only [↓reduceIte]
            exact Mem.OwnsC.union
              ((ho.owns w ht).mono (VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)))
              ((ho.owns u hul).mono (VClock.le_merge_right _ _))
          · rw [upd_ne _ _ hwt]; simp only [hwt, ↓reduceIte]; exact ho.owns w hw
      · simp only [Array.size_setIfInBounds] at hw
        rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
        exact ho.outside w hw

end Owned

/-! ## In a thread -/

namespace Conc
namespace Proto

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Heap}

/-- A `MemM` step of thread `t` with a thread triple on its part `own t`: after it, `t`'s part
is the triple's post, and the other parts are unchanged. -/
theorem WP.liftMem_owned {x : MemM α} {Pa : Assn} {Qa : α → Assn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : TTriple Pa x Qa) (ho : Owned own m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' hQ, Owned (upd own t hQ) m' → Qa a hQ → StepIn (m.heap.diff (own t)) m m' →
      m'.heap = hQ ∪ m.heap.diff (own t) → Q a G m' n) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨hm, hd⟩ := Heap.diff_split (ho.sub t)
  have hcs : m.current < m.clocks.size := by rw [hc, ho.csize]; exact htl
  have hx := ht m (own t) _ hd hm hp hcs (hc ▸ ho.owns t htl)
  refine WP.liftMem (fun e he => ?_) fun a m' hr => ?_
  · rw [he] at hx; exact hx.elim
  · rw [hr] at hx
    obtain ⟨hQ, hd', hm', hq, ho', hs⟩ := hx
    have ho'' : m'.Owns t hQ := by rw [hs.current, hc] at ho'; exact ho'
    exact ⟨by rw [hs.threads],
      h a m' hQ (ho.step hc htl hs hm' hd' ho'') hq hs hm'⟩

/-- `WP.liftMem_owned` for a step of generated code (`liftM`). -/
theorem WP.liftM_owned {x : MemM α} {s : σ} {Pa : Assn} {Qa : α → Assn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : TTriple Pa x Qa) (ho : Owned own m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' hQ, Owned (upd own t hQ) m' → Qa a hQ → StepIn (m.heap.diff (own t)) m m' →
      m'.heap = hQ ∪ m.heap.diff (own t) → Q (a, s) G m' n) :
    P.WP t ((_root_.liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (WP.liftMem_owned ht ho hc htl hp fun a m' hQ ho' hq hs hm' =>
    WP.pure' (h a m' hQ ho' hq hs hm'))

end Proto
end Conc

end Zig
