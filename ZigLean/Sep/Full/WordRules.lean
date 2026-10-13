import ZigLean.Sep.Full.Word
import ZigLean.Conc.WeakWord

/-!
# The rules of the ops at a shared word, over full-state resources

The ops of a sync object's code at a shared word (the state and the epoch of a condition, the
state of an event; `ZigLean/Sep/Full/Word.lean`), proved once for every protocol that has a lock
(`FLock.FitsOn`) and keeps the word's cells in its rest (`Word.InRest`: the protocol's `U` says
that its rest `rX` is the word's cells and a rest `rY` without the word's bytes, and that the
word is `Ok`). Each rule is the stop (the pick of the op, or the futex op) and then the op; it
hands the client the facts of the memory model about the op (`Word.Ok.load`, `Ok.rmw`, `Ok.cas`,
`Ok.weakCas`, `Ok.futexWait`; `ZigLean/Conc/Word.lean`) and the lock's invariant after the op, whose
rest has the word's new cells (`FLock.Inv.wordOp`). The client shows its `U` after the op.

| Rule | Op |
|---|---|
| `wp_wordLoad`, `wp_wordLoadAs` | atomic load (bits, or decoded) |
| `wp_wordRmw`, `wp_wordRmwAs` | atomic RMW (bits, or decoded) |
| `wp_wordCas`, `wp_wordCasAs` | strong `cmpxchg` (bits, or decoded) |
| `wp_wordWeakCas`, `wp_wordWeakCasAs` | weak `cmpxchg` (bits, or decoded) |
| `wp_wordWake` | futex wake at the word |
| `wp_wordWait` | futex wait at the word, by a thread out of the lock's code (`away` while it waits) |
| `wp_liftPartW` | a step of a thread on its own part (a stack block of the sync object's code) |
-/

namespace Zig

namespace Conc
namespace Word

open Full

/-- The protocol's rest has the word's cells: for each `U G rX m`, the word is `Ok` and `rX` is
its cells and a rest without its bytes. -/
def InRest {γ : Type} (W : Word 32 4) (U : (ThreadId → γ) → Res → Mem → Prop) : Prop :=
  ∀ G rX m, U G rX m → W.Ok m ∧ ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none

end Word
end Conc

namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {L : FLock γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {W : Word 32 4}

/-- The invariant at a stop of `t` (`current := t`), with the word's cells in the rest. -/
theorem FitsOn.stopW (hP : L.FitsOn P U ok) (hW : W.InRest U) {G₁ : ThreadId → γ} {m₁ : Mem}
    {t : ThreadId} (hi₁ : P.inv G₁ m₁) (hok : ok (G₁ t)) (hgone : L.ph (G₁ t) ≠ .gone) :
    ∃ rY, L.Inv G₁ (rsum (W.cellsR { m₁ with current := t }) rY) { m₁ with current := t } ∧
      U G₁ (rsum (W.cellsR { m₁ with current := t }) rY) { m₁ with current := t } ∧
      (∀ l, W.In l → rY.heap l = none) ∧ W.Ok { m₁ with current := t } ∧
      t < m₁.threads.size ∧ m₁.clocks.size = m₁.threads.size := by
  obtain ⟨rX, hiL, hU, -⟩ := hP.cur t hi₁ hok hgone
  have hU' := hP.curU t hU hok hgone
  obtain ⟨hw, rY, rfl, hY⟩ := hW G₁ rX _ hU'
  exact ⟨rY, hiL, hU', hY, hw, (hiL.ht hgone).1, hiL.w.csize⟩

variable {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}

/-- An atomic load of a `u32` at the word (`atomicLoadC`), by thread `t` (`g`). -/
theorem wp_wordLoad (hP : L.FitsOn P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {ord : AtomicOrder} (hok : ok g) (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' v j, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      Q (v, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) ord 4 W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.load_noErr ht hcs hcr e he).elim) fun v m' hr => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hw.load rfl ht hcs hr
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' v j hg₁ rfl hU hY hj hv hfl hacq hh hw' hop
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- An atomic load at the word with a decode (`atomicLoadAsC`), by thread `t` (`g`). -/
theorem wp_wordLoadAs {α : Type} [Packed α 32] (hP : L.FitsOn P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {ord : AtomicOrder} (hok : ok g) (hgone : L.ph g ≠ .gone)
    (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' b r j, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) →
      (Packed.ofBits? (α := α) b).run = some (.ok r) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α ord 4 W.ptr : CM Tgt σ α).run s) Q G m n := by
  unfold atomicLoadAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (atomicLoadAs_noErr (hw.load_noErr ht hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨j, hj, hv, -⟩ := hw.load rfl ht hcs hr
    exact hdec G₁ rY _ hg₁ rfl hU j hj b hv
  obtain ⟨b, hb, hd⟩ := atomicLoadAs_ok hr
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hw.load rfl ht hcs hb
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' b r j hg₁ rfl hU hY hd hj hv hfl hacq hh hw' hop
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- An RMW of a `u32` at the word (`atomicRmwC`), by thread `t` (`g`): it reads the newest write
`old`, and its write is the newest. -/
theorem wp_wordRmw (hP : L.FitsOn P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec 32} (hok : ok g)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' old, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) →
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]! (op.apply signed old v)) →
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' → Q (old, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC op signed ord 4 W.ptr v : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.rmw_noErr ht hcs hcr e he).elim) fun old m' hr => ?_
  obtain ⟨hv, hw', hop, hH, hh, hacq⟩ := hw.rmw rfl ht hcs hr
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' old hg₁ rfl hU hY hv hH hh hacq hw' hop
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- An RMW at the word with a decode (`atomicRmwAsC`), by thread `t` (`g`). -/
theorem wp_wordRmwAs {α : Type} [Packed α 32] (hP : L.FitsOn P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {op : RmwOp} {ord : AtomicOrder} {v : α} (hok : ok g)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ b, (W.hist m₁)[(W.hist m₁).size - 1]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' old r, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val old →
      W.Holds m' (op.apply false old (Packed.toBits v)) →
      W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]!
        (op.apply false old (Packed.toBits v))) →
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC op ord 4 W.ptr v : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (atomicRmwAs_noErr (hw.rmw_noErr ht hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨hv, -⟩ := hw.rmw rfl ht hcs hr
    exact hdec G₁ rY _ hg₁ rfl hU b hv
  obtain ⟨old, hb, hd⟩ := atomicRmwAs_ok hr
  obtain ⟨hv, hw', hop, hH, hh, hacq⟩ := hw.rmw rfl ht hcs hb
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' old r hg₁ rfl hU hY hd hv hH hh hacq hw' hop
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- A strong `cmpxchg` at the word with a decode (`cmpxchgAsC`), by thread `t` (`g`): on success
an RMW of the newest write, which holds `exp`; on failure a read of write `j`. -/
theorem wp_wordCasAs {α : Type} [Packed α 32] (hP : L.FitsOn P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {succ fail : AtomicOrder} {exp new : α} (hok : ok g)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! (Packed.toBits new)) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, b ≠ Packed.toBits exp → (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (cmpxchgAs_noErr (hw.cas_noErr (fail := fail)
    (new := Packed.toBits new) ht hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, -, hj, hv, -⟩⟩ := hw.cas rfl ht hcs hr
    · cases he
    · cases he
      exact hdec G₁ rY _ hg₁ rfl hU j hj _ hv
  rcases cmpxchgAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hH, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hw.cas rfl ht hcs ho
    · exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop
        (hiL.wordOp hY hw hw' hop hap)).1 hv hH hh hacq⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hne, hj, hv, hfl, hacq, hh⟩⟩ := hw.cas rfl ht hcs ho
    · cases he
    · cases he
      exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop
        (hiL.wordOp hY hw hw' hop hap)).2 j b v hne hd hj hv hfl hacq hh⟩

/-- A strong `cmpxchg` of a `u32` at the word (`cmpxchgC`), by thread `t` (`g`): on success an
RMW of the newest write, which holds `exp`; on failure a read of write `j`, whose value is not
`exp`. -/
theorem wp_wordCas (hP : L.FitsOn P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {succ fail : AtomicOrder} {exp new : BitVec 32} (hok : ok g) (hgone : L.ph g ≠ .gone)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val exp → W.Holds m' new →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! new) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b, b ≠ exp → j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b →
        Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgC (n := 32) succ fail 4 W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.cas_noErr (fail := fail) (new := new) ht hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hop, hcase⟩ := hw.cas rfl ht hcs hr
  have hk := h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop (hiL.wordOp hY hw hw' hop hap)
  refine ⟨by rw [hop.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hH, hh, hacq⟩ | ⟨j, b, rfl, hne, hj, hv, hfl, hacq, hh⟩
  · exact hk.1 hv hH hh hacq
  · exact hk.2 j b hne hj hv hfl hacq hh

/-- A weak `cmpxchg` of a `u32` at the word (`cmpxchgWeakC`), by thread `t` (`g`): on success an
RMW of the newest write, which holds `exp`; on failure (spurious ones too) a read of write `j`. -/
theorem wp_wordWeakCas (hP : L.FitsOn P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {succ fail : AtomicOrder} {exp new : BitVec 32} (hok : ok g) (hgone : L.ph g ≠ .gone)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val exp → W.Holds m' new →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! new) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b, j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b →
        Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakC (n := 32) succ fail 4 W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgWeakC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.weakCas_noErr (fail := fail) (new := new) ht hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hop, hcase⟩ := hw.weakCas rfl ht hcs hr
  have hk := h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop (hiL.wordOp hY hw hw' hop hap)
  refine ⟨by rw [hop.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hH, hh, hacq⟩ | ⟨j, b, rfl, hj, hv, hfl, hacq, hh⟩
  · exact hk.1 hv hH hh hacq
  · exact hk.2 j b hj hv hfl hacq hh

/-- A weak `cmpxchg` at the word with a decode (`cmpxchgWeakAsC`), by thread `t` (`g`). -/
theorem wp_wordWeakCasAs {α : Type} [Packed α 32] (hP : L.FitsOn P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {succ fail : AtomicOrder} {exp new : α} (hok : ok g)
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' → L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! (Packed.toBits new)) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgWeakAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hok) (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (cmpxchgWeakAs_noErr (hw.weakCas_noErr (fail := fail)
    (new := Packed.toBits new) ht hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, hj, hv, -⟩⟩ := hw.weakCas rfl ht hcs hr
    · cases he
    · cases he
      exact hdec G₁ rY _ hg₁ rfl hU j hj _ hv
  rcases cmpxchgWeakAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hH, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hw.weakCas rfl ht hcs ho
    · exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop
        (hiL.wordOp hY hw hw' hop hap)).1 hv hH hh hacq⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hj, hv, hfl, hacq, hh⟩⟩ := hw.weakCas rfl ht hcs ho
    · cases he
    · cases he
      exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop
        (hiL.wordOp hY hw hw' hop hap)).2 j b v hd hj hv hfl hacq hh⟩

/-- A futex wake at the word (`futexWakeC`), by thread `t` (`g`): the lock's invariant holds with
the same rest; the client shows its `U` after the wake. -/
theorem wp_wordWake (hP : L.FitsOn P U ok) (hap : W.ApartL L.toLockWord) {io : Io}
    {c : BitVec 32} (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rX m₁ cs m', G₁ t = g → U G₁ rX m₁ →
      ((Thread.futexWake W.ptr c.toNat cs).run { m₁ with current := t }).run =
        some (.ok ((), m')) → L.Inv G₁ rX m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io W.ptr c : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWakeC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ cs m' hw => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  exact h k hk G₁ rX m₁ cs m' hg₁ hU hw (hiL.wakeOff hap hw)

/-- **A futex wait at the word** (`futexWaitC`, the bits `e`) by thread `t` out of the lock's
code (`g`, at `out`): while it waits it is `away` (`L.set g .away rnil`). The client says that
its `U` lets `t` go away (`hUa`), that `t` is not the last thread while it waits (`hlive`), that
`U` holds when `t` sleeps (the kernel's read, an op `M` that keeps the word's writes, read `e`;
`hUs`), and that `U` holds with `t` back at `out` after the kernel's read, a wake that was
pending, or a spurious return (`hUo`). It goes on at `g`. -/
theorem wp_wordWait (hP : L.FitsOn P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {ε : Type} {w : Nat} [Packed ε w] {io : Io} {e : ε} (hok : ok g) (hg : L.ph g = .out)
    (hi : P.inv (upd G t g) m)
    (hUa : ∀ rX, U (upd G t g) rX m → U (upd G t (L.set g .away rnil)) rX m)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Op t { m₁ with current := t } M → W.hist M = W.hist m₁ → W.Ok M → M.blocks = m₁.blocks →
      W.Holds m₁ ((Packed.toBits e).setWidth 32) →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.ptr) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) → (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Op t { m₁ with current := t } M ∧ W.hist M = W.hist m₁ ∧ W.Ok M ∧
          M.blocks = m₁.blocks)) →
      U (upd G₁ t g) (rsum (W.cellsR m₁) rY) M)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → P.inv (upd G₁ t g) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io W.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  have hph : L.ph (L.set g .away rnil) = .away := L.ph_set _ _ _
  -- `t` holds nothing at `out`, so `g` is `g` with the place `out`
  obtain ⟨rX₀, hiL₀, hU₀⟩ := (hP.inv _ _).mp hi
  have hgo : L.set (L.set g .away rnil) .out rnil = g := by
    have hheld : L.held g = rnil := by
      have := hiL₀.idle t (by rw [upd_self, hg]; decide); rwa [upd_self] at this
    rw [L.set_set, ← hg, ← hheld, L.set_self]
  -- `t` goes away
  have hia : P.inv (upd G t (L.set g .away rnil)) m := by
    have hl := hiL₀.ghost (t := t) (g := L.set g .away rnil) (by rw [upd_self]; exact hg)
      (.inr (.inr hph)) (by rw [upd_self, L.part_set]) (L.held_set _ _ _)
      (fun _ => hiL₀.ht (t := t) (by rw [upd_self, hg]; decide))
      (fun r hr => by
        have := (L.R_set (upd G t g) t .away rnil r).mpr hr
        rwa [upd_self] at this)
    rw [upd_upd] at hl
    exact (hP.inv _ _).mpr ⟨rX₀, hl, hUa _ hU₀⟩
  refine WP.futexWaitC fun k hk => ⟨L.set g .away rnil, hia, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  obtain ⟨hw, rY, rfl, hY⟩ := hW G₁ rX m₁ hU
  have hph₁ : L.ph (G₁ t) = .away := by rw [hg₁]; exact hph
  have ht0 : t < m₁.threads.size := (hiL.ht (by rw [hph₁]; decide)).1
  have hw₀ : W.Ok { m₁ with current := t } :=
    hw.keep (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _)
  have hX : ∀ l, W.In l → (rsum (W.cellsR m₁) rY).heap l ≠ none := fun l hl => by
    simp only [FHeap.union_apply, cellsAt_of hl]
    cases e : m₁.heap l with
    | none => exact absurd e (hw.cellIn hl)
    | some c => simp
  -- back at `out`: `upd G₁ t g` is `upd G₁ t (L.set (G₁ t) .out rnil)`
  have hback : upd G₁ t (L.set (G₁ t) .out rnil) = upd G₁ t g := by rw [hg₁, hgo]
  refine ⟨fun _ => hlive G₁ m₁ hg₁ hi₁, fun hq => ⟨fun _ => hw₀.futexWait_run ht0, fun b m' hr => ?_⟩⟩
  have hl := hiL.waitOff hph₁ hw hap hX hq hr
  rcases hw₀.futexWait rfl ht0 hiL.w.csize hr with
    ⟨-, rfl, rfl⟩ | ⟨-, M, hok₂, hop, hh, hbl, ⟨hU32, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨-, hl'⟩ := hl
    rw [hback] at hl'
    exact h k hk G₁ _ rfl ((hP.inv _ _).mpr ⟨_, hl', hUo G₁ rY m₁ _ hg₁ hU hY (.inl rfl)⟩)
  · simp only [↓reduceIte] at hl ⊢
    have hs := hiL.spuriousOff hph₁ hq
    rw [hback] at hs
    exact ⟨(hP.inv _ _).mpr ⟨_, hl, hUs G₁ rY m₁ M hg₁ hU hY hop hh hok₂ hbl hU32⟩,
      h k hk G₁ _ rfl ((hP.inv _ _).mpr ⟨_, hs, hUo G₁ rY m₁ _ hg₁ hU hY (.inr (.inl rfl))⟩)⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨hc, hl'⟩ := hl
    rw [hback] at hl'
    exact h k hk G₁ _ hc
      ((hP.inv _ _).mpr ⟨_, hl', hUo G₁ rY m₁ _ hg₁ hU hY (.inr (.inr ⟨hop, hh, hok₂, hbl⟩))⟩)

/-- The rest with the word's cells of a memory whose word cells are the same up to `Cell.norm`. -/
theorem Inv.restW {G : ThreadId → γ} {rY : Res} {m m' : Mem}
    (hi : L.Inv G (rsum (W.cellsR m) rY) m')
    (hcells : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    L.Inv G (rsum (W.cellsR m') rY) m' := by
  refine hi.congrX (fun l => ?_) (by simp [Word.cellsR, cellsAt])
    (by simp [Word.cellsR, cellsAt])
  simp only [FHeap.union_apply]
  by_cases hl : W.In l
  · simp only [Word.cellsR, cellsAt_of hl]
    have := hcells l hl
    cases e : m.heap l <;> cases e' : m'.heap l <;> simp_all [Option.map]
  · simp [Word.cellsR, cellsAt_none hl]

/-- **A step of thread `t` on its own part** (out of the lock's code, `g`; a stack block of a
sync object's code), with a thread triple: the client gets the rest with the word's cells before
the step, the step (`StepIn`, `KeepK`: the word stays), and the lock's invariant after it, with
`t`'s part the triple's post (`FLock.setPart`) and the word's new cells. -/
theorem wp_liftPartW (hP : L.FitsOn P U ok) (hW : W.InRest U) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r' rY, (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      U (upd G t g) (rsum (W.cellsR m) rY) m → (∀ l, W.In l → rY.heap l = none) →
      StepIn (rsum (W.cellsR m) rY).heap.erase m m' → W.KeepK m m' →
      L.Inv (upd G t (L.setPart g r')) (rsum (W.cellsR m') rY) m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨rX, hL, hU⟩ := (hP.inv _ _).mp hi
  obtain ⟨hw, rY, rfl, hY⟩ := hW _ _ _ hU
  refine hL.wp_liftPart hc hgo htt hp (fun a m' r' hr hq hs hc' hL' => ?_) hret
  have hcells : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => hL'.cellsN hl (hw.cellIn hl)
  have hwF : ∀ l, W.In l → (rsum (W.cellsR m) rY).heap.erase l ≠ none := fun l hl => by
    have := cellsAt_some hl (hw.cellIn hl) (m := m)
    simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
      Option.or_eq_none_iff, not_and]
    intro h; exact absurd h this
  exact h a m' r' rY hr hq hc' hU hY hs (Word.keepK_stepIn hs hwF hcells) (hL'.restW hcells)

end FLock

end Full
end Zig
