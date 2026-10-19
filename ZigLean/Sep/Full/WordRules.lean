import ZigLean.Sep.Full.Word
import ZigLean.Conc.WeakWord

/-!
# The rules of the ops at a shared word, over full-state resources

The ops of a sync object's code at a shared word (the state and the epoch of a condition, the
state of an event; `ZigLean/Sep/Full/Word.lean`), proved once for every protocol that has a lock
(`FLock.Fits`, with any primitive next to it) and keeps the word's cells in its rest (`Word.InRest`: the protocol's `U` says
that its rest `rX` is the word's cells and a rest `rY` without the word's bytes, and that the
word is `Ok`). Each rule is the stop (the pick of the op, or the futex op) and then the op; it
hands the client the facts of the memory model about the op (`Word.Ok.load`, `Ok.rmw`, `Ok.cas`,
`Ok.weakCas`, `Ok.futexWait`; `ZigLean/Conc/Word.lean`) and the lock's invariant after the op, whose
rest has the word's new cells (`FLock.Inv.wordOp`). The client shows its `U` after the op.

The continuations also receive the actual reader's resulting floor (or the new last position
for a write), conditionally on the invariant's existing `Word.Fresh`. This is information
derived from the primitive run, not an initial precondition. A read's witness has the returned
value; it need not be the separate happens-before witness when several writes have equal bytes.

| Rule | Op |
|---|---|
| `wp_wordLoad`, `wp_wordLoadAs` | atomic load (bits, or decoded) |
| `wp_wordRmw`, `wp_wordRmwAs` | atomic RMW (bits, or decoded) |
| `wp_wordCas`, `wp_wordCasAs` | strong `cmpxchg` (bits, or decoded) |
| `wp_wordWeakCas`, `wp_wordWeakCasAs` | weak `cmpxchg` (bits, or decoded) |
| `wp_wordWake` | futex wake at the word |
| `wp_wordWait` | futex wait at the word, by a thread out of the lock's code (`away` while it waits) |
| `wp_wordOsWake` | OS futex wake at the word (`Os.futexWake`, OSF-02) |
| `wp_wordOsWait` | untimed OS futex wait at the word (`Os.futexWait`, OSF-01): the kernel's compare at `out`, the sleep `away` |
| `wp_liftPartW` | a step of a thread on its own part (a stack block of the sync object's code) |

From `ZigLean/Conc/Word.lean` and `ZigLean/Conc/WeakWord.lean` (`Ok.weakCas`) this file uses only
facts of the memory model; it uses none of the legacy concurrent logic there (`Conc.Lock`,
`Lock.Inv`, `Lock.Inv.wordOp`, `offWord`).
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
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {W : Word 32 4} {K : FPrim γ}

/-- The invariant at a stop of `t` (`current := t`), with the word's cells in the rest. -/
theorem Fits.stopW (hP : L.Fits K P U ok) (hW : W.InRest U) {G₁ : ThreadId → γ} {m₁ : Mem}
    {t : ThreadId} (hi₁ : P.inv G₁ m₁) (hgone : L.ph (G₁ t) ≠ .gone) :
    ∃ rY, L.Inv G₁ (rsum (W.cellsR { m₁ with current := t }) rY) { m₁ with current := t } ∧
      U G₁ (rsum (W.cellsR { m₁ with current := t }) rY) { m₁ with current := t } ∧
      (∀ l, W.In l → rY.heap l = none) ∧ W.Ok { m₁ with current := t } ∧
      t < m₁.threads.size ∧ m₁.clocks.size = m₁.threads.size := by
  obtain ⟨rX, hiL, hU, -⟩ := hP.cur t hi₁ hgone
  have hU' := hP.curU t hU hgone
  obtain ⟨hw, rY, rfl, hY⟩ := hW G₁ rX _ hU'
  exact ⟨rY, hiL, hU', hY, hw, (hiL.ht hgone).1, hiL.w.csize⟩

variable {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}

/-- An atomic load of a `u32` at the word (`atomicLoadC`), by thread `t` (`g`). -/
theorem wp_wordLoad (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {ord : AtomicOrder} (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' v j, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → ∃ i < (W.hist m').size,
        (W.hist m')[i]!.Val v ∧ W.ownPos m' t = i) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      Q (v, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) ord 4 W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.load_noErr ht hcs hcr e he).elim) fun v m' hr => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hw.load rfl ht hcs hr
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.atomicLoad_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hr
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' v j hg₁ rfl hU hY hj hv hfl hacq hh hw' hop hA (fun hf => let hs := Word.atomicLoad_seen hw hf hr; ⟨hs.1, hs.2.1⟩)
    (fun hf => (Word.atomicLoad_read_seen hw hf hr).2.2)
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- An atomic load at the word with a decode (`atomicLoadAsC`), by thread `t` (`g`). -/
theorem wp_wordLoadAs {α : Type} [Packed α 32] (hP : L.Fits K P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {ord : AtomicOrder} (hgone : L.ph g ≠ .gone)
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
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → ∃ i < (W.hist m').size,
        (W.hist m')[i]!.Val b ∧ W.ownPos m' t = i) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α ord 4 W.ptr : CM Tgt σ α).run s) Q G m n := by
  unfold atomicLoadAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (atomicLoadAs_noErr (hw.load_noErr ht hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨j, hj, hv, -⟩ := hw.load rfl ht hcs hr
    exact hdec G₁ rY _ hg₁ rfl hU j hj b hv
  obtain ⟨b, hb, hd⟩ := atomicLoadAs_ok hr
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hw.load rfl ht hcs hb
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.atomicLoad_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hb
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' b r j hg₁ rfl hU hY hd hj hv hfl hacq hh hw' hop hA (fun hf => let hs := Word.atomicLoad_seen hw hf hb; ⟨hs.1, hs.2.1⟩)
    (fun hf => (Word.atomicLoad_read_seen hw hf hb).2.2)
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- An RMW of a `u32` at the word (`atomicRmwC`), by thread `t` (`g`): it reads the newest write
`old`, and its write is the newest. -/
theorem wp_wordRmw (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec 32}
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' old, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) →
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]! (op.apply signed old v)) →
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → Q (old, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC op signed ord 4 W.ptr v : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.rmw_noErr ht hcs hcr e he).elim) fun old m' hr => ?_
  obtain ⟨hv, hw', hop, hH, hh, hacq⟩ := hw.rmw rfl ht hcs hr
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.atomicRmw_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hr
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' old hg₁ rfl hU hY hv hH hh hacq hw' hop hA (fun hf => let hs := Word.atomicRmw_seen hw hf hr; ⟨hs.1, hs.2.1⟩)
    (fun hf => Word.atomicRmw_write_seen hw hf hr)
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- An RMW at the word with a decode (`atomicRmwAsC`), by thread `t` (`g`). -/
theorem wp_wordRmwAs {α : Type} [Packed α 32] (hP : L.Fits K P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {op : RmwOp} {ord : AtomicOrder} {v : α}
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
      W.Ok m' → W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC op ord 4 W.ptr v : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (atomicRmwAs_noErr (hw.rmw_noErr ht hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨hv, -⟩ := hw.rmw rfl ht hcs hr
    exact hdec G₁ rY _ hg₁ rfl hU b hv
  obtain ⟨old, hb, hd⟩ := atomicRmwAs_ok hr
  obtain ⟨hv, hw', hop, hH, hh, hacq⟩ := hw.rmw rfl ht hcs hb
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.atomicRmw_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hb
  exact ⟨by rw [hop.threads], h k hk G₁ rY _ m' old r hg₁ rfl hU hY hd hv hH hh hacq hw' hop hA (fun hf => let hs := Word.atomicRmw_seen hw hf hb; ⟨hs.1, hs.2.1⟩)
    (fun hf => Word.atomicRmw_write_seen hw hf hb)
    (hiL.wordOp hY hw hw' hop hap)⟩

/-- A strong `cmpxchg` at the word with a decode (`cmpxchgAsC`), by thread `t` (`g`): on success
an RMW of the newest write, which holds `exp`; on failure a read of write `j`. -/
theorem wp_wordCasAs {α : Type} [Packed α 32] (hP : L.Fits K P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {succ fail : AtomicOrder} {exp new : α}
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! (Packed.toBits new)) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, b ≠ Packed.toBits exp → (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ →
        (W.Fresh m₁ → ∃ i < (W.hist m').size,
          (W.hist m')[i]!.Val b ∧ W.ownPos m' t = i) → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (cmpxchgAs_noErr (hw.cas_noErr (fail := fail)
    (new := Packed.toBits new) ht hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, -, hj, hv, -⟩⟩ := hw.cas rfl ht hcs hr
    · cases he
    · cases he
      exact hdec G₁ rY _ hg₁ rfl hU j hj _ hv
  rcases cmpxchgAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hH, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hw.cas rfl ht hcs ho
    · have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
        Word.cmpxchg_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff ho
      exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop hA (fun hf => let hs := Word.cmpxchg_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordOp hY hw hw' hop hap)).1 hv hH hh hacq
        (fun hf => Word.cmpxchg_write_seen hw hf ho)⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hne, hj, hv, hfl, hacq, hh⟩⟩ := hw.cas rfl ht hcs ho
    · cases he
    · cases he
      have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
        Word.cmpxchg_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff ho
      exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop hA (fun hf => let hs := Word.cmpxchg_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordOp hY hw hw' hop hap)).2 j b v hne hd hj hv hfl hacq hh
        (fun hf => (Word.cmpxchg_read_seen hw hf ho).2.2)⟩

/-- A strong `cmpxchg` of a `u32` at the word (`cmpxchgC`), by thread `t` (`g`): on success an
RMW of the newest write, which holds `exp`; on failure a read of write `j`, whose value is not
`exp`. -/
theorem wp_wordCas (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {succ fail : AtomicOrder} {exp new : BitVec 32} (hgone : L.ph g ≠ .gone)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val exp → W.Holds m' new →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! new) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b, b ≠ exp → j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b →
        Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ →
        (W.Fresh m₁ → ∃ i < (W.hist m').size,
          (W.hist m')[i]!.Val b ∧ W.ownPos m' t = i) → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgC (n := 32) succ fail 4 W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.cas_noErr (fail := fail) (new := new) ht hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hop, hcase⟩ := hw.cas rfl ht hcs hr
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.cmpxchg_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hr
  have hk := h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop hA (fun hf => let hs := Word.cmpxchg_seen hw hf hr; ⟨hs.1, hs.2.1⟩) (hiL.wordOp hY hw hw' hop hap)
  refine ⟨by rw [hop.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hH, hh, hacq⟩ | ⟨j, b, rfl, hne, hj, hv, hfl, hacq, hh⟩
  · exact hk.1 hv hH hh hacq (fun hf => Word.cmpxchg_write_seen hw hf hr)
  · exact hk.2 j b hne hj hv hfl hacq hh (fun hf => (Word.cmpxchg_read_seen hw hf hr).2.2)

/-- A weak `cmpxchg` of a `u32` at the word (`cmpxchgWeakC`), by thread `t` (`g`): on success an
RMW of the newest write, which holds `exp`; on failure (spurious ones too) a read of write `j`. -/
theorem wp_wordWeakCas (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {succ fail : AtomicOrder} {exp new : BitVec 32} (hgone : L.ph g ≠ .gone)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val exp → W.Holds m' new →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! new) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b, j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b →
        Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ →
        (W.Fresh m₁ → ∃ i < (W.hist m').size,
          (W.hist m')[i]!.Val b ∧ W.ownPos m' t = i) → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakC (n := 32) succ fail 4 W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgWeakC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (hw.weakCas_noErr (fail := fail) (new := new) ht hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hop, hcase⟩ := hw.weakCas rfl ht hcs hr
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.cmpxchgWeak_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hr
  have hk := h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop hA (fun hf => let hs := Word.cmpxchgWeak_seen hw hf hr; ⟨hs.1, hs.2.1⟩) (hiL.wordOp hY hw hw' hop hap)
  refine ⟨by rw [hop.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hH, hh, hacq⟩ | ⟨j, b, rfl, hj, hv, hfl, hacq, hh⟩
  · exact hk.1 hv hH hh hacq (fun hf => Word.cmpxchgWeak_write_seen hw hf hr)
  · exact hk.2 j b hj hv hfl hacq hh (fun hf => (Word.cmpxchgWeak_read_seen hw hf hr).2.2)

/-- A weak `cmpxchg` at the word with a decode (`cmpxchgWeakAsC`), by thread `t` (`g`). -/
theorem wp_wordWeakCasAs {α : Type} [Packed α 32] (hP : L.Fits K P U ok) (hW : W.InRest U)
    (hap : W.ApartL L.toLockWord) {succ fail : AtomicOrder} {exp new : α}
    (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → (∀ l, W.In l → rY.heap l = none) → W.Ok m' →
      W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      ((W.hist m₁)[(W.hist m₁).size - 1]!.Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push
          (Word.rmwEnt m' t succ (W.hist m₁)[(W.hist m₁).size - 1]! (Packed.toBits new)) →
        (succ.isAcq = true →
          VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
        (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ →
        (W.Fresh m₁ → ∃ i < (W.hist m').size,
          (W.hist m')[i]!.Val b ∧ W.ownPos m' t = i) → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgWeakAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ :=
    hP.stopW hW hi₁ (by rw [hg₁]; exact hgone)
  refine WP.callMC (fun e he => (cmpxchgWeakAs_noErr (hw.weakCas_noErr (fail := fail)
    (new := Packed.toBits new) ht hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, hj, hv, -⟩⟩ := hw.weakCas rfl ht hcs hr
    · cases he
    · cases he
      exact hdec G₁ rY _ hg₁ rfl hU j hj _ hv
  rcases cmpxchgWeakAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hH, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hw.weakCas rfl ht hcs ho
    · have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
        Word.cmpxchgWeak_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff ho
      exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop hA (fun hf => let hs := Word.cmpxchgWeak_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordOp hY hw hw' hop hap)).1 hv hH hh hacq
        (fun hf => Word.cmpxchgWeak_write_seen hw hf ho)⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hj, hv, hfl, hacq, hh⟩⟩ := hw.weakCas rfl ht hcs ho
    · cases he
    · cases he
      have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
        Word.cmpxchgWeak_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff ho
      exact ⟨by rw [hop.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hY hw' hop hA (fun hf => let hs := Word.cmpxchgWeak_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordOp hY hw hw' hop hap)).2 j b v hd hj hv hfl hacq hh
        (fun hf => (Word.cmpxchgWeak_read_seen hw hf ho).2.2)⟩

/-- A futex wake at the word (`futexWakeC`), by thread `t` (`g`): the lock's invariant holds with
the same rest; the client shows its `U` after the wake. -/
theorem wp_wordWake (hP : L.Fits K P U ok) (hap : W.ApartL L.toLockWord) {io : Io}
    {c : BitVec 32} (hi : P.inv (upd G t g) m) {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rX m₁ cs m', G₁ t = g → U G₁ rX m₁ →
      ((Thread.futexWake W.ptr c.toNat cs).run { m₁ with current := t }).run =
        some (.ok ((), m')) → L.Inv G₁ rX m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io W.ptr c : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWakeC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ cs m' hw => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  exact h k hk G₁ rX m₁ cs m' hg₁ hU hw (hiL.wakeOff hap hw)

/-- The thread `t` at `out` (`g`) holds nothing of the lock. -/
theorem Fits.heldOut (hP : L.Fits K P U ok) (hg : L.ph g = .out) (hi : P.inv (upd G t g) m) :
    L.held g = rnil :=
  hP.held (by rw [hg]; decide) hi

/-- Thread `t` at `out` (`g`) goes `away`, to a futex wait off the lock's word, when its `U` lets
it (`hUa`). -/
theorem Fits.goAway (hP : L.Fits K P U ok) (hg : L.ph g = .out) (hi : P.inv (upd G t g) m)
    (hUa : ∀ rX, U (upd G t g) rX m → U (upd G t (L.set g .away rnil)) rX m) :
    P.inv (upd G t (L.set g .away rnil)) m := by
  obtain ⟨rX₀, hiL₀, hU₀⟩ := (hP.inv _ _).mp hi
  have hl := hiL₀.ghost (t := t) (g := L.set g .away rnil) (by rw [upd_self]; exact hg)
    (.inr (.inr (L.ph_set _ _ _))) (by rw [upd_self, L.part_set]) (L.held_set _ _ _)
    (fun _ => hiL₀.ht (t := t) (by rw [upd_self, hg]; decide))
    (fun r hr => by
      have := (L.R_set (upd G t g) t .away rnil r).mpr hr
      rwa [upd_self] at this)
  rw [upd_upd] at hl
  exact (hP.inv _ _).mpr ⟨rX₀, hl, hUa _ hU₀⟩

/-- **The scheduler's futex wait at the word** (`SyncOp.wait`, the bits `e`) by thread `t`, which
is `away` from `g` at `out`, with the client's facts of `wp_wordWait`: it goes on at `g`. The
stop of `futexWaitC` and the sleep of the OS wait (`wp_wordOsWait`). -/
theorem Fits.wordWaitStep (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {e : BitVec 32} (hg : L.ph g = .out) (hheld : L.held g = rnil)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Op t { m₁ with current := t } M →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M → M.blocks = m₁.blocks → W.Holds m₁ e →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.ptr) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Op t { m₁ with current := t } M ∧ W.hist M = W.hist m₁ ∧ W.Ok M ∧
          M.blocks = m₁.blocks)) →
      U (upd G₁ t g) (rsum (W.cellsR m₁) rY) M)
    {K' : Unit → (ThreadId → γ) → Mem → Prop}
    (h : ∀ G₁ m', m'.current = t → P.inv (upd G₁ t g) m' → K' () G₁ m')
    {G₁ : ThreadId → γ} {m₁ : Mem} (hg₁ : G₁ t = L.set g .away rnil) (hi₁ : P.inv G₁ m₁) :
    P.Step t (.wait W.ptr e) G₁ m₁ K' := by
  have hph : L.ph (L.set g .away rnil) = .away := L.ph_set _ _ _
  -- `t` holds nothing at `out`, so `g` is `g` with the place `out`
  have hgo : L.set (L.set g .away rnil) .out rnil = g := by
    rw [L.set_set, ← hg, ← hheld, L.set_self]
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
  simp only [Proto.Step]
  refine ⟨fun _ => hlive G₁ m₁ hg₁ hi₁, fun hq => ⟨fun _ => hw₀.futexWait_run ht0,
    fun _ he => Zig.Conc.Proto.noErr_of_ok (he := he) (hw₀.futexWait_run ht0), fun b m' hr => ?_⟩⟩
  have hl := hiL.waitOff hph₁ hw hap hX hq hr
  have hfields := Word.futexWait_fields hr
  rcases hw₀.futexWait rfl ht0 hiL.w.csize hr with
    ⟨-, rfl, rfl⟩ | ⟨-, M, hok₂, hop, hh, hbl, ⟨hU32, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨-, hl'⟩ := hl
    rw [hback] at hl'
    exact h G₁ _ rfl ((hP.inv _ _).mpr ⟨_, hl', hUo G₁ rY m₁ _ hg₁ hU hY hfields (.inl rfl)⟩)
  · simp only [↓reduceIte] at hl ⊢
    have hs := hiL.spuriousOff hph₁ hq
    rw [hback] at hs
    exact ⟨(hP.inv _ _).mpr ⟨_, hl, hUs G₁ rY m₁ M hg₁ hU hY hop hfields hh hok₂ hbl hU32⟩,
      h G₁ _ rfl ((hP.inv _ _).mpr ⟨_, hs,
        hUo G₁ rY m₁ _ hg₁ hU hY ⟨rfl, rfl, rfl⟩ (.inr (.inl rfl))⟩)⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨hc, hl'⟩ := hl
    rw [hback] at hl'
    exact h G₁ _ hc
      ((hP.inv _ _).mpr ⟨_, hl', hUo G₁ rY m₁ _ hg₁ hU hY hfields (.inr (.inr ⟨hop, hh, hok₂, hbl⟩))⟩)

/-- **A futex wait at the word** (`futexWaitC`, the bits `e`) by thread `t` out of the lock's
code (`g`, at `out`): while it waits it is `away` (`L.set g .away rnil`). The client says that
its `U` lets `t` go away (`hUa`), that `t` is not the last thread while it waits (`hlive`), that
`U` holds when `t` sleeps (the kernel's read, an op `M` that keeps the word's writes, read `e`;
`hUs`), and that `U` holds with `t` back at `out` after the kernel's read, a wake that was
pending, or a spurious return (`hUo`). It goes on at `g`. -/
theorem wp_wordWait (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {ε : Type} {w : Nat} [Packed ε w] {io : Io} {e : ε} (hg : L.ph g = .out)
    (hi : P.inv (upd G t g) m)
    (hUa : ∀ rX, U (upd G t g) rX m → U (upd G t (L.set g .away rnil)) rX m)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Op t { m₁ with current := t } M →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M → M.blocks = m₁.blocks →
      W.Holds m₁ ((Packed.toBits e).setWidth 32) →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.ptr) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Op t { m₁ with current := t } M ∧ W.hist M = W.hist m₁ ∧ W.Ok M ∧
          M.blocks = m₁.blocks)) →
      U (upd G₁ t g) (rsum (W.cellsR m₁) rY) M)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → P.inv (upd G₁ t g) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io W.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWaitC fun k hk =>
    ⟨L.set g .away rnil, hP.goAway hg hi hUa, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  exact hP.wordWaitStep hW hap hg (hP.heldOut hg hi) hlive hUs hUo
    (K' := fun _ G' m' => Q ((), s) G' m' k) (fun G₁ m' hc hi' => h k hk G₁ m' hc hi') hg₁ hi₁

/-- `FStepIn` of a change of the OS state only (an interrupt's delivery, `Os.takeInterrupt`). -/
theorem _root_.Zig.FStepIn.os (m : Mem) (hF : Heap) (o : OsState) : FStepIn hF m { m with os := o } :=
  have h := FStepIn.refl m hF
  ⟨h.current, h.threads, h.waiters, h.woken, h.groups, h.size, h.others, h.mine, h.blocks,
    h.nextMsg, ⟨some, AMap.of_eq rfl rfl⟩, h.fp, h.fpc, h.const, h.cov⟩

/-- **The untimed OS futex wait at the word** (`Os.futexWait`, OSF-01; the bits `e`) by thread
`t` out of the lock's code (`g`, at `out`), the current thread. A pending interrupt is delivered
(`hos`: the protocol's invariant does not read the OS state there), the thread stops at the
oracle's pick at `g`, and in the same turn the kernel compares the word, an atomic relaxed read
by `t` at `g` (`hrd`: the client's `U` after it, as after `wp_wordLoad`). If it sleeps, it goes
`away` (`hUa`, for every ghost value, as `wp_wordWait`'s) and the sleep is the scheduler's wait
with `wp_wordWait`'s facts (`hlive`, `hUs`, `hUo`; `Fits.wordWaitStep`). It goes on at `g` with a
result other than `timedOut`. -/
theorem wp_wordOsWait (hP : L.Fits K P U ok) (hW : W.InRest U) (hap : W.ApartL L.toLockWord)
    {e : BitVec 32} (hg : L.ph g = .out) (hc : m.current = t) (hi : P.inv (upd G t g) m)
    (hos : ∀ G₁ m₁ o, G₁ t = g → m₁.current = t → P.inv G₁ m₁ → P.inv G₁ { m₁ with os := o })
    (hrd : ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' →
      (m₁.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
        (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        ∃ σ, AMap hF { m₁ with current := t } { m' with current := t } σ) →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → P.inv G₁ m')
    (hUa : ∀ G₁ rX m₁, U (upd G₁ t g) rX m₁ → U (upd G₁ t (L.set g .away rnil)) rX m₁)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Op t { m₁ with current := t } M →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M → M.blocks = m₁.blocks → W.Holds m₁ e →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.ptr) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Op t { m₁ with current := t } M ∧ W.hist M = W.hist m₁ ∧ W.Ok M ∧
          M.blocks = m₁.blocks)) →
      U (upd G₁ t g) (rsum (W.cellsR m₁) rY) M)
    {Q : Os.WaitResult → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ d, d < n → ∀ r G₁ m', m'.current = t → r ≠ .timedOut → P.inv (upd G₁ t g) m' →
      Q r G₁ m' d)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWait W.ptr e false : ConcM Tgt Os.WaitResult) Q G m n := by
  have hng : L.ph g ≠ .gone := by rw [hg]; decide
  have hheld := hP.heldOut hg hi
  refine WP.osFutexWait fun b₀ m₀ h₀ k hk => ⟨g, ?_, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  · obtain ⟨o, rfl⟩ := Os.takeInterrupt_os h₀
    exact hos _ m o (upd_self _ _ _) hc hi
  -- the kernel's compare at the pick: an atomic relaxed read of the newest message, by `t` at `g`
  obtain ⟨rY, hiL, hU, hY, hw, ht, hcs⟩ := hP.stopW hW hi₁ (by rw [hg₁]; exact hng)
  have hcr : 0 < loadCount 32 .relaxed 4 W.ptr { m₁ with current := t } ∨
      loadCount 32 .relaxed 4 W.ptr { m₁ with current := t } = 0 ∧ 0 = 0 :=
    (Nat.eq_zero_or_pos _).symm.imp_right (⟨·, rfl⟩)
  refine ⟨fun er he => absurd he (hw.load_noErr ht hcs hcr er), fun _ => .inr hcost,
    fun v m₂ hr => ?_⟩
  obtain ⟨-, -, -, -, -, hh, hw', hop⟩ := hw.load rfl ht hcs hr
  have hA := Word.amap_for_actor (W := W) rfl fun hF hoff =>
    Word.atomicLoad_amap hw (by change t < m₁.clocks.size; rw [hcs]; exact ht) hoff hr
  have hc₂ : m₂.current = t := hop.current
  have hi₂ : P.inv (upd G₁ t g) m₂ := by
    rw [← hg₁, upd_same]
    exact hrd G₁ rY _ m₂ hg₁ rfl hU hY hh hw' hop hA (fun hf => let hs := Word.atomicLoad_seen hw hf hr; ⟨hs.1, hs.2.1⟩) (hiL.wordOp hY hw hw' hop hap)
  refine ⟨by rw [hop.threads], fun _ => h k (by omega) _ G₁ m₂ hc₂ (by decide) hi₂,
    fun _ => ⟨h k (by omega) _ G₁ m₂ hc₂ (by decide) hi₂, fun k' hk' => ?_⟩⟩
  -- the sleep: `t` goes away, then the scheduler's wait; at the end an interrupt's delivery
  refine ⟨L.set g .away rnil, hP.goAway hg hi₂ (hUa G₁ · m₂), fun G₂ m₃ hg₂ hi₃ =>
    hP.wordWaitStep hW hap hg hheld hlive hUs hUo (fun G₄ m₄ hc₄ hi₄ => ?_) hg₂ hi₃⟩
  dsimp only
  split
  · exact h k' (by omega) _ G₄ _ hc₄ (by decide) (hos _ _ _ (upd_self _ _ _) hc₄ hi₄)
  · exact h k' (by omega) _ G₄ _ hc₄ (by decide) hi₄

/-- **An OS futex wake at the word** (`Os.futexWake`, OSF-02) by thread `t` (`g`): a wake keeps
the lock's invariant with the same rest, and the client shows its `U` after it; a spurious
`EINTR` (`spurious`, macOS) wakes nobody, and the protocol's invariant holds at the stop. -/
theorem wp_wordOsWake (hP : L.Fits K P U ok) (hap : W.ApartL L.toLockWord) {w : Option Nat}
    {spurious : Bool} (hgone : L.ph g ≠ .gone) (hi : P.inv (upd G t g) m)
    {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ →
      (∀ cs m', ((Thread.futexWake W.ptr (Os.wakeSize w (m₁.waitersAt W.ptr).length) cs).run
          { m₁ with current := t }).run = some (.ok ((), m')) → L.Inv G₁ rX m' →
        Q (some (Os.wakeSize w (m₁.waitersAt W.ptr).length)) G₁ m' k) ∧
      (spurious = true → P.inv (upd G₁ t g) { m₁ with current := t } →
        Q none G₁ { m₁ with current := t } k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWake W.ptr w spurious : ConcM Tgt (Option Nat)) Q G m n := by
  refine WP.osFutexWake fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  obtain ⟨hw, hsp⟩ := h k hk G₁ rX m₁ hg₁ hU
  refine ⟨fun cs m' hr => hw cs m' hr (hiL.wakeOff hap hr), fun hs => hsp hs ?_⟩
  obtain ⟨-, -, -, hic⟩ := hP.cur t hi₁ (by rw [hg₁]; exact hgone)
  rw [← hg₁, upd_same]; exact hic

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

/-- **A step of thread `t` on its own part** (`g`, out of the lock's code or holding the lock; a
stack block of a sync object's code), with a thread triple: the client gets the rest with the
word's cells and the lock's invariant before the step, the step (`FStepIn` of the lock's word and
the rest, `KeepK`: the word stays), and the lock's invariant after it, with `t`'s part the
triple's post (`FLock.setPart`) and the word's new cells. -/
theorem wp_liftPartW (hP : L.Fits K P U ok) (hW : W.InRest U) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r' rY, (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      U (upd G t g) (rsum (W.cellsR m) rY) m → L.Inv (upd G t g) (rsum (W.cellsR m) rY) m →
      (∀ l, W.In l → rY.heap l = none) →
      FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m' → W.KeepK m m' →
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
  have hwF : ∀ l, W.In l → (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase l ≠ none :=
    fun l hl => by
      have := cellsAt_some hl (hw.cellIn hl) (m := m)
      simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
        Option.or_eq_none_iff, not_and]
      intro _ h; exact absurd h this
  exact h a m' r' rY hr hq hc' hU hL hY hs
    (Word.keepK_fstep hs hwF (fun i l hl => (hw.loc i l hl).1) hcells) (hL'.restW hcells)

/-- A thread not in the futex queue. -/
theorem notQ_mem {ws : Array (ThreadId × Ptr)} {t : ThreadId} (h : ws.any (·.1 == t) = false) :
    ∀ w ∈ ws, w.1 ≠ t := fun w hw e => by
  have : ws.any (·.1 == t) = true := Array.any_eq_true'.mpr ⟨w, hw, by simp [e]⟩
  rw [h] at this; cases this

end FLock

/-- **A sync primitive over futex words** next to the lock `L` (an event, a condition; module
`ZigLean/Sep/Full/Lock.lean`, `FPrim`): its place `pl` (`out` out of its code), the calm places,
the roles, its words `Ws`, its invariant `Inv`, the steps of its code at a word
(`Move W t g p q h m m'`: thread `t` at `g` goes to the place `p`, the lock place `q` and the
lock resource `h`) and the lock places `ownAt` at which a thread in its code steps on its own
part. The rest has each word's cells (`Sub`, `Word.InRest`); a step is a step of its code at a
word or a step on the thread's own part (`FStepIn`, `KeepK`), with the word's new cells in the
rest and the invariant after it. -/
abbrev FPrim.ofWords {γ Ph Rl : Type} (L : FLock γ) (pl : FPlace γ Ph) (out : Ph)
    (calm : Ph → Prop) (role : Rl → γ → Prop) (Ws : Word 32 4 → Prop)
    (Inv : (ThreadId → γ) → Mem → Prop)
    (Move : Word 32 4 → ThreadId → γ → Ph → LPh → Res → Mem → Mem → Prop)
    (ownAt : LPh → Prop) : FPrim γ where
  Ph := Ph
  pl := pl
  out := out
  calm := calm
  Role := Rl
  role := role
  Sub G rX m := Inv G m ∧ ∀ W, Ws W →
    W.Ok m ∧ ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none
  Apart := ∀ W, Ws W → W.ApartL L.toLockWord
  Step t G rX m G' rX' m' := ∃ W rY, Ws W ∧ rX = rsum (W.cellsR m) rY ∧
    rX' = rsum (W.cellsR m') rY ∧ (∀ l, W.In l → rY.heap l = none) ∧ Inv G' m' ∧
    ((∃ p q h, Move W t (G t) p q h m m' ∧ G' = upd G t (L.set (pl.set (G t) p) q h)) ∨
     (∃ r, ownAt (L.ph (G t)) ∧ L.Inv G rX m ∧ m.current = t ∧
       FStepIn (rsum (L.wordR m) rX).heap.erase m m' ∧ W.KeepK m m' ∧ L.Inv G' rX' m' ∧
       G' = upd G t (L.setPart (G t) r)))

namespace FLock

/-! ## A protocol that keeps a primitive over futex words

What `Fits` gives for `FPrim.ofWords`, once for every such primitive (the event, the condition). -/

section Words

variable {γ : Type} {L : FLock γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {W : Word 32 4} {Ph Rl : Type}
  {pl : FPlace γ Ph} {out : Ph} {calm : Ph → Prop} {role : Rl → γ → Prop}
  {Ws : Word 32 4 → Prop} {Inv : (ThreadId → γ) → Mem → Prop}
  {Move : Word 32 4 → ThreadId → γ → Ph → LPh → Res → Mem → Mem → Prop} {ownAt : LPh → Prop}
  {t : ThreadId} {G G₁ : ThreadId → γ} {m m₁ m' : Mem} {rY : Res} {g : γ} {p : Ph}

/-- The rest keeps the primitive's invariant. -/
theorem Fits.wInv (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    (G : ThreadId → γ) (rX : Res) (m : Mem) (hU : U G rX m) : Inv G m :=
  (hK.sub G rX m hU).1

/-- The rest has each word's cells. -/
theorem Fits.wRest (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    (hW : Ws W) : W.InRest U :=
  fun G rX m hU => (hK.sub G rX m hU).2 W hW

/-- Each word is apart from the lock's word. -/
theorem Fits.wAp (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    (hW : Ws W) : W.ApartL L.toLockWord :=
  hK.apart W hW

/-- **A step of the primitive's code** at the word `W` keeps the rest, with the stepping thread's
new place `p`, lock place `q` and lock resource `h`, given the invariant after it. -/
theorem Fits.wStep (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    {q : LPh} {h : Res} (hW : Ws W) (hmv : Move W t (G t) p q h m m')
    (hU : U G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hI : Inv (upd G t (L.set (pl.set (G t) p) q h)) m') :
    U (upd G t (L.set (pl.set (G t) p) q h)) (rsum (W.cellsR m') rY) m' :=
  hK.kstep t G _ m _ _ m' ⟨W, rY, hW, rfl, rfl, hY, hI, .inl ⟨p, q, h, hmv, rfl⟩⟩ hU

/-- **A step of a thread on its own part** in the primitive's code (at a lock place `ownAt`; a
stack block) keeps the rest, with the thread's new part `r`, given the lock's invariant before it
and the lock's and the primitive's invariants after it. -/
theorem Fits.wOwn (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    {r : Res} (hW : Ws W) (hat : ownAt (L.ph (G t))) (hU : U G (rsum (W.cellsR m) rY) m)
    (hL : L.Inv G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hc : m.current = t) (hs : FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m')
    (hk : W.KeepK m m') (hL' : L.Inv (upd G t (L.setPart (G t) r)) (rsum (W.cellsR m') rY) m')
    (hI : Inv (upd G t (L.setPart (G t) r)) m') :
    U (upd G t (L.setPart (G t) r)) (rsum (W.cellsR m') rY) m' :=
  hK.kstep t G _ m _ _ m' ⟨W, rY, hW, rfl, rfl, hY, hI, .inr ⟨r, hat, hL, hc, hs, hk, hL', rfl⟩⟩ hU

/-- **After a step of the primitive's code** by `t` (`g`, new place `p`) at the word `W` that
keeps `t`'s lock place and resource: the protocol's invariant, from the lock's invariant after the
step, the rest before it, and the primitive's invariant after it. -/
theorem Fits.back (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    (hW : Ws W) (hg₁ : G₁ t = g) (hmv : Move W t g p (L.ph g) (L.held g) m₁ m')
    (hU : U G₁ (rsum (W.cellsR m₁) rY) m₁) (hY : ∀ l, W.In l → rY.heap l = none)
    (hL : L.Inv G₁ (rsum (W.cellsR m') rY) m') (hI : Inv (upd G₁ t (pl.set g p)) m') :
    P.inv (upd G₁ t (pl.set g p)) m' := by
  subst hg₁
  have hset : L.set (pl.set (G₁ t) p) (L.ph (G₁ t)) (L.held (G₁ t)) = pl.set (G₁ t) p := by
    have := L.set_self (pl.set (G₁ t) p); rwa [hK.lph, hK.lheld] at this
  have hU' := hK.wStep hW hmv hU hY (by rw [hset]; exact hI)
  rw [hset] at hU'
  have hL' := hL.relabel (g := pl.set (G₁ t) p) (hK.lph _ _) (hK.lpart _ _) (hK.lheld _ _)
    (fun r hr => hK.lR G₁ t p r hr)
  exact (hK.inv _ _).mpr ⟨_, hL', hU'⟩

/-- The facts at a stop of `t` (not at a futex) before an op at a word: the primitive's
invariant, `t` is not in the futex queue. -/
theorem Fits.atOp (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    {rX rX' : Res} (hU : U G₁ rX m₁) (hw : L.ph (G₁ t) ≠ .wait) (ha : L.ph (G₁ t) ≠ .away)
    (hop : W.Op t m₁ m') (hL : L.Inv G₁ rX' m') :
    Inv G₁ m₁ ∧ ∀ w ∈ m₁.waiters, w.1 ≠ t := by
  refine ⟨hK.wInv _ _ _ hU, ?_⟩
  have := hL.w.notQ (t := t) hw ha
  rw [hop.waiters] at this
  exact notQ_mem this

/-- **An interrupt's delivery** (`Os.takeInterrupt`: only the OS state changes) by the current
thread `t`, at a lock place where it steps on its own part (`ownAt`), keeps the protocol's
invariant: it is a step on `t`'s own part that keeps its part (`Fits.wOwn`), given that the
primitive's invariant does not read the OS state (`hIos`). -/
theorem Fits.wOs (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Inv Move ownAt) P U ok)
    (hW : Ws W) (hIos : ∀ G m o, Inv G m → Inv G { m with os := o })
    (hat : ownAt (L.ph (G t))) (hc : m.current = t) (hi : P.inv G m) (o : OsState) :
    P.inv G { m with os := o } := by
  obtain ⟨rX, hL, hU⟩ := (hK.inv _ _).mp hi
  obtain ⟨-, rY, rfl, hY⟩ := (hK.wRest hW) _ _ _ hU
  have hst : L.Step t m { m with os := o } :=
    LockWord.Step.same rfl rfl rfl rfl rfl rfl (fun _ _ => Iff.rfl)
  have hL' : L.Inv G (rsum (W.cellsR m) rY) { m with os := o } := hL.lstay hst (hL.w.osState o)
  have hset : upd G t (L.setPart (G t) (L.part (G t))) = G := by rw [L.setPart_self, upd_same]
  have hcl : W.cellsR { m with os := o } = W.cellsR m := Word.cellsR_congr rfl
  have hU' := hK.wOwn (r := L.part (G t)) hW hat hU hL hY hc (FStepIn.os m _ o)
    (Word.keep_of (W := W) (m := m) (m' := { m with os := o }) rfl rfl rfl rfl
      fun _ => VClock.le_refl _).toK (by rw [hset, hcl]; exact hL')
    (by rw [hset]; exact hIos _ _ o (hK.wInv _ _ _ hU))
  rw [hset, hcl] at hU'
  exact (hK.inv _ _).mpr ⟨_, hL', hU'⟩

end Words

end FLock

end Full
end Zig
