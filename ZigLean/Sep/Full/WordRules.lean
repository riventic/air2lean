import ZigLean.Sep.Full.Word
import ZigLean.Conc.Base.WeakCas

/-!
# The rules of the ops at a shared word, over full-state resources

Ordinary atomic rules cover the existing `Word` domain: 32/4 and 64/8, naturally aligned.
Futex rules below remain specialized to 32/4.

The ops of a sync object's code at a shared word (the state and the epoch of a condition, the
state of an event; `ZigLean/Sep/Full/Word.lean`), proved once for every protocol that has a lock
(`FLock.Fits`, with any primitive next to it) and keeps the word's cells in its rest (`Word.InRest`: the protocol's `U` says
that its rest `rX` is the word's cells and a rest `rY` without the word's bytes, and that the
word is `Ok`). Each rule is the stop (the pick of the op, or the futex op) and then the op; it
hands the client the native facts from the actual primitive run (`Word.Ok.load_native`,
`Ok.rmw_native`, `Ok.cas_native`, `Ok.weakCas_native`, `Ok.futexWait_native`) and the lock's invariant after the op, whose
rest has the word's new cells (`FLock.Inv.wordStep`), and the lock's word invariant before the
op (`LockWord.WInv`, from the stop's `FLock.Inv`; a step of a primitive over futex words carries
it, `FPrim.ofWords`). The client shows its `U` after the op.

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
| `wp_wordWait`, `wp_wordWaitTo` | futex wait at the word, by a thread out of the lock's code (`away` while it waits; `To`: it returns at a new place of the primitive) |
| `wp_wordOsWake` | OS futex wake at the word (`Os.futexWake`, OSF-02) |
| `wp_wordOsWait`, `wp_wordOsWaitTo` | untimed OS futex wait at the word (`Os.futexWait`, OSF-01): the kernel's compare at `out`, the sleep `away` |
| `wp_liftPartW` | a step of a thread on its own part (a stack block of the sync object's code) |

The primitive facts come from the existing memory model and the native producers in
`ZigLean/Sep/Full/Word.lean`; decoded weak CAS uses `ZigLean/Conc/Base/WeakCas.lean` directly.
-/

namespace Zig

namespace Conc
namespace Word

open Full

/-- The protocol's rest has the word's cells: for each `U G rX m`, the word is `Ok` for the live
set of the threads whose ghost values have `A` (the protocol's threads that may still access the
word; every thread by default), and `rX` is its cells and a rest without its bytes. -/
def InRest {γ : Type} {bits bytes : Nat} (W : Word bits bytes)
    (U : (ThreadId → γ) → Res → Mem → Prop) (A : γ → Prop := fun _ => True) : Prop :=
  ∀ G rX m, U G rX m → W.Ok m (fun u => A (G u)) ∧
    ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none

end Word
end Conc

namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {L : FLock γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {K : FPrim γ}

variable {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}
  {A : γ → Prop}

section Atomic

variable {bits bytes : Nat} {W : Word bits bytes}

/-- Any shared word kept in a protocol's rest is a live writable word (`Mem.wordAt`), which the
futex rows' address validation needs. -/
theorem Fits.wordWordAt {W : Word 32 4} (hP : L.Fits K P U ok) (hW : W.InRest U A)
    {G : ThreadId → γ} {m : Mem} (hi : P.inv G m) : m.wordAt W.ptr = true := by
  obtain ⟨rX, -, hU⟩ := (hP.inv _ _).mp hi
  obtain ⟨blk, hb, hl, hs, ha, hk, hlo⟩ := (hW _ _ _ hU).1.blk
  exact Mem.wordAt_of hb hl hs ha hk hlo

/-- The invariant at a stop of `t` (`current := t`, a thread that exists), with the word's cells
in the rest. -/
theorem Fits.stopW (hP : L.Fits K P U ok) (hW : W.InRest U A) {G₁ : ThreadId → γ} {m₁ : Mem}
    {t : ThreadId} (hi₁ : P.inv G₁ m₁) (ht : t < m₁.threads.size) :
    ∃ rY, L.Inv G₁ (rsum (W.cellsR { m₁ with current := t }) rY) { m₁ with current := t } ∧
      U G₁ (rsum (W.cellsR { m₁ with current := t }) rY) { m₁ with current := t } ∧
      (∀ l, W.In l → rY.heap l = none) ∧ W.Ok { m₁ with current := t } (fun u => A (G₁ u)) ∧
      m₁.clocks.size = m₁.threads.size := by
  obtain ⟨rX, hiL, hU, -⟩ := hP.curT t hi₁ ht
  have hU' := hP.curU t hU ht
  obtain ⟨hw, rY, rfl, hY⟩ := hW G₁ rX _ hU'
  exact ⟨rY, hiL, hU', hY, hw, hiL.w.csize⟩

/-- An atomic load at the word (`atomicLoadC`), by thread `t` (`g`). -/
theorem wp_wordLoad (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {ord : AtomicOrder} (hi : P.inv (upd G t g) m)
    {Q : BitVec bits × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' v j, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' (fun u => A (G₁ u)) → W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c, ((atomicLoadAt c ord bytes W.ptr).run m₁).run = some (.ok (v, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → ∃ i < (W.hist m').size,
        (W.hist m')[i]!.Val v ∧ W.ownPos m' t = i) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      Q (v, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((atomicLoadC (n := bits) ord bytes W.ptr : CM Tgt σ (BitVec bits)).run s) Q G m n := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (hw.load_noErr_native ht hAt hcs hcr e he).elim) fun v m' hr => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw'⟩ := hw.load_native rfl ht hcs hr
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.atomicLoad_rest hw hc₁ hr
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m' :=
    fun hF hoff => Word.atomicLoad_fstep hw hc₁ hoff hr
  exact ⟨by rw [hrest.threads], h k hk G₁ rY _ m' v j hg₁ rfl hU hiL.w hY hj hv hfl hacq hh hw' hw hc₁ ⟨c, hr⟩ hA (fun hf => let hs := Word.atomicLoad_seen hw hf hr; ⟨hs.1, hs.2.1⟩)
    (fun hf => (Word.atomicLoad_read_seen hw hf hr).2.2)
    (hiL.wordStep hY hw hrest hA hap)⟩

/-- An atomic load at the word with a decode (`atomicLoadAsC`), by thread `t` (`g`). -/
theorem wp_wordLoadAs {α : Type} [Packed α bits] (hP : L.Fits K P U ok) (hW : W.InRest U A)
    (hap : W.ApartL L.toLockWord) {ord : AtomicOrder} (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' b r j, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      (Packed.ofBits? (α := α) b).run = some (.ok r) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' (fun u => A (G₁ u)) → W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c, ((atomicLoadAt c ord bytes W.ptr).run m₁).run = some (.ok (b, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → ∃ i < (W.hist m').size,
        (W.hist m')[i]!.Val b ∧ W.ownPos m' t = i) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' →
      Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((atomicLoadAsC α ord bytes W.ptr : CM Tgt σ α).run s) Q G m n := by
  unfold atomicLoadAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (atomicLoadAs_noErr (hw.load_noErr_native ht hAt hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨j, hj, hv, -⟩ := hw.load_native rfl ht hcs hr
    exact hdec G₁ rY _ hg₁ rfl hU j hj b hv
  obtain ⟨b, hb, hd⟩ := atomicLoadAs_ok hr
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw'⟩ := hw.load_native rfl ht hcs hb
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.atomicLoad_rest hw hc₁ hb
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m' :=
    fun hF hoff => Word.atomicLoad_fstep hw hc₁ hoff hb
  exact ⟨by rw [hrest.threads], h k hk G₁ rY _ m' b r j hg₁ rfl hU hiL.w hY hd hj hv hfl hacq hh hw' hw hc₁ ⟨c, hb⟩ hA (fun hf => let hs := Word.atomicLoad_seen hw hf hb; ⟨hs.1, hs.2.1⟩)
    (fun hf => (Word.atomicLoad_read_seen hw hf hb).2.2)
    (hiL.wordStep hY hw hrest hA hap)⟩

/-- An RMW at the word (`atomicRmwC`), by thread `t` (`g`): it reads the newest write
`old`, and its write is the newest. -/
theorem wp_wordRmw (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec bits}
    (hi : P.inv (upd G t g) m)
    {Q : BitVec bits × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' old, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]! (op.apply signed old v)) →
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
      W.Ok m' (fun u => A (G₁ u)) → W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c, ((atomicRmwAt c op signed ord bytes W.ptr v).run m₁).run =
        some (.ok (old, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → Q (old, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((atomicRmwC op signed ord bytes W.ptr v : CM Tgt σ (BitVec bits)).run s) Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (hw.rmw_noErr_native ht hAt hcs hcr e he).elim) fun old m' hr => ?_
  obtain ⟨hv, hw', hH, hh, hacq⟩ := hw.rmw_native rfl ht hAt hcs hr
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.atomicRmw_rest hw hc₁ hr
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m' :=
    fun hF hoff => Word.atomicRmw_fstep hw hc₁ hoff hr
  exact ⟨by rw [hrest.threads], h k hk G₁ rY _ m' old hg₁ rfl hU hiL.w hY hv hH hh hacq hw' hw hc₁ ⟨c, hr⟩ hA (fun hf => let hs := Word.atomicRmw_seen hw hf hr; ⟨hs.1, hs.2.1⟩)
    (fun hf => Word.atomicRmw_write_seen hw hf hr)
    (hiL.wordStep hY hw hrest hA hap)⟩

/-- An RMW at the word with a decode (`atomicRmwAsC`), by thread `t` (`g`). -/
theorem wp_wordRmwAs {α : Type} [Packed α bits] (hP : L.Fits K P U ok) (hW : W.InRest U A)
    (hap : W.ApartL L.toLockWord) {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ b, (W.hist m₁)[(W.hist m₁).size - 1]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m' old r, G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      (W.hist m₁)[(W.hist m₁).size - 1]!.Val old →
      W.Holds m' (op.apply false old (Packed.toBits v)) →
      W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]!
        (op.apply false old (Packed.toBits v))) →
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (m'.clocks[t]!) = true) →
      W.Ok m' (fun u => A (G₁ u)) → W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c, ((atomicRmwAt c op false ord bytes W.ptr (Packed.toBits v)).run m₁).run =
        some (.ok (old, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      (W.Fresh m₁ → W.ownPos m' t = (W.hist m').size - 1) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((atomicRmwAsC op ord bytes W.ptr v : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (atomicRmwAs_noErr (hw.rmw_noErr_native ht hAt hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨hv, -⟩ := hw.rmw_native rfl ht hAt hcs hr
    exact hdec G₁ rY _ hg₁ rfl hU b hv
  obtain ⟨old, hb, hd⟩ := atomicRmwAs_ok hr
  obtain ⟨hv, hw', hH, hh, hacq⟩ := hw.rmw_native rfl ht hAt hcs hb
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.atomicRmw_rest hw hc₁ hb
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m' :=
    fun hF hoff => Word.atomicRmw_fstep hw hc₁ hoff hb
  exact ⟨by rw [hrest.threads], h k hk G₁ rY _ m' old r hg₁ rfl hU hiL.w hY hd hv hH hh hacq hw' hw hc₁ ⟨c, hb⟩ hA (fun hf => let hs := Word.atomicRmw_seen hw hf hb; ⟨hs.1, hs.2.1⟩)
    (fun hf => Word.atomicRmw_write_seen hw hf hb)
    (hiL.wordStep hY hw hrest hA hap)⟩

/-- A strong `cmpxchg` at the word with a decode (`cmpxchgAsC`), by thread `t` (`g`): on success
an RMW of the newest write, which holds `exp`; on failure a read of write `j`. -/
theorem wp_wordCasAs {α : Type} [Packed α bits] (hP : L.Fits K P U ok) (hW : W.InRest U A)
    (hap : W.ApartL L.toLockWord) {succ fail : AtomicOrder} {exp new : α}
    (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Ok m' (fun u => A (G₁ u)) →
      W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c r, ((cmpxchgAt c succ fail bytes W.ptr (Packed.toBits exp)
        (Packed.toBits new)).run m₁).run = some (.ok (r, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
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
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((cmpxchgAsC succ fail bytes W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (cmpxchgAs_noErr (hw.cas_noErr_native (fail := fail)
    (new := Packed.toBits new) ht hAt hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, ⟨he, -⟩ | ⟨j, old, he, -, hj, hv, -⟩⟩ := hw.cas_native rfl ht hAt hcs hr
    · cases he
    · cases he
      exact hdec G₁ rY _ hg₁ rfl hU j hj _ hv
  rcases cmpxchgAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', ⟨-, hv, hH, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hw.cas_native rfl ht hAt hcs ho
    · have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
      have hrest := Word.cmpxchg_rest hw hc₁ ho
      have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
          FStepIn hF { m₁ with current := t } m' :=
        fun hF hoff => Word.cmpxchg_fstep hw hc₁ hoff ho
      exact ⟨by rw [hrest.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hiL.w hY hw' hw hc₁ ⟨c, none, ho⟩ hA (fun hf => let hs := Word.cmpxchg_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordStep hY hw hrest hA hap)).1 hv hH hh hacq
        (fun hf => Word.cmpxchg_write_seen hw hf ho)⟩
    · cases he
  · obtain ⟨hw', ⟨he, -⟩ | ⟨j, old, he, hne, hj, hv, hfl, hacq, hh⟩⟩ := hw.cas_native rfl ht hAt hcs ho
    · cases he
    · cases he
      have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
      have hrest := Word.cmpxchg_rest hw hc₁ ho
      have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
          FStepIn hF { m₁ with current := t } m' :=
        fun hF hoff => Word.cmpxchg_fstep hw hc₁ hoff ho
      exact ⟨by rw [hrest.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hiL.w hY hw' hw hc₁ ⟨c, some b, ho⟩ hA (fun hf => let hs := Word.cmpxchg_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordStep hY hw hrest hA hap)).2 j b v hne hd hj hv hfl hacq hh
        (fun hf => (Word.cmpxchg_read_seen hw hf ho).2.2)⟩

/-- A strong `cmpxchg` at the word (`cmpxchgC`), by thread `t` (`g`): on success an
RMW of the newest write, which holds `exp`; on failure a read of write `j`, whose value is not
`exp`. -/
theorem wp_wordCas (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {succ fail : AtomicOrder} {exp new : BitVec bits} (hi : P.inv (upd G t g) m) {Q : Option (BitVec bits) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Ok m' (fun u => A (G₁ u)) →
      W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c r, ((cmpxchgAt c succ fail bytes W.ptr exp new).run m₁).run =
        some (.ok (r, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
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
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((cmpxchgC (n := bits) succ fail bytes W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (hw.cas_noErr_native (fail := fail) (new := new) ht hAt hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hcase⟩ := hw.cas_native rfl ht hAt hcs hr
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.cmpxchg_rest hw hc₁ hr
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m' :=
    fun hF hoff => Word.cmpxchg_fstep hw hc₁ hoff hr
  have hk := h k hk G₁ rY _ m' hg₁ rfl hU hiL.w hY hw' hw hc₁ ⟨c, r, hr⟩ hA (fun hf => let hs := Word.cmpxchg_seen hw hf hr; ⟨hs.1, hs.2.1⟩) (hiL.wordStep hY hw hrest hA hap)
  refine ⟨by rw [hrest.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hH, hh, hacq⟩ | ⟨j, b, rfl, hne, hj, hv, hfl, hacq, hh⟩
  · exact hk.1 hv hH hh hacq (fun hf => Word.cmpxchg_write_seen hw hf hr)
  · exact hk.2 j b hne hj hv hfl hacq hh (fun hf => (Word.cmpxchg_read_seen hw hf hr).2.2)

/-- A weak `cmpxchg` at the word (`cmpxchgWeakC`), by thread `t` (`g`): on success an
RMW of the newest write, which holds `exp`; on failure (spurious ones too) a read of write `j`. -/
theorem wp_wordWeakCas (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {succ fail : AtomicOrder} {exp new : BitVec bits} (hi : P.inv (upd G t g) m) {Q : Option (BitVec bits) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Ok m' (fun u => A (G₁ u)) →
      W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c r, ((cmpxchgWeakAt c succ fail bytes W.ptr exp new).run m₁).run =
        some (.ok (r, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
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
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((cmpxchgWeakC (n := bits) succ fail bytes W.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  unfold cmpxchgWeakC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (hw.weakCas_noErr_native (fail := fail) (new := new) ht hAt hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hcase⟩ := hw.weakCas_native rfl ht hAt hcs hr
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.cmpxchgWeak_rest hw hc₁ hr
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m' :=
    fun hF hoff => Word.cmpxchgWeak_fstep hw hc₁ hoff hr
  have hk := h k hk G₁ rY _ m' hg₁ rfl hU hiL.w hY hw' hw hc₁ ⟨c, r, hr⟩ hA (fun hf => let hs := Word.cmpxchgWeak_seen hw hf hr; ⟨hs.1, hs.2.1⟩) (hiL.wordStep hY hw hrest hA hap)
  refine ⟨by rw [hrest.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hH, hh, hacq⟩ | ⟨j, b, rfl, hj, hv, hfl, hacq, hh⟩
  · exact hk.1 hv hH hh hacq (fun hf => Word.cmpxchgWeak_write_seen hw hf hr)
  · exact hk.2 j b hj hv hfl hacq hh (fun hf => (Word.cmpxchgWeak_read_seen hw hf hr).2.2)

/-- A weak `cmpxchg` at the word with a decode (`cmpxchgWeakAsC`), by thread `t` (`g`). -/
theorem wp_wordWeakCasAs {α : Type} [Packed α bits] (hP : L.Fits K P U ok) (hW : W.InRest U A)
    (hap : W.ApartL L.toLockWord) {succ fail : AtomicOrder} {exp new : α}
    (hi : P.inv (upd G t g) m)
    (hdec : ∀ G₁ rY m₁, G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      ∀ j < (W.hist m₁).size, ∀ b, (W.hist m₁)[j]!.Val b →
        ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t →
      U G₁ (rsum (W.cellsR m₁) rY) m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ l, W.In l → rY.heap l = none) → W.Ok m' (fun u => A (G₁ u)) →
      W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c r, ((cmpxchgWeakAt c succ fail bytes W.ptr (Packed.toBits exp)
        (Packed.toBits new)).run m₁).run = some (.ok (r, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
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
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) :
    P.WP t ((cmpxchgWeakAsC succ fail bytes W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgWeakAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC_exists fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht c hcr => ?_⟩)
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine WP.callMC (fun e he => (cmpxchgWeakAs_noErr (hw.weakCas_noErr_native (fail := fail)
    (new := Packed.toBits new) ht hAt hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, ⟨he, -⟩ | ⟨j, old, he, hj, hv, -⟩⟩ := hw.weakCas_native rfl ht hAt hcs hr
    · cases he
    · cases he
      exact hdec G₁ rY _ hg₁ rfl hU j hj _ hv
  rcases cmpxchgWeakAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', ⟨-, hv, hH, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hw.weakCas_native rfl ht hAt hcs ho
    · have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
      have hrest := Word.cmpxchgWeak_rest hw hc₁ ho
      have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
          FStepIn hF { m₁ with current := t } m' :=
        fun hF hoff => Word.cmpxchgWeak_fstep hw hc₁ hoff ho
      exact ⟨by rw [hrest.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hiL.w hY hw' hw hc₁ ⟨c, none, ho⟩ hA (fun hf => let hs := Word.cmpxchgWeak_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordStep hY hw hrest hA hap)).1 hv hH hh hacq
        (fun hf => Word.cmpxchgWeak_write_seen hw hf ho)⟩
    · cases he
  · obtain ⟨hw', ⟨he, -⟩ | ⟨j, old, he, hj, hv, hfl, hacq, hh⟩⟩ := hw.weakCas_native rfl ht hAt hcs ho
    · cases he
    · cases he
      have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
      have hrest := Word.cmpxchgWeak_rest hw hc₁ ho
      have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + bytes → hF (W.b, x) = none) →
          FStepIn hF { m₁ with current := t } m' :=
        fun hF hoff => Word.cmpxchgWeak_fstep hw hc₁ hoff ho
      exact ⟨by rw [hrest.threads], (h k hk G₁ rY _ m' hg₁ rfl hU hiL.w hY hw' hw hc₁ ⟨c, some b, ho⟩ hA (fun hf => let hs := Word.cmpxchgWeak_seen hw hf ho; ⟨hs.1, hs.2.1⟩)
        (hiL.wordStep hY hw hrest hA hap)).2 j b v hd hj hv hfl hacq hh
        (fun hf => (Word.cmpxchgWeak_read_seen hw hf ho).2.2)⟩

end Atomic

variable {W : Word 32 4}

/-- A futex wake at the word (`futexWakeC`), by thread `t` (`g`): the lock's invariant holds with
the same rest; the client shows its `U` after the wake, given its `U` and the lock's word invariant
at the stop. The wake is at the word's futex key (`Word.Ok.keyAt`), as in `wp_wordOsWake`. -/
theorem wp_wordWake (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {io : Io} {c : BitVec 32} (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rX m₁ cs m', G₁ t = g → U G₁ rX m₁ → L.WInv (L.pl G₁) m₁ →
      ((Thread.futexWake (W.key m₁) c.toNat cs).run { m₁ with current := t }).run =
        some (.ok ((), m')) → L.Inv G₁ rX m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io W.ptr c : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWakeC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ cs m' hw => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  have hWo := (hW _ _ _ hU).1
  refine h k hk G₁ rX m₁ cs m' hg₁ hU hiL.w ?_ (hiL.wakeOff hWo hap hw)
  rwa [Thread.futexWakePtr_eq (m := { m₁ with current := t }) hWo.keyAt] at hw

/-- The thread `t` at `out` (`g`) holds nothing of the lock. -/
theorem Fits.heldOut (hP : L.Fits K P U ok) (hg : L.ph g = .out) (hi : P.inv (upd G t g) m) :
    L.held g = rnil :=
  hP.held (by rw [hg]; decide) hi

/-- Thread `t` at `out` (`g`) goes `away`, to a futex wait off the lock's word, when its `U` lets
it (`hUa`). -/
theorem Fits.goAway (hP : L.Fits K P U ok) (hg : L.ph g = .out) (hi : P.inv (upd G t g) m)
    (hUa : ∀ rX, U (upd G t g) rX m → L.WInv (L.pl (upd G t g)) m →
      U (upd G t (L.set g .away rnil)) rX m) :
    P.inv (upd G t (L.set g .away rnil)) m := by
  obtain ⟨rX₀, hiL₀, hU₀⟩ := (hP.inv _ _).mp hi
  have hl := hiL₀.ghost (t := t) (g := L.set g .away rnil) (by rw [upd_self]; exact hg)
    (.inr (.inr (L.ph_set _ _ _))) (by rw [upd_self, L.part_set]) (L.held_set _ _ _)
    (fun _ => hiL₀.ht (t := t) (by rw [upd_self, hg]; decide))
    (fun r hr => by
      have := (L.R_set (upd G t g) t .away rnil r).mpr hr
      rwa [upd_self] at this)
  rw [upd_upd] at hl
  exact (hP.inv _ _).mpr ⟨rX₀, hl, hUa _ hU₀ hiL₀.w⟩

/-- A change of `t`'s place in the primitive keeps the lock's invariant (`Inv.relabel`: the
primitive's place and the lock's are independent, `Fits.lph`, …). -/
theorem Fits.relabelK (hP : L.Fits K P U ok) {rX : Res} (p : K.Ph)
    (hL : L.Inv (upd G t g) rX m) : L.Inv (upd G t (K.pl.set g p)) rX m := by
  have := hL.relabel (t := t) (g := K.pl.set g p) (by rw [upd_self, hP.lph])
    (by rw [upd_self, hP.lpart]) (by rw [upd_self, hP.lheld]) (fun r hr => by
      have := hP.lR (upd G t g) t p r hr; rwa [upd_self] at this)
  rwa [upd_upd] at this

/-- **The scheduler's futex wait at the word** (`SyncOp.wait`, the bits `e`) by thread `t`, which
is `away` from `g` at `out`, with the client's facts of `wp_wordWait`: it goes on at `g` with the
primitive's place `p` (the return of the wait is a step of the primitive's code: `hUo` shows the
rest there). The stop of `futexWaitC` and the sleep of the OS wait (`wp_wordOsWaitTo`). -/
theorem Fits.wordWaitStepTo (hP : L.Fits K P U ok) (hW : W.InRest U A)
    (hap : W.ApartL L.toLockWord) (p : K.Ph)
    {e : BitVec 32} (hg : L.ph g = .out) (hheld : L.held g = rnil)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.woken.contains t = false →
      m₁.waiters.any (·.1 == t) = false →
      W.Ok { m₁ with current := t } (fun u => A (G₁ u)) → t < m₁.clocks.size →
      M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M (fun u => A (G₁ u)) → M.blocks = m₁.blocks → W.Holds m₁ e →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.key m₁) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.waiters.any (·.1 == t) = false →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Ok { m₁ with current := t } (fun u => A (G₁ u)) ∧ t < m₁.clocks.size ∧
          M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead ∧
          W.hist M = W.hist m₁ ∧ W.Ok M (fun u => A (G₁ u)) ∧ M.blocks = m₁.blocks)) →
      U (upd G₁ t (K.pl.set g p)) (rsum (W.cellsR m₁) rY) M)
    {K' : Unit → (ThreadId → γ) → Mem → Prop}
    (h : ∀ G₁ m', m'.current = t → P.inv (upd G₁ t (K.pl.set g p)) m' → K' () G₁ m')
    {G₁ : ThreadId → γ} {m₁ : Mem} (hg₁ : G₁ t = L.set g .away rnil) (hi₁ : P.inv G₁ m₁)
    (hlv : A (L.set g .away rnil) := by trivial) :
    P.Step t (.wait W.ptr e false) G₁ m₁ K' := by
  have hph : L.ph (L.set g .away rnil) = .away := L.ph_set _ _ _
  -- `t` holds nothing at `out`, so `g` is `g` with the place `out`
  have hgo : L.set (L.set g .away rnil) .out rnil = g := by
    rw [L.set_set, ← hg, ← hheld, L.set_self]
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  obtain ⟨hw, rY, rfl, hY⟩ := hW G₁ rX m₁ hU
  have hph₁ : L.ph (G₁ t) = .away := by rw [hg₁]; exact hph
  have ht0 : t < m₁.threads.size := (hiL.ht (by rw [hph₁]; decide)).1
  have hw₀ : W.Ok { m₁ with current := t } (fun u => A (G₁ u)) :=
    (hw.fields_native (m' := { m₁ with current := t }) rfl rfl rfl rfl
      (fun _ => VClock.le_refl _)).1
  have hc₁ : t < m₁.clocks.size := by rw [hiL.w.csize]; exact ht0
  have hX : ∀ l, W.In l → (rsum (W.cellsR m₁) rY).heap l ≠ none := fun l hl => by
    simp only [FHeap.union_apply, cellsAt_of hl]
    cases e : m₁.heap l with
    | none => exact absurd e (hw.cellIn hl)
    | some c => simp
  -- back at `out`: `upd G₁ t g` is `upd G₁ t (L.set (G₁ t) .out rnil)`
  have hback : upd G₁ t (L.set (G₁ t) .out rnil) = upd G₁ t g := by rw [hg₁, hgo]
  simp only [Proto.Step]
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  refine ⟨fun _ => hlive G₁ m₁ hg₁ hi₁, fun hq => ⟨fun _ => hw₀.futexWait_run ht0 hAt,
    fun _ he => Zig.Conc.Proto.noErr_of_ok (he := he) (hw₀.futexWait_run ht0 hAt),
    fun b m' hr => ?_⟩⟩
  have hl := hiL.waitOff hph₁ hw hap hX hq hr
  have hfields := Word.futexWait_fields hr
  have hUo' := fun M => hUo G₁ rY m₁ M hg₁ hU hiL.w hY hq
  rcases hw₀.futexWait_native rfl ht0 hiL.w.csize hr with
    ⟨-, rfl, rfl⟩ | ⟨hwk, M, hok₂, hrecord, hh, hbl, ⟨hU32, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨-, hl'⟩ := hl
    rw [hback] at hl'
    exact h G₁ _ rfl ((hP.inv _ _).mpr ⟨_, hP.relabelK p hl', hUo' _ hfields (.inl rfl)⟩)
  · simp only [↓reduceIte] at hl ⊢
    have hs := hiL.spuriousOff hph₁ hq
    rw [hback] at hs
    exact ⟨(hP.inv _ _).mpr ⟨_, hl,
        hUs G₁ rY m₁ M hg₁ hU hiL.w hY hwk hq hw₀ hc₁ hrecord hfields hh hok₂ hbl hU32⟩,
      h G₁ _ rfl ((hP.inv _ _).mpr ⟨_, hP.relabelK p hs,
        hUo' _ ⟨rfl, rfl, rfl⟩ (.inr (.inl rfl))⟩)⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨hc, hl'⟩ := hl
    rw [hback] at hl'
    exact h G₁ _ hc ((hP.inv _ _).mpr ⟨_, hP.relabelK p hl', hUo' _ hfields
      (.inr (.inr ⟨hw₀, hc₁, hrecord, hh, hok₂, hbl⟩))⟩)

/-- **A futex wait at the word** (`futexWaitC`, the bits `e`) by thread `t` out of the lock's
code (`g`, at `out`): while it waits it is `away` (`L.set g .away rnil`). The client says that
its `U` lets `t` go away (`hUa`), that `t` is not the last thread while it waits (`hlive`), that
`U` holds when `t` sleeps (the kernel's recorded read `M`, which keeps the word's writes, read `e`;
`t` had no pending wake and was not queued; `hUs`), and that `U` holds with `t` back at `out` after the kernel's
read, a wake that was pending, or a spurious return (`t` was not queued; `hUo`), at the
primitive's place `p` (the return is a step of the primitive's code). It goes on at `g` with the
place `p` (`wp_wordWait`: at `g`). -/
theorem wp_wordWaitTo (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    (p : K.Ph)
    {ε : Type} {w : Nat} [Packed ε w] {io : Io} {e : ε} (hg : L.ph g = .out)
    (hi : P.inv (upd G t g) m)
    (hUa : ∀ rX, U (upd G t g) rX m → L.WInv (L.pl (upd G t g)) m →
      U (upd G t (L.set g .away rnil)) rX m)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.woken.contains t = false →
      m₁.waiters.any (·.1 == t) = false →
      W.Ok { m₁ with current := t } (fun u => A (G₁ u)) → t < m₁.clocks.size →
      M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M (fun u => A (G₁ u)) → M.blocks = m₁.blocks →
      W.Holds m₁ ((Packed.toBits e).setWidth 32) →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.key m₁) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.waiters.any (·.1 == t) = false →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Ok { m₁ with current := t } (fun u => A (G₁ u)) ∧ t < m₁.clocks.size ∧
          M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead ∧
          W.hist M = W.hist m₁ ∧ W.Ok M (fun u => A (G₁ u)) ∧ M.blocks = m₁.blocks)) →
      U (upd G₁ t (K.pl.set g p)) (rsum (W.cellsR m₁) rY) M)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → P.inv (upd G₁ t (K.pl.set g p)) m' →
      Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A (L.set g .away rnil) := by trivial) :
    P.WP t ((futexWaitC io W.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWaitC fun k hk =>
    ⟨L.set g .away rnil, hP.goAway hg hi hUa, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  exact hP.wordWaitStepTo hW hap p hg (hP.heldOut hg hi) hlive hUs hUo
    (K' := fun _ G' m' => Q ((), s) G' m' k) (fun G₁ m' hc hi' => h k hk G₁ m' hc hi') hg₁ hi₁
    hlv

/-- **A futex wait at the word** (`wp_wordWaitTo`) that goes on at `g`. -/
theorem wp_wordWait (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {ε : Type} {w : Nat} [Packed ε w] {io : Io} {e : ε} (hg : L.ph g = .out)
    (hi : P.inv (upd G t g) m)
    (hUa : ∀ rX, U (upd G t g) rX m → L.WInv (L.pl (upd G t g)) m →
      U (upd G t (L.set g .away rnil)) rX m)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.woken.contains t = false →
      m₁.waiters.any (·.1 == t) = false →
      W.Ok { m₁ with current := t } (fun u => A (G₁ u)) → t < m₁.clocks.size →
      M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M (fun u => A (G₁ u)) → M.blocks = m₁.blocks →
      W.Holds m₁ ((Packed.toBits e).setWidth 32) →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.key m₁) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.waiters.any (·.1 == t) = false →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Ok { m₁ with current := t } (fun u => A (G₁ u)) ∧ t < m₁.clocks.size ∧
          M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead ∧
          W.hist M = W.hist m₁ ∧ W.Ok M (fun u => A (G₁ u)) ∧ M.blocks = m₁.blocks)) →
      U (upd G₁ t g) (rsum (W.cellsR m₁) rY) M)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → P.inv (upd G₁ t g) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A (L.set g .away rnil) := by trivial) :
    P.WP t ((futexWaitC io W.ptr e : CM Tgt σ Unit).run s) Q G m n :=
  wp_wordWaitTo hP hW hap (K.pl.ph g) hg hi hUa hlive hUs (by rw [K.pl.set_self]; exact hUo)
    (by rw [K.pl.set_self]; exact h) hcost hlv

/-- `FStepIn` of a change of the OS state only (an interrupt's delivery, `Os.takeInterrupt`). -/
theorem _root_.Zig.FStepIn.os (m : Mem) (hF : Heap) (o : OsState) : FStepIn hF m { m with os := o } :=
  have h := FStepIn.refl m hF
  ⟨h.current, h.threads, h.waiters, h.woken, h.groups, h.size, h.others, h.mine, h.addrs,
    h.nextMsg, ⟨some, AMap.of_eq rfl rfl⟩, h.fp, h.fpc, h.const, h.cov⟩

/-- **The untimed OS futex wait at the word** (`Os.futexWait`, OSF-01; the bits `e`) by thread
`t` out of the lock's code (`g`, at `out`), the current thread. A pending interrupt is delivered
(`hos`: the protocol's invariant does not read the OS state there), the thread stops at the
oracle's pick at `g`, and in the same turn the kernel compares the word, an atomic relaxed read
by `t` at `g` (`hrd`: the client's `U` after it, as after `wp_wordLoad`). If it sleeps, it goes
`away` (`hUa`, for every ghost value, as `wp_wordWait`'s) and the sleep is the scheduler's wait
with `wp_wordWait`'s facts (`hlive`, `hUs`, `hUo`; `Fits.wordWaitStepTo`). It goes on at `g`
with the primitive's place `p` and a result other than `timedOut`: a return without a sleep
moves to `p` in the protocol's invariant (`hret`), the sleep's return through `hUo`; an
interrupt's delivery is at `g` or at the place `p` (`hos`). `wp_wordOsWait`: at `g`. -/
theorem wp_wordOsWaitTo (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    (p : K.Ph)
    {e : BitVec 32} (hg : L.ph g = .out) (hc : m.current = t) (hi : P.inv (upd G t g) m)
    (hos : ∀ G₁ m₁ o, (G₁ t = g ∨ G₁ t = K.pl.set g p) → m₁.current = t → P.inv G₁ m₁ →
      P.inv G₁ { m₁ with os := o })
    (hret : ∀ G₁ m₁, G₁ t = g → m₁.current = t → P.inv G₁ m₁ →
      P.inv (upd G₁ t (K.pl.set g p)) m₁)
    (hrd : ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → W.hist m' = W.hist m₁ → W.Ok m' (fun u => A (G₁ u)) → W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c, ∃ v : BitVec 32, ((atomicLoadAt c .relaxed 4 W.ptr).run m₁).run =
        some (.ok (v, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → P.inv G₁ m')
    (hUa : ∀ G₁ rX m₁, U (upd G₁ t g) rX m₁ → L.WInv (L.pl (upd G₁ t g)) m₁ →
      U (upd G₁ t (L.set g .away rnil)) rX m₁)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.woken.contains t = false →
      m₁.waiters.any (·.1 == t) = false →
      W.Ok { m₁ with current := t } (fun u => A (G₁ u)) → t < m₁.clocks.size →
      M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M (fun u => A (G₁ u)) → M.blocks = m₁.blocks → W.Holds m₁ e →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.key m₁) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.waiters.any (·.1 == t) = false →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Ok { m₁ with current := t } (fun u => A (G₁ u)) ∧ t < m₁.clocks.size ∧
          M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead ∧
          W.hist M = W.hist m₁ ∧ W.Ok M (fun u => A (G₁ u)) ∧ M.blocks = m₁.blocks)) →
      U (upd G₁ t (K.pl.set g p)) (rsum (W.cellsR m₁) rY) M)
    {Q : Os.WaitResult → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ d, d < n → ∀ r G₁ m', m'.current = t → r ≠ .timedOut →
      P.inv (upd G₁ t (K.pl.set g p)) m' → Q r G₁ m' d)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) (hlva : A (L.set g .away rnil) := by trivial) :
    P.WP t (Os.futexWait W.ptr e false : ConcM Tgt Os.WaitResult) Q G m n := by
  have hheld := hP.heldOut hg hi
  refine WP.osFutexWait fun b₀ m₀ h₀ k hk => ⟨g, ?_, fun G₁ m₁ hg₁ hi₁ ht => ?_⟩
  · obtain ⟨o, rfl⟩ := Os.takeInterrupt_os h₀
    exact hos _ m o (.inl (upd_self _ _ _)) hc hi
  -- the kernel's compare at the pick: an atomic relaxed read of the newest message, by `t` at `g`
  obtain ⟨rY, hiL, hU, hY, hw, hcs⟩ := hP.stopW hW hi₁ ht
  have hAt : A (G₁ t) := hg₁ ▸ hlv
  have hcr : 0 < loadCount 32 .relaxed 4 W.ptr { m₁ with current := t } ∨
      loadCount 32 .relaxed 4 W.ptr { m₁ with current := t } = 0 ∧ 0 = 0 :=
    (Nat.eq_zero_or_pos _).symm.imp_right (⟨·, rfl⟩)
  refine ⟨fun er he => absurd he (hw.load_noErr_native ht hAt hcs hcr er), fun _ => .inr hcost,
    fun v m₂ hr => ?_⟩
  obtain ⟨-, -, -, -, -, hh, hw'⟩ := hw.load_native rfl ht hcs hr
  have hc₁ : t < m₁.clocks.size := by rw [hcs]; exact ht
  have hrest := Word.atomicLoad_rest hw hc₁ hr
  have hA : ∀ hF, (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
      FStepIn hF { m₁ with current := t } m₂ :=
    fun hF hoff => Word.atomicLoad_fstep hw hc₁ hoff hr
  have hc₂ : m₂.current = t :=
    (hA (fun _ => none) (fun _ _ _ => rfl)).current
  have hi₂ : P.inv (upd G₁ t g) m₂ := by
    rw [← hg₁, upd_same]
    exact hrd G₁ rY _ m₂ hg₁ rfl hU hiL.w hY hh hw' hw hc₁ ⟨0, v, hr⟩ hA (fun hf => let hs := Word.atomicLoad_seen hw hf hr; ⟨hs.1, hs.2.1⟩) (hiL.wordStep hY hw hrest hA hap)
  have hr₂ : P.inv (upd G₁ t (K.pl.set g p)) m₂ := by
    have := hret _ _ (upd_self _ _ _) hc₂ hi₂; rwa [upd_upd] at this
  refine ⟨by rw [hrest.threads], fun _ => h k (by omega) _ G₁ m₂ hc₂ (by decide) hr₂,
    fun _ => ⟨h k (by omega) _ G₁ m₂ hc₂ (by decide) hr₂, fun k' hk' => ?_⟩⟩
  -- the sleep: `t` goes away, then the scheduler's wait; at the end an interrupt's delivery
  refine ⟨L.set g .away rnil, hP.goAway hg hi₂ (hUa G₁ · m₂), fun G₂ m₃ hg₂ hi₃ _ =>
    hP.wordWaitStepTo hW hap p hg hheld hlive hUs hUo (fun G₄ m₄ hc₄ hi₄ => ?_) hg₂ hi₃ hlva⟩
  dsimp only
  split
  · exact h k' (by omega) _ G₄ _ hc₄ (by decide) (hos _ _ _ (.inr (upd_self _ _ _)) hc₄ hi₄)
  · exact h k' (by omega) _ G₄ _ hc₄ (by decide) hi₄

/-- **The untimed OS futex wait at the word** (`wp_wordOsWaitTo`) that goes on at `g`. -/
theorem wp_wordOsWait (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {e : BitVec 32} (hg : L.ph g = .out) (hc : m.current = t) (hi : P.inv (upd G t g) m)
    (hos : ∀ G₁ m₁ o, G₁ t = g → m₁.current = t → P.inv G₁ m₁ → P.inv G₁ { m₁ with os := o })
    (hrd : ∀ G₁ rY m₁ m', G₁ t = g → m₁.current = t → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → W.hist m' = W.hist m₁ → W.Ok m' (fun u => A (G₁ u)) → W.Ok m₁ (fun u => A (G₁ u)) → t < m₁.clocks.size →
      (∃ c, ∃ v : BitVec 32, ((atomicLoadAt c .relaxed 4 W.ptr).run m₁).run =
        some (.ok (v, m'))) →
      (∀ hF, (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
        FStepIn hF m₁ m') →
      (W.Fresh m₁ → W.Fresh m' ∧ ∀ u, W.ownPos m₁ u ≤ W.ownPos m' u) →
      L.Inv G₁ (rsum (W.cellsR m') rY) m' → P.inv G₁ m')
    (hUa : ∀ G₁ rX m₁, U (upd G₁ t g) rX m₁ → L.WInv (L.pl (upd G₁ t g)) m₁ →
      U (upd G₁ t (L.set g .away rnil)) rX m₁)
    (hlive : ∀ G₁ m₁, G₁ t = L.set g .away rnil → P.inv G₁ m₁ → P.Live t G₁ m₁)
    (hUs : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.woken.contains t = false →
      m₁.waiters.any (·.1 == t) = false →
      W.Ok { m₁ with current := t } (fun u => A (G₁ u)) → t < m₁.clocks.size →
      M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      W.hist M = W.hist m₁ → W.Ok M (fun u => A (G₁ u)) → M.blocks = m₁.blocks → W.Holds m₁ e →
      U G₁ (rsum (W.cellsR m₁) rY) { M with waiters := M.waiters.push (t, W.key m₁) })
    (hUo : ∀ G₁ rY m₁ M, G₁ t = L.set g .away rnil → U G₁ (rsum (W.cellsR m₁) rY) m₁ →
      L.WInv (L.pl G₁) m₁ → (∀ l, W.In l → rY.heap l = none) → m₁.waiters.any (·.1 == t) = false →
      (M.atomics = m₁.atomics ∧ M.seen = m₁.seen ∧ M.nextMsg = m₁.nextMsg) →
      (M = { m₁ with current := t, woken := m₁.woken.erase t } ∨ M = { m₁ with current := t } ∨
        (W.Ok { m₁ with current := t } (fun u => A (G₁ u)) ∧ t < m₁.clocks.size ∧
          M = ({ m₁ with current := t } : Mem).recordAt W.b W.o 4 .atomicRead ∧
          W.hist M = W.hist m₁ ∧ W.Ok M (fun u => A (G₁ u)) ∧ M.blocks = m₁.blocks)) →
      U (upd G₁ t g) (rsum (W.cellsR m₁) rY) M)
    {Q : Os.WaitResult → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ d, d < n → ∀ r G₁ m', m'.current = t → r ≠ .timedOut → P.inv (upd G₁ t g) m' →
      Q r G₁ m' d)
    (hcost : P.cost = none := by first | rfl | assumption)
    (hlv : A g := by trivial) (hlva : A (L.set g .away rnil) := by trivial) :
    P.WP t (Os.futexWait W.ptr e false : ConcM Tgt Os.WaitResult) Q G m n :=
  wp_wordOsWaitTo hP hW hap (K.pl.ph g) hg hc hi
    (fun G₁ m₁ o hg₁ => hos G₁ m₁ o (by rw [K.pl.set_self, or_self] at hg₁; exact hg₁))
    (fun G₁ m₁ hg₁ _ hi₁ => by rw [K.pl.set_self, ← hg₁, upd_same]; exact hi₁) hrd hUa hlive hUs
    (by rw [K.pl.set_self]; exact hUo) (by rw [K.pl.set_self]; exact h) hcost hlv hlva

/-- **An OS futex wake at the word** (`Os.futexWake`, OSF-02) by thread `t` (`g`): a wake keeps
the lock's invariant with the same rest, and the client shows its `U` after it (given its `U`
and the lock's word invariant at the stop); a spurious
`EINTR` (`spurious`, macOS) wakes nobody, and the protocol's invariant holds at the stop. -/
theorem wp_wordOsWake (hP : L.Fits K P U ok) (hW : W.InRest U A) (hap : W.ApartL L.toLockWord)
    {w : Option Nat} {spurious : Bool} (hi : P.inv (upd G t g) m)
    {Q : Option Nat → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → L.WInv (L.pl G₁) m₁ →
      (∀ cs m', ((Thread.futexWake (W.key m₁)
          (Os.wakeSize w (m₁.waitersAt (W.key m₁)).length) cs).run
          { m₁ with current := t }).run = some (.ok ((), m')) → L.Inv G₁ rX m' →
        Q (some (Os.wakeSize w (m₁.waitersAt (W.key m₁)).length)) G₁ m' k) ∧
      (spurious = true → P.inv (upd G₁ t g) { m₁ with current := t } →
        Q none G₁ { m₁ with current := t } k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t (Os.futexWake W.ptr false w spurious : ConcM Tgt (Option Nat)) Q G m n := by
  refine WP.osFutexWake fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ ht => ?_⟩
  obtain ⟨rX, hiL, hU⟩ := (hP.inv _ _).mp hi₁
  have hWo := (hW _ _ _ hU).1
  obtain ⟨hw, hsp⟩ := h k hk G₁ rX m₁ hg₁ hU hiL.w
  refine ⟨W.key m₁, hWo.keyAt, fun cs m' hr => hw cs m' hr (hiL.wakeOffKey (hiL.key_ne hWo hap) hr),
    fun hs => hsp hs ?_⟩
  obtain ⟨-, -, -, hic⟩ := hP.curT t hi₁ ht
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

/-- The native word facts shared by ordinary and cur-aware caller-part steps. The actual
protected rest contains the word, so its normalized cells and exact history are retained. -/
private theorem Inv.partWordPost {G' : ThreadId → γ} {rY : Res} {m' : Mem}
    {B : ThreadId → Prop} (hi : L.Inv G' (rsum (W.cellsR m) rY) m') (hw : W.Ok m B)
    (hs : FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m') :
    (∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) ∧
    W.Ok m' B ∧ W.hist m' = W.hist m ∧ L.Inv G' (rsum (W.cellsR m') rY) m' := by
  have hcells : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => hi.cellsN hl (hw.cellIn hl)
  have hwF : ∀ l, W.In l → (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase l ≠ none :=
    fun l hl => by
      have := cellsAt_some hl (hw.cellIn hl) (m := m)
      simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
        Option.or_eq_none_iff, not_and]
      intro _ h; exact absurd h this
  exact ⟨hcells, hw.fstep hs hwF hcells, Word.hist_fstep hw hs hwF hcells, hi.restW hcells⟩

/-- **A step of thread `t` on its own part** (`g`, out of the lock's code or holding the lock; a
stack block of a sync object's code), with a thread triple: the client gets the rest with the
word's cells and the lock's invariant before the step, the native framed step, the word's
validity and exact history after it, and the lock's invariant after it, with `t`'s part the
triple's post (`FLock.setPart`) and the word's new cells. -/
theorem wp_liftPartW (hP : L.Fits K P U ok) (hW : W.InRest U A) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r' rY, (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      U (upd G t g) (rsum (W.cellsR m) rY) m → L.Inv (upd G t g) (rsum (W.cellsR m) rY) m →
      (∀ l, W.In l → rY.heap l = none) →
      FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m' →
      (∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) →
      W.Ok m' (fun u => A (upd G t g u)) → W.hist m' = W.hist m →
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
  obtain ⟨hcells, hw', hh, hL'⟩ := hL'.partWordPost hw hs
  exact h a m' r' rY hr hq hc' hU hL hY hs hcells hw' hh hL'

/-- A caller-part step requiring ephemeral `cur t`, with the same native word/rest facts as
`wp_liftPartW`. The token is supplied for the local step and never stored across a stop. -/
theorem wp_liftPartWCur (hP : L.Fits K P U ok) (hW : W.InRest U A) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t)) (hp : Pa (L.part g))
    (h : ∀ a m' r' rY, (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      U (upd G t g) (rsum (W.cellsR m) rY) m → L.Inv (upd G t g) (rsum (W.cellsR m) rY) m →
      (∀ l, W.In l → rY.heap l = none) →
      FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m' →
      (∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) →
      W.Ok m' (fun u => A (upd G t g u)) → W.hist m' = W.hist m →
      L.Inv (upd G t (L.setPart g r')) (rsum (W.cellsR m') rY) m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
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
  refine hL.wp_liftPartCur hc hgo htt hp (fun a m' r' hr hq hs hc' hL' => ?_) hret
  obtain ⟨hcells, hw', hh, hL'⟩ := hL'.partWordPost hw hs
  exact h a m' r' rY hr hq hc' hU hL hY hs hcells hw' hh hL'

/-- A thread not in the futex queue. -/
theorem notQ_mem {α : Type} {ws : Array (ThreadId × α)} {t : ThreadId}
    (h : ws.any (·.1 == t) = false) :
    ∀ w ∈ ws, w.1 ≠ t := fun w hw e => by
  have : ws.any (·.1 == t) = true := Array.any_eq_true'.mpr ⟨w, hw, by simp [e]⟩
  rw [h] at this; cases this

/-- A pending wake of another thread stays when `t`'s goes. -/
theorem woken_erase {ws : Array ThreadId} {t u : ThreadId} (hu : u ≠ t) :
    (ws.erase t).contains u = ws.contains u := by
  rw [Bool.eq_iff_iff, Array.contains_iff_mem, Array.contains_iff_mem, Array.mem_erase_of_ne hu]

/-- **A futex wake at `p` keeps the queue at another futex `q` exactly**, when a thread queued at
`q` is not queued at `p` (`hone`; the wake drops a woken thread's entries by its id). -/
theorem futexWake_waitersAt {p q : FutexKey} {n : Nat} {cs : List Nat} {m m' : Mem}
    (hone : ∀ w ∈ m.waiters, w.2 = q → ∀ w' ∈ m.waiters, w'.1 = w.1 → w'.2 ≠ p)
    (h : ((Thread.futexWake p n cs).run m).run = some (.ok ((), m'))) :
    m'.waiters.filter (·.2 == q) = m.waiters.filter (·.2 == q) := by
  rw [Proto.modify_ok h]
  show (m.waiters.filter _).filter _ = _
  rw [Array.filter_filter]
  apply Array.toList_inj.mp
  simp only [Array.toList_filter]
  refine List.filter_congr fun w hw => ?_
  cases hq : w.2 == q
  · simp
  · have hwq : w.2 = q := by simpa using hq
    have hw' := Array.mem_toList_iff.mp hw
    suffices hn : w.1 ∉ Thread.wakeSet m.waiters p n cs by simp [hn]
    intro hc
    have hmem := Thread.wakePick_mem (List.mem_toArray.mp hc)
    obtain ⟨w', hw'm, he⟩ := List.mem_map.mp hmem
    obtain ⟨hw'w, hw'p⟩ := Array.mem_filter.mp (Array.mem_toList_iff.mp hw'm)
    exact hone w hw' hwq w' hw'w he (by simpa using hw'p)

end FLock

/-- **A sync primitive over futex words** next to the lock `L` (an event, a condition; module
`ZigLean/Sep/Full/Lock.lean`, `FPrim`): its place `pl` (`out` out of its code), the calm places,
the roles, its words `Ws`, its invariant `Inv`, the steps of its code at a word
(`Move W t g p q h m m'`: thread `t` at `g` goes to the place `p`, the lock place `q` and the
lock resource `h`) and the lock places `ownAt` at which a thread in its code steps on its own
part. The rest has each word's cells (`Sub`, `Word.InRest`), the word `Ok` for its live set `Lv W`
(the ghost values of the threads that may still access it). A step, with the word's new cells in
the rest and the invariant after it, is either a step of its code at a word, with the lock's word
invariant before it (`LockWord.WInv`: the step is taken from a state of the protocol, so a client's
rest may use who holds the lock, e.g. `FLock.HB.le`), or a native framed step on the thread's own
part that preserves word validity and exact history. -/
abbrev FPrim.ofWords {γ Ph Rl : Type} (L : FLock γ) (pl : FPlace γ Ph) (out : Ph)
    (calm : Ph → Prop) (role : Rl → γ → Prop) (Ws : Word 32 4 → Prop)
    (Lv : Word 32 4 → γ → Prop) (Inv : (ThreadId → γ) → Mem → Prop)
    (Move : Word 32 4 → ThreadId → γ → Ph → LPh → Res → Mem → Mem → Prop)
    (ownAt : LPh → Prop) : FPrim γ where
  Ph := Ph
  pl := pl
  out := out
  calm := calm
  Role := Rl
  role := role
  Sub G rX m := Inv G m ∧ ∀ W, Ws W →
    W.Ok m (fun u => Lv W (G u)) ∧ ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none
  Apart := ∀ W, Ws W → W.ApartL L.toLockWord
  Step t G rX m G' rX' m' := ∃ W rY, Ws W ∧ rX = rsum (W.cellsR m) rY ∧
    rX' = rsum (W.cellsR m') rY ∧ (∀ l, W.In l → rY.heap l = none) ∧ Inv G' m' ∧
    ((∃ p q h, Move W t (G t) p q h m m' ∧ L.WInv (L.pl G) m ∧
        G' = upd G t (L.set (pl.set (G t) p) q h)) ∨
     (∃ r, ownAt (L.ph (G t)) ∧ L.Inv G rX m ∧ m.current = t ∧
       FStepIn (rsum (L.wordR m) rX).heap.erase m m' ∧
       (∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) ∧
       W.Ok m' (fun u => Lv W (G u)) ∧ W.hist m' = W.hist m ∧
       L.Inv G' rX' m' ∧
       G' = upd G t (L.setPart (G t) r)))

namespace FLock

/-! ## A protocol that keeps a primitive over futex words

What `Fits` gives for `FPrim.ofWords`, once for every such primitive (the event, the condition). -/

section Words

variable {γ : Type} {L : FLock γ} {Tgt : Type} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {W : Word 32 4} {Ph Rl : Type}
  {pl : FPlace γ Ph} {out : Ph} {calm : Ph → Prop} {role : Rl → γ → Prop}
  {Ws : Word 32 4 → Prop} {Lv : Word 32 4 → γ → Prop} {Inv : (ThreadId → γ) → Mem → Prop}
  {Move : Word 32 4 → ThreadId → γ → Ph → LPh → Res → Mem → Mem → Prop} {ownAt : LPh → Prop}
  {t : ThreadId} {G G₁ : ThreadId → γ} {m m₁ m' : Mem} {rY : Res} {g : γ} {p : Ph}

/-- The rest keeps the primitive's invariant. -/
theorem Fits.wInv (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    (G : ThreadId → γ) (rX : Res) (m : Mem) (hU : U G rX m) : Inv G m :=
  (hK.sub G rX m hU).1

/-- The rest has each word's cells. -/
theorem Fits.wRest (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    (hW : Ws W) : W.InRest U (Lv W) :=
  fun G rX m hU => (hK.sub G rX m hU).2 W hW

/-- Each word is apart from the lock's word. -/
theorem Fits.wAp (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    (hW : Ws W) : W.ApartL L.toLockWord :=
  hK.apart W hW

/-- **A step of the primitive's code** at the word `W` keeps the rest, with the stepping thread's
new place `p`, lock place `q` and lock resource `h`, given the lock's word invariant before it and
the primitive's invariant after it. -/
theorem Fits.wStep (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    {q : LPh} {h : Res} (hW : Ws W) (hmv : Move W t (G t) p q h m m')
    (hU : U G (rsum (W.cellsR m) rY) m) (hwL : L.WInv (L.pl G) m)
    (hY : ∀ l, W.In l → rY.heap l = none)
    (hI : Inv (upd G t (L.set (pl.set (G t) p) q h)) m') :
    U (upd G t (L.set (pl.set (G t) p) q h)) (rsum (W.cellsR m') rY) m' :=
  hK.kstep t G _ m _ _ m' (.inl ⟨W, rY, hW, rfl, rfl, hY, hI, .inl ⟨p, q, h, hmv, hwL, rfl⟩⟩) hU

/-- **A step of a thread on its own part** in the primitive's code (at a lock place `ownAt`; a
stack block) keeps the rest, with the thread's new part `r`, given the lock's invariant before it
and the lock's and the primitive's invariants after it. -/
theorem Fits.wOwn (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    {r : Res} (hW : Ws W) (hat : ownAt (L.ph (G t))) (hU : U G (rsum (W.cellsR m) rY) m)
    (hL : L.Inv G (rsum (W.cellsR m) rY) m) (hY : ∀ l, W.In l → rY.heap l = none)
    (hc : m.current = t) (hs : FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m')
    (hcW : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hw' : W.Ok m' (fun u => Lv W (G u))) (hh : W.hist m' = W.hist m)
    (hL' : L.Inv (upd G t (L.setPart (G t) r)) (rsum (W.cellsR m') rY) m')
    (hI : Inv (upd G t (L.setPart (G t) r)) m') :
    U (upd G t (L.setPart (G t) r)) (rsum (W.cellsR m') rY) m' :=
  hK.kstep t G _ m _ _ m' (.inl ⟨W, rY, hW, rfl, rfl, hY, hI,
    .inr ⟨r, hat, hL, hc, hs, hcW, hw', hh, hL', rfl⟩⟩) hU

/-- **After a step of the primitive's code** by `t` (`g`, new place `p`) at the word `W` that
keeps `t`'s lock place and resource: the protocol's invariant, from the lock's invariant after the
step, the rest and the lock's word invariant before it, and the primitive's invariant after it. -/
theorem Fits.back (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    (hW : Ws W) (hg₁ : G₁ t = g) (hmv : Move W t g p (L.ph g) (L.held g) m₁ m')
    (hU : U G₁ (rsum (W.cellsR m₁) rY) m₁) (hwL : L.WInv (L.pl G₁) m₁)
    (hY : ∀ l, W.In l → rY.heap l = none)
    (hL : L.Inv G₁ (rsum (W.cellsR m') rY) m') (hI : Inv (upd G₁ t (pl.set g p)) m') :
    P.inv (upd G₁ t (pl.set g p)) m' := by
  subst hg₁
  have hset : L.set (pl.set (G₁ t) p) (L.ph (G₁ t)) (L.held (G₁ t)) = pl.set (G₁ t) p := by
    have := L.set_self (pl.set (G₁ t) p); rwa [hK.lph, hK.lheld] at this
  have hU' := hK.wStep hW hmv hU hwL hY (by rw [hset]; exact hI)
  rw [hset] at hU'
  have hL' := hL.relabel (g := pl.set (G₁ t) p) (hK.lph _ _) (hK.lpart _ _) (hK.lheld _ _)
    (fun r hr => hK.lR G₁ t p r hr)
  exact (hK.inv _ _).mpr ⟨_, hL', hU'⟩

/-- The facts at a stop of `t` (not at a futex) before an op at a word: the primitive's
invariant, `t` is not in the futex queue. -/
theorem Fits.atOp (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    {rX rX' : Res} (hU : U G₁ rX m₁) (hw : L.ph (G₁ t) ≠ .wait) (ha : L.ph (G₁ t) ≠ .away)
    (hh : L.ph (G₁ t) ≠ .holdsAway) (hwait : m'.waiters = m₁.waiters) (hL : L.Inv G₁ rX' m') :
    Inv G₁ m₁ ∧ ∀ w ∈ m₁.waiters, w.1 ≠ t := by
  refine ⟨hK.wInv _ _ _ hU, ?_⟩
  have := hL.w.notQ (t := t) hw ha hh
  rw [hwait] at this
  exact notQ_mem this

/-- **An interrupt's delivery** (`Os.takeInterrupt`: only the OS state changes) by the current
thread `t`, at a lock place where it steps on its own part (`ownAt`), keeps the protocol's
invariant: it is a step on `t`'s own part that keeps its part (`Fits.wOwn`), given that the
primitive's invariant does not read the OS state (`hIos`). -/
theorem Fits.wOs (hK : L.Fits (FPrim.ofWords L pl out calm role Ws Lv Inv Move ownAt) P U ok)
    (hW : Ws W) (hIos : ∀ G m o, Inv G m → Inv G { m with os := o })
    (hat : ownAt (L.ph (G t))) (hc : m.current = t) (hi : P.inv G m) (o : OsState) :
    P.inv G { m with os := o } := by
  obtain ⟨rX, hL, hU⟩ := (hK.inv _ _).mp hi
  obtain ⟨hw, rY, rfl, hY⟩ := (hK.wRest hW) _ _ _ hU
  have hst : L.Step t m { m with os := o } :=
    LockWord.Step.same rfl rfl rfl rfl rfl rfl rfl
  have hL' := hL.lstay hst (hL.w.osState o)
  have hset : upd G t (L.setPart (G t) (L.part (G t))) = G := by rw [L.setPart_self, upd_same]
  have hcl : W.cellsR { m with os := o } = W.cellsR m := Word.cellsR_congr rfl
  have hs := FStepIn.os m (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase o
  obtain ⟨hw', hh⟩ := hw.fields_native (m' := { m with os := o })
    rfl rfl rfl rfl (fun _ => VClock.le_refl _)
  have hU' := hK.wOwn (r := L.part (G t)) hW hat hU hL hY hc hs (fun _ _ => rfl)
    hw' hh
    (by rw [hset, hcl]; exact hL')
    (by rw [hset]; exact hIos _ _ o (hK.wInv _ _ _ hU))
  rw [hset, hcl] at hU'
  exact (hK.inv _ _).mpr ⟨_, hL', hU'⟩

end Words

end FLock

end Full
end Zig
