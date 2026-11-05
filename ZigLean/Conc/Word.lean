import ZigLean.Conc.Base.Word
import ZigLean.Conc.LockRules
import ZigLean.Sep.Full.Word

/-!
# A shared atomic word: the legacy remainder

The permanent vocabulary of a shared word (`Word`, `Word.Ok`, `Word.hist`, `Word.Extends`, the
records and locations of its ops, the no-error lemmas) is in `ZigLean/Conc/Base/Word.lean`. This
file holds what depends on the legacy layer:

- **The step records** (`Word.BlkStep`, `Word.AtomsStep`; `Word.Keep`, `Word.KeepK`: the same
  cells and location, and no new access to the word): a step of a thread on its own part
  (`keep_stepIn`, over the legacy `StepIn`), a spawn, a join and a plain read keep each word that
  the step does not touch, with the same writes (`hist_keep`).
- **The Lock-typed lemmas**: a word apart from a legacy lock (`Apart`) is kept by a step of the
  lock's code (`keep_lockStep`), an op at it keeps the lock's invariant (`Lock.Inv.wordOp`), and a
  futex wait at it is off the lock (`offWord`).
- **The old Word contract** (`Word.Op`, whose `locs` field is the legacy `LocsKeep`): its
  producers, a load (`Ok.load`), an RMW (`Ok.rmw`, `Ok.rmwAt`), a `cmpxchg` (`Ok.cas`), a read
  (`Ok.read`), a record (`Ok.record`, `Ok.prep`) and a futex wait (`Ok.futexWait`); and its
  projections (`Op.clocks`, `keep_op`, `BlkStep.eq_set`, `Op.rest`, `Op.block`, `Op.lockLoc`,
  `Op.fpAt`, `Op.word`, `FLock.Inv.wordOp`).

It leaves with `ZigLean/Conc/Lock.lean` (stage D-d, engine-ledger row
`seen-floor-sync-retirement`).
-/

namespace Zig
namespace Conc

open Assn Proto

namespace Word

variable {n nb : Nat} (W : Word n nb)

/-- The blocks after an op at the word: the same, but the bytes of the word. -/
structure BlkStep (m m' : Mem) : Prop where
  size : m'.blocks.size = m.blocks.size
  other : ∀ b, b ≠ W.b → m'.blocks[b]? = m.blocks[b]?
  word : ∀ blk, m.blocks[W.b]? = some blk → ∃ blk', m'.blocks[W.b]? = some blk' ∧
    blk'.addr = blk.addr ∧ blk'.live = blk.live ∧ blk'.kind = blk.kind ∧
    blk'.bytes.size = blk.bytes.size ∧ ∀ x, (x < W.o ∨ W.o + nb ≤ x) → blk'.bytes[x]? = blk.bytes[x]?

/-- The atomic locations after an op at the word: the same shapes, or one new location at the
word, where there was none. -/
def AtomsStep (m m' : Mem) : Prop :=
  keys m' = keys m ∨
    (keys m' = (keys m).push (W.b, W.o, nb) ∧ ∀ l ∈ m.atomics, ¬ (l.block = W.b ∧ l.off = W.o))

/-- A step that keeps the word, its cells up to `cellKey` (a step of the full-state logic,
`FStepIn`, whose frame keeps cells up to `Cell.norm`): the word's location stays (perhaps at
another index), a location of the step has the bytes of an old one or is apart from the word, an
access to the word is an old one or a narrowing of one, and the clocks of the threads do not get
smaller. -/
structure KeepK (m m' : Mem) : Prop where
  cells : ∀ x, W.o ≤ x → x < W.o + nb →
    (m'.heap (W.b, x)).map cellKey = (m.heap (W.b, x)).map cellKey
  loc : ∀ l, (∃ i, W.Loc m' i l) ↔ (∃ i, W.Loc m i l)
  only : ∀ l ∈ m'.atomics, (∃ l₀ ∈ m.atomics, l.block = l₀.block ∧ l.off = l₀.off ∧ l.len = l₀.len) ∨
    l.block ≠ W.b ∨ l.off + l.len ≤ W.o ∨ W.o + nb ≤ l.off
  fp : ∀ e ∈ m'.footprint, (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨ ¬ W.Hits e
  all : ∀ c, AllLe m c → AllLe m' c
  some : ∀ c, SomeLe m c → SomeLe m' c

/-- A step that keeps the word (module doc): the clocks of the threads do not get smaller (a
new thread's clock is above another one's). -/
structure Keep (m m' : Mem) : Prop where
  cells : ∀ x, W.o ≤ x → x < W.o + nb → m'.heap (W.b, x) = m.heap (W.b, x)
  loc : ∀ i l, W.Loc m' i l ↔ W.Loc m i l
  only : ∀ l ∈ m'.atomics, l ∈ m.atomics ∨ l.block ≠ W.b ∨ l.off + l.len ≤ W.o ∨ W.o + nb ≤ l.off
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ ¬ W.Hits e
  all : ∀ c, AllLe m c → AllLe m' c
  some : ∀ c, SomeLe m c → SomeLe m' c

variable {W}

/-! ## The blocks and the atomic layout after an op -/

theorem BlkStep.of_eq {m m' : Mem} (h : m'.blocks = m.blocks) : W.BlkStep m m' :=
  ⟨by rw [h], fun b _ => by rw [h], fun blk hb => ⟨blk, by rw [h]; exact hb, rfl, rfl, rfl, rfl,
    fun _ _ => rfl⟩⟩

/-- An op at the word keeps every block's address, so every futex key (`Mem.keyAt_of_addrs`). -/
theorem BlkStep.addrs {m m' : Mem} (h : W.BlkStep m m') : m.SameAddrs m' := fun b blk hb => by
  by_cases e : b = W.b
  · subst e
    obtain ⟨blk', h1, h2, -⟩ := h.word blk hb
    exact ⟨blk', h1, h2⟩
  · exact ⟨blk, by rw [h.other b e]; exact hb, rfl⟩

/-- A step that keeps the word keeps the futex keys of its block: a cell of the word holds the
block's address (`Mem.wordKey_of_heap`). -/
theorem Keep.wordKey {m m' : Mem} (hk : W.Keep m m') (hw : W.Ok m) (hnb : 0 < nb) (o : Nat)
    (sh : Bool) : m'.wordKey W.b o sh = m.wordKey W.b o sh := by
  obtain ⟨blk, hblk, hl, hs, -, -, hlo⟩ := hw.blk
  exact Mem.wordKey_of_heap ((Mem.heap_of hblk W.o).trans (dif_pos ⟨hl, by omega, hlo⟩))
    (hk.cells W.o (Nat.le_refl _) (by omega)) _ _

/-- A step that keeps the word keeps its futex key (`Keep.wordKey`). -/
theorem Keep.key {m m' : Mem} (hk : W.Keep m m') (hw : W.Ok m) (hnb : 0 < nb) :
    W.key m' = W.key m :=
  hk.wordKey hw hnb _ _

theorem BlkStep.trans {m₁ m₂ m₃ : Mem} (h₁ : W.BlkStep m₁ m₂) (h₂ : W.BlkStep m₂ m₃) :
    W.BlkStep m₁ m₃ := by
  refine ⟨h₂.size.trans h₁.size, fun b hb => (h₂.other b hb).trans (h₁.other b hb), fun blk hb => ?_⟩
  obtain ⟨blk₂, hb₂, a₂, l₂, k₂, s₂, x₂⟩ := h₁.word blk hb
  obtain ⟨blk₃, hb₃, a₃, l₃, k₃, s₃, x₃⟩ := h₂.word blk₂ hb₂
  exact ⟨blk₃, hb₃, a₃.trans a₂, l₃.trans l₂, k₃.trans k₂, s₃.trans s₂,
    fun x hx => (x₃ x hx).trans (x₂ x hx)⟩

/-- A write of the word's bytes. -/
theorem BlkStep.write {m m' : Mem} {blk : Block} {bs : Array Byte} (hb : m.blocks[W.b]? = some blk)
    (hs : bs.size = nb) (hsz : W.o + nb ≤ blk.bytes.size)
    (h : m'.blocks = m.blocks.set! W.b { blk with bytes := writeBytes blk.bytes W.o bs }) :
    W.BlkStep m m' := by
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨by rw [h]; simp, fun b hne => ?_, fun blk' hb' => ?_⟩
  · rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
  · rw [hb] at hb'; cases hb'
    refine ⟨{ blk with bytes := writeBytes blk.bytes W.o bs },
      by rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt],
      rfl, rfl, rfl, writeBytes_size _ _ _ (by omega), fun x hx => ?_⟩
    show (writeBytes blk.bytes W.o bs)[x]? = blk.bytes[x]?
    rw [writeBytes_getElem? _ _ _ (by omega), if_neg (by omega)]

theorem AtomsStep.of_eq {m m' : Mem} (h : m'.atomics = m.atomics) : W.AtomsStep m m' :=
  .inl (by unfold keys; rw [h])

theorem AtomsStep.trans {m₁ m₂ m₃ : Mem} (h₁ : W.AtomsStep m₁ m₂) (h₂ : W.AtomsStep m₂ m₃) :
    W.AtomsStep m₁ m₃ := by
  rcases h₁ with e₁ | ⟨e₁, n₁⟩ <;> rcases h₂ with e₂ | ⟨e₂, n₂⟩
  · exact .inl (e₂.trans e₁)
  · refine .inr ⟨by rw [e₂, e₁], fun l hl hw => ?_⟩
    obtain ⟨l', hl', he⟩ := mem_keys.mp (show (l.block, l.off, l.len) ∈ keys m₂ by
      rw [e₁]; exact mem_keys.mpr ⟨l, hl, rfl⟩)
    simp only [Prod.mk.injEq] at he
    exact n₂ l' hl' ⟨he.1.trans hw.1, he.2.1.trans hw.2⟩
  · exact .inr ⟨by rw [e₂, e₁], n₁⟩
  · exfalso
    obtain ⟨l', hl', he⟩ := mem_keys.mp (show (W.b, W.o, nb) ∈ keys m₂ by
      rw [e₁]; exact Array.mem_push_self)
    simp only [Prod.mk.injEq] at he
    exact n₂ l' hl' ⟨he.1, he.2.1⟩

/-! ## Steps that keep the word -/

/-- A step that keeps the word with the same cells keeps them up to `cellKey`. -/
theorem Keep.toK {m m' : Mem} (hk : W.Keep m m') : W.KeepK m m' :=
  ⟨fun x h1 h2 => by rw [hk.cells x h1 h2],
    fun l => ⟨fun ⟨i, h⟩ => ⟨i, (hk.loc i l).mp h⟩, fun ⟨i, h⟩ => ⟨i, (hk.loc i l).mpr h⟩⟩,
    fun l hl => (hk.only l hl).imp (fun h => ⟨l, h, rfl, rfl, rfl⟩) id,
    fun e he => (hk.fp e he).imp (fun h => ⟨e, h, .refl e⟩) id, hk.all, hk.some⟩

theorem hist_keepK {m m' : Mem} (hw : W.Ok m) (hk : W.KeepK m m') : W.hist m' = W.hist m := by
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨j, hj⟩ := (hk.loc _).mpr ⟨i, hl⟩
    rw [hist_loc hl, hist_loc hj]
  | none =>
    have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    have hn' : ∀ i l, ¬ W.Loc m' i l := fun i l hl => by
      obtain ⟨j, hj⟩ := (hk.loc l).mp ⟨i, hl⟩
      exact hn j l hj
    rw [hist_none hn, hist_none hn', (congr hk.cells hw.blk).2]

theorem hist_keep {m m' : Mem} (hw : W.Ok m) (hk : W.Keep m m') : W.hist m' = W.hist m :=
  hist_keepK hw hk.toK

/-- A step that keeps the word (`Keep`, `KeepK`: a lock step, a step on a thread's own part, a
spawn, a join, a plain read, an op at another word). -/
theorem Extends.keepK {m m' : Mem} (hw : W.Ok m) (hk : W.KeepK m m') : W.Extends m m' :=
  .of_eq (hist_keepK hw hk)

/-- A step that keeps the word keeps its invariant. -/
theorem Ok.keepK {m m' : Mem} (hw : W.Ok m) (hk : W.KeepK m m') : W.Ok m' := by
  obtain ⟨hb', hcur⟩ := congr hk.cells hw.blk
  refine ⟨hb', fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun e he hh => ?_, ?_,
    fun i l hl e he hp => ?_⟩
  · rcases hk.only l hl with ⟨l₀, hl₀, eb, eo, el⟩ | h | h | h
    · have := hw.only l₀ hl₀ (eb.symm.trans hb) (by omega) (by omega)
      omega
    · exact absurd hb h
    · omega
    · omega
  · obtain ⟨j, hj⟩ := (hk.loc l).mp ⟨i, hl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw.loc j l hj
    exact ⟨h1, h2, h3, by rw [h4, hcur], h5⟩
  · rcases hk.fp e he with ⟨e₀, he₀, hn⟩ | h
    · rcases hw.wfp e₀ he₀ (hits_narrows hn hh) with ⟨ha, u, hu, hle⟩ | ha
      · exact .inl ⟨by rw [hn.2.2.1]; exact ha, hk.some _ ⟨u, hu, VClock.le_trans hn.clock hle⟩⟩
      · exact .inr ((hk.all _ fun u hu => VClock.le_trans hn.clock (ha u hu trivial)).on _)
    · exact absurd hh h
  · obtain ⟨v, hv⟩ := hw.val; exact ⟨v, by unfold Word.Holds; rw [hcur]; exact hv⟩
  · obtain ⟨j, hj⟩ := (hk.loc l).mp ⟨i, hl⟩
    rcases hk.fp e he with ⟨e₀, he₀, hn⟩ | h
    · exact VClock.le_trans hn.clock (hw.plain j l hj e₀ he₀ (hn.plainHit hp))
    · rw [plainHit_false h] at hp; cases hp

theorem Ok.keep {m m' : Mem} (hw : W.Ok m) (hk : W.Keep m m') : W.Ok m' := hw.keepK hk.toK

/-- The same blocks, atomic locations and footprint, and clocks that do not get smaller. -/
theorem keep_of {m m' : Mem} (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) (ht : m'.threads = m.threads)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) : W.Keep m m' :=
  ⟨fun x _ _ => by simp only [Mem.heap, hb], fun i l => by unfold Word.Loc; rw [ha],
    fun l hl => .inl (ha ▸ hl), fun e he => .inl (hf ▸ he),
    fun _ h u hu => VClock.le_trans (h u (ht ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, ht ▸ hu, VClock.le_trans hle (hcl u)⟩⟩

/-- The same memory, but `current`, `seen`, `nextMsg`, the futex queue, the woken threads and
the groups. -/
theorem keep_same (m : Mem) (c : ThreadId) (s : Array (ThreadId × Nat × Nat)) (k : Nat)
    (ws : Array (ThreadId × FutexKey)) (wk : Array ThreadId) (gs : Array (Ptr × ThreadId)) :
    W.Keep m { m with current := c, seen := s, nextMsg := k, waiters := ws, woken := wk, groups := gs } :=
  keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _

/-- A step of thread `t` on its own part (`WP.liftMem_owned`), which has no byte of the word
(its cells are in the rest of the heap, `hF`). -/
theorem keep_stepIn_of {m m' : Mem} {own hQ : Heap}
    (hF : ∀ x, W.o ≤ x → x < W.o + nb → m.heap.diff own (W.b, x) ≠ none)
    (hs : StepIn (m.heap.diff own) m m') (hm' : m'.heap = hQ ∪ m.heap.diff own)
    (hd : Heap.Disjoint hQ (m.heap.diff own)) : W.Keep m m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    by_cases hu : u = m.current
    · subst hu; exact hs.mine
    · rw [hs.others u hu]; exact VClock.le_refl _
  refine ⟨fun x h1 h2 => ?_, fun i l => by unfold Word.Loc; rw [hs.atomics],
    fun l hl => .inl (hs.atomics ▸ hl), fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u (hs.threads ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hs.threads ▸ hu, VClock.le_trans hle (hcl u)⟩⟩
  · rw [hm', Heap.union_of_right ((hd (W.b, x)).resolve_right (hF x h1 h2))]
    have hF' := hF x h1 h2
    unfold Heap.diff at hF' ⊢; split at hF' <;> simp_all
  · rcases hs.fp e he with h | ⟨-, hnt, -⟩
    · exact .inl h
    · exact .inr fun hh => hnt (touches_of hh hF)

/-- A step of thread `t` on its own part (`WP.liftMem_owned`), which has no byte of the word. -/
theorem keep_stepIn {m m' : Mem} {own hQ : Heap} (hw : W.Ok m) (hoff : W.Off own)
    (hs : StepIn (m.heap.diff own) m m') (hm' : m'.heap = hQ ∪ m.heap.diff own)
    (hd : Heap.Disjoint hQ (m.heap.diff own)) : W.Keep m m' :=
  keep_stepIn_of (fun x h1 h2 => by
    simp only [Heap.diff, hoff x h1 h2, ↓reduceIte]; exact hw.cell h1 h2) hs hm' hd

/-- A spawn by `t`. -/
theorem keep_fork {m m' : Mem} {t c : ThreadId} (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) : W.Keep m m' := by
  obtain ⟨rfl, rfl⟩ := fork_eq hf
  obtain ⟨hcl, hcn, -⟩ := fork_clocks (cs := m.clocks) (t := t) (by rw [hcs]; exact ht)
  refine ⟨fun x _ _ => rfl, fun i l => Iff.rfl, fun l hl => .inl hl, fun e he => .inl he,
    fun _ h u hu => ?_, fun _ ⟨u, hu, hle⟩ => ⟨u, by simp only [Array.size_push]; omega,
      VClock.le_trans hle (hcl u (by rw [hcs]; exact hu))⟩⟩
  simp only [Array.size_push] at hu
  by_cases hu' : u < m.threads.size
  · exact VClock.le_trans (h u hu') (hcl u (by rw [hcs]; exact hu'))
  · have : u = m.threads.size := by omega
    subst this; rw [← hcs]; exact VClock.le_trans (h t ht) hcn

/-- A join of `u` by `t`. -/
theorem keep_join {m m' : Mem} {t u : ThreadId}
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) : W.Keep m m' := by
  obtain ⟨rec, -, -, rfl⟩ := Proto.join_eq hj
  have hcl : ∀ w : Nat, VClock.le (m.clocks[w]!) ((m.clocks.set! t (VClock.merge
      (VClock.bump (m.clocks[t]!) t) (m.clocks[u]!)))[w]!) = true := by
    intro w
    rw [Proto.getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hsz : (m.threads.set! u { rec with joined := true }).size = m.threads.size := by simp
  exact ⟨fun x _ _ => rfl, fun i l => Iff.rfl, fun l hl => .inl hl, fun e he => .inl he,
    fun _ h w hw => VClock.le_trans (h w (hsz ▸ hw)) (hcl w),
    fun _ ⟨w, hw, hle⟩ => ⟨w, by rw [hsz]; exact hw, VClock.le_trans hle (hcl w)⟩⟩

/-- A plain read of `n` bytes at `o` of block `b` that do not hit the word. -/
theorem keep_read (m : Mem) {b o n : Nat} (hnw : b ≠ W.b ∨ o + n ≤ W.o ∨ W.o + nb ≤ o) :
    W.Keep m (m.recordAt b o n .read) := by
  refine ⟨fun x _ _ => rfl, fun i l => Iff.rfl, fun l hl => .inl hl, fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u hu) (recordAt_le m _ _ _ _ u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hu, VClock.le_trans hle (recordAt_le m _ _ _ _ u)⟩⟩
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact .inl he
  · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
    dsimp only at hb' h1 h2
    rcases hnw with h | h | h
    · exact h hb'
    · omega
    · omega

/-! ## A word apart from a legacy lock -/

/-- The lock's word and `W` do not overlap. -/
def Apart {γ : Type} (L : Lock γ) {n nb : Nat} (W : Word n nb) : Prop := L.b ≠ W.b ∨ L.o + 4 ≤ W.o ∨ W.o + nb ≤ L.o

/-- A step of the lock's code keeps a word apart from the lock's. -/
theorem keep_lockStep {γ : Type} {L : Lock γ} {t : ThreadId} {m m' : Mem} (hs : L.Step t m m')
    (hap : Apart L W) : W.Keep m m' := by
  have hsz0 := W.sz_pos
  refine ⟨fun x h1 h2 => hs.heap ?_, fun i l => ?_, fun l hl => ?_, fun e he => ?_,
    fun _ h => hs.allLe h, fun _ h => hs.someLe h⟩
  · rintro ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb.symm
    · omega
    · omega
  · have hne : W.b ≠ L.b ∨ W.o ≠ L.o := by
      rcases hap with h | h | h
      · exact .inl (Ne.symm h)
      · exact .inr (by omega)
      · exact .inr (by omega)
    exact hs.locs.same W.b W.o hne i l
  · rcases hs.locs.new l hl with h | ⟨hb, ho, hlen⟩
    · exact .inl h
    · rcases hap with h | h | h
      · exact .inr (.inl (by rw [hb]; exact h))
      · exact .inr (.inr (.inl (by omega)))
      · exact .inr (.inr (.inr (by omega)))
  · rcases hs.fp e he with h | ⟨hb, ho, hl, -⟩
    · exact .inl h
    · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
      rw [hb] at hb'
      rcases hap with h | h | h
      · exact h hb'
      · omega
      · omega

/-! ## An atomic op at the word -/

/-- An atomic op at the word by thread `t`: the threads, the futex queue and the groups stay,
only `t`'s clock grows, only the word's cells change, each new access is an atomic access to the
word, and the atomic locations of other addresses stay. -/
structure Op (t : ThreadId) (m m' : Mem) : Prop where
  current : m'.current = t
  threads : m'.threads = m.threads
  waiters : m'.waiters = m.waiters
  woken : m'.woken = m.woken
  groups : m'.groups = m.groups
  csize : m'.clocks.size = m.clocks.size
  others : ∀ u, u ≠ t → m'.clocks[u]! = m.clocks[u]!
  mine : VClock.le (m.clocks[t]!) (m'.clocks[t]!) = true
  bsize : m'.blocks.size = m.blocks.size
  cells : ∀ l : Zig.Loc, ¬ (l.1 = W.b ∧ W.o ≤ l.2 ∧ l.2 < W.o + nb) → m'.heap l = m.heap l
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    (e.block = W.b ∧ e.off = W.o ∧ e.len = nb ∧ e.kind.isAtomic = true ∧ SomeLe m' e.clock)
  locs : LocsKeep W.b W.o nb m m'
  /-- A new access is by thread `t`, below its new clock. -/
  fpt : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.tid = t ∧ VClock.le e.clock (m'.clocks[t]!) = true)
  /-- The blocks stay, but the word's bytes. -/
  blocks : W.BlkStep m m'
  /-- The atomic layout changes at most by a new location at the word. -/
  atoms : W.AtomsStep m m'
  /-- The stack states, the placement and the step count stay (`Mem.Aux`). -/
  aux : m.Aux m'
  /-- The messages stay covered (`Mem.MsgCov`). -/
  cov : m.MsgCov → m'.MsgCov

theorem Op.clocks {t : ThreadId} {m m' : Mem} (h : W.Op t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  by_cases hu : u = t
  · subst hu; exact h.mine
  · rw [h.others u hu]; exact VClock.le_refl _

theorem Op.someLe {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {c : VClock} (hc : SomeLe m c) :
    SomeLe m' c := by
  obtain ⟨u, hu, hle⟩ := hc
  exact ⟨u, h.threads ▸ hu, VClock.le_trans hle (h.clocks u)⟩

theorem Op.allLe {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {c : VClock} (hc : AllLe m c) :
    AllLe m' c := fun u hu => VClock.le_trans (hc u (h.threads ▸ hu)) (h.clocks u)

theorem Op.trans {t : ThreadId} {m₁ m₂ m₃ : Mem} (h₁ : W.Op t m₁ m₂) (h₂ : W.Op t m₂ m₃) :
    W.Op t m₁ m₃ := by
  refine ⟨h₂.current, h₂.threads.trans h₁.threads, h₂.waiters.trans h₁.waiters,
    h₂.woken.trans h₁.woken, h₂.groups.trans h₁.groups, h₂.csize.trans h₁.csize,
    fun u hu => (h₂.others u hu).trans (h₁.others u hu), VClock.le_trans h₁.mine h₂.mine,
    h₂.bsize.trans h₁.bsize, fun l hl => (h₂.cells l hl).trans (h₁.cells l hl), fun e he => ?_,
    h₁.locs.trans h₂.locs, fun e he => ?_, h₁.blocks.trans h₂.blocks, h₁.atoms.trans h₂.atoms,
    h₁.aux.trans h₂.aux, fun h => h₂.cov (h₁.cov h)⟩
  · rcases h₂.fp e he with h | h
    · rcases h₁.fp e h with h' | ⟨a, b, c, d, f⟩
      · exact .inl h'
      · exact .inr ⟨a, b, c, d, h₂.someLe f⟩
    · exact .inr h
  · rcases h₂.fpt e he with h | h
    · rcases h₁.fpt e h with h' | ⟨ht, hle⟩
      · exact .inl h'
      · exact .inr ⟨ht, VClock.le_trans hle h₂.mine⟩
    · exact .inr h

/-- An op from a stop of `t` (`current := c`) is an op from the memory before it. -/
theorem Op.of_cur {t c : ThreadId} {m m' : Mem} (hop : W.Op t { m with current := c } m') :
    W.Op t m m' :=
  ⟨hop.current, hop.threads, hop.waiters, hop.woken, hop.groups, hop.csize, hop.others,
    hop.mine, hop.bsize, hop.cells, hop.fp, ⟨hop.locs.new, hop.locs.same⟩, hop.fpt,
    ⟨hop.blocks.size, hop.blocks.other, hop.blocks.word⟩, hop.atoms, hop.aux, hop.cov⟩

/-- An op at the word keeps a word apart from it. -/
theorem keep_op {n' nb' : Nat} {W' : Word n' nb'} {t : ThreadId} {m m' : Mem} (h : W.Op t m m')
    (hap : W.b ≠ W'.b ∨ W.o + nb ≤ W'.o ∨ W'.o + nb' ≤ W.o) : W'.Keep m m' := by
  have hsz0 := W.sz_pos
  have hsz1 := W'.sz_pos
  refine ⟨fun x h1 h2 => h.cells _ ?_, fun i l => ?_, fun l hl => ?_, fun e he => ?_,
    fun _ hc => h.allLe hc, fun _ hc => h.someLe hc⟩
  · rintro ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb.symm
    · omega
    · omega
  · have hne : W'.b ≠ W.b ∨ W'.o ≠ W.o := by
      rcases hap with h | h | h
      · exact .inl (Ne.symm h)
      · exact .inr (by omega)
      · exact .inr (by omega)
    exact h.locs.same W'.b W'.o hne i l
  · rcases h.locs.new l hl with h' | ⟨hb, ho, hlen⟩
    · exact .inl h'
    · rcases hap with h' | h' | h'
      · exact .inr (.inl (by rw [hb]; exact h'))
      · exact .inr (.inr (.inl (by omega)))
      · exact .inr (.inr (.inr (by omega)))
  · rcases h.fp e he with h' | ⟨hb, ho, hl, -⟩
    · exact .inl h'
    · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
      rw [hb] at hb'
      rcases hap with h' | h' | h'
      · exact h' hb'
      · omega
      · omega

/-- Recording an atomic access preserves the shared word and its history. -/
theorem Ok.record {m : Mem} {t : Nat} {k : AccessKind} (hw : W.Ok m) (hc : m.current = t)
    (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size) (hk : k.isAtomic = true) :
    W.Ok (m.recordAt W.b W.o nb k) ∧ W.Op t m (m.recordAt W.b W.o nb k) ∧
      W.hist (m.recordAt W.b W.o nb k) = W.hist m := by
  obtain ⟨hwr, hh⟩ := hw.record_native hc ht hcs hk
  subst hc
  have hct : m.current < m.clocks.size := by rw [hcs]; exact ht
  -- the record
  let mr := m.recordAt W.b W.o nb k
  have hrt : mr.clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current := by
    simp only [mr, Mem.recordAt]; rw [Proto.getElem!_set!_ite]; simp [hct]
  have hro : ∀ u, u ≠ m.current → mr.clocks[u]! = m.clocks[u]! := by
    intro u hu; simp only [mr, Mem.recordAt]; rw [Proto.getElem!_set!_ite, if_neg (fun h => hu h.1)]
  have hopr : W.Op m.current m mr := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [mr, Mem.recordAt], hro,
      by rw [hrt]; exact VClock.le_bump _ _, rfl, fun l _ => rfl, fun e he => ?_, .of_eq rfl,
      fun e he => ?_, .of_eq rfl, .of_eq rfl, ⟨rfl, rfl, rfl⟩, Mem.MsgCov.recordAt⟩
    · simp only [mr, Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · refine .inr ⟨rfl, rfl, rfl, hk, m.current, ht, ?_⟩
        show VClock.le _ (mr.clocks[m.current]!) = true
        rw [hrt]; exact VClock.le_refl _
    · simp only [mr, Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact .inl he
      · refine .inr ⟨rfl, ?_⟩
        show VClock.le _ (mr.clocks[m.current]!) = true
        rw [hrt]; exact VClock.le_refl _
  exact ⟨hwr, hopr, hh⟩

/-- The record of an atomic access to the word, and the word's location (`locIdx`): the
location exists after it, with the same writes. -/
theorem Ok.prep {m m₁ : Mem} {t li : Nat} {k : AccessKind} (hw : W.Ok m) (hc : m.current = t)
    (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size) (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m₁))) :
    ∃ l, W.Loc m₁ li l ∧ W.Ok m₁ ∧ W.Op t m m₁ ∧ W.hist m₁ = W.hist m ∧ m₁.blocks = m.blocks ∧
      m₁.seen = m.seen ∧ W.Rec m₁ t := by
  obtain ⟨l₁, hl₁, hw₁, hh₁, hb₁, hs₁, hrec₁⟩ := hw.prep_native hc ht hcs hk h
  refine ⟨l₁, hl₁, hw₁, ?_, hh₁, hb₁, hs₁, hrec₁⟩
  subst hc
  let mr := m.recordAt W.b W.o nb k
  obtain ⟨hwr, hopr, -⟩ := hw.record rfl ht hcs hk
  have hcov : mr.MsgCov → m₁.MsgCov := by
    obtain ⟨blk, hb, -, hsz, -⟩ := hw.blk
    exact (FStepIn.locIdx (m := mr) (hF := fun _ => none) W.sz_pos (fun _ _ _ => rfl)
      ⟨blk, hb, hsz⟩ h).msgCov
  -- the location
  cases hf : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨hlen, -, -, hlast, -⟩ := hwr.loc i _ hl
    obtain ⟨rfl, rfl⟩ := locIdx_found hf hlen hlast (hwr.plain i _ hl) h
    exact hopr
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new hf (noOverlap_of_only hf hwr.only) h
    refine hopr.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _, rfl,
      fun _ _ => rfl, fun e he => .inl he, .push rfl rfl rfl rfl, fun e he => .inl he,
      .of_eq rfl, .inr ⟨by unfold keys; rw [Array.map_push], fun l hl hw => ?_⟩, ⟨rfl, rfl, rfl⟩,
      hcov⟩
    have := Array.findIdx?_eq_none_iff.mp hf l hl
    simp [hw.1, hw.2] at this

/-! ## The ops at the word -/

/-- An RMW at the word by thread `t` that read the newest message of `l` and wrote `new`. -/
theorem Ok.rmwAt {m₁ M : Mem} {t li : Nat} {l : ALoc} {ord : AtomicOrder} {new : BitVec n}
    (hw : W.Ok m₁) (hl : W.Loc m₁ li l) (hc : m₁.current = t) (ht : t < m₁.threads.size)
    (hcs : m₁.clocks.size = m₁.threads.size) (hrec : W.Rec m₁ t)
    (hM : M = rmwM m₁ li (l.msgs.size - 1) ord (l.msgs[l.msgs.size - 1]!) new) :
    W.Ok M ∧ W.Op t m₁ M ∧ W.Holds M new ∧
      W.hist M = (W.hist m₁).push (rmwEnt M t ord (W.hist m₁)[(W.hist m₁).size - 1]! new) ∧
      (ord.isAcq = true →
        VClock.le (W.hist m₁)[(W.hist m₁).size - 1]!.relClock (M.clocks[t]!) = true) := by
  subst hc
  obtain ⟨hlen, h0, hch, hlast, hval⟩ := hw.loc li l hl
  obtain ⟨hlb, hlo⟩ := loc_at hl
  obtain ⟨hli, -, hl0⟩ := loc_get hl
  obtain ⟨blk, hb, hlv, hsz, ha4, hk⟩ := hw.blk
  have hct : m₁.current < m₁.clocks.size := by rw [hcs]; exact ht
  let rd := l.msgs[l.msgs.size - 1]!
  let m₂ := if ord.isAcq then acqM m₁ rd.relClock else m₁
  have h2 : m₂.atomics = m₁.atomics ∧ m₂.blocks = m₁.blocks ∧ m₂.threads = m₁.threads ∧
      m₂.footprint = m₁.footprint ∧ m₂.waiters = m₁.waiters ∧ m₂.current = m₁.current ∧
      m₂.groups = m₁.groups ∧ m₂.woken = m₁.woken ∧ m₂.nextMsg = m₁.nextMsg ∧
      m₂.clocks.size = m₁.clocks.size := by
    simp only [m₂]; split <;> simp [acqM]
  obtain ⟨ha₂, hb₂, ht₂, hf₂, hw₂, hc₂, hg₂, hk₂, hn₂, hcs₂⟩ := h2
  have hl₂ : m₂.atomics[li]! = l := by rw [ha₂]; exact hl0
  have hblk₂ : m₂.blocks[(m₂.atomics[li]!).block]? = some blk := by rw [hl₂, hlb, hb₂]; exact hb
  have hins := insertM_last (msg := rmwMsg m₂ ord rd new) hblk₂
  rw [hl₂] at hins
  have hp : l.msgs.size - 1 + 1 = l.msgs.size := by omega
  have hMe : M = observeM { m₂ with
      atomics := m₂.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) },
      nextMsg := m₂.nextMsg + 1,
      blocks := m₂.blocks.set! l.block
        { blk with bytes := writeBytes blk.bytes l.off (rmwMsg m₂ ord rd new).bytes } } li m₂.nextMsg := by
    rw [hM]; unfold rmwM; simp only; rw [hp, hins]
  -- the clocks
  have hcl₂ : ∀ u, u ≠ m₁.current → m₂.clocks[u]! = m₁.clocks[u]! := by
    intro u hu; simp only [m₂]; split
    · simp only [acqM]; rw [Proto.getElem!_set!_ite, if_neg (fun h => hu h.1)]
    · rfl
  have hct₂ : VClock.le (m₁.clocks[m₁.current]!) (m₂.clocks[m₁.current]!) = true := by
    simp only [m₂]; split
    · rw [acqM_clock _ _ hct]; exact VClock.le_merge_left _ _
    · exact VClock.le_refl _
  have hMc : M.clocks = m₂.clocks := by rw [hMe]; rfl
  have hMa : M.atomics = m₁.atomics.set! li { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) } := by
    rw [hMe]; simp only [observeM, ha₂]
  have hMb : M.blocks[W.b]? = some { blk with bytes := writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new)) } := by
    rw [hMe]; simp only [observeM, hb₂, hlb, hlo, rmwMsg]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (Array.getElem?_eq_some_iff.mp hb).1]
  have hMbs : M.blocks.size = m₁.blocks.size := by rw [hMe]; simp [observeM, hb₂]
  have hbs : (padTo (intSize n) (intBytes new)).size = nb := W.enc_size new
  have hcur : curBytes M W.b W.o nb = padTo (intSize n) (intBytes new) := by
    unfold curBytes; rw [hMb]
    simp only [Option.map_some, Option.getD_some]
    have := extract_writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new)) (by omega)
    rwa [hbs] at this
  let l' : ALoc := { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) }
  have hl' : W.Loc M li l' := by
    obtain ⟨hi', hpr, hj⟩ := Array.findIdx?_eq_some_iff_getElem.mp hl.1
    have hs : (m₁.atomics.set! li l').size = m₁.atomics.size := by simp
    refine ⟨Array.findIdx?_eq_some_iff_getElem.mpr ⟨by rw [hMa, hs]; exact hi', ?_,
      fun j hji => ?_⟩, ?_⟩
    · simp only [hMa, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds, ↓reduceIte]
      simp [l', hlb, hlo]
    · simp only [hMa, Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds (by omega), if_neg (Nat.ne_of_gt hji)]
      exact hj j hji
    · rw [hMa, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hli, l']
  have hmr : (rmwMsg m₂ ord rd new).rmwOf = some (l.msgs[l.msgs.size - 1]!).id := rfl
  have hhc : M.heap = (m₁.write W.b blk W.o (padTo (intSize n) (intBytes new))).heap := by
    funext x; obtain ⟨b', o'⟩ := x
    simp only [Mem.heap, Mem.write]
    by_cases hb' : b' = W.b
    · subst hb'; rw [hMb, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hb).1]
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hb')]
      rw [hMe]; simp only [observeM, hb₂, hlb]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hb')]
  have hrel : (rmwMsg m₂ ord rd new).relClock =
      if ord.isRel then VClock.merge rd.relClock (M.clocks[m₁.current]!) else rd.relClock := by
    simp only [rmwMsg, hMc, hc₂]
  have hsz' : W.o + nb ≤ (writeBytes blk.bytes W.o (padTo (intSize n) (intBytes new))).size := by
    rw [writeBytes_size _ _ _ (by omega)]; exact hsz
  have hcov : m₁.MsgCov → M.MsgCov := fun h => by
    obtain ⟨e, he, heb, heo, hel, hec⟩ := hrec
    rw [hM]
    refine (FStepIn.rmwM (hF := fun _ => none) (blk := blk) (e := e) ord _ new hct
      (by rw [hl0]; omega) (by rw [hl0, hlb]; exact hb) (fun hin => ?_) he (by rw [hl0, hlb]; exact heb)
      (by rw [hl0, hlo]; exact heo) hel hec
      (by rw [hl0, getElem!_pos l.msgs _ (by omega)]; exact Array.getElem_mem _)).msgCov h
    have := W.sz_pos
    exact hin _ (Nat.le_refl _) (by rw [hl0, hlen]; omega) rfl
  refine ⟨⟨⟨_, hMb, hlv, hsz', ha4, hk⟩,
    fun l₀ hl₀ hb' h1 h2 => ?_, fun i l₀ hl₀ => ?_, fun e he hh => ?_,
    ⟨new, by unfold Word.Holds; rw [hcur]; exact W.enc_val new⟩, fun i l₀ hl₀ => ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_,
    fun u hu => by rw [hMc]; exact hcl₂ u hu, by rw [hMc]; exact hct₂, hMbs, fun x hx => ?_,
    fun e he => .inl (by rw [hMe] at he; simpa [observeM, hf₂] using he), ?_,
    fun e he => .inl (by rw [hMe] at he; simpa [observeM, hf₂] using he),
    BlkStep.write hb hbs hsz (by rw [hMe]; simp only [observeM, hb₂, hlb, hlo, rmwMsg]),
    .inl (keys_set (l' := l') hl.2 rfl hMa),
    by rw [hMe]; unfold Mem.Aux observeM; simp only [m₂]; split <;> simp [acqM], hcov⟩,
    by unfold Word.Holds; rw [hcur]; exact W.enc_val new, ?_, fun hq => ?_⟩
  · rw [hMa, Array.set!_eq_setIfInBounds] at hl₀
    rcases Array.mem_or_eq_of_mem_set (w := hli) (by simpa [Array.setIfInBounds, hli] using hl₀)
      with h | rfl
    · exact hw.only l₀ h hb' h1 h2
    · exact hlo
  · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl'
    refine ⟨hlen, by simp [l'], hch.push h0 hmr, ?_, fun j hj => ?_⟩
    · unfold ALoc.lastBytes; simp [l', hcur, rmwMsg]
    · simp only [l', Array.size_push] at hj
      simp only [l', Array.getElem_push]
      split
      · exact hval j (by assumption)
      · exact ⟨new, W.enc_val new⟩
  · have he' : e ∈ m₁.footprint := by rw [hMe] at he; simpa [observeM, hf₂] using he
    rcases hw.wfp e he' hh with ⟨ha', hle⟩ | hle
    · refine .inl ⟨ha', ?_⟩
      obtain ⟨u, hu, hle'⟩ := hle
      refine ⟨u, by rw [hMe]; simpa [observeM, ht₂] using hu, VClock.le_trans hle' ?_⟩
      rw [hMc]; by_cases hu' : u = m₁.current
      · subst hu'; exact hct₂
      · rw [hcl₂ u hu']; exact VClock.le_refl _
    · refine .inr fun u hu _ =>
        VClock.le_trans (hle u (by rw [hMe] at hu; simpa [observeM, ht₂] using hu) trivial) ?_
      rw [hMc]; by_cases hu' : u = m₁.current
      · subst hu'; exact hct₂
      · rw [hcl₂ u hu']; exact VClock.le_refl _
  · obtain ⟨rfl, rfl⟩ := loc_unique hl₀ hl'
    intro e he hh
    have he' : e ∈ m₁.footprint := by rw [hMe] at he; simpa [observeM, hf₂] using he
    have hlc : l'.lastClock = m₂.clocks[m₁.current]! := by simp [l', ALoc.lastClock, rmwMsg, hc₂]
    rw [hlc]
    rcases hw.wfp e he' (hits_of_plain hh) with ⟨ha', -⟩ | hle
    · rw [plainHit_atomic ha'] at hh; cases hh
    · exact VClock.le_trans (hle _ ht trivial) hct₂
  · rw [hMe]; simp [observeM, hc₂]
  · rw [hMe]; simp [observeM, ht₂]
  · rw [hMe]; simp [observeM, hw₂]
  · rw [hMe]; simp [observeM, hk₂]
  · rw [hMe]; simp [observeM, hg₂]
  · rw [hMc, hcs₂]
  · rw [hhc, Mem.heap_write_out hb (by omega) _ (by rw [hbs]; exact hx)]
  · exact LocsKeep.set hl.2 hlb hlo (by exact hlb) (by exact hlo) (by exact hlen) hMa
  · rw [hist_loc hl', hist_loc hl, Array.mapIdx_push]
    congr 1
    have hk : (l.msgs.mapIdx ent).size - 1 = l.msgs.size - 1 := by simp
    have hrd : rd = l.msgs[l.msgs.size - 1] := getElem!_pos l.msgs _ (by omega)
    rw [hk, getElem!_pos _ _ (by simp; omega), Array.getElem_mapIdx]
    simp only [ent, rmwEnt, rmwMsg, hMc, hc₂, if_neg (by omega : l.msgs.size ≠ 0), ← hrd]
  · have : ord.isAcq = true := hq
    have hk : (l.msgs.mapIdx ent).size - 1 = l.msgs.size - 1 := by simp
    rw [hist_loc hl, hk, getElem!_pos _ _ (by simp; omega)]
    simp only [Array.getElem_mapIdx, ent]
    rw [hMc]; simp only [m₂, this, ↓reduceIte]
    rw [acqM_clock _ _ hct, ← getElem!_pos l.msgs _ (by omega)]
    exact VClock.le_merge_right _ _

/-- An RMW at the word by thread `t`: it reads the newest write (`old`), and its write is the
newest. -/
theorem Ok.rmw {m m' : Mem} {t c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    (W.hist m)[(W.hist m).size - 1]!.Val old ∧ W.Ok m' ∧ W.Op t m m' ∧
      W.Holds m' (op.apply signed old v) ∧
      W.hist m' = (W.hist m).push
        (rmwEnt m' t ord (W.hist m)[(W.hist m).size - 1]! (op.apply signed old v)) ∧
      (ord.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -, hrec⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hpl := rmw_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact h0) (by rw [hl0]; exact hch) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨hw', hop₂, hU, hh, hacq⟩ := hw₁.rmwAt hl' hop₁.current (by rw [hop₁.threads]; exact ht)
    (by rw [hop₁.csize, hop₁.threads]; exact hcs) hrec hm'
  have hsz := hist_size hl'
  refine ⟨?_, hw', hop₁.trans hop₂, hU, by rw [hh, hh₁], by rw [← hh₁]; exact hacq⟩
  rw [← hh₁, hsz]; exact val_of hl' (by omega) hold

/-- A read of message `pos ≥ floorPos` of the word by thread `t` (`loadM`). -/
theorem Ok.read {m m₁ : Mem} {t li pos : Nat} {l : ALoc} {ord : AtomicOrder} (hw₁ : W.Ok m₁)
    (hl : W.Loc m₁ li l) (hop : W.Op t m m₁) (hct : t < m₁.clocks.size) (hlt : pos < l.msgs.size)
    (hfl : floorPos m₁ li ≤ pos) :
    (∀ k < (W.hist m₁).size, VClock.le (W.hist m₁)[k]!.clock (m.clocks[t]!) = true → k ≤ pos) ∧
      (ord.isAcq = true → VClock.le (W.hist m₁)[pos]!.relClock
        ((loadM m₁ li ord (l.msgs[pos]!)).clocks[t]!) = true) ∧
      W.hist (loadM m₁ li ord (l.msgs[pos]!)) = W.hist m₁ ∧
      W.Ok (loadM m₁ li ord (l.msgs[pos]!)) ∧ W.Op t m₁ (loadM m₁ li ord (l.msgs[pos]!)) := by
  have hl0 := (loc_get hl).2.2
  have hg := grows_loadM m₁ li ord (l.msgs[pos]!)
  have hcu : (loadM m₁ li ord (l.msgs[pos]!)).current = t := by rw [loadM_current]; exact hop.current
  have hcs₁ : m₁.current < m₁.clocks.size := by rw [hop.current]; exact hct
  refine ⟨fun k hk hle => ?_, fun hq => ?_, hist_congr hg.atomics hg.blocks,
    hw₁.keep (keep_of hg.blocks hg.atomics hg.footprint hg.threads hg.cle),
    ⟨hcu, hg.threads, hg.waiters, by unfold loadM; split <;> rfl, by unfold loadM; split <;> rfl,
      hg.csize, fun u hu => loadM_others _ _ _ _ (by rw [hop.current]; exact hu),
      hg.cle t, by rw [hg.blocks], fun x _ => by simp only [Mem.heap, hg.blocks],
      fun e he => .inl (hg.footprint ▸ he), .of_eq hg.atomics,
      fun e he => .inl (hg.footprint ▸ he), .of_eq hg.blocks, .of_eq hg.atomics,
      by unfold Mem.Aux loadM acqM observeM; split <;> simp,
      (FStepIn.loadM (hF := fun _ => none) hcs₁ ord (l.msgs[pos]!) (by
        intro hin
        have hlen := (hw₁.loc li l hl).1
        have hpos := W.sz_pos
        rw [hl0] at hin
        exact hin l.off (Nat.le_refl _) (by omega) rfl)).msgCov⟩⟩
  · by_cases hk0 : k = 0
    · omega
    · rw [hist_size hl] at hk
      rw [hist_get hl hk] at hle
      simp only [ent, hk0, ↓reduceIte] at hle
      have hk' : k < (m₁.atomics[li]!).msgs.size := by rw [hl0]; exact hk
      have e : ((m₁.atomics[li]!).msgs[k]'hk').clock = l.msgs[k].clock := by simp [hl0]
      have : k ≤ floorPos m₁ li := le_floorPos hk'
        (by rw [e, hop.current]; exact VClock.le_trans hle hop.mine)
      omega
  · rw [hist_get hl hlt]
    simp only [ent]
    unfold loadM; simp only [hq, ↓reduceIte]
    rw [← hop.current]
    simp only [acqM, observeM]
    rw [Proto.getElem!_set!_ite]
    simp only [true_and, hcs₁, ↓reduceIte]
    rw [← getElem!_pos l.msgs _ hlt]; exact VClock.le_merge_right _ _

/-- An atomic load at the word by thread `t`: it reads write `j`, at least each write that
happened before `t`. -/
theorem Ok.load {m m' : Mem} {t c : Nat} {ord : AtomicOrder} {v : BitVec n} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((atomicLoadAt c ord nb W.ptr : MemM (BitVec n)).run m).run = some (.ok (v, m'))) :
    ∃ j, j < (W.hist m).size ∧ (W.hist m)[j]!.Val v ∧ Floor (W.hist m) (m.clocks[t]!) j ∧
      (ord.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m ∧ W.Ok m' ∧ W.Op t m m' := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  have hl0 := (loc_get hl').2.2
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  rw [hl0]
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  obtain ⟨hfl, hacq, hh, hw', hop₂⟩ := hw₁.read (ord := ord) hl' hop₁ hct hlt (floor_le hpos)
  refine ⟨pos, by rw [← hh₁, hist_size hl']; exact hlt, by rw [← hh₁]; exact val_of hl' hlt hv,
    by rw [← hh₁]; exact hfl, by rw [← hh₁]; exact hacq, by rw [hh, hh₁], hw', hop₁.trans hop₂⟩

/-- A `cmpxchg` at the word by thread `t`: on success (`none`) an RMW of the newest write, which
holds `exp`; on failure a read with the failure order of write `j`, which does not hold `exp`. -/
theorem Ok.cas {m m' : Mem} {t c : Nat} {succ fail : AtomicOrder} {exp new : BitVec n}
    {r : Option (BitVec n)} (hw : W.Ok m) (hc : m.current = t) (ht : t < m.threads.size)
    (hcs : m.clocks.size = m.threads.size)
    (h : ((cmpxchgAt c succ fail nb W.ptr exp new).run m).run = some (.ok (r, m'))) :
    W.Ok m' ∧ W.Op t m m' ∧
    ((r = none ∧ (W.hist m)[(W.hist m).size - 1]!.Val exp ∧ W.Holds m' new ∧
      W.hist m' = (W.hist m).push (rmwEnt m' t succ (W.hist m)[(W.hist m).size - 1]! new) ∧
      (succ.isAcq = true →
        VClock.le (W.hist m)[(W.hist m).size - 1]!.relClock (m'.clocks[t]!) = true)) ∨
     (∃ j old, r = some old ∧ old ≠ exp ∧ j < (W.hist m).size ∧ (W.hist m)[j]!.Val old ∧
      Floor (W.hist m) (m.clocks[t]!) j ∧
      (fail.isAcq = true → VClock.le (W.hist m)[j]!.relClock (m'.clocks[t]!) = true) ∧
      W.hist m' = W.hist m)) := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, -, -, -, -, ha₀⟩ := hw.access
  rw [W.sz_eq, ha₀] at hacc
  rw [W.sz_eq] at hl
  cases hacc
  obtain ⟨l, hl', hw₁, hop₁, hh₁, -, -⟩ := hw.prep hc ht hcs rfl hl
  obtain ⟨-, h0, hch, -, -⟩ := hw₁.loc li l hl'
  have hl0 := (loc_get hl').2.2
  have hct : t < m₁.clocks.size := by rw [hop₁.csize, hcs]; exact ht
  have hsz := hist_size hl'
  rcases hcase with ⟨rfl, rfl, -, hm'⟩ | ⟨hne, rfl, hm'⟩
  · have hpl := cas_chain_pos (m := m₁) (li := li) (by rw [hl0]; exact hch) hpos hold
    rw [hl0] at hpl hold hm'
    rw [hpl] at hold hm'
    rw [W.sz_eq] at hm'
    obtain ⟨hw₂, hop₂, hh₂⟩ := hw₁.record hop₁.current
      (by rw [hop₁.threads]; exact ht) (by rw [hop₁.csize, hop₁.threads]; exact hcs)
      (k := .atomicWrite) rfl
    have hl₂ : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl'
    obtain ⟨hw', hop₃, hU, hh, hacq⟩ := hw₂.rmwAt (M := m') (ord := succ) (new := new) hl₂ hop₂.current
      (by rw [hop₂.threads, hop₁.threads]; exact ht)
      (by rw [hop₂.csize, hop₂.threads, hop₁.csize, hop₁.threads]; exact hcs)
      (rec_recordAt hop₁.current hct) hm'
    refine ⟨hw', hop₁.trans (hop₂.trans hop₃), .inl ⟨rfl, ?_, hU,
      by rw [hh, hh₂, hh₁], by rw [← hh₁]; exact hacq⟩⟩
    rw [← hh₁, hsz]; exact val_of hl' (by omega) hold
  · have hlt := (casOpts_pos hpos).1
    have hfl := casOpts_floor hpos
    rw [hl0] at hlt hold hm'
    rw [hm']
    obtain ⟨hfl', hacq, hh, hw', hop₂⟩ := hw₁.read (ord := fail) hl' hop₁ hct hlt hfl
    refine ⟨hw', hop₁.trans hop₂, .inr ⟨pos, old, rfl, hne, by rw [← hh₁, hsz]; exact hlt,
      by rw [← hh₁]; exact val_of hl' hlt hold, by rw [← hh₁]; exact hfl',
      by rw [← hh₁]; exact hacq, by rw [hh, hh₁]⟩⟩

/-! ## An op at the word keeps a lock's invariant -/

/-- An op at a word apart from the lock's, which no part and no resource has, keeps the lock's
invariant. -/
theorem _root_.Zig.Conc.Lock.Inv.wordOp {γ : Type} {L : Lock γ} {G : ThreadId → γ} {t : ThreadId}
    {m m' : Mem} (hi : L.Inv G m) (hw : W.Ok m) (hop : W.Op t m m') (hap : Apart L W)
    (hoff : ∀ u, W.Off (L.own G m u)) (hR : ∀ hL, L.R G hL → W.Off hL) : L.Inv G m' := by
  have hsz0 := W.sz_pos
  have hjb : joinedB m' = joinedB m := Lock.joinedB_congr hop.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold Lock.own; rw [hjb]
  have hnw : ∀ x, L.o ≤ x → x < L.o + 4 → ¬ ((L.b, x).1 = W.b ∧ W.o ≤ (L.b, x).2 ∧ (L.b, x).2 < W.o + nb) := by
    rintro x h1 h2 ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb
    · omega
    · omega
  obtain ⟨hblk', hcur⟩ := Lock.word_congr (L := L) (fun x h1 h2 => hop.cells _ (hnw x h1 h2)) hi.blk
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold Lock.U32; rw [hcur]
  have hne : L.b ≠ W.b ∨ L.o ≠ W.o := by
    rcases hap with h | h | h
    · exact .inl h
    · exact .inr (by omega)
    · exact .inr (by omega)
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => hop.locs.same L.b L.o hne i l
  have hkey := L.key_congr (fun x h1 h2 => hop.cells _ (hnw x h1 h2)) hi.blk
  have hWb : W.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hw.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  -- a new access is at the word, so it touches no heap without the word's bytes
  have hnt : ∀ {h : Heap}, W.Off h → ∀ e ∈ m'.footprint, e ∉ m.footprint → ¬ e.Touches h := by
    intro h ho e he hn ht
    rcases hop.fp e he with h' | ⟨hb, heo, hl, -⟩
    · exact hn h'
    · obtain ⟨x, h1, h2, h3⟩ := ht
      rw [hb] at h3
      rw [heo] at h1; rw [heo, hl] at h2
      rw [ho x h1 (by omega)] at h3; exact h3 rfl
  have hsub : ∀ {h : Heap}, W.Off h → h.Sub m.heap → h.Sub m'.heap := fun ho hs l c hc => by
    have hw' : ¬ (l.1 = W.b ∧ W.o ≤ l.2 ∧ l.2 < W.o + nb) := by
      rintro ⟨h1, h2, h3⟩
      obtain ⟨b, x⟩ := l; simp only at h1 h2 h3; subst h1
      rw [ho x h2 h3] at hc; cases hc
    rw [hop.cells l hw']; exact hs l c hc
  refine ⟨?_, hi.pdisj, hi.idle, fun u hu => ?_, hblk', ?_, hi.one,
    ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_,
      fun i l hl => (hi.loc.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
        (hop.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1⟩, fun u => hown ▸ hi.off u,
    fun e he hh => ?_, fun i l hl => ?_, fun hF => ?_, hi.res,
    by rw [hop.waiters]; exact Lock.Queue.of_key L hkey hi.fq,
    fun hp => ?_, fun u hu =>
      let ⟨i, l, hl, hw⟩ := hi.owner u hu; ⟨i, l, (hloc i l).mpr hl, hw⟩⟩
  · rw [hown]
    refine hi.own.keep (by rw [hop.threads]) hop.csize (fun u => hsub (hoff u) (hi.own.sub u))
      (Nat.le_of_eq hop.bsize.symm) (fun u _ => hop.clocks u) (fun e he => ?_)
    by_cases hm : e ∈ m.footprint
    · exact .inl hm
    · refine .inr ⟨?_, fun u => hnt (hoff u) e he hm⟩
      rcases hop.fp e he with h' | ⟨hb, -⟩
      · exact absurd h' hm
      · rw [hb, hop.bsize]; exact hWb
  · rw [hop.threads, hjb]; exact hi.live u hu
  · obtain ⟨w, hw', hu, hz⟩ := hi.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
  · rcases hop.locs.new l hl with h | ⟨hb', ho, hlen⟩
    · exact hi.loc.only l h hb h1 h2
    · rw [ho] at h1; rw [ho, hlen] at h2; rw [hb'] at hb
      rcases hap with h | h | h
      · exact absurd hb.symm h
      · omega
      · omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.loc.ok i l ((hloc i l).mp hl)
    exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
  · rcases hop.fp e he with h' | ⟨hb, heo, hl, -⟩
    · rcases hi.wfp e h' hh with ⟨ha, hs⟩ | ha
      · exact .inl ⟨ha, hop.someLe hs⟩
      · exact .inr (Lock.LiveLe.mono hop.threads (fun u _ => hop.clocks u) ha)
    · exfalso
      obtain ⟨hb', x, h1, h2, h3, h4⟩ := hh
      rw [hb] at hb'; rw [heo] at h1; rw [heo, hl] at h2
      rcases hap with h | h | h
      · exact h hb'.symm
      · omega
      · omega
  · obtain ⟨h1, h2⟩ := hi.rel i l ((hloc i l).mp hl)
    exact ⟨hop.someLe h1, fun u hu => VClock.le_trans (h2 u hu) (hop.clocks u)⟩
  · obtain ⟨hL, hRL, hsL, hdj, hoffL, how⟩ := hi.free hF
    refine ⟨hL, hRL, hsub (hR hL hRL) hsL, fun u => hown ▸ hdj u, hoffL, fun e he htc => ?_⟩
    by_cases hm : e ∈ m.footprint
    · rcases how e hm (htc.imp id fun h => by rw [← hop.bsize]; exact h) with h | ⟨i, l, hl, hle⟩
      · exact .inl (Lock.LiveLe.mono hop.threads (fun u _ => hop.clocks u) h)
      · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
    · rcases htc with htc | hbe
      · exact absurd htc (hnt (hR hL hRL) e he hm)
      · rcases hop.fp e he with h' | ⟨hb, -⟩
        · exact absurd h' hm
        · rw [hb, hop.bsize] at hbe; exact absurd hWb (Nat.not_lt.mpr hbe)
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit (Lock.Waits.of_key L hkey (hop.waiters ▸ hp))
    exact ⟨v, hop.threads ▸ hv, hop.waiters ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩

/-! ## A futex wait at the word

The kernel's compare of a futex wait is a recorded atomic read of the word (`Thread.futexWait`):
an `Op` that keeps the word's writes. -/

section futex

variable {W : Word 32 4}

/-- A futex wait at the word by the current thread `t`: a woken thread goes on; else the
kernel's read of the word is an op `M` that keeps the word's writes and the blocks (a read),
and the thread sleeps (it joins `waiters`) only if the word holds `e`. -/
theorem Ok.futexWait {m m' : Mem} {t : ThreadId} {e : BitVec 32} {sh b : Bool} (hw : W.Ok m)
    (hc : m.current = t) (ht : t < m.threads.size) (hcs : m.clocks.size = m.threads.size)
    (h : ((Thread.futexWait W.ptr e sh).run m).run = some (.ok (b, m'))) :
    (m.woken.contains m.current = true ∧ b = false ∧
      m' = { m with woken := m.woken.erase m.current }) ∨
    (m.woken.contains m.current = false ∧ ∃ M, W.Ok M ∧ W.Op t m M ∧ W.hist M = W.hist m ∧
      M.blocks = m.blocks ∧
      ((W.Holds m e ∧ b = true ∧
          m' = { M with waiters := M.waiters.push (t, m.wordKey W.b W.o sh) }) ∨
       (b = false ∧ m' = M))) := by
  rcases futexWait_eq h with hwk | ⟨hwk, bid, blk, o, v, ha, -, hv, hcase⟩
  · exact .inl hwk
  obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hw.access
  rw [ha₀] at ha
  cases ha
  obtain ⟨hok, hop, hh⟩ := hw.record (k := .atomicRead) hc ht hcs rfl
  refine .inr ⟨hwk, _, hok, hop, hh, rfl, ?_⟩
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · subst hc; exact .inl ⟨(holds_bytes hb₀).mpr hv, rfl, by rw [Mem.wordKey_of hb₀]; rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- The word is off the lock's word, the threads' parts and the resources: a futex wait at it
keeps the lock's invariant (`Lock.Inv.waitOff`). -/
theorem offWord {γ : Type} {L : Lock γ} {G : ThreadId → γ} {m : Mem} (hw : W.Ok m)
    (hown : ∀ u, W.Off (L.own G m u)) (hR : ∀ hL, L.R G hL → W.Off hL) (hap : Apart L W) :
    L.OffWord G m W.ptr := by
  intro bid blk o ha
  obtain ⟨blk₀, -, -, -, ha₀, -⟩ := hw.access
  rw [ha₀] at ha
  cases ha
  refine ⟨fun u x h1 h2 => hown u x h1 h2, fun hL hRL x h1 h2 => hR hL hRL x h1 h2, ?_⟩
  rcases hap with h | h | h
  · exact .inl (Ne.symm h)
  · exact .inr (.inr h)
  · exact .inr (.inl h)

end futex

/-! ## The old Word contract over full-state resources

The roots of the full-state word that consume `Word.Op` and its `BlkStep` (moved from
`ZigLean/Sep/Full/Word.lean`). -/

open Full

/-- The blocks after an op at the word, from the block of the word. -/
theorem BlkStep.eq_set {m m' : Mem} (h : W.BlkStep m m') {blk : Block}
    (hb : m.blocks[W.b]? = some blk) : ∃ blk', m'.blocks[W.b]? = some blk' ∧
      blk'.addr = blk.addr ∧ blk'.live = blk.live ∧ blk'.kind = blk.kind ∧
      blk'.bytes.size = blk.bytes.size ∧ m'.blocks = m.blocks.set! W.b blk' := by
  obtain ⟨blk', hb', ha, hl, hk, hs, -⟩ := h.word blk hb
  refine ⟨blk', hb', ha, hl, hk, hs, ?_⟩
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  apply Array.ext_getElem? fun i => ?_
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : W.b = i
  · subst e; simp [hlt, hb']
  · simp only [e, ↓reduceIte]; exact h.other i (Ne.symm e)

/-- **An op at the word is a step at its bytes** (`RestStep`). -/
theorem Op.rest {t : ThreadId} {m m' : Mem} (hop : W.Op t m m') (hw : W.Ok m) (hw' : W.Ok m') :
    RestStep W.In m m' := by
  have hsz0 := W.sz_pos
  obtain ⟨blk, hb, hl, hsz, -, hk, -⟩ := hw.blk
  obtain ⟨blk', hb', ha', hl', hk', hs', hset⟩ := hop.blocks.eq_set hb
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨hop.threads, hop.csize, hop.clocks, hop.bsize, fun l hl => hop.cells l hl,
    fun l hl => hw'.cellIn hl, KMono.set hb ha' hk hset,
    KeepsExt.set hb hl' hs' hk' hset,
    fun hd => LDMono.set hb (fun h => by rw [← hl']; exact h) ha' (Nat.le_of_eq hs') hset
      (Nat.le_of_eq (by rw [hk'])) hd,
    fun b x hx => ?_, fun hwf => ?_, fun e he => ?_,
    MemAuth.Keep.set (m' := { m' with current := m.current }) hb hset hl' ha' hs' hk' hop.aux.1
      (by rw [hop.aux.2.1]) hop.aux.2.2, hop.cov⟩
  · rcases hop.atoms with e | ⟨e, -⟩
    · rw [← keys_toList, e, keys_toList]
    · rw [← keys_toList, e, Array.toList_push, keys_toList, tagOf_append_single]
      have : ¬ Full.Covers b x (W.b, W.o, nb) := fun ⟨h1, h2, h3⟩ => hx ⟨h1.symm, h2, h3⟩
      simp [this]
  · rcases hop.atoms with e | ⟨e, hno⟩
    · rw [← keys_toList, e, keys_toList]; exact hwf
    · rw [← keys_toList, e, Array.toList_push, keys_toList]
      refine ⟨fun s hs => ?_, List.pairwise_append.mpr ⟨hwf.2, by simp, fun a ha b hb => ?_⟩⟩
      · rcases List.mem_append.mp hs with h | h
        · exact hwf.1 s h
        · simp at h; subst h; exact hsz0
      · simp at hb; subst hb
        obtain ⟨l, hlm, rfl⟩ : ∃ l ∈ m.atomics, ALoc.shape l = a := by
          simpa [shapes] using ha
        intro hlb
        simp only [ALoc.shape] at hlb ⊢
        by_cases h1 : l.off < W.o + nb
        · by_cases h2 : W.o < l.off + l.len
          · exact absurd ⟨hlb, hw.only l hlm hlb h1 h2⟩ (hno l hlm)
          · exact .inl (by omega)
        · exact .inr (by omega)
  · rcases hop.fp e he with h | ⟨h1, h2, h3, -, -⟩
    · exact .inl h
    · refine .inr ⟨fun x hx1 hx2 => ⟨h1, by omega, by omega⟩, by
        rw [h1]; exact hlt⟩

/-! ### The memory facts of an op, for the steps of a sync object's code

A step of a futex-based sync object's code (`FEvent.MStep`, `FCond.MStep`) is an op at one of
its words, a futex wait's sleep (an op that keeps the word's writes, then a new waiter), or a
change of the current thread, the futex queue or the woken threads only. The lemmas
`FEvent.MStep.*` and `FCond.MStep.*` give what such a step does to the memory, from these facts of
an op. -/

/-- The block `b` after an op at the word: as live, as large and of the same kind. -/
theorem Op.block {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {b : BlockId} {blk : Block}
    (hb : m.blocks[b]? = some blk) : ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  by_cases e : b = W.b
  · subst e
    obtain ⟨blk', h1, -, h2, h3, h4, -⟩ := h.blocks.word blk hb
    exact ⟨blk', h1, h2, h4, h3⟩
  · exact ⟨blk, by rw [h.blocks.other b e]; exact hb, rfl, rfl, rfl⟩

/-- An op at the word keeps the atomic location of a lock's word apart from it. -/
theorem Op.lockLoc {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {L : LockWord}
    (hap : W.ApartL L) {i : Nat} {l : ALoc} (hl : L.Loc m i l) : L.Loc m' i l :=
  (h.locs.same _ _ hap.ne i l).mpr hl

/-- An op at the word: a new access is at the word. -/
theorem Op.fpAt {t : ThreadId} {m m' : Mem} (h : W.Op t m m') :
    ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := fun e he =>
  (h.fp e he).imp id fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-- An op at the word keeps a word `W'` apart from it that is valid before: valid after it,
with the same writes. -/
theorem Op.word {n' nb' : Nat} {W' : Word n' nb'} {t : ThreadId} {m m' : Mem} (h : W.Op t m m')
    (hok : W'.Ok m) (hap : W.b ≠ W'.b ∨ W.o + nb ≤ W'.o ∨ W'.o + nb' ≤ W.o) :
    W'.Ok m' ∧ W'.hist m' = W'.hist m :=
  ⟨hok.keep (keep_op h hap), hist_keep hok (keep_op h hap)⟩

end Word
end Conc

namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {L : FLock γ} {n nb : Nat} {W : Word n nb}

/-- **An op at a shared word apart from the lock's keeps the lock's invariant**, whose rest has
the word's cells: the rest gets the word's new cells. -/
theorem Inv.wordOp {G : ThreadId → γ} {rY : Res} {t : ThreadId} {m m' : Mem}
    (hi : L.Inv G (rsum (W.cellsR m) rY) m) (hWY : ∀ l, W.In l → rY.heap l = none) (hw : W.Ok m)
    (hw' : W.Ok m') (hop : W.Op t m m') (hap : W.ApartL L.toLockWord) :
    L.Inv G (rsum (W.cellsR m') rY) m' := by
  have hsz0 := W.sz_pos
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hop.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold FLock.own; rw [hjb]
  have hnw : ∀ l, L.In l → ¬ W.In l := by
    rintro ⟨b, x⟩ ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩; simp only at h1 h2 h3 h4 h5 h6
    rcases hap with h | h | h
    · exact h (h1.symm.trans h4)
    · omega
    · omega
  have hLcells : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x) :=
    fun x h1 h2 => hop.cells _ (hnw _ ⟨rfl, h1, h2⟩)
  obtain ⟨hblk', hcur⟩ := LockWord.word_congr hLcells hi.w.blk
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold LockWord.U32; rw [hcur]
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => hop.locs.same L.b L.o hap.ne i l
  have hWb : W.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hw.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  have hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true :=
    fun u _ => hop.clocks u
  obtain ⟨blk₀, hb₀, -⟩ := hi.w.blk
  have hadd : m.SameAddrs m' := hop.blocks.addrs
  -- a new access is at the word, so it does not touch the lock's word
  have hnL : ∀ e ∈ m'.footprint, e ∉ m.footprint → ¬ L.Hits e := by
    intro e he hn ⟨hb, x, h1, h2, h3, h4⟩
    rcases hop.fp e he with h' | ⟨hb', ho, hl, -⟩
    · exact hn h'
    · rw [hb'] at hb; rw [ho] at h1; rw [ho, hl] at h2
      rcases hap with h | h | h
      · exact h hb.symm
      · omega
      · omega
  have hwi : L.WInv (L.pl G) m' := by
    refine ⟨by rw [hop.csize, hop.threads]; exact hi.w.csize, fun u hu => ?_, hblk', ?_, hi.w.one,
      ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun i l hl => ?_⟩, fun e he hh => ?_,
      fun i l hl => ?_, by rw [hop.waiters]; exact (hi.w.fq.of_key L.toLockWord
        (L.toLockWord.key_of_addrs hadd hb₀) hadd),
      fun hp => ?_,
      fun u hu => let ⟨i, l, hl, hw⟩ := hi.w.owner u hu; ⟨i, l, (hloc i l).mpr hl, hw⟩⟩
    · rw [hop.threads, hjb]; exact hi.w.live u hu
    · obtain ⟨w, hw', hu, hz⟩ := hi.w.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
    · rcases hop.locs.new l hl with h | ⟨hb', ho, hlen⟩
      · exact hi.w.loc.only l h hb h1 h2
      · rw [ho] at h1; rw [ho, hlen] at h2; rw [hb'] at hb
        rcases hap with h | h | h
        · exact absurd hb.symm h
        · omega
        · omega
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.w.loc.ok i l ((hloc i l).mp hl)
      exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
    · exact (hi.w.loc.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
        (hop.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1
    · by_cases hm : e ∈ m.footprint
      · rcases hi.w.wfp e hm hh with ⟨ha, hs⟩ | ha
        · exact .inl ⟨ha, Conc.someLe_mono hop.threads hcl hs⟩
        · exact .inr (LockWord.LiveLe.mono hop.threads hcl ha)
      · exact absurd hh (hnL e he hm)
    · obtain ⟨h1, h2⟩ := hi.w.rel i l ((hloc i l).mp hl)
      exact ⟨Conc.someLe_mono hop.threads hcl h1,
        fun u hu => VClock.le_trans (h2 u hu) (hop.clocks u)⟩
    · obtain ⟨v, hv, hq, h1, h2⟩ :=
        hi.w.wit (LockWord.Waits.of_key L.toLockWord (L.toLockWord.key_of_addrs hadd hb₀)
          (hop.waiters ▸ hp))
      exact ⟨v, hop.threads ▸ hv, hop.waiters ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  -- the rest as `cells W ⋆ (word ⋆ (rL ⋆ rY))`
  have hWw : FHeap.Disjoint (W.cellsR m).heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  have hXY := FHeap.disjoint_union_right.mp hLX
  -- `rL` has no byte of the word
  have hLW : ∀ l, W.In l → rL.heap l = none := fun l hl =>
    (hXY.1 l).resolve_right (cellsAt_some hl (hw.cellIn hl))
  have hLW' : FHeap.Disjoint rL.heap (W.cellsR m').heap := fun l => by
    by_cases hl : W.In l
    · exact .inl (hLW l hl)
    · exact .inr (cellsAt_none hl)
  have hWw' : FHeap.Disjoint (W.cellsR m').heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  -- regroup `word ⋆ (rL ⋆ (C ⋆ rY))` as `C ⋆ (word ⋆ (rL ⋆ rY))`
  have regroup : ∀ C : Res, FHeap.Disjoint C.heap (L.wordR m).heap → FHeap.Disjoint rL.heap C.heap →
      rsum (L.wordR m) (rsum rL (rsum C rY)) = rsum C (rsum (L.wordR m) (rsum rL rY)) := by
    intro C h1 h2
    rw [← rsum_assoc (a := rL), rsum_comm h2, rsum_assoc, ← rsum_assoc (a := L.wordR m),
      rsum_comm h1.symm, rsum_assoc]
  have hwR : L.wordR m' = L.wordR m := by
    simp only [LockWord.wordR, cellsAt]
    congr 1; funext ⟨b, x⟩
    split
    · rename_i hl; obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
      rw [hLcells x h2 h3]
    · rfl
  rw [regroup _ hWw hXY.1] at ho
  have ho' := ho.restStep (hop.rest hw hw') (fun l hl => hw.cellIn hl) (fun l hl => by
    simp only [FHeap.union_apply, cellsAt_none (fun h => hnw l h hl), hLW l hl, hWY l hl]; rfl)
  rw [← regroup _ hWw' hLW', ← hwR, ← hown] at ho'
  refine ⟨hwi, ⟨rL, ho', hLoff, FHeap.disjoint_union_right.mpr ⟨hLW', hXY.2⟩, fun hF' => ?_, hnF⟩,
    LockWord.off_erase.mpr fun l hl => ?_, hi.pdisj, hi.idle, hi.res⟩
  · obtain ⟨hR, hO⟩ := hF hF'
    refine ⟨hR, fun e he htc => ?_⟩
    by_cases hm : e ∈ m.footprint
    · rcases hO e hm (htc.imp id fun h => by rw [← hop.bsize]; exact h) with h | ⟨i, l, hl, hle⟩
      · exact .inl (LockWord.LiveLe.mono hop.threads hcl h)
      · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
    · rcases hop.fp e he with h | ⟨hb, heo, hlen, -⟩
      · exact absurd h hm
      · rcases htc with ⟨x, h1, h2, h3⟩ | hbe
        · rw [hb] at h3; rw [heo] at h1; rw [heo, hlen] at h2
          exact absurd (by simp [FHeap.erase, hLW (W.b, x) ⟨rfl, h1, by omega⟩]) h3
        · rw [hb, hop.bsize] at hbe; exact absurd hWb (Nat.not_lt.mpr hbe)
  · have := LockWord.off_erase.mp hi.xoff l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff]
      at this ⊢
    exact ⟨cellsAt_none fun h => hnw l hl h, this.2⟩

end FLock

end Full

end Zig
