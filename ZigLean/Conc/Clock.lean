import ZigLean.Conc.Lemmas
import ZigLean.Sep.Heap

/-!
# Ownership by clocks

Which bytes a thread may access without a race, read from the recorded accesses (the footprint)
and the threads' vector clocks. Both thread logics use it: the full-state thread triples
(`FTTriple`, `ZigLean/Sep/Full/Thread.lean`) and the legacy ones (`TTriple`,
`ZigLean/Conc/Own.lean`).

- **Ownership** (`Mem.OwnsC`, `Mem.Owns`). The clock `c` owns the heap `h` if every recorded
  access to a byte of `h` happened before `c`. Thread `t` owns `h` if its clock does. Then a
  plain access by `t` to the bytes of `h` does not race (`Mem.Owns.noRace`): no recorded access
  to them is concurrent with `t`. Ownership moves with the clocks: a clock that is later owns
  what an earlier one owns (`Mem.OwnsC.mono`). So a spawn gives ownership to the child, and a
  join gives it back.
- **A step of the owner** (`StepIn hF`). A step of the current thread that changes only the
  bytes it owns: the frame `hF` (the rest of the heap) and the other threads' clocks stay
  unchanged, and each new footprint entry is the current thread's and touches no byte of `hF`.
  So the ownership of every part of `hF`, by any clock, stays (`Mem.OwnsC.frame`).

A zero-length access touches no byte (`FootprintEntry.Touches`), as in the model's race checks
(`raceAt`, `Mem.freeRaces`, `plainHit`): no clock needs to cover it.
-/

namespace Zig

/-- The footprint entry `e` accesses a byte that `h` has (a zero-length entry accesses none). -/
def FootprintEntry.Touches (e : FootprintEntry) (h : Heap) : Prop :=
  ∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ h (e.block, x) ≠ none

/-- The clock `c` owns `h`: every recorded access to a byte of `h`, and every access to a block
that does not exist yet, happened before `c`. -/
def Mem.OwnsC (m : Mem) (c : VClock) (h : Heap) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches h ∨ m.blocks.size ≤ e.block) → VClock.le e.clock c = true

/-- Thread `t` owns `h`. -/
def Mem.Owns (m : Mem) (t : ThreadId) (h : Heap) : Prop := m.OwnsC (m.clocks[t]!) h

/-- A step of the current thread that changes only the bytes it owns (module doc). -/
structure StepIn (hF : Heap) (m m' : Mem) : Prop where
  current : m'.current = m.current
  threads : m'.threads = m.threads
  atomics : m'.atomics = m.atomics
  seen : m'.seen = m.seen
  nextMsg : m'.nextMsg = m.nextMsg
  waiters : m'.waiters = m.waiters
  woken : m'.woken = m.woken
  groups : m'.groups = m.groups
  size : m'.clocks.size = m.clocks.size
  others : ∀ u, u ≠ m.current → m'.clocks[u]! = m.clocks[u]!
  mine : VClock.le (m.clocks[m.current]!) (m'.clocks[m.current]!) = true
  blocks : m.blocks.size ≤ m'.blocks.size
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    (e.tid = m.current ∧ ¬ e.Touches hF ∧ e.block < m'.blocks.size)
  /-- A new access happened before the thread's new clock. -/
  fpc : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ VClock.le e.clock (m'.clocks[m.current]!) = true

section Owns

variable {m m' : Mem} {c c' : VClock} {h h₁ h₂ hF : Heap}

theorem Mem.OwnsC.mono (ho : m.OwnsC c h) (hc : VClock.le c c' = true) : m.OwnsC c' h :=
  fun e he ht => VClock.le_trans (ho e he ht) hc

/-- A part of an owned heap is owned. -/
theorem Mem.OwnsC.sub (ho : m.OwnsC c h) (hs : ∀ l, h₁ l ≠ none → h l ≠ none) : m.OwnsC c h₁ :=
  fun e he ht => ho e he (ht.imp (fun ⟨x, h1, h2, h3⟩ => ⟨x, h1, h2, hs _ h3⟩) id)

theorem Mem.OwnsC.union (h1 : m.OwnsC c h₁) (h2 : m.OwnsC c h₂) : m.OwnsC c (h₁ ∪ h₂) := by
  intro e he ht
  rcases ht with ⟨x, hx1, hx2, hx3⟩ | hb
  · by_cases hn : h₁ (e.block, x) = none
    · exact h2 e he (.inl ⟨x, hx1, hx2, by simpa [hn] using hx3⟩)
    · exact h1 e he (.inl ⟨x, hx1, hx2, hn⟩)
  · exact h1 e he (.inr hb)

theorem Mem.OwnsC.left (ho : m.OwnsC c (h₁ ∪ h₂)) : m.OwnsC c h₁ :=
  ho.sub fun l hl => by simp only [Heap.union_apply]; cases e : h₁ l <;> simp_all

theorem Mem.OwnsC.right (ho : m.OwnsC c (h₁ ∪ h₂)) : m.OwnsC c h₂ :=
  ho.sub fun l hl => by simp only [Heap.union_apply]; cases e : h₁ l <;> simp_all

/-- A `StepIn hF` keeps the ownership of each part of `hF`, by any clock. -/
theorem Mem.OwnsC.frame (hs : StepIn hF m m') (ho : m.OwnsC c h) (hsub : ∀ l, h l ≠ none → hF l ≠ none) :
    m'.OwnsC c h := by
  intro e he ht
  rcases hs.fp e he with he | ⟨-, hnt, hb⟩
  · exact ho e he (ht.imp id fun hb => Nat.le_trans hs.blocks hb)
  · rcases ht with ⟨x, hx1, hx2, hx3⟩ | hb'
    · exact absurd ⟨x, hx1, hx2, hsub _ hx3⟩ hnt
    · exact absurd hb' (Nat.not_le.mpr hb)

/-- **Revived bytes are owned by every clock**: after `Mem.forgetFrom b S` (an in-place growth),
no recorded access to an offset `≥ S` of block `b` is concurrent with anything, so every clock
owns those bytes, given that it covers the recorded accesses to blocks that do not exist yet
(`hnew`). -/
theorem Mem.OwnsC.forgotten {b : BlockId} {S : Nat} (hfp : m'.footprint = (m.forgetFrom b S).footprint)
    (hh : ∀ l, h l ≠ none → l.1 = b ∧ S ≤ l.2)
    (hnew : ∀ e ∈ m'.footprint, m'.blocks.size ≤ e.block → VClock.le e.clock c = true) :
    m'.OwnsC c h := by
  intro e he ht
  rcases ht with ⟨x, h1, h2, h3⟩ | hb
  · obtain ⟨hb, hS⟩ := hh _ h3
    rcases Mem.forgetFrom_entry (hfp ▸ he) hb with hc | ⟨hlt, hend⟩
    · rw [hc]; exact VClock.le_default c
    · exfalso
      have hS' : S ≤ x := hS
      omega
  · exact hnew e he hb

/-- Another thread keeps what it owns over a `StepIn hF` when that is a part of `hF`. -/
theorem Mem.Owns.frame {u : ThreadId} (hs : StepIn hF m m') (hu : u ≠ m.current) (ho : m.Owns u h)
    (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.Owns u h := by
  unfold Mem.Owns; rw [hs.others u hu]; exact Mem.OwnsC.frame hs ho hsub

/-- The current thread keeps what it owns in `hF` over a `StepIn hF`. -/
theorem Mem.Owns.frameSelf (hs : StepIn hF m m') (ho : m.Owns m.current h)
    (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.Owns m'.current h := by
  unfold Mem.Owns; rw [hs.current]; exact (Mem.OwnsC.frame hs ho hsub).mono hs.mine

/-- A plain access by the current thread to bytes it owns does not race. -/
theorem Mem.Owns.noRace {b : BlockId} {off len : Nat} {kind : AccessKind} (ho : m.Owns m.current h)
    (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none) :
    NoRace m b off len kind := by
  apply noRace_of_raceAt
  unfold raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hb, hl⟩, hel⟩, h1⟩, h2⟩, hcon⟩ := hc
    subst hb
    have ht : e.Touches h := by
      by_cases ho' : e.off ≤ off
      · exact ⟨off, ho', h1, hin off (Nat.le_refl _) (by omega)⟩
      · exact ⟨e.off, Nat.le_refl _, by omega, hin e.off (by omega) h2⟩
    have hle := VClock.le_trans (ho e he (.inl ht)) (VClock.le_bump (m.clocks[m.current]!) m.current)
    simp [VClock.concurrent, hle] at hcon
  · rfl

end Owns

namespace StepIn

variable {m m' m'' : Mem} {hF hF' : Heap}

/-- No clock gets smaller. -/
theorem clock (hs : StepIn hF m m') (u : ThreadId) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  by_cases hc : u = m.current
  · subst hc; exact hs.mine
  · rw [hs.others u hc]; exact VClock.le_refl _

theorem refl (m : Mem) (hF : Heap) : StepIn hF m m :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _, Nat.le_refl _,
    fun _ he => .inl he, fun _ he => .inl he⟩

theorem trans (h₁ : StepIn hF m m') (h₂ : StepIn hF m' m'') : StepIn hF m m'' := by
  refine ⟨h₂.current.trans h₁.current, h₂.threads.trans h₁.threads, h₂.atomics.trans h₁.atomics,
    h₂.seen.trans h₁.seen, h₂.nextMsg.trans h₁.nextMsg, h₂.waiters.trans h₁.waiters,
    h₂.woken.trans h₁.woken, h₂.groups.trans h₁.groups, h₂.size.trans h₁.size,
    fun u hu => (h₂.others u (h₁.current ▸ hu)).trans (h₁.others u hu), ?_,
    Nat.le_trans h₁.blocks h₂.blocks, fun e he => ?_, fun e he => ?_⟩
  · have := h₂.mine; rw [h₁.current] at this; exact VClock.le_trans h₁.mine this
  · rcases h₂.fp e he with he' | ⟨ht, hnt, hb⟩
    · rcases h₁.fp e he' with he'' | ⟨ht, hnt, hb⟩
      · exact .inl he''
      · exact .inr ⟨ht, hnt, Nat.lt_of_lt_of_le hb h₂.blocks⟩
    · exact .inr ⟨ht.trans h₁.current, hnt, hb⟩
  · rcases h₂.fpc e he with he' | hle
    · rcases h₁.fpc e he' with he'' | hle
      · exact .inl he''
      · have := h₂.mine; rw [h₁.current] at this; exact .inr (VClock.le_trans hle this)
    · rw [h₁.current] at hle; exact .inr hle

/-- A step in a larger frame is a step in a part of it. -/
theorem weaken (hs : StepIn hF m m') (hsub : ∀ l, hF' l ≠ none → hF l ≠ none) : StepIn hF' m m' :=
  { hs with
    fp := fun e he => (hs.fp e he).imp id fun ⟨ht, hnt, hb⟩ =>
      ⟨ht, fun ⟨x, h1, h2, h3⟩ => hnt ⟨x, h1, h2, hsub _ h3⟩, hb⟩ }

/-- A change of one block (bytes, kind, liveness) records no access. -/
theorem setBlock (m : Mem) (hF : Heap) (b : BlockId) (nb : Block) :
    StepIn hF m { m with blocks := m.blocks.set! b nb } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
    by simp, fun _ he => .inl he, fun _ he => .inl he⟩

/-- `Mem.write` changes only the bytes of a block. -/
theorem write (m : Mem) (hF : Heap) (b : BlockId) (blk : Block) (o : Nat) (bs : Array Byte) :
    StepIn hF m (m.write b blk o bs) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
    by simp [Mem.write], fun _ he => .inl he, fun _ he => .inl he⟩

end StepIn

section Record

variable {m : Mem} {h hF : Heap} {b : BlockId} {off len : Nat} {kind : AccessKind}

theorem recordAt_clock (hc : m.current < m.clocks.size) :
    (m.recordAt b off len kind).clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current :=
  Array.getElem!_set!_self m.clocks m.current _ hc

/-- A recorded access by the current thread that touches no byte of `hF`. -/
theorem StepIn.recordAt_of (hc : m.current < m.clocks.size)
    (hnt : ∀ x, off ≤ x → x < off + len → hF (b, x) = none)
    (hb : b < m.blocks.size) : StepIn hF m (m.recordAt b off len kind) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [Mem.recordAt], fun u hu => ?_, ?_,
    Nat.le_refl _, fun e he => ?_, fun e he => ?_⟩
  · show (m.clocks.set! m.current _)[u]! = _
    rw [Conc.Proto.getElem!_set!_ite]; simp [hu]
  · rw [recordAt_clock hc]; exact VClock.le_bump _ _
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr ⟨rfl, fun ⟨x, h1, h2, h3⟩ => h3 (hnt x h1 h2), hb⟩
  · simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · right; show VClock.le _ ((m.clocks.set! m.current _)[m.current]!) = true
      rw [Array.getElem!_set!_self _ _ _ hc]; exact VClock.le_refl _

/-- A recorded access by the current thread to bytes it owns (in `h`, not in `hF`). -/
theorem StepIn.recordAt (hc : m.current < m.clocks.size) (hd : Heap.Disjoint h hF)
    (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none)
    (hb : b < m.blocks.size) : StepIn hF m (m.recordAt b off len kind) :=
  StepIn.recordAt_of hc (fun x h1 h2 => (hd (b, x)).resolve_left (hin x h1 h2)) hb

/-- A read by the current thread of bytes it owns: recorded (`StepIn.recordAt`), or nothing for a
`const` global. -/
theorem StepIn.readAt {blk : Block} (hc : m.current < m.clocks.size) (hd : Heap.Disjoint h hF)
    (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none)
    (hb : b < m.blocks.size) : StepIn hF m (m.readAt blk b off len kind) :=
  Mem.readAt_cases (P := StepIn hF m) (StepIn.refl m hF) (StepIn.recordAt hc hd hin hb)

/-- The current thread keeps what it owns over one of its recorded accesses. -/
theorem Mem.Owns.recordAt (hc : m.current < m.clocks.size) (ho : m.Owns m.current h) :
    (m.recordAt b off len kind).Owns (m.recordAt b off len kind).current h := by
  show (m.recordAt b off len kind).OwnsC ((m.recordAt b off len kind).clocks[m.current]!) h
  rw [recordAt_clock hc]
  intro e he ht
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact VClock.le_trans (ho e he ht) (VClock.le_bump _ _)
  · exact VClock.le_refl _

theorem Mem.Owns.readAt {blk : Block} (hc : m.current < m.clocks.size) (ho : m.Owns m.current h) :
    (m.readAt blk b off len kind).Owns (m.readAt blk b off len kind).current h :=
  Mem.readAt_cases (P := fun x => x.Owns x.current h) ho (Mem.Owns.recordAt hc ho)

theorem Mem.Owns.write (ho : m.Owns m.current h) {b : BlockId} {blk : Block} {o : Nat}
    {bs : Array Byte} : (m.write b blk o bs).Owns (m.write b blk o bs).current h := by
  intro e he ht
  exact ho e he (ht.imp id fun h' => by simpa [Mem.write] using h')

end Record

/-! ## The step relation of the full-state thread triples

`StepIn` fixes the atomic locations, the threads' views of them and the message counter, and
keeps every recorded access as it is, so no atomic op and no revival of bytes (`Mem.forgetFrom`)
is a `StepIn`. The full-state thread triples (`FTTriple`, `ZigLean/Sep/Full/Thread.lean`) use the
general relation `FStepIn hF`: everything `StepIn hF` says about the threads, their clocks and the
frame's bytes, and

* the **atomic locations** (`AMap`): the ones in the frame's bytes stay as they are, the others
  may change their messages or be retired, and new ones have no byte of the frame. The
  locations that stay keep their order (`σ` gives the new index of each), and the other
  threads' views of them move with them. The current thread's view of a location in the
  frame stays too (`AMap.seenAt_frame`); a step on its own bytes does not observe the frame;
* the **record of accesses**: an old entry stays or is narrowed (`FootprintEntry.Narrows`: part
  of its bytes, an earlier clock; `Mem.forgetFrom`), a new one is the current thread's, touches
  no byte of the frame and writes no `const` global;
* **`const` globals**: no block of `m` becomes one.

A `StepIn` that writes no `const` global and makes none is an `FStepIn` (`FStepIn.of_stepIn`). -/

/-- Block `b` of `m` is a `const` global. -/
def Mem.IsConst (m : Mem) (b : BlockId) : Prop :=
  ∃ blk, m.blocks[b]? = some blk ∧ blk.kind = .constGlobal

/-- Every byte of the atomic location `l` is a byte of `h`. -/
def ALoc.In (h : Heap) (l : ALoc) : Prop :=
  ∀ x, l.off ≤ x → x < l.off + l.len → h (l.block, x) ≠ none

/-- No byte of the atomic location `l` is a byte of `h`. -/
def ALoc.Off (h : Heap) (l : ALoc) : Prop :=
  ∀ x, l.off ≤ x → x < l.off + l.len → h (l.block, x) = none

/-- The entry `e` is `e₀` or a narrowing of it: the same thread, block and kind, part of its
bytes, and a clock that happened before `e₀`'s. -/
def FootprintEntry.Narrows (e e₀ : FootprintEntry) : Prop :=
  e.tid = e₀.tid ∧ e.block = e₀.block ∧ e.kind = e₀.kind ∧ e₀.off ≤ e.off ∧
    e.off + e.len ≤ e₀.off + e₀.len ∧ VClock.le e.clock e₀.clock = true

/-- The id last read or written by thread `u` at atomic location `li`. -/
def Mem.seenAt (m : Mem) (u li : Nat) : Option Nat :=
  (m.seen.find? fun p => p.1 == u && p.2.1 == li).map (·.2.2)

/-- An injective reindexing carries a retained location's view to its new index. -/
theorem seen_reindex {s : Array (ThreadId × Nat × Nat)} {σ : Nat → Option Nat}
    (hinj : ∀ i i' j, σ i = some j → σ i' = some j → i = i') {u i j : Nat} (hij : σ i = some j) :
    ((s.filterMap fun p => (σ p.2.1).map fun j => (p.1, j, p.2.2)).find?
      fun p => p.1 == u && p.2.1 == j).map (·.2.2) =
    (s.find? fun p => p.1 == u && p.2.1 == i).map (·.2.2) := by
  rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_filterMap, List.find?_filterMap]
  have hp : (fun a : ThreadId × Nat × Nat => ((σ a.2.1).map fun j => (a.1, j, a.2.2)).any
      fun p => p.1 == u && p.2.1 == j) = fun a => a.1 == u && a.2.1 == i := by
    funext a
    cases h : σ a.2.1 with
    | none =>
      have : a.2.1 ≠ i := fun e => by rw [e, hij] at h; cases h
      simp [beq_eq_false_iff_ne.mpr this]
    | some k =>
      by_cases hk : k = j
      · subst hk; simp [hinj _ _ _ h hij]
      · have : a.2.1 ≠ i := fun e => by rw [e, hij] at h; exact hk (Option.some.inj h).symm
        simp [beq_eq_false_iff_ne.mpr hk, beq_eq_false_iff_ne.mpr this]
  rw [hp]
  cases hf : s.toList.find? (fun a => a.1 == u && a.2.1 == i) with
  | none => rfl
  | some a =>
    have := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    simp [this.2, hij]

/-- Filtering out only other threads keeps thread `u`'s views. -/
theorem seenAt_filter {s : Array (ThreadId × Nat × Nat)} {q : ThreadId × Nat × Nat → Bool}
    {u li : Nat} (hq : ∀ p : ThreadId × Nat × Nat, p.1 = u → q p = true) :
    (s.filter q).find? (fun p => p.1 == u && p.2.1 == li) =
      s.find? fun p => p.1 == u && p.2.1 == li := by
  rw [Array.find?_filter]
  congr 1; funext p
  by_cases h : p.1 = u <;> by_cases h2 : p.2.1 = li <;> simp [h, h2, hq p]

/-- `find?` with pointwise equal predicates. -/
theorem find?_congr {α : Type} {s : Array α} {p q : α → Bool} (h : ∀ a, p a = q a) :
    s.find? p = s.find? q := by rw [funext h]

/-- A raw observation changes just the current thread's view of the observed location.
It need not be an allowed read; actual loads select a position from `readOpts`. -/
theorem seenAt_observe (m : Mem) (li id u i : Nat) :
    (Conc.Proto.observeM m li id).seenAt u i =
      if u = m.current ∧ i = li then some id else m.seenAt u i := by
  unfold Mem.seenAt Conc.Proto.observeM
  dsimp only
  rw [Array.find?_push, Array.find?_filter]
  by_cases hu : u = m.current
  · subst hu
    by_cases hi : i = li
    · subst hi
      rw [find?_congr (q := fun _ => false) fun ⟨t, j, k⟩ => by
        by_cases h1 : t = m.current <;> by_cases h2 : j = i <;> simp [h1, h2],
        Array.find?_eq_none.mpr fun _ _ => by simp]
      simp
    · rw [find?_congr (q := fun p => p.1 == m.current && p.2.1 == i) fun ⟨t, j, k⟩ => by
        by_cases h1 : t = m.current <;> by_cases h2 : j = i <;> simp [h1, h2, hi]]
      simp [Ne.symm hi, hi]
  · rw [find?_congr (q := fun p => p.1 == u && p.2.1 == i) fun ⟨t, j, k⟩ => by
      by_cases h1 : t = u <;> by_cases h2 : j = i <;> simp [h1, h2, hu]]
    simp [Ne.symm hu, hu]

/-- The atomic locations of `m'` after a step from `m` with the frame `hF` (module doc): `σ i` is
the new index of location `i` if it stays. -/
structure AMap (hF : Heap) (m m' : Mem) (σ : Nat → Option Nat) : Prop where
  /-- The locations that stay keep their order. -/
  mono : ∀ i i' j j', σ i = some j → σ i' = some j' → i < i' → j < j'
  /-- A location that stays keeps its bytes. -/
  kept : ∀ i j l, σ i = some j → m.atomics[i]? = some l →
    ∃ l', m'.atomics[j]? = some l' ∧ l'.block = l.block ∧ l'.off = l.off ∧ l'.len = l.len
  /-- A location in the frame's bytes stays as it is. -/
  frame : ∀ i l, m.atomics[i]? = some l → l.In hF → ∃ j, σ i = some j ∧ m'.atomics[j]? = some l
  /-- A new location has a byte, and no byte of the frame. -/
  new : ∀ j l', m'.atomics[j]? = some l' → (∀ i < m.atomics.size, σ i ≠ some j) →
    0 < l'.len ∧ l'.Off hF
  /-- The other threads' views move with their locations. -/
  seen : m'.seen.filter (·.1 != m.current) =
    (m.seen.filter (·.1 != m.current)).filterMap fun p => (σ p.2.1).map fun j => (p.1, j, p.2.2)
  /-- A step on its own bytes does not observe a location in the frame. -/
  own : ∀ i l j, m.atomics[i]? = some l → l.In hF → σ i = some j →
    m'.seenAt m.current j = m.seenAt m.current i

/-! ## Message coverage (`Mem.MsgCov`)

A thread that owns the bytes of an atomic word has every recorded access to them before its
clock (`Mem.Owns`). It reads the newest message of the word's location only if every message
happened before it, too: the floor of its read (`floorPos`) is the newest position. Ownership
does not say that (`tests/roadmap/sep-full/MsgFloorCX.lean`: a sequential memory whose owned word
offers an old message). `Mem.MsgCov` ties the messages to the accesses: **every clock that covers
the recorded accesses to a location's bytes (`ALoc.over`) covers each of its messages' clocks and
release clocks** (`ALoc.CovBy`), and every location lies in its block's bytes (`ALoc.InBlock`, so
a revival past a block's end, `Mem.forgetFrom`, forgets no access to a location's bytes).

Each step keeps it (`FStepIn.cov`): a step only adds accesses, narrows ones past a block's end
(no location there), retires locations, and makes messages whose clocks are those of its own
recorded access (a store, an RMW, a `cmpxchg`), of the plain writes to the bytes (`locIdx`,
`retireAt`: `plainClock`), or joined with the release clock of a message it read (an acquiring
RMW). The step relation states it relative to any record in front (`Mem.withFp`), as the
thread rules of the memory primitives run a step without the record (`Mem.noFp`,
`ZigLean/Sep/Full/ThreadStep.lean`). Spawns, joins and the futex queue change neither the
locations nor the record. The invariant is not one of `Mem.FSeq` (`MsgFloorCX.fseq`); the
concurrent logics carry it (`FOwned`, the resumption of `CTriple.Run`). -/

/-- `m₀` with the recorded accesses `F` before its own. -/
def Mem.withFp (m₀ : Mem) (F : Array FootprintEntry) : Mem :=
  { m₀ with footprint := F ++ m₀.footprint }

/-- The atomic location `l` lies in the bytes of its block. -/
def ALoc.InBlock (m : Mem) (l : ALoc) : Prop :=
  ∃ blk, m.blocks[l.block]? = some blk ∧ l.off + l.len ≤ blk.bytes.size

/-- The clock `k` happened before every clock that covers the recorded accesses to the bytes of
`l` (`ALoc.over`). -/
def ALoc.CovBy (m : Mem) (l : ALoc) (k : VClock) : Prop :=
  ∀ c, l.over m c = true → VClock.le k c = true

/-- **Message coverage** (section doc). -/
def Mem.MsgCov (m : Mem) : Prop :=
  ∀ l ∈ m.atomics, 0 < l.len → l.InBlock m ∧
    ∀ msg ∈ l.msgs, l.CovBy m msg.clock ∧ l.CovBy m msg.relClock

/-- The entry `e` accesses a byte of the location `l` (as `ALoc.over` reads it). -/
def FootprintEntry.Hits (e : FootprintEntry) (l : ALoc) : Prop :=
  e.block = l.block ∧ 0 < e.len ∧ l.off < e.off + e.len ∧ e.off < l.off + l.len

section MsgCov

variable {m m' : Mem} {l : ALoc} {k k' : VClock}

theorem ALoc.over_iff {c : VClock} :
    l.over m c = true ↔ ∀ e ∈ m.footprint, e.Hits l → VClock.le e.clock c = true := by
  unfold ALoc.over FootprintEntry.Hits
  rw [Array.all_eq_true']
  refine forall_congr' fun e => imp_congr_right fun _ => ?_
  constructor
  · rintro h ⟨h1, h2, h3, h4⟩
    simpa [h1, h2, h3, h4] using h
  · intro h
    by_cases h1 : e.block = l.block
    · by_cases h2 : 0 < e.len
      · by_cases h3 : l.off < e.off + e.len
        · by_cases h4 : e.off < l.off + l.len
          · simp [h ⟨h1, h2, h3, h4⟩]
          · simp [h4]
        · simp [h3]
      · simp [h2]
    · simp [h1]

/-- `ALoc.overAt` byte by byte: every recorded access to a byte of the location `l` and of
`o..o+len` in block `b` happened before `c`. -/
theorem ALoc.overAt_iff {c : VClock} {b o len : Nat} :
    l.overAt m c b o len = true ↔ ∀ e ∈ m.footprint, ∀ x, e.block = l.block → e.block = b →
      e.off ≤ x → x < e.off + e.len → l.off ≤ x → x < l.off + l.len → o ≤ x → x < o + len →
      VClock.le e.clock c = true := by
  unfold ALoc.overAt
  rw [Array.all_eq_true']
  refine forall_congr' fun e => imp_congr_right fun _ => ?_
  constructor
  · intro h x h1 h2 h3 h4 h5 h6 h7 h8
    cases hle : VClock.le e.clock c
    · rw [hle, Bool.or_false, Bool.not_eq_true'] at h
      have hb1 : (e.block == l.block) = true := by simp [h1]
      have hb2 : (e.block == b) = true := by simp [h2]
      simp only [hb1, hb2, Bool.true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        Nat.max_lt, Nat.lt_min] at h
      omega
    · rfl
  · intro h
    rw [Bool.or_eq_true]
    by_cases hle : VClock.le e.clock c = true
    · exact .inr hle
    · refine .inl ?_
      rw [Bool.not_eq_true']
      refine Bool.eq_false_iff.mpr fun hc => hle ?_
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Nat.max_lt, Nat.lt_min] at hc
      obtain ⟨⟨⟨h1, h2⟩, -⟩, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := hc
      exact h (Nat.max e.off (Nat.max l.off o)) h1 h2 (Nat.le_max_left _ _)
        (Nat.max_lt.mpr ⟨a1, Nat.max_lt.mpr ⟨a2, a3⟩⟩)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.max_lt.mpr ⟨b1, Nat.max_lt.mpr ⟨b2, b3⟩⟩)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.max_lt.mpr ⟨c1, Nat.max_lt.mpr ⟨c2, c3⟩⟩)

/-- The per-byte check is weaker than the whole-location one: `retireAt` retires at least where
it did with `ALoc.over` (MM-21). -/
theorem ALoc.overAt_of_over {c : VClock} {b o len : Nat} (h : l.over m c = true) :
    l.overAt m c b o len = true :=
  ALoc.overAt_iff.mpr fun e he x h1 _ hx1 hx2 hx3 hx4 _ _ =>
    ALoc.over_iff.mp h e he ⟨h1, by omega, by omega, by omega⟩

/-- **A mixed-size access to owned bytes may retire** (`retireAt`, MM-21): every recorded access to
the bytes `o..o+len` that the current thread owns happened before it, so in particular every one
to the bytes that they share with a location `l`. -/
theorem ALoc.overAt_of_owns {h : Heap} {b o len : Nat} (ho : m.Owns m.current h)
    (hin : ∀ x, o ≤ x → x < o + len → h (b, x) ≠ none) :
    l.overAt m (m.clocks[m.current]!) b o len = true :=
  ALoc.overAt_iff.mpr fun e he x _ h2 hx1 hx2 _ _ hx5 hx6 =>
    ho e he (.inl ⟨x, hx1, hx2, by rw [h2]; exact hin x hx5 hx6⟩)

/-- Coverage reads only the record: more accesses cover more. -/
theorem ALoc.CovBy.mono (h : l.CovBy m k) (hfp : ∀ e ∈ m.footprint, e ∈ m'.footprint) :
    l.CovBy m' k := fun c hc =>
  h c (ALoc.over_iff.mpr fun e he hh => ALoc.over_iff.mp hc e (hfp e he) hh)

/-- The clock of an access to the location's bytes is covered. -/
theorem ALoc.CovBy.entry {e : FootprintEntry} (he : e ∈ m.footprint) (hh : e.Hits l) :
    l.CovBy m e.clock := fun _ hc => ALoc.over_iff.mp hc e he hh

theorem ALoc.CovBy.le (h : l.CovBy m k) (hk : VClock.le k' k = true) : l.CovBy m k' :=
  fun c hc => VClock.le_trans hk (h c hc)

theorem ALoc.CovBy.merge (h : l.CovBy m k) (h' : l.CovBy m k') : l.CovBy m (VClock.merge k k') :=
  fun c hc => VClock.merge_le (h c hc) (h' c hc)

theorem ALoc.CovBy.empty : l.CovBy m #[] := fun c _ => VClock.le_default c

/-- Coverage depends only on the location's bytes and the record. -/
theorem ALoc.CovBy.congr {l' : ALoc} (h : l.CovBy m k) (hb : l'.block = l.block) (ho : l'.off = l.off)
    (hn : l'.len = l.len) (hfp : m'.footprint = m.footprint) : l'.CovBy m' k := fun c hc =>
  h c (ALoc.over_iff.mpr fun e he ⟨h1, h2, h3, h4⟩ =>
    ALoc.over_iff.mp hc e (hfp ▸ he) ⟨hb ▸ h1, h2, ho ▸ h3, by rw [ho, hn]; exact h4⟩)

/-- **The clock of the plain writes to a location's bytes is covered** (the message `locIdx` makes
of them). -/
theorem ALoc.CovBy.plainClock {m₀ : Mem} (hfp : ∀ e ∈ m₀.footprint, e ∈ m.footprint) :
    l.CovBy m (Zig.plainClock m₀ l.block l.off l.len) := fun c hc =>
  Conc.Proto.plainClock_le_of fun e he hp => by
    obtain ⟨h0, he0, h1, h2⟩ := Conc.Proto.plainHit_range hp
    exact ALoc.over_iff.mp hc e (hfp e he) ⟨Conc.Proto.plainHit_block hp, he0, h1, h2⟩

/-- **The thread's clock after its access to a location's bytes is covered**: the access is
recorded with that clock (the clock of a store's or an RMW's message). -/
theorem ALoc.CovBy.recordAt {m₀ : Mem} {b : BlockId} {o n : Nat} {kind : AccessKind}
    (hc : m₀.current < m₀.clocks.size)
    (hfp : ∀ e ∈ (m₀.recordAt b o n kind).footprint, e ∈ m.footprint)
    (hn : 0 < n) (hb : l.block = b) (ho : l.off = o) (hpos : 0 < l.len) :
    l.CovBy m ((m₀.recordAt b o n kind).clocks[m₀.current]!) := by
  rw [recordAt_clock hc]
  let e : FootprintEntry :=
    { tid := m₀.current, clock := VClock.bump (m₀.clocks[m₀.current]!) m₀.current,
      block := b, off := o, len := n, kind := kind }
  exact ALoc.CovBy.entry (e := e) (hfp _ (by simp [e, Mem.recordAt]))
    ⟨hb.symm, hn, by simp only [e]; omega, by simp only [e]; omega⟩

/-- The record of `m` is part of the record of `m` with `F` in front. -/
theorem Mem.mem_withFp {e : FootprintEntry} {F : Array FootprintEntry} (he : e ∈ m.footprint) :
    e ∈ (m.withFp F).footprint := Array.mem_append.mpr (.inr he)

theorem Mem.withFp_footprint (m : Mem) (F : Array FootprintEntry) :
    (m.withFp F).footprint = F ++ m.footprint := rfl

theorem Mem.withFp_nil (m : Mem) : m.withFp #[] = m := by
  cases m; simp [Mem.withFp]

/-- A memory without atomic locations covers its messages. -/
theorem Mem.MsgCov.of_atomics (h : m.atomics = #[]) : m.MsgCov := by
  intro l hl; rw [h] at hl; simp at hl

/-- **A step that keeps the locations' bytes and messages, keeps every block (or grows it) and
adds accesses keeps the coverage.** -/
theorem Mem.MsgCov.keep (h : m.MsgCov)
    (ha : ∀ l ∈ m'.atomics, 0 < l.len → l ∈ m.atomics)
    (hb : ∀ l ∈ m.atomics, 0 < l.len → l.InBlock m → l.InBlock m')
    (hfp : ∀ e ∈ m.footprint, e ∈ m'.footprint) : m'.MsgCov := by
  intro l hl hpos
  obtain ⟨hin, hmsg⟩ := h l (ha l hl hpos) hpos
  exact ⟨hb l (ha l hl hpos) hpos hin, fun msg hm =>
    ⟨(hmsg msg hm).1.mono hfp, (hmsg msg hm).2.mono hfp⟩⟩

/-- `Mem.MsgCov.keep` relative to any record in front. -/
theorem Mem.MsgCov.keepFp
    (ha : ∀ l ∈ m'.atomics, 0 < l.len → l ∈ m.atomics)
    (hb : ∀ l ∈ m.atomics, 0 < l.len → l.InBlock m → l.InBlock m')
    (hfp : ∀ e ∈ m.footprint, e ∈ m'.footprint) (F : Array FootprintEntry)
    (h : (m.withFp F).MsgCov) : (m'.withFp F).MsgCov :=
  h.keep ha hb fun e he => by
    rcases Array.mem_append.mp he with he | he
    · exact Array.mem_append.mpr (.inl he)
    · exact Array.mem_append.mpr (.inr (hfp e he))

/-- A recorded access keeps the coverage. -/
theorem Mem.MsgCov.recordAt {b : BlockId} {o n : Nat} {kind : AccessKind} (h : m.MsgCov) :
    (m.recordAt b o n kind).MsgCov :=
  h.keep (fun _ hl _ => hl) (fun _ _ _ h => h) fun _ he => by
    simp only [Mem.recordAt, Array.mem_push]; exact .inl he

theorem ALoc.InBlock.of_blocks (h : l.InBlock m) (hb : m'.blocks = m.blocks) : l.InBlock m' := by
  obtain ⟨blk, h1, h2⟩ := h; exact ⟨blk, hb ▸ h1, h2⟩

/-- A new block at the end keeps every location in its block. -/
theorem ALoc.InBlock.push (h : l.InBlock m) (x : Block) (hb : m'.blocks = m.blocks.push x) :
    l.InBlock m' := by
  obtain ⟨blk, h1, h2⟩ := h
  refine ⟨blk, ?_, h2⟩
  rw [hb, Array.getElem?_push_lt (Array.getElem?_eq_some_iff.mp h1).1]
  exact (Array.getElem?_eq_getElem _).symm.trans h1

theorem writeBytes_size_ge (a : Array Byte) (o : Nat) (bs : Array Byte) :
    a.size ≤ (writeBytes a o bs).size := by
  simp [writeBytes]; omega

/-- **New locations and messages**: a step that keeps the record and the blocks, and whose
locations are old ones or covered ones in their blocks, keeps the coverage. -/
theorem Mem.MsgCov.ofAtomics (h : m.MsgCov) (hfp : m'.footprint = m.footprint)
    (hbl : m'.blocks = m.blocks)
    (ha : ∀ l ∈ m'.atomics, 0 < l.len → l ∈ m.atomics ∨
      (l.InBlock m ∧ ∀ msg ∈ l.msgs, l.CovBy m msg.clock ∧ l.CovBy m msg.relClock)) :
    m'.MsgCov := by
  intro l hl hpos
  obtain ⟨hin, hmsg⟩ := (ha l hl hpos).elim (h l · hpos) id
  exact ⟨hin.of_blocks hbl, fun msg hm =>
    ⟨(hmsg msg hm).1.congr rfl rfl rfl hfp, (hmsg msg hm).2.congr rfl rfl rfl hfp⟩⟩

end MsgCov

/-- **The step relation of `FTTriple`** (module doc). -/
structure FStepIn (hF : Heap) (m m' : Mem) : Prop where
  current : m'.current = m.current
  threads : m'.threads = m.threads
  waiters : m'.waiters = m.waiters
  woken : m'.woken = m.woken
  groups : m'.groups = m.groups
  size : m'.clocks.size = m.clocks.size
  others : ∀ u, u ≠ m.current → m'.clocks[u]! = m.clocks[u]!
  mine : VClock.le (m.clocks[m.current]!) (m'.clocks[m.current]!) = true
  blocks : m.blocks.size ≤ m'.blocks.size
  nextMsg : m.nextMsg ≤ m'.nextMsg
  atomics : ∃ σ, AMap hF m m' σ
  fp : ∀ e ∈ m'.footprint, (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨
    (e.tid = m.current ∧ ¬ e.Touches hF ∧ e.block < m'.blocks.size ∧
      (e.kind.isWrite = true → ¬ m'.IsConst e.block))
  /-- A new access happened before the thread's new clock. -/
  fpc : ∀ e ∈ m'.footprint, (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨
    VClock.le e.clock (m'.clocks[m.current]!) = true
  /-- No block of `m` becomes a `const` global. -/
  const : ∀ b, b < m.blocks.size → m'.IsConst b → m.IsConst b
  /-- The messages stay covered, relative to any record in front (`Mem.MsgCov`). -/
  cov : ∀ F, (m.withFp F).MsgCov → (m'.withFp F).MsgCov

theorem FootprintEntry.Narrows.refl (e : FootprintEntry) : e.Narrows e :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, VClock.le_refl _⟩

theorem FootprintEntry.Narrows.trans {e e₁ e₂ : FootprintEntry} (h₁ : e.Narrows e₁)
    (h₂ : e₁.Narrows e₂) : e.Narrows e₂ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, Nat.le_trans h₂.2.2.2.1 h₁.2.2.2.1,
    Nat.le_trans h₁.2.2.2.2.1 h₂.2.2.2.2.1, VClock.le_trans h₁.2.2.2.2.2 h₂.2.2.2.2.2⟩

theorem FootprintEntry.Narrows.clock {e e₀ : FootprintEntry} (hn : e.Narrows e₀) :
    VClock.le e.clock e₀.clock = true := hn.2.2.2.2.2

/-- Forgetting the accesses past an offset (`Mem.forgetFrom`) narrows an entry. -/
theorem FootprintEntry.forgetFrom_narrows (b : BlockId) (S : Nat) (e : FootprintEntry) :
    (e.forgetFrom b S).Narrows e := by
  unfold FootprintEntry.forgetFrom
  split
  · exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, VClock.le_default _⟩
  · split
    · exact ⟨rfl, rfl, rfl, Nat.le_refl _, by simp only; omega, VClock.le_refl _⟩
    · exact .refl e

/-- A narrowing of a plain write to bytes is one of the entry. -/
theorem FootprintEntry.Narrows.plainHit {e e₀ : FootprintEntry} {b o len : Nat} (hn : e.Narrows e₀)
    (h : Zig.plainHit b o len e = true) : Zig.plainHit b o len e₀ = true := by
  obtain ⟨-, hb, hk, ho, hl, -⟩ := hn
  have hk' := Conc.Proto.plainHit_kind h
  obtain ⟨h0, h1, h2, h3⟩ := Conc.Proto.plainHit_range h
  have hb' := Conc.Proto.plainHit_block h
  simp only [Zig.plainHit, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hb ▸ hb', hk ▸ hk'⟩, h0⟩, by omega⟩, by omega⟩, by omega⟩

/-- A narrowing touches only bytes that the entry touches. -/
theorem FootprintEntry.Narrows.touches {e e₀ : FootprintEntry} {h : Heap} (hn : e.Narrows e₀)
    (ht : e.Touches h) : e₀.Touches h := by
  obtain ⟨x, h1, h2, h3⟩ := ht
  obtain ⟨-, hb, -, ho, hl, -⟩ := hn
  exact ⟨x, by omega, by omega, hb ▸ h3⟩

namespace AMap

variable {hF hF' : Heap} {m m' m'' : Mem} {σ σ' : Nat → Option Nat}

theorem refl (m : Mem) (hF : Heap) : AMap hF m m some where
  mono _ _ _ _ h h' hlt := by cases h; cases h'; exact hlt
  kept _ _ l h hl := by cases h; exact ⟨l, hl, rfl, rfl, rfl⟩
  frame i _ hl _ := ⟨i, rfl, hl⟩
  new j _ hl hn := absurd rfl (hn j (Array.getElem?_eq_some_iff.mp hl).1)
  seen := by
    conv => lhs; rw [← Array.filterMap_some (xs := m.seen.filter _)]
    rfl
  own _ _ _ _ _ h := by cases h; rfl

/-- A step that keeps the atomic locations and the views. -/
theorem of_eq (ha : m'.atomics = m.atomics) (hs : m'.seen = m.seen) : AMap hF m m' some := by
  have h := refl m hF
  exact { mono := h.mono, kept := fun i j l hi hl => by rw [ha]; exact h.kept i j l hi hl,
          frame := fun i l hl hin => by rw [ha]; exact h.frame i l hl hin,
          new := fun j l hl hn => h.new j l (ha ▸ hl) hn, seen := by rw [hs]; exact h.seen,
          own := fun _ _ _ _ _ h => by cases h; simp only [Mem.seenAt, hs] }

theorem trans (h₁ : AMap hF m m' σ) (h₂ : AMap hF m' m'' σ') (hc : m'.current = m.current) :
    AMap hF m m'' fun i => (σ i).bind σ' where
  mono i i' j j' h h' hlt := by
    obtain ⟨k, hk, hkj⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k', hk', hkj'⟩ := Option.bind_eq_some_iff.mp h'
    exact h₂.mono k k' j j' hkj hkj' (h₁.mono i i' k k' hk hk' hlt)
  kept i j l h hl := by
    obtain ⟨k, hk, hkj⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l', hl', hb, ho, hn⟩ := h₁.kept i k l hk hl
    obtain ⟨l'', hl'', hb', ho', hn'⟩ := h₂.kept k j l' hkj hl'
    exact ⟨l'', hl'', hb'.trans hb, ho'.trans ho, hn'.trans hn⟩
  frame i l hl hin := by
    obtain ⟨k, hk, hl'⟩ := h₁.frame i l hl hin
    obtain ⟨j, hj, hl''⟩ := h₂.frame k l hl' hin
    exact ⟨j, by simp [hk, hj], hl''⟩
  new j l'' hl'' hn := by
    by_cases hk : ∃ k < m'.atomics.size, σ' k = some j
    · obtain ⟨k, hks, hkj⟩ := hk
      obtain ⟨l', hl'⟩ : ∃ l', m'.atomics[k]? = some l' := ⟨_, Array.getElem?_eq_getElem hks⟩
      obtain ⟨hpos, hoff⟩ := h₁.new k l' hl' fun i hi hik => hn i hi (by simp [hik, hkj])
      obtain ⟨l₂, hl₂, hb, ho, hlen⟩ := h₂.kept k j l' hkj hl'
      rw [hl''] at hl₂; cases hl₂
      exact ⟨by omega, fun x h1 h2 => by rw [hb]; exact hoff x (by omega) (by omega)⟩
    · exact h₂.new j l'' hl'' fun k hks hkj => hk ⟨k, hks, hkj⟩
  seen := by
    rw [← hc, h₂.seen, hc, h₁.seen, Array.filterMap_filterMap]
    congr 1; funext p
    cases σ p.2.1 <;> simp
  own i l j hl hin h := by
    obtain ⟨k, hk, hkj⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k', hk', hl'⟩ := h₁.frame i l hl hin
    rw [hk] at hk'; cases hk'
    rw [← hc, h₂.own k l j hl' hin hkj, hc, h₁.own i l k hl hin hk]

theorem weaken (h : AMap hF m m' σ) (hsub : ∀ l, hF' l ≠ none → hF l ≠ none) :
    AMap hF' m m' σ :=
  { h with
    frame := fun i l hl hin => h.frame i l hl fun x h1 h2 => hsub _ (hin x h1 h2)
    own := fun i l j hl hin => h.own i l j hl fun x h1 h2 => hsub _ (hin x h1 h2)
    new := fun j l hl hn => ⟨(h.new j l hl hn).1, fun x h1 h2 => by
      have := (h.new j l hl hn).2 x h1 h2
      cases e : hF' (l.block, x) with
      | none => rfl
      | some _ => exact absurd this (hsub _ (by simp [e]))⟩ }

theorem inj (h : AMap hF m m' σ) {i i' j : Nat} (hi : σ i = some j) (hi' : σ i' = some j) :
    i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | e | hlt
  · exact absurd (h.mono i i' j j hi hi' hlt) (Nat.lt_irrefl j)
  · exact e
  · exact absurd (h.mono i' i j j hi' hi hlt) (Nat.lt_irrefl j)

/-- Another thread's view moves with a retained location. -/
theorem seenAt_other (h : AMap hF m m' σ) {u i j : Nat} (hu : u ≠ m.current)
    (hij : σ i = some j) : m'.seenAt u j = m.seenAt u i := by
  have hq : ∀ p : ThreadId × Nat × Nat, p.1 = u → (p.1 != m.current) = true := fun p hp => by
    simp [hp, hu]
  unfold Mem.seenAt
  rw [← seenAt_filter (s := m'.seen) hq, h.seen, seen_reindex (fun _ _ _ => h.inj) hij,
    seenAt_filter hq]

/-- Every thread's view of a framed location stays at its new index. -/
theorem seenAt_frame (h : AMap hF m m' σ) {i j : Nat} {l : ALoc} (hl : m.atomics[i]? = some l)
    (hin : l.In hF) (hij : σ i = some j) (u : Nat) : m'.seenAt u j = m.seenAt u i := by
  by_cases hu : u = m.current
  · subst hu; exact h.own i l j hl hin hij
  · exact h.seenAt_other hu hij

/-- A location after the step is one of `m`'s with the same bytes, or a new one with a byte,
none of the frame's. -/
theorem mem (h : AMap hF m m' σ) {l' : ALoc} (hl : l' ∈ m'.atomics) :
    (∃ l ∈ m.atomics, l'.block = l.block ∧ l'.off = l.off ∧ l'.len = l.len) ∨
      (0 < l'.len ∧ l'.Off hF) := by
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hl
  by_cases hk : ∃ i < m.atomics.size, σ i = some j
  · obtain ⟨i, hi, hij⟩ := hk
    obtain ⟨l', hl', hb, ho, hn⟩ := h.kept i j _ hij (Array.getElem?_eq_getElem hi)
    rw [Array.getElem?_eq_getElem hj] at hl'; cases hl'
    exact .inl ⟨_, Array.getElem_mem hi, hb, ho, hn⟩
  · exact .inr (h.new j _ (Array.getElem?_eq_getElem hj) fun i hi hij => hk ⟨i, hi, hij⟩)

/-- A byte property covered by the frame can only belong to a retained location. -/
theorem kept_of_cov (h : AMap hF m m' σ) {p : ALoc → Bool}
    (hp : ∀ l l', l.block = l'.block → l.off = l'.off → l.len = l'.len → p l = p l')
    (hcov : ∀ l, p l = true → 0 < l.len → ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ hF (l.block, x) ≠ none)
    {k : Nat} (hk : k < m'.atomics.size) (hpk : p m'.atomics[k] = true) :
    ∃ i, ∃ hi : i < m.atomics.size, σ i = some k ∧ p m.atomics[i] = true := by
  by_cases hx : ∃ i < m.atomics.size, σ i = some k
  · obtain ⟨i, hi, hik⟩ := hx
    obtain ⟨l', hl', hb, ho, hn⟩ := h.kept i k _ hik (Array.getElem?_eq_getElem hi)
    rw [Array.getElem?_eq_getElem hk] at hl'; cases hl'
    exact ⟨i, hi, hik, (hp _ _ hb ho hn).symm.trans hpk⟩
  · obtain ⟨hpos, hoff⟩ := h.new k _ (Array.getElem?_eq_getElem hk) fun i hi hik => hx ⟨i, hi, hik⟩
    obtain ⟨x, h1, h2, h3⟩ := hcov _ hpk hpos
    exact absurd (hoff x h1 h2) h3

/-- The first framed location with a byte property stays first, at its new index. -/
theorem first_eq (h : AMap hF m m' σ) {p : ALoc → Bool}
    (hp : ∀ l l', l.block = l'.block → l.off = l'.off → l.len = l'.len → p l = p l')
    (hin : ∀ i l, m.atomics.findIdx? p = some i → m.atomics[i]? = some l → l.In hF)
    (hcov : ∀ l, p l = true → 0 < l.len → ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ hF (l.block, x) ≠ none)
    {i j : Nat} (hfi : m.atomics.findIdx? p = some i) (hij : σ i = some j) :
    m'.atomics.findIdx? p = some j := by
  obtain ⟨hi, hpi, hfirst⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfi
  obtain ⟨j', hij', hl'⟩ := h.frame i _ (Array.getElem?_eq_getElem hi)
    (hin i _ hfi (Array.getElem?_eq_getElem hi))
  rw [hij] at hij'; cases hij'
  have hj : j < m'.atomics.size := (Array.getElem?_eq_some_iff.mp hl').1
  refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨hj, ?_, fun k hkj hpk => ?_⟩
  · rw [Array.getElem?_eq_getElem hj] at hl'
    rw [Option.some.inj hl']; exact hpi
  · obtain ⟨i', hi', hik, hpi'⟩ := h.kept_of_cov hp hcov _ (by simpa using hpk)
    rcases Nat.lt_trichotomy i' i with hlt | rfl | hgt
    · exact hfirst i' hlt hpi'
    · rw [hij] at hik; cases hik; exact Nat.lt_irrefl _ hkj
    · exact Nat.lt_asymm hkj (h.mono i i' j k hij hik hgt)

/-- **The first location with a property of its bytes stays the first one**, when the first one
of `m` lies in the frame and every location with the property has a byte of the frame. -/
theorem first_iff (h : AMap hF m m' σ) {p : ALoc → Bool}
    (hp : ∀ l l', l.block = l'.block → l.off = l'.off → l.len = l'.len → p l = p l')
    (hin : ∀ i l, m.atomics.findIdx? p = some i → m.atomics[i]? = some l → l.In hF)
    (hcov : ∀ l, p l = true → 0 < l.len → ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ hF (l.block, x) ≠ none)
    (l : ALoc) :
    (∃ i, m.atomics.findIdx? p = some i ∧ m.atomics[i]? = some l) ↔
      (∃ j, m'.atomics.findIdx? p = some j ∧ m'.atomics[j]? = some l) := by
  constructor
  · rintro ⟨i, hfi, hl⟩
    obtain ⟨j, hij, hl'⟩ := h.frame i l hl (hin i l hfi hl)
    exact ⟨j, h.first_eq hp hin hcov hfi hij, hl'⟩
  · rintro ⟨j, hfj, hl⟩
    obtain ⟨hj, hpj, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfj
    obtain ⟨i₀, hi₀, -, hpi₀⟩ := h.kept_of_cov hp hcov hj hpj
    obtain ⟨i, hfi⟩ : ∃ i, m.atomics.findIdx? p = some i := Option.isSome_iff_exists.mp (by
      rw [Array.findIdx?_isSome, Array.any_eq_true]; exact ⟨i₀, hi₀, hpi₀⟩)
    obtain ⟨hi, -, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfi
    obtain ⟨j₁, hij₁, hl₁⟩ := h.frame i _ (Array.getElem?_eq_getElem hi)
      (hin i _ hfi (Array.getElem?_eq_getElem hi))
    have hjj : j₁ = j := Option.some.inj ((h.first_eq hp hin hcov hfi hij₁).symm.trans hfj)
    subst j₁
    rw [hl] at hl₁
    exact ⟨i, hfi, by rw [Array.getElem?_eq_getElem hi, hl₁]⟩

end AMap

/-! ## Retiring atomic locations (`Mem.retire`) -/

theorem List.zipIdx_pairwise_snd {α : Type} (L : List α) (k : Nat) :
    (L.zipIdx k).Pairwise (fun a b => a.2 < b.2) := by
  induction L generalizing k with
  | nil => exact List.Pairwise.nil
  | cons a L ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    exact ⟨fun y hy => Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (List.le_snd_of_mem_zipIdx hy),
      ih (k + 1)⟩

section Retire

variable {m : Mem} {b : BlockId} {o len : Nat}

/-- The kept indices increase. -/
theorem Mem.retireIdx_lt {i j : Nat} (hi : i < (m.retireIdx b o len).size)
    (hj : j < (m.retireIdx b o len).size) (hij : i < j) :
    (m.retireIdx b o len)[i] < (m.retireIdx b o len)[j] := by
  have hp : (m.retireIdx b o len).toList.Pairwise (· < ·) := by
    simp only [Mem.retireIdx, Array.toList_map, Array.toList_filter, Array.toList_zipIdx]
    exact List.pairwise_map.mpr ((List.zipIdx_pairwise_snd _ 0).filter _)
  have := List.pairwise_iff_getElem.mp hp i j (by simpa using hi) (by simpa using hj) hij
  simpa using this

/-- The kept indices are the locations that do not overlap the bytes. -/
theorem Mem.mem_retireIdx {i : Nat} :
    i ∈ m.retireIdx b o len ↔ ∃ h : i < m.atomics.size, m.atomics[i].hits b o len = false := by
  simp only [Mem.retireIdx, Array.mem_map, Array.mem_filter, Array.mem_zipIdx_iff_getElem?,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨⟨l, j⟩, ⟨hl, hh⟩, rfl⟩
    obtain ⟨hj, e⟩ := Array.getElem?_eq_some_iff.mp hl
    exact ⟨hj, by rw [e]; exact hh⟩
  · rintro ⟨hi, hh⟩
    exact ⟨⟨m.atomics[i], i⟩, ⟨Array.getElem?_eq_getElem hi, hh⟩, rfl⟩

theorem Mem.retireIdx_bound {j : Nat} (hj : j < (m.retireIdx b o len).size) :
    (m.retireIdx b o len)[j] < m.atomics.size :=
  (Mem.mem_retireIdx.mp (Array.getElem_mem hj)).1

theorem Mem.retireIdx_idxOf {j : Nat} (hj : j < (m.retireIdx b o len).size) :
    (m.retireIdx b o len).idxOf? (m.retireIdx b o len)[j] = some j := by
  have e : (m.retireIdx b o len).finIdxOf? (m.retireIdx b o len)[j] = some ⟨j, hj⟩ :=
    Array.finIdxOf?_eq_some_iff.mpr ⟨rfl, fun k hk =>
      Nat.ne_of_lt (Mem.retireIdx_lt (m := m) (b := b) (o := o) (len := len) k.2 hj hk)⟩
  rw [Array.idxOf?, e]; rfl

theorem Mem.retireIdx_of_idxOf {i j : Nat} (h : (m.retireIdx b o len).idxOf? i = some j) :
    ∃ hj : j < (m.retireIdx b o len).size, (m.retireIdx b o len)[j] = i := by
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨f.2, (Array.finIdxOf?_eq_some_iff.mp hf).1⟩

theorem Mem.retire_get {j : Nat} (hj : j < (m.retireIdx b o len).size) :
    (m.retire b o len).atomics[j]? = m.atomics[(m.retireIdx b o len)[j]]? := by
  have hb := Mem.retireIdx_bound hj
  simp only [Mem.retire, Array.getElem?_map, Array.getElem?_eq_getElem hj, Option.map_some,
    Array.getElem?_eq_getElem hb]
  rw [getElem!_pos m.atomics ((m.retireIdx b o len)[j]) hb]

/-- Retirement carries every view of a retained location to its new index. -/
theorem Mem.retire_seenAt {i j : Nat} (hij : (m.retireIdx b o len).idxOf? i = some j) (u : Nat) :
    (m.retire b o len).seenAt u j = m.seenAt u i :=
  seen_reindex (fun _ _ _ h h' => by
    obtain ⟨_, e⟩ := Mem.retireIdx_of_idxOf h
    obtain ⟨_, e'⟩ := Mem.retireIdx_of_idxOf h'
    exact e.symm.trans e') hij

/-- **Retiring the locations over bytes that the frame does not have** keeps the frame's
locations (each at its new index) and the other threads' views of them. -/
theorem AMap.retire {hF : Heap} (hcut : ∀ x, o ≤ x → x < o + len → hF (b, x) = none) :
    AMap hF m (m.retire b o len) fun i => (m.retireIdx b o len).idxOf? i where
  mono i i' j j' h h' hlt := by
    obtain ⟨hj, ej⟩ := Mem.retireIdx_of_idxOf h
    obtain ⟨hj', ej'⟩ := Mem.retireIdx_of_idxOf h'
    rcases Nat.lt_trichotomy j j' with hjj | rfl | hjj
    · exact hjj
    · omega
    · have := Mem.retireIdx_lt hj' hj hjj; omega
  kept i j l h hl := by
    obtain ⟨hj, ej⟩ := Mem.retireIdx_of_idxOf h
    exact ⟨l, by rw [Mem.retire_get hj, ej, hl], rfl, rfl, rfl⟩
  frame i l hl hin := by
    obtain ⟨hi, e⟩ := Array.getElem?_eq_some_iff.mp hl
    have hn : m.atomics[i].hits b o len = false := by
      cases hh : m.atomics[i].hits b o len
      · rfl
      · exfalso
        simp only [ALoc.hits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, e] at hh
        obtain ⟨⟨⟨⟨hb, h0⟩, hl0⟩, h1⟩, h2⟩ := hh
        have hx : ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ o ≤ x ∧ x < o + len :=
          ⟨if o ≤ l.off then l.off else o, by split <;> omega, by split <;> omega,
            by split <;> omega, by split <;> omega⟩
        obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hx
        exact hin x hx1 hx2 (by rw [hb]; exact hcut x hx3 hx4)
    obtain ⟨j, hj, ej⟩ := Array.getElem_of_mem (Mem.mem_retireIdx.mpr ⟨hi, hn⟩)
    exact ⟨j, by rw [← ej]; exact Mem.retireIdx_idxOf hj, by rw [Mem.retire_get hj, ej, hl]⟩
  new j l hl hn := by
    have hj : j < (m.retireIdx b o len).size := by
      have := (Array.getElem?_eq_some_iff.mp hl).1; simpa [Mem.retire] using this
    exact absurd (Mem.retireIdx_idxOf hj) (hn _ (Mem.retireIdx_bound hj))
  seen := by
    simp only [Mem.retire, Array.filter_filterMap, Array.filterMap_filter]
    congr 1; funext p
    cases h : p.1 != m.current <;> cases (m.retireIdx b o len).idxOf? p.2.1 <;> simp_all
  own i _ j _ _ hij := Mem.retire_seenAt hij _

/-- Forgetting the accesses past `S` of block `b` keeps every access to the bytes of a location
before `S`, with its clock. -/
theorem FootprintEntry.forgetFrom_hits {e : FootprintEntry} {l : ALoc} {b : BlockId} {S : Nat}
    (hl : l.block = b → l.off + l.len ≤ S) (hpos : 0 < l.len) (hh : e.Hits l) :
    (e.forgetFrom b S).Hits l ∧ (e.forgetFrom b S).clock = e.clock := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  unfold FootprintEntry.forgetFrom
  split
  · rename_i hc
    have := hl (h1 ▸ hc.1); omega
  · split
    · rename_i hc
      have := hl (h1 ▸ hc.1)
      exact ⟨⟨h1, by simp only; omega, by simp only; omega, h4⟩, rfl⟩
    · exact ⟨⟨h1, h2, h3, h4⟩, rfl⟩

/-- A location that a retirement keeps is an old one that does not overlap the bytes. -/
theorem Mem.mem_retire {l : ALoc} (hl : l ∈ (m.retire b o len).atomics) :
    l ∈ m.atomics ∧ l.hits b o len = false := by
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hl
  have hj' : j < (m.retireIdx b o len).size := by simpa [Mem.retire] using hj
  have := Mem.retire_get (m := m) hj'
  rw [Array.getElem?_eq_getElem hj] at this
  rw [Array.getElem?_eq_getElem (Mem.retireIdx_bound hj')] at this
  rw [Option.some.inj this]
  exact ⟨Array.getElem_mem _, (Mem.mem_retireIdx.mp (Array.getElem_mem hj')).2⟩

theorem Mem.mem_retire_atomics {l : ALoc} (hl : l ∈ (m.retire b o len).atomics) : l ∈ m.atomics :=
  (Mem.mem_retire hl).1

/-- **Forgetting the accesses past the end of block `b'`** (`Mem.forgetFrom`, a revival: `S` at
least the block's size) is a step of the thread for every frame: it only narrows entries, and no
location lies past the block's end (`Mem.MsgCov`). -/
theorem FStepIn.forgetFrom {hF : Heap} (b' : BlockId) (S : Nat)
    (hS : ∀ blk, m.blocks[b']? = some blk → blk.bytes.size ≤ S) :
    FStepIn hF m (m.forgetFrom b' S) where
  current := rfl
  threads := rfl
  waiters := rfl
  woken := rfl
  groups := rfl
  size := rfl
  others _ _ := rfl
  mine := VClock.le_refl _
  blocks := Nat.le_refl _
  nextMsg := Nat.le_refl _
  atomics := ⟨some, AMap.of_eq rfl rfl⟩
  fp e he := by
    obtain ⟨e₀, he₀, rfl⟩ := Array.mem_map.mp he
    exact .inl ⟨e₀, he₀, FootprintEntry.forgetFrom_narrows _ _ _⟩
  fpc e he := by
    obtain ⟨e₀, he₀, rfl⟩ := Array.mem_map.mp he
    exact .inl ⟨e₀, he₀, FootprintEntry.forgetFrom_narrows _ _ _⟩
  const _ _ h := h
  cov F h := by
    intro l hl hpos
    obtain ⟨hin, hmsg⟩ := h l hl hpos
    have hl' : l.block = b' → l.off + l.len ≤ S := fun e => by
      obtain ⟨blk, h1, h2⟩ := hin
      rw [e] at h1; exact Nat.le_trans h2 (hS blk h1)
    have hover : ∀ c, l.over ((m.forgetFrom b' S).withFp F) c = true →
        l.over (m.withFp F) c = true := by
      intro c hc
      refine ALoc.over_iff.mpr fun e he hh => ?_
      rcases Array.mem_append.mp he with he | he
      · exact ALoc.over_iff.mp hc e (Array.mem_append.mpr (.inl he)) hh
      · obtain ⟨h1, h2⟩ := FootprintEntry.forgetFrom_hits hl' hpos hh
        have := ALoc.over_iff.mp hc _
          (Array.mem_append.mpr (.inr (Array.mem_map.mpr ⟨e, he, rfl⟩))) h1
        rwa [h2] at this
    exact ⟨hin, fun msg hm => ⟨fun c hc => (hmsg msg hm).1 c (hover c hc),
      fun c hc => (hmsg msg hm).2 c (hover c hc)⟩⟩

/-- Retiring the locations over bytes that the frame does not have is a step of the thread. -/
theorem FStepIn.retire {hF : Heap} (hcut : ∀ x, o ≤ x → x < o + len → hF (b, x) = none) :
    FStepIn hF m (m.retire b o len) where
  current := rfl
  threads := rfl
  waiters := rfl
  woken := rfl
  groups := rfl
  size := rfl
  others _ _ := rfl
  mine := VClock.le_refl _
  blocks := Nat.le_refl _
  nextMsg := Nat.le_refl _
  atomics := ⟨_, AMap.retire hcut⟩
  fp e he := .inl ⟨e, he, .refl e⟩
  fpc e he := .inl ⟨e, he, .refl e⟩
  const _ _ h := h
  cov := Mem.MsgCov.keepFp (fun _ hl _ => Mem.mem_retire_atomics hl) (fun _ _ _ h => h)
    (fun _ he => he)

end Retire

section FStep

variable {m m' m'' : Mem} {hF hF' : Heap}

/-- A `StepIn` that makes no `const` global, writes none and keeps the messages covered is an
`FStepIn`. -/
theorem FStepIn.of_stepIn (hs : StepIn hF m m')
    (hk : ∀ b, b < m.blocks.size → m'.IsConst b → m.IsConst b)
    (hw : ∀ e ∈ m'.footprint, e ∉ m.footprint → e.kind.isWrite = true → ¬ m'.IsConst e.block)
    (hcov : ∀ F, (m.withFp F).MsgCov → (m'.withFp F).MsgCov) :
    FStepIn hF m m' where
  current := hs.current
  threads := hs.threads
  waiters := hs.waiters
  woken := hs.woken
  groups := hs.groups
  size := hs.size
  others := hs.others
  mine := hs.mine
  blocks := hs.blocks
  nextMsg := Nat.le_of_eq hs.nextMsg.symm
  atomics := ⟨some, AMap.of_eq hs.atomics hs.seen⟩
  fp e he := by
    by_cases hm : e ∈ m.footprint
    · exact .inl ⟨e, hm, .refl e⟩
    · rcases hs.fp e he with h | ⟨ht, hnt, hb⟩
      · exact absurd h hm
      · exact .inr ⟨ht, hnt, hb, hw e he hm⟩
  fpc e he := (hs.fpc e he).imp (fun h => ⟨e, h, .refl e⟩) id
  const := hk
  cov := hcov

theorem FStepIn.refl (m : Mem) (hF : Heap) : FStepIn hF m m :=
  .of_stepIn (StepIn.refl m hF) (fun _ _ h => h) (fun _ he hn => absurd he hn) fun _ h => h

/-- A step keeps the messages covered (`FStepIn.cov`, no record in front). -/
theorem FStepIn.msgCov (hs : FStepIn hF m m') (h : m.MsgCov) : m'.MsgCov := by
  have := hs.cov #[] (by rw [Mem.withFp_nil]; exact h)
  rwa [Mem.withFp_nil] at this

theorem FStepIn.trans (h₁ : FStepIn hF m m') (h₂ : FStepIn hF m' m'') : FStepIn hF m m'' := by
  obtain ⟨σ, ha⟩ := h₁.atomics
  obtain ⟨σ', ha'⟩ := h₂.atomics
  have hmine : VClock.le (m.clocks[m.current]!) (m''.clocks[m.current]!) = true := by
    have := h₂.mine; rw [h₁.current] at this; exact VClock.le_trans h₁.mine this
  refine ⟨h₂.current.trans h₁.current, h₂.threads.trans h₁.threads, h₂.waiters.trans h₁.waiters,
    h₂.woken.trans h₁.woken, h₂.groups.trans h₁.groups, h₂.size.trans h₁.size,
    fun u hu => (h₂.others u (h₁.current ▸ hu)).trans (h₁.others u hu), hmine,
    Nat.le_trans h₁.blocks h₂.blocks, Nat.le_trans h₁.nextMsg h₂.nextMsg,
    ⟨_, ha.trans ha' h₁.current⟩, fun e he => ?_, fun e he => ?_,
    fun b hb hc => h₁.const b hb (h₂.const b (Nat.lt_of_lt_of_le hb h₁.blocks) hc),
    fun F h => h₂.cov F (h₁.cov F h)⟩
  · rcases h₂.fp e he with ⟨e₁, he₁, hn⟩ | ⟨ht, hnt, hb, hw⟩
    · rcases h₁.fp e₁ he₁ with ⟨e₀, he₀, hn'⟩ | ⟨ht, hnt, hb, hw⟩
      · exact .inl ⟨e₀, he₀, hn.trans hn'⟩
      · have hnt' : ¬ e.Touches hF := fun h => hnt (hn.touches h)
        obtain ⟨h1, h2, h3, -⟩ := hn
        refine .inr ⟨h1.trans ht, hnt', h2 ▸ Nat.lt_of_lt_of_le hb h₂.blocks, fun hwr hc => ?_⟩
        rw [h3] at hwr
        exact hw hwr (h2 ▸ h₂.const _ (h2 ▸ hb) (h2 ▸ hc))
    · exact .inr ⟨ht.trans h₁.current, hnt, hb, hw⟩
  · rcases h₂.fpc e he with ⟨e₁, he₁, hn⟩ | hle
    · rcases h₁.fpc e₁ he₁ with ⟨e₀, he₀, hn'⟩ | hle
      · exact .inl ⟨e₀, he₀, hn.trans hn'⟩
      · have := h₂.mine; rw [h₁.current] at this
        exact .inr (VClock.le_trans hn.clock (VClock.le_trans hle this))
    · rw [h₁.current] at hle; exact .inr hle

/-- A step in a larger frame is a step in a part of it. -/
theorem FStepIn.weaken (hs : FStepIn hF m m') (hsub : ∀ l, hF' l ≠ none → hF l ≠ none) :
    FStepIn hF' m m' :=
  { hs with
    atomics := let ⟨σ, ha⟩ := hs.atomics; ⟨σ, ha.weaken hsub⟩
    fp := fun e he => (hs.fp e he).imp id fun ⟨ht, hnt, hb, hw⟩ =>
      ⟨ht, fun ⟨x, h1, h2, h3⟩ => hnt ⟨x, h1, h2, hsub _ h3⟩, hb, hw⟩ }

/-- No clock gets smaller. -/
theorem FStepIn.clock (hs : FStepIn hF m m') (u : ThreadId) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  by_cases hc : u = m.current
  · subst hc; exact hs.mine
  · rw [hs.others u hc]; exact VClock.le_refl _

/-- An `FStepIn hF` keeps the ownership of each part of `hF`, by any clock. -/
theorem Mem.OwnsC.fstep (hs : FStepIn hF m m') {c : VClock} {h : Heap} (ho : m.OwnsC c h)
    (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.OwnsC c h := by
  intro e he ht
  rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, hb, -⟩
  · refine VClock.le_trans hn.clock (ho e₀ he₀ ?_)
    rcases ht with ht | hb
    · exact .inl (hn.touches ht)
    · exact .inr (hn.2.1 ▸ Nat.le_trans hs.blocks hb)
  · rcases ht with ⟨x, hx1, hx2, hx3⟩ | hb'
    · exact absurd ⟨x, hx1, hx2, hsub _ hx3⟩ hnt
    · exact absurd hb' (Nat.not_le.mpr hb)

/-- Another thread keeps what it owns over an `FStepIn hF` when that is a part of `hF`. -/
theorem Mem.Owns.fstep {u : ThreadId} {h : Heap} (hs : FStepIn hF m m') (hu : u ≠ m.current)
    (ho : m.Owns u h) (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.Owns u h := by
  unfold Mem.Owns; rw [hs.others u hu]; exact Mem.OwnsC.fstep hs ho hsub

/-- The current thread keeps what it owns in `hF` over an `FStepIn hF`. -/
theorem Mem.Owns.fstepSelf {h : Heap} (hs : FStepIn hF m m') (ho : m.Owns m.current h)
    (hsub : ∀ l, h l ≠ none → hF l ≠ none) : m'.Owns m'.current h := by
  unfold Mem.Owns; rw [hs.current]; exact (Mem.OwnsC.fstep hs ho hsub).mono hs.mine

/-- The plain writes to bytes of the frame stay before `c` over an `FStepIn` of the frame. -/
theorem Conc.Proto.PlainLe.fstep {b o len : Nat} {c : VClock} (h : PlainLe m b o len c)
    (hs : FStepIn hF m m') (hw : ∀ x, o ≤ x → x < o + len → hF (b, x) ≠ none) :
    PlainLe m' b o len c := by
  intro e he hh
  rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
  · exact VClock.le_trans hn.clock (h e₀ he₀ (hn.plainHit hh))
  · exfalso
    obtain ⟨h0, he0, h1, h2⟩ := plainHit_range hh
    have hx : ∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ o ≤ x ∧ x < o + len :=
      ⟨if o ≤ e.off then e.off else o, by split <;> omega, by split <;> omega,
        by split <;> omega, by split <;> omega⟩
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hx
    exact hnt ⟨x, hx1, hx2, by rw [plainHit_block hh]; exact hw x hx3 hx4⟩

/-- A change of block `b` to `nb` keeps every location in its block's bytes if the locations of
`b` fit in `nb`. -/
theorem ALoc.InBlock.setBlock {l : ALoc} {b : BlockId} {nb : Block} (h : l.InBlock m)
    (hsz : l.block = b → l.off + l.len ≤ nb.bytes.size) :
    l.InBlock { m with blocks := m.blocks.set! b nb } := by
  obtain ⟨blk, h1, h2⟩ := h
  show ∃ blk, (m.blocks.set! b nb)[l.block]? = some blk ∧ _
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : b = l.block
  · subst e
    exact ⟨nb, by simp [(Array.getElem?_eq_some_iff.mp h1).1], hsz rfl⟩
  · exact ⟨blk, by simp [e, h1], h2⟩

/-- A change of block `b` to `nb` records no access; `nb` is a `const` global only if `b` was,
and the locations of `b` fit in it. -/
theorem FStepIn.setBlock {b : BlockId} {nb : Block} (hk : nb.kind = .constGlobal → m.IsConst b)
    (hsz : ∀ l ∈ m.atomics, l.block = b → 0 < l.len → l.InBlock m → l.off + l.len ≤ nb.bytes.size) :
    FStepIn hF m { m with blocks := m.blocks.set! b nb } := by
  refine .of_stepIn (StepIn.setBlock m hF b nb) (fun b' hb' ⟨blk', h1, h2⟩ => ?_)
    (fun _ he hn => absurd he hn)
    (Mem.MsgCov.keepFp (fun _ hl _ => hl) (fun l hl hpos hin => hin.setBlock fun e => hsz l hl e hpos hin)
      fun _ he => he)
  have h1' : (m.blocks.set! b nb)[b']? = some blk' := h1
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h1'
  by_cases e : b = b'
  · subst e
    have : nb = blk' := by simpa [hb'] using h1'
    subst this; exact hk h2
  · simp only [e, ↓reduceIte] at h1'; exact ⟨blk', h1', h2⟩

/-- `Mem.write` of block `b` of `m` keeps its kind. -/
theorem FStepIn.write {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) (o : Nat)
    (bs : Array Byte) : FStepIn hF m (m.write b blk o bs) :=
  FStepIn.setBlock (fun h => ⟨blk, hb, h⟩) fun _ _ e _ ⟨blk', h1, h2⟩ => by
    rw [e, hb] at h1; cases h1
    exact Nat.le_trans h2 (writeBytes_size_ge _ _ _)

/-- A recorded access by the current thread that touches no byte of `hF` and writes no `const`
global. -/
theorem FStepIn.recordAt_of {b : BlockId} {off len : Nat} {kind : AccessKind}
    (hc : m.current < m.clocks.size) (hnt : ∀ x, off ≤ x → x < off + len → hF (b, x) = none)
    (hb : b < m.blocks.size) (hw : kind.isWrite = true → ¬ m.IsConst b) :
    FStepIn hF m (m.recordAt b off len kind) := by
  refine .of_stepIn (StepIn.recordAt_of hc hnt hb) (fun _ _ h => h) (fun e he hn hwr => ?_)
    (Mem.MsgCov.keepFp (fun _ hl _ => hl) (fun _ _ _ h => h) fun _ he =>
      by simp only [Mem.recordAt, Array.mem_push]; exact .inl he)
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact absurd he hn
  · exact hw hwr

/-- A recorded access by the current thread to bytes it owns (in `h`, not in `hF`) that writes
no `const` global. -/
theorem FStepIn.recordAt {h : Heap} {b : BlockId} {off len : Nat} {kind : AccessKind}
    (hc : m.current < m.clocks.size) (hd : Heap.Disjoint h hF)
    (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none) (hb : b < m.blocks.size)
    (hw : kind.isWrite = true → ¬ m.IsConst b) : FStepIn hF m (m.recordAt b off len kind) :=
  FStepIn.recordAt_of hc (fun x h1 h2 => (hd (b, x)).resolve_left (hin x h1 h2)) hb hw

/-- A read by the current thread that touches no byte of `hF`: recorded, or nothing for a
`const` global. -/
theorem FStepIn.readAt_of {blk : Block} {b : BlockId} {off len : Nat} {kind : AccessKind}
    (hc : m.current < m.clocks.size) (hnt : ∀ x, off ≤ x → x < off + len → hF (b, x) = none)
    (hb : b < m.blocks.size) (hw : kind.isWrite = true → ¬ m.IsConst b) :
    FStepIn hF m (m.readAt blk b off len kind) :=
  Mem.readAt_cases (P := FStepIn hF m) (FStepIn.refl m hF) (FStepIn.recordAt_of hc hnt hb hw)

theorem FStepIn.readAt {h : Heap} {blk : Block} {b : BlockId} {off len : Nat} {kind : AccessKind}
    (hc : m.current < m.clocks.size) (hd : Heap.Disjoint h hF)
    (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none) (hb : b < m.blocks.size)
    (hw : kind.isWrite = true → ¬ m.IsConst b) : FStepIn hF m (m.readAt blk b off len kind) :=
  FStepIn.readAt_of hc (fun x h1 h2 => (hd (b, x)).resolve_left (hin x h1 h2)) hb hw

theorem FStepIn.cur (hs : FStepIn hF m m') (hc : m.current < m.clocks.size) :
    m'.current < m'.clocks.size := by
  rw [hs.current, hs.size]; exact hc

end FStep

/-! ## The steps of an atomic op

An atomic op on a word (`ZigLean/Mem/Thread.lean`) records its access, finds or makes the word's
location (`locIdx`: a location of the word's bytes gets messages, a new one is pushed, a
mixed-size access retires the overlapping ones first), and then reads or inserts a message,
updates the thread's view (`observeM`) and, for an acquire, its clock (`acqM`). Each of these is
an `FStepIn` of every frame that has none of the word's bytes (`FStepIn.locIdx`, `observe`,
`acq`, `insertLast`, `loadM`, `storeM`, `rmwM`): the locations that change or are new lie over
the word, and only the current thread's view and clock change. -/

section AtomicStep

open Conc.Proto

variable {m m' : Mem} {hF : Heap}

/-- The locations stay at their indices (`σ = some`): a location keeps its bytes, and stays as it
is if it lies in the frame's bytes; a new one (past the old end) has a byte and none of the
frame's; the other threads' views stay. -/
theorem AMap.ofSome
    (hkept : ∀ (i : Nat) (l : ALoc), m.atomics[i]? = some l → ∃ l' : ALoc, m'.atomics[i]? = some l' ∧
      l'.block = l.block ∧ l'.off = l.off ∧ l'.len = l.len ∧ (l.In hF → l' = l))
    (hnew : ∀ (j : Nat) (l' : ALoc), m'.atomics[j]? = some l' → m.atomics.size ≤ j →
      0 < l'.len ∧ l'.Off hF)
    (hseen : m'.seen.filter (·.1 != m.current) = m.seen.filter (·.1 != m.current))
    (hown : ∀ i l, m.atomics[i]? = some l → l.In hF →
      m'.seenAt m.current i = m.seenAt m.current i) :
    AMap hF m m' some where
  mono _ _ _ _ h h' hlt := by cases h; cases h'; exact hlt
  kept i j l h hl := by
    cases h
    obtain ⟨l', hl', hb, ho, hn, -⟩ := hkept i l hl
    exact ⟨l', hl', hb, ho, hn⟩
  frame i l hl hin := by
    obtain ⟨l', hl', -, -, -, he⟩ := hkept i l hl
    exact ⟨i, rfl, by rw [hl', he hin]⟩
  new j l hl hn := hnew j l hl (Nat.le_of_not_lt fun hj => hn j hj rfl)
  seen := by
    rw [hseen]
    conv => lhs; rw [← Array.filterMap_some (xs := m.seen.filter _)]
    rfl
  own i l j hl hin h := by cases h; exact hown i l hl hin

/-- A step that changes only the atomic locations, the views and the message counter (which
grows). -/
theorem FStepIn.ofAMap {σ : Nat → Option Nat} (ha : AMap hF m m' σ) (hn : m.nextMsg ≤ m'.nextMsg)
    (he : m' = { m with atomics := m'.atomics, seen := m'.seen, nextMsg := m'.nextMsg })
    (hcov : ∀ F, (m.withFp F).MsgCov → (m'.withFp F).MsgCov) :
    FStepIn hF m m' := by
  have hfp : m'.footprint = m.footprint := (congrArg Mem.footprint he).trans rfl
  have hcl : m'.clocks = m.clocks := (congrArg Mem.clocks he).trans rfl
  have hbl : m'.blocks = m.blocks := (congrArg Mem.blocks he).trans rfl
  refine ⟨(congrArg Mem.current he).trans rfl, (congrArg Mem.threads he).trans rfl,
    (congrArg Mem.waiters he).trans rfl, (congrArg Mem.woken he).trans rfl,
    (congrArg Mem.groups he).trans rfl, by rw [hcl], fun u _ => by rw [hcl],
    by rw [hcl]; exact VClock.le_refl _, by rw [hbl]; exact Nat.le_refl _, hn, ⟨σ, ha⟩,
    fun e he' => .inl ⟨e, hfp ▸ he', .refl e⟩, fun e he' => .inl ⟨e, hfp ▸ he', .refl e⟩,
    fun b _ hc => ?_, hcov⟩
  obtain ⟨blk, h1, h2⟩ := hc
  exact ⟨blk, hbl ▸ h1, h2⟩

/-- The messages of a new location are covered in a memory with the record `F` in front. -/
def ALoc.NewCov (m : Mem) (l : ALoc) : Prop :=
  ∀ F, (m.withFp F).MsgCov → 0 < l.len →
    l.InBlock m ∧ ∀ msg ∈ l.msgs, l.CovBy (m.withFp F) msg.clock ∧ l.CovBy (m.withFp F) msg.relClock

/-- A new message `msg` of location `li` of `m` is covered, with any record in front. -/
def Mem.MsgCovAt (m : Mem) (li : Nat) (msg : Msg) : Prop :=
  ∀ F, (m.withFp F).MsgCov → 0 < (m.atomics[li]!).len →
    (m.atomics[li]!).CovBy (m.withFp F) msg.clock ∧ (m.atomics[li]!).CovBy (m.withFp F) msg.relClock

/-- **The message of a store or an RMW is covered**: its clock is that of the op's recorded access
to the word `e` (joined, for an acquiring RMW, with a covered clock `X`: the release clock of the
message it read), and its release clock is `X` joined with its clock, `X`, its clock or empty. -/
theorem Mem.MsgCovAt.of_entry {li : Nat} {msg : Msg} {e : FootprintEntry} {X : VClock}
    (he : e ∈ m.footprint) (hb : e.block = (m.atomics[li]!).block)
    (ho : e.off = (m.atomics[li]!).off) (hel : 0 < e.len)
    (hX : ∀ F, (m.withFp F).MsgCov → 0 < (m.atomics[li]!).len →
      (m.atomics[li]!).CovBy (m.withFp F) X)
    (hcl : msg.clock = e.clock ∨ msg.clock = VClock.merge e.clock X)
    (hrel : msg.relClock = VClock.merge X msg.clock ∨ msg.relClock = X ∨
      msg.relClock = msg.clock ∨ msg.relClock = #[]) :
    m.MsgCovAt li msg := by
  intro F h hpos
  have he' : (m.atomics[li]!).CovBy (m.withFp F) e.clock :=
    ALoc.CovBy.entry (Mem.mem_withFp he) ⟨hb, hel, by omega, by omega⟩
  have hc : (m.atomics[li]!).CovBy (m.withFp F) msg.clock := by
    rcases hcl with e1 | e1 <;> rw [e1]
    · exact he'
    · exact he'.merge (hX F h hpos)
  refine ⟨hc, ?_⟩
  rcases hrel with e2 | e2 | e2 | e2 <;> rw [e2]
  · exact (hX F h hpos).merge hc
  · exact hX F h hpos
  · exact hc
  · exact ALoc.CovBy.empty

/-- The release clock of a message of the location is covered. -/
theorem Mem.MsgCovAt.relClock_of_mem {li : Nat} {rd : Msg} (hrd : rd ∈ (m.atomics[li]!).msgs) :
    ∀ F, (m.withFp F).MsgCov → 0 < (m.atomics[li]!).len →
      (m.atomics[li]!).CovBy (m.withFp F) rd.relClock := by
  intro F h hpos
  by_cases hi : li < m.atomics.size
  · have hmem : m.atomics[li]! ∈ m.atomics := by
      rw [getElem!_pos m.atomics li hi]; exact Array.getElem_mem hi
    exact ((h _ hmem hpos).2 rd hrd).2
  · exfalso
    have : (m.atomics[li]!).len = 0 := by rw [getElem!_neg m.atomics li hi]; rfl
    omega

/-- A new location, over bytes that are not the frame's, in its block and with covered messages. -/
theorem FStepIn.pushLoc {l : ALoc} (hl : 0 < l.len) (hoff : l.Off hF) (hcov : l.NewCov m) :
    FStepIn hF m { m with atomics := m.atomics.push l, nextMsg := m.nextMsg + 1 } := by
  refine .ofAMap (AMap.ofSome (fun i l₀ h => ⟨l₀, ?_, rfl, rfl, rfl, fun _ => rfl⟩)
    (fun j l' h hj => ?_) rfl fun _ _ _ _ => rfl) (Nat.le_succ _) rfl
    fun F h => h.ofAtomics rfl rfl fun l' hl' hpos => ?_
  · have hi := (Array.getElem?_eq_some_iff.mp h).1
    show (m.atomics.push l)[i]? = some l₀
    rw [Array.getElem?_push_lt hi, ← Array.getElem?_eq_getElem hi]; exact h
  · have hj' := (Array.getElem?_eq_some_iff.mp h).1
    simp only [Array.size_push] at hj'
    have : j = m.atomics.size := by omega
    subst this
    have e : (m.atomics.push l)[m.atomics.size]? = some l := Array.getElem?_push_size
    rw [show ({ m with atomics := m.atomics.push l, nextMsg := m.nextMsg + 1 } : Mem).atomics =
      m.atomics.push l from rfl, e] at h
    cases h
    exact ⟨hl, hoff⟩
  · rcases Array.mem_push.mp hl' with hl' | rfl
    · exact .inl hl'
    · exact .inr (hcov F h hpos)

/-- New messages of a location with a byte that is not the frame's, covered. -/
theorem FStepIn.setLoc {i : Nat} {M : Array Msg} {n : Nat} (hn : m.nextMsg ≤ n)
    (hnot : ¬ (m.atomics[i]!).In hF)
    (hM : ∀ F, (m.withFp F).MsgCov → 0 < (m.atomics[i]!).len → ∀ msg ∈ M,
      (m.atomics[i]!).CovBy (m.withFp F) msg.clock ∧ (m.atomics[i]!).CovBy (m.withFp F) msg.relClock) :
    FStepIn hF m { m with atomics := m.atomics.set! i { m.atomics[i]! with msgs := M }, nextMsg := n } := by
  refine .ofAMap (AMap.ofSome (fun j l h => ?_) (fun j l' h hj => ?_) rfl
    fun _ _ _ _ => rfl) hn rfl
    fun F h => h.ofAtomics rfl rfl fun l' hl' hpos => ?_
  rotate_left 2
  · rw [Array.set!_eq_setIfInBounds] at hl'
    rcases Array.mem_or_eq_of_mem_setIfInBounds hl' with hl' | rfl
    · exact .inl hl'
    · by_cases hi : i < m.atomics.size
      · have hmem : m.atomics[i]! ∈ m.atomics := by
          rw [getElem!_pos m.atomics i hi]; exact Array.getElem_mem hi
        exact .inr ⟨(h _ hmem hpos).1, fun msg hm =>
          ⟨(hM F h hpos msg hm).1.congr rfl rfl rfl rfl, (hM F h hpos msg hm).2.congr rfl rfl rfl rfl⟩⟩
      · exfalso
        have : (m.atomics[i]!).len = 0 := by
          rw [getElem!_neg m.atomics i hi]; rfl
        simp only at hpos; omega
  · have hj := (Array.getElem?_eq_some_iff.mp h).1
    show ∃ l', (m.atomics.set! i _)[j]? = some l' ∧ _
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : i = j
    · subst e
      rw [getElem!_pos m.atomics i hj, Array.getElem?_eq_getElem hj] at *
      cases h
      exact ⟨{ m.atomics[i] with msgs := M }, by simp [hj], rfl, rfl, rfl,
        fun hin => absurd hin hnot⟩
    · exact ⟨l, by simp [e, h], rfl, rfl, rfl, fun _ => rfl⟩
  · have := (Array.getElem?_eq_some_iff.mp h).1
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at this
    omega

/-- The current thread observes a location that is not wholly in the frame. -/
theorem FStepIn.observe {li : Nat} (id : Nat) (hnot : ¬ (m.atomics[li]!).In hF) :
    FStepIn hF m (observeM m li id) := by
  refine .ofAMap (AMap.ofSome (fun i l h => ⟨l, h, rfl, rfl, rfl, fun _ => rfl⟩)
    (fun j l' h hj => absurd (Array.getElem?_eq_some_iff.mp h).1 (Nat.not_lt.mpr hj)) ?_ ?_)
    (Nat.le_refl _) rfl (Mem.MsgCov.keepFp (fun _ hl _ => hl) (fun _ _ _ h => h) fun _ he => he)
  · simp only [observeM, Array.filter_push, Array.filter_filter]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    congr 1; funext x
    rcases x with ⟨t, j, k⟩
    by_cases ht : t = m.current <;> simp [ht]
  · intro i l hl hin
    rw [seenAt_observe, ite_eq_right]
    rintro ⟨-, rfl⟩
    rw [getElem!_pos m.atomics i (Array.getElem?_eq_some_iff.mp hl).1,
      (Array.getElem?_eq_some_iff.mp hl).2] at hnot
    exact hnot hin

/-- Insertion changes a location's messages, its block's bytes and the message counter. -/
theorem insertM_atomics {li p : Nat} {msg : Msg} : (insertM m li p msg).atomics = m.atomics.set! li
    { m.atomics[li]! with msgs := (m.atomics[li]!).msgs.insertIdxIfInBounds p msg } := by
  unfold insertM; dsimp only; split
  · split <;> rfl
  · rfl

theorem insertM_seen {li p : Nat} {msg : Msg} : (insertM m li p msg).seen = m.seen := by
  unfold insertM; dsimp only; split
  · split <;> rfl
  · rfl

theorem insertM_nextMsg {li p : Nat} {msg : Msg} :
    (insertM m li p msg).nextMsg = m.nextMsg + 1 := by
  unfold insertM; dsimp only; split
  · split <;> rfl
  · rfl

theorem insertM_current {li p : Nat} {msg : Msg} : (insertM m li p msg).current = m.current := by
  unfold insertM; dsimp only; split
  · split <;> rfl
  · rfl

/-- Insertion keeps the location's byte range. -/
theorem insertM_in {li p : Nat} {msg : Msg} :
    ((insertM m li p msg).atomics[li]!).In hF ↔ (m.atomics[li]!).In hF := by
  rw [insertM_atomics]
  by_cases h : li < m.atomics.size
  · rw [Array.getElem!_set!_self _ _ _ h]; exact Iff.rfl
  · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds, dite_eq_right h]

/-- An acquire: the current thread's clock grows. -/
theorem FStepIn.acq (hc : m.current < m.clocks.size) (c : VClock) : FStepIn hF m (acqM m c) where
  current := rfl
  threads := rfl
  waiters := rfl
  woken := rfl
  groups := rfl
  size := by simp [acqM]
  others u hu := by
    show (m.clocks.set! m.current _)[u]! = _
    rw [Conc.Proto.getElem!_set!_ite]; simp [hu]
  mine := by
    show VClock.le _ ((m.clocks.set! m.current _)[m.current]!) = true
    rw [Array.getElem!_set!_self _ _ _ hc]; exact VClock.le_merge_left _ _
  blocks := Nat.le_refl _
  nextMsg := Nat.le_refl _
  atomics := ⟨some, AMap.of_eq rfl rfl⟩
  fp e he := .inl ⟨e, he, .refl e⟩
  fpc e he := .inl ⟨e, he, .refl e⟩
  const _ _ h := h
  cov _ h := h

/-- An atomic read of a message (`atomicLoadAt` after `loadPrep`). -/
theorem FStepIn.loadM (hc : m.current < m.clocks.size) {li : Nat} (ord : AtomicOrder) (msg : Msg)
    (hnot : ¬ (m.atomics[li]!).In hF) :
    FStepIn hF m (Conc.Proto.loadM m li ord msg) := by
  unfold Conc.Proto.loadM
  dsimp only
  split
  · exact (FStepIn.observe msg.id hnot).trans (FStepIn.acq (m := observeM m li msg.id) hc _)
  · exact FStepIn.observe msg.id hnot

/-- A message at the end of a location with a byte that is not the frame's: the location gets
it, and the block its bytes. -/
theorem FStepIn.insertLast {li : Nat} {msg : Msg} {blk : Block}
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) (hnot : ¬ (m.atomics[li]!).In hF)
    (hmsg : m.MsgCovAt li msg) :
    FStepIn hF m (insertM m li (m.atomics[li]!).msgs.size msg) := by
  rw [insertM_last hb]
  refine (FStepIn.setLoc (M := (m.atomics[li]!).msgs.push msg) (Nat.le_succ _) hnot
    fun F h hpos x hx => ?_).trans (FStepIn.setBlock (fun h => ⟨blk, hb, h⟩) fun l _ e _ hin => ?_)
  · rcases Array.mem_push.mp hx with hx | rfl
    · by_cases hi : li < m.atomics.size
      · have hmem : m.atomics[li]! ∈ m.atomics := by
          rw [getElem!_pos m.atomics li hi]; exact Array.getElem_mem hi
        exact ((h _ hmem hpos).2 x hx)
      · exfalso
        have : (m.atomics[li]!).len = 0 := by rw [getElem!_neg m.atomics li hi]; rfl
        omega
    · exact hmsg F h hpos
  · obtain ⟨blk', h1, h2⟩ := hin
    have h1' : m.blocks[l.block]? = some blk' := h1
    rw [e, hb] at h1'; cases h1'
    exact Nat.le_trans h2 (writeBytes_size_ge _ _ _)

/-- An atomic store at the end of a location with a byte that is not the frame's. -/
theorem FStepIn.storeM {n : Nat} {li : Nat} {blk : Block} (ord : AtomicOrder) (v : BitVec n)
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) (hnot : ¬ (m.atomics[li]!).In hF)
    (hmsg : m.MsgCovAt li (storeMsg m ord v)) :
    FStepIn hF m (Conc.Proto.storeM m li (m.atomics[li]!).msgs.size ord v) :=
  (FStepIn.insertLast hb hnot hmsg).trans (FStepIn.observe _ ((not_congr insertM_in).mpr hnot))

/-- **An RMW that read the newest message `rd` of a location** with a byte that is not the
frame's, after its recorded access `e` to the location's bytes at the thread's clock: its message
is covered (its clock is `e`'s, joined with `rd`'s release clock for an acquire). -/
theorem FStepIn.rmwM {n : Nat} {li pos : Nat} {blk : Block} {e : FootprintEntry} (ord : AtomicOrder)
    (rd : Msg) (new : BitVec n) (hc : m.current < m.clocks.size)
    (hpos : pos + 1 = (m.atomics[li]!).msgs.size)
    (hb : m.blocks[(m.atomics[li]!).block]? = some blk) (hnot : ¬ (m.atomics[li]!).In hF)
    (he : e ∈ m.footprint) (heb : e.block = (m.atomics[li]!).block)
    (heo : e.off = (m.atomics[li]!).off) (hel : 0 < e.len) (hec : e.clock = m.clocks[m.current]!)
    (hrd : rd ∈ (m.atomics[li]!).msgs) :
    FStepIn hF m (Conc.Proto.rmwM m li pos ord rd new) := by
  unfold Conc.Proto.rmwM
  dsimp only
  have hrel : ∀ M : Mem, (rmwMsg M ord rd new).relClock =
      VClock.merge rd.relClock (rmwMsg M ord rd new).clock ∨
      (rmwMsg M ord rd new).relClock = rd.relClock ∨
      (rmwMsg M ord rd new).relClock = (rmwMsg M ord rd new).clock ∨
      (rmwMsg M ord rd new).relClock = #[] := fun M => by
    simp only [rmwMsg]; cases ord.isRel <;> simp
  have key : ∀ M : Mem, FStepIn hF m M → M.atomics = m.atomics → M.blocks = m.blocks →
      M.footprint = m.footprint →
      ((rmwMsg M ord rd new).clock = e.clock ∨
        (rmwMsg M ord rd new).clock = VClock.merge e.clock rd.relClock) →
      FStepIn hF m (observeM (insertM M li (pos + 1) (rmwMsg M ord rd new)) li M.nextMsg) := by
    intro M hs ha hbl hfp hcl
    have hm : M.MsgCovAt li (rmwMsg M ord rd new) :=
      Mem.MsgCovAt.of_entry (hfp ▸ he) (ha ▸ heb) (ha ▸ heo) hel
        (Mem.MsgCovAt.relClock_of_mem (ha ▸ hrd)) hcl (hrel M)
    rw [hpos, ← ha]
    have hnot' : ¬ (M.atomics[li]!).In hF := by rw [ha]; exact hnot
    exact (hs.trans (FStepIn.insertLast (by rw [ha, hbl]; exact hb) hnot'
      hm)).trans (FStepIn.observe _ ((not_congr insertM_in).mpr hnot'))
  split
  · refine key _ (FStepIn.acq hc _) rfl rfl rfl (.inr ?_)
    show (m.clocks.set! m.current (VClock.merge (m.clocks[m.current]!) rd.relClock))[m.current]! =
      VClock.merge e.clock rd.relClock
    rw [Array.getElem!_set!_self _ _ _ hc, hec]
  · exact key _ (FStepIn.refl m hF) rfl rfl rfl (.inl hec.symm)

/-- **`locIdx` over bytes that are not the frame's** is a step of the thread, whichever branch
it takes: new messages of the word's location, a new location, or a mixed-size retirement and a
new location. -/
theorem FStepIn.locIdx {b o len li : Nat} {m₁ : Mem} (hlen : 0 < len)
    (hoff : ∀ x, o ≤ x → x < o + len → hF (b, x) = none)
    (hin : ∃ blk, m.blocks[b]? = some blk ∧ o + len ≤ blk.bytes.size)
    (h : ((Zig.locIdx b o len).run m).run = some (.ok (li, m₁))) : FStepIn hF m m₁ := by
  -- a new location of the word: in its block, its first message from the plain writes
  have hnew : ∀ (M : Mem) (bs : Array Byte) (id : Nat), M.blocks = m.blocks →
      (∀ e ∈ m.footprint, e ∈ M.footprint) →
      ALoc.NewCov M
        { block := b, off := o, len := len,
          msgs := #[{ id := id, bytes := bs, clock := plainClock m b o len, relClock := #[] }] } := by
    intro M bs id hbl hfp F _ _
    refine ⟨by obtain ⟨blk, h1, h2⟩ := hin; exact ⟨blk, hbl ▸ h1, h2⟩, fun msg hm => ?_⟩
    simp only [List.mem_toArray, List.mem_singleton] at hm
    subst hm
    exact ⟨ALoc.CovBy.plainClock fun e he => Mem.mem_withFp (hfp e he), ALoc.CovBy.empty⟩
  have hret : ∀ {li : Nat} {m₁ : Mem}, ((retireAt b o len).run m).run = some (.ok (li, m₁)) →
      FStepIn hF m m₁ := by
    intro li m₁ h
    unfold retireAt at h
    obtain ⟨_, _, hg, h1⟩ := MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    dsimp only at h1
    split at h1
    · exact (MemM.throw_ok h1).elim
    · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
      exact (FStepIn.retire hoff).trans
        (FStepIn.pushLoc hlen hoff (hnew _ _ _ rfl fun _ he => he))
  -- the word's location (at `(b, o)`, of `len` bytes) is not in the frame
  have hnot : ∀ i, m.atomics.findIdx? (fun l => l.block == b && l.off == o) = some i →
      (m.atomics[i]!).len = len → ¬ (m.atomics[i]!).In hF := by
    intro i hi hl hin
    obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [getElem!_pos m.atomics i hlt] at hl hin
    have := hin o (by rw [hp.2]; exact Nat.le_refl _) (by rw [hp.2, hl]; omega)
    have h' : hF (b, o) ≠ none := by simpa [hp.1] using this
    exact h' (hoff o (Nat.le_refl _) (by omega))
  unfold Zig.locIdx at h
  obtain ⟨a₀, m₀, hg, h1⟩ := MemM.bind_ok h
  obtain ⟨ha, hm₀⟩ := MemM.get_ok hg
  subst a₀; subst m₀
  dsimp only at h1
  split at h1
  · rename_i i hi
    split at h1
    · exact hret h1
    · rename_i hne
      have hl : (m.atomics[i]!).len = len := by simpa using hne
      obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have hmem : m.atomics[i]! ∈ m.atomics := by
        rw [getElem!_pos m.atomics i hlt]; exact Array.getElem_mem hlt
      have hbo : (m.atomics[i]!).block = b ∧ (m.atomics[i]!).off = o := by
        rw [getElem!_pos m.atomics i hlt]; exact hp
      -- the old messages are covered, and so is a message of the plain writes
      have hold : ∀ F, (m.withFp F).MsgCov → 0 < (m.atomics[i]!).len →
          ∀ x ∈ (m.atomics[i]!).msgs, (m.atomics[i]!).CovBy (m.withFp F) x.clock ∧
            (m.atomics[i]!).CovBy (m.withFp F) x.relClock := fun F h hpos x hx =>
        (h _ hmem hpos).2 x hx
      have hplain : ∀ F, (m.atomics[i]!).CovBy (m.withFp F) (plainClock m b o len) := fun F => by
        have := ALoc.CovBy.plainClock (l := m.atomics[i]!) (m := m.withFp F) (m₀ := m)
          fun e he => Mem.mem_withFp he
        rwa [hbo.1, hbo.2, hl] at this
      split at h1
      · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
        have := MemM.set_ok hs
        subst this
        obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
        exact FStepIn.setLoc (Nat.le_refl _) (hnot _ hi hl) hold
      · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
        have := MemM.set_ok hs
        subst this
        obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
        refine FStepIn.setLoc (Nat.le_succ _) (hnot _ hi hl) fun F h hpos x hx => ?_
        rcases Array.mem_push.mp hx with hx | rfl
        · exact hold F h hpos x hx
        · exact ⟨hplain F, ALoc.CovBy.empty⟩
  · split at h1
    · exact hret h1
    · obtain ⟨_, _, hs, h2⟩ := MemM.bind_ok h1
      have := MemM.set_ok hs
      subst this
      obtain ⟨rfl, rfl⟩ := MemM.pure_ok h2
      exact FStepIn.pushLoc hlen hoff (hnew _ _ _ rfl fun _ he => he)

end AtomicStep

end Zig
