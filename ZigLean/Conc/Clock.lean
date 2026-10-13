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
  threads' views of them move with them;
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

/-- A step that keeps the atomic locations and the views. -/
theorem of_eq (ha : m'.atomics = m.atomics) (hs : m'.seen = m.seen) : AMap hF m m' some := by
  have h := refl m hF
  exact { mono := h.mono, kept := fun i j l hi hl => by rw [ha]; exact h.kept i j l hi hl,
          frame := fun i l hl hin => by rw [ha]; exact h.frame i l hl hin,
          new := fun j l hl hn => h.new j l (ha ▸ hl) hn, seen := by rw [hs]; exact h.seen }

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

theorem weaken (h : AMap hF m m' σ) (hsub : ∀ l, hF' l ≠ none → hF l ≠ none) :
    AMap hF' m m' σ :=
  { h with
    frame := fun i l hl hin => h.frame i l hl fun x h1 h2 => hsub _ (hin x h1 h2)
    new := fun j l hl hn => ⟨(h.new j l hl hn).1, fun x h1 h2 => by
      have := (h.new j l hl hn).2 x h1 h2
      cases e : hF' (l.block, x) with
      | none => rfl
      | some _ => exact absurd this (hsub _ (by simp [e]))⟩ }

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

/-- **The first location with a property of its bytes stays the first one**, when the first one
of `m` lies in the frame and every location with the property has a byte of the frame. -/
theorem first_iff (h : AMap hF m m' σ) {p : ALoc → Bool}
    (hp : ∀ l l', l.block = l'.block → l.off = l'.off → l.len = l'.len → p l = p l')
    (hin : ∀ i l, m.atomics.findIdx? p = some i → m.atomics[i]? = some l → l.In hF)
    (hcov : ∀ l, p l = true → 0 < l.len → ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ hF (l.block, x) ≠ none)
    (l : ALoc) :
    (∃ i, m.atomics.findIdx? p = some i ∧ m.atomics[i]? = some l) ↔
      (∃ j, m'.atomics.findIdx? p = some j ∧ m'.atomics[j]? = some l) := by
  -- A location of `m'` with `p` is a kept one.
  have kept : ∀ k (hk : k < m'.atomics.size), p m'.atomics[k] = true →
      ∃ i, ∃ hi : i < m.atomics.size, σ i = some k ∧ p m.atomics[i] = true := by
    intro k hk hpk
    by_cases hx : ∃ i < m.atomics.size, σ i = some k
    · obtain ⟨i, hi, hik⟩ := hx
      obtain ⟨l', hl', hb, ho, hn⟩ := h.kept i k _ hik (Array.getElem?_eq_getElem hi)
      rw [Array.getElem?_eq_getElem hk] at hl'; cases hl'
      exact ⟨i, hi, hik, (hp _ _ hb ho hn).symm.trans hpk⟩
    · obtain ⟨hpos, hoff⟩ := h.new k _ (Array.getElem?_eq_getElem hk) fun i hi hik => hx ⟨i, hi, hik⟩
      obtain ⟨x, h1, h2, h3⟩ := hcov _ hpk hpos
      exact absurd (hoff x h1 h2) h3
  constructor
  · rintro ⟨i, hfi, hl⟩
    obtain ⟨hi, hpi, hfirst⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfi
    obtain ⟨j, hij, hl'⟩ := h.frame i l hl (hin i l hfi hl)
    have hj : j < m'.atomics.size := (Array.getElem?_eq_some_iff.mp hl').1
    refine ⟨j, Array.findIdx?_eq_some_iff_getElem.mpr ⟨hj, ?_, fun k hkj hpk => ?_⟩, hl'⟩
    · rw [Array.getElem?_eq_getElem hi] at hl
      rw [Array.getElem?_eq_getElem hj] at hl'
      rw [Option.some.inj hl', ← Option.some.inj hl]; exact hpi
    · obtain ⟨i', hi', hik, hpi'⟩ := kept k _ (by simpa using hpk)
      rcases Nat.lt_trichotomy i' i with hlt | rfl | hgt
      · exact hfirst i' hlt hpi'
      · rw [hij] at hik; cases hik; exact Nat.lt_irrefl _ hkj
      · exact Nat.lt_asymm hkj (h.mono i i' j k hij hik hgt)
  · rintro ⟨j, hfj, hl⟩
    obtain ⟨hj, hpj, hfirst⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfj
    obtain ⟨i₀, hi₀, hij₀, hpi₀⟩ := kept j hj hpj
    obtain ⟨i, hfi⟩ : ∃ i, m.atomics.findIdx? p = some i := Option.isSome_iff_exists.mp (by
      rw [Array.findIdx?_isSome, Array.any_eq_true]; exact ⟨i₀, hi₀, hpi₀⟩)
    obtain ⟨hi, hpi, hfirst'⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfi
    obtain ⟨j₁, hij₁, hl₁⟩ := h.frame i _ (Array.getElem?_eq_getElem hi)
      (hin i _ hfi (Array.getElem?_eq_getElem hi))
    have hj₁ : j₁ < m'.atomics.size := (Array.getElem?_eq_some_iff.mp hl₁).1
    have hjj : j ≤ j₁ := Nat.le_of_not_lt fun hlt => hfirst j₁ hlt (by
      rw [Option.some.inj ((Array.getElem?_eq_getElem hj₁).symm.trans hl₁)]; exact hpi)
    rcases Nat.lt_or_ge i i₀ with hlt | hge
    · exact absurd (h.mono i i₀ j₁ j hij₁ hij₀ hlt) (Nat.not_lt.mpr hjj)
    · have hii : i = i₀ := Nat.le_antisymm (Nat.le_of_not_lt fun h' => hfirst' i₀ h' hpi₀) hge
      subst hii
      rw [hij₀] at hij₁; cases hij₁
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

/-- **Forgetting the accesses past an offset** (`Mem.forgetFrom`, a revival) is a step of the
thread for every frame: it only narrows entries. -/
theorem FStepIn.forgetFrom {hF : Heap} (b' : BlockId) (S : Nat) :
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

end Retire

section FStep

variable {m m' m'' : Mem} {hF hF' : Heap}

/-- A `StepIn` that makes no `const` global and writes none is an `FStepIn`. -/
theorem FStepIn.of_stepIn (hs : StepIn hF m m')
    (hk : ∀ b, b < m.blocks.size → m'.IsConst b → m.IsConst b)
    (hw : ∀ e ∈ m'.footprint, e ∉ m.footprint → e.kind.isWrite = true → ¬ m'.IsConst e.block) :
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

theorem FStepIn.refl (m : Mem) (hF : Heap) : FStepIn hF m m :=
  .of_stepIn (StepIn.refl m hF) (fun _ _ h => h) (fun _ he hn => absurd he hn)

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
    fun b hb hc => h₁.const b hb (h₂.const b (Nat.lt_of_lt_of_le hb h₁.blocks) hc)⟩
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
        exact .inr (VClock.le_trans hn.2.2.2.2.2 (VClock.le_trans hle this))
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
  · refine VClock.le_trans hn.2.2.2.2.2 (ho e₀ he₀ ?_)
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

/-- A change of block `b` to `nb` records no access; `nb` is a `const` global only if `b` was. -/
theorem FStepIn.setBlock {b : BlockId} {nb : Block} (hk : nb.kind = .constGlobal → m.IsConst b) :
    FStepIn hF m { m with blocks := m.blocks.set! b nb } := by
  refine .of_stepIn (StepIn.setBlock m hF b nb) (fun b' hb' ⟨blk', h1, h2⟩ => ?_)
    (fun _ he hn => absurd he hn)
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
  FStepIn.setBlock fun h => ⟨blk, hb, h⟩

/-- A recorded access by the current thread that touches no byte of `hF` and writes no `const`
global. -/
theorem FStepIn.recordAt_of {b : BlockId} {off len : Nat} {kind : AccessKind}
    (hc : m.current < m.clocks.size) (hnt : ∀ x, off ≤ x → x < off + len → hF (b, x) = none)
    (hb : b < m.blocks.size) (hw : kind.isWrite = true → ¬ m.IsConst b) :
    FStepIn hF m (m.recordAt b off len kind) := by
  refine .of_stepIn (StepIn.recordAt_of hc hnt hb) (fun _ _ h => h) fun e he hn hwr => ?_
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

end FStep

end Zig
