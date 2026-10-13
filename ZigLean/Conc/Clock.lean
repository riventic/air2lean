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

A zero-length access counts as its first byte (`FootprintEntry.Touches`). The race check
ignores it (it touches no byte, `raceAt`), so this only asks more of an owner than needed.
-/

namespace Zig

/-- The footprint entry `e` accesses a byte that `h` has (a zero-length entry: its first byte,
conservatively). -/
def FootprintEntry.Touches (e : FootprintEntry) (h : Heap) : Prop :=
  ∃ x, e.off ≤ x ∧ (x < e.off + e.len ∨ x = e.off) ∧ h (e.block, x) ≠ none

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
    (hlen : 0 < len) (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none) :
    NoRace m b off len kind := by
  apply noRace_of_raceAt
  unfold raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hb, -⟩, -⟩, h1⟩, h2⟩, hcon⟩ := hc
    subst hb
    have ht : e.Touches h := by
      by_cases ho' : e.off ≤ off
      · exact ⟨off, ho', by omega, hin off (Nat.le_refl _) (by omega)⟩
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
    (hnt : ∀ x, off ≤ x → (x < off + len ∨ x = off) → hF (b, x) = none)
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
    (hlen : 0 < len) (hin : ∀ x, off ≤ x → x < off + len → h (b, x) ≠ none)
    (hb : b < m.blocks.size) : StepIn hF m (m.recordAt b off len kind) :=
  StepIn.recordAt_of hc (fun x h1 h2 => (hd (b, x)).resolve_left (hin x h1 (by omega))) hb

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

end Zig
