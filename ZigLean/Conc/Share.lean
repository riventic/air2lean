import ZigLean.Conc.LockRules
import ZigLean.Mem.Alloc
import ZigLean.Simp

/-!
# Shared reads and join-before-free reclamation

A contract for a region read by several threads at once and then reclaimed by one thread.
The region is a set `R` of footprint entries (for example, the entries of block `b` below
offset `n`). The contract is a predicate on the memory of the existing model
(`ZigLean/Mem/Basic.lean`'s footprint and vector clocks). It adds no new semantics.

- **Read shares** (`ReadShared R m`). Each access in the region is a read that happened before
  some thread (its read share), or happened before every thread (the writes before the region
  was shared). Any number of threads can hold a share at once: a read by any thread does not race
  (`ReadShared.noRace_read`), and it keeps the contract (`ReadShared.read`).
- **Split.** The region is shared once each access happened before every thread
  (`ReadShared.ofAllLe`). A spawn gives the child a share: its clock is above its spawner's
  (`ReadShared.fork`). A step that does not access the region keeps every share
  (`ReadShared.keep`).
- **Join.** A share ends when its thread is joined: the join merges the reader's clock into the
  joiner's. Once every thread's clock is below the clock of `t`, all shares are back, and `t`
  owns the region alone (`ReadShared.reclaim`, `RegionOwned`).
- **Reclamation.** A write over the region, such as `std`'s poison write before `free`, needs full
  ownership. With it, no access of any kind races (`RegionOwned.noRace`). If a read share is
  outstanding (a read in the region that did not happen before the thread), the write races
  (`outstanding_races`), and freeing a heap region throws `.illegal` (`poisonFree_outstanding`).
  A read after the free throws `.illegal`: the block is dead (`access_freed`). So
  freeing with a share outstanding is rejected in either order.

Model-level runtime negative tests for the stack early-free and heap free contracts are in
`tests/roadmap/shared-reclamation/`. A stack `free` records no access. Its shares are covered
by the all-schedules client proof (`Proofs/Iogroup/Counter.lean`'s `groupCounter_reclaim`), which
shows that every access to the shared `io` region happened before `main` when it frees the block.
-/

namespace Zig
namespace Conc

open Proto

/-- The region `R` is read-shared (module doc): each access in it is a read that happened before
some thread, or happened before every thread. -/
def ReadShared (R : FootprintEntry → Prop) (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, R e → (e.kind = .read ∧ SomeLe m e.clock) ∨ AllLe m e.clock

/-- The clock `c` owns the region `R` alone: every access in it happened before `c`. -/
def RegionOwned (R : FootprintEntry → Prop) (m : Mem) (c : VClock) : Prop :=
  ∀ e ∈ m.footprint, R e → VClock.le e.clock c = true

/-- `R` covers the bytes `[o, o + len)` of block `b`: every entry that overlaps them is in `R`. -/
def Covers (R : FootprintEntry → Prop) (b o len : Nat) : Prop :=
  ∀ e : FootprintEntry, e.block = b → o < e.off + e.len → e.off < o + len → R e

variable {R : FootprintEntry → Prop} {m m' : Mem}

namespace ReadShared

/-- Share out: once each access in the region happened before every thread, the region is
shared. -/
theorem ofAllLe (h : ∀ e ∈ m.footprint, R e → AllLe m e.clock) : ReadShared R m :=
  fun e he hr => .inr (h e he hr)

/-- A read of a covered range by any thread does not race. -/
theorem noRace_read (hs : ReadShared R m) (ht : m.current < m.threads.size) {b o len : Nat}
    (hc : Covers R b o len) : NoRace m b o len .read :=
  noRace_of fun e he hb h1 h2 => by
    rcases hs e he (hc e hb h1 h2) with ⟨hk, -⟩ | h
    · exact .inr (by rw [hk]; rfl)
    · exact .inl (h _ ht)

/-- A read by a thread keeps the contract: the reader holds a share of its own read. -/
theorem read (hs : ReadShared R m) (ht : m.current < m.threads.size)
    (hcs : m.clocks.size = m.threads.size) (b o len : Nat) :
    ReadShared R (m.recordAt b o len .read) := by
  intro e he hr
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · rcases hs e he hr with ⟨hk, u, hu, hle⟩ | h
    · exact .inl ⟨hk, u, hu, VClock.le_trans hle (Lock.recordAt_le m b o len .read u)⟩
    · exact .inr fun u hu => VClock.le_trans (h u hu) (Lock.recordAt_le m b o len .read u)
  · refine .inl ⟨rfl, m.current, ht, ?_⟩
    rw [recordAt_clock (hcs ▸ ht)]
    exact VClock.le_refl _

/-- A step that keeps the number of threads, makes no clock smaller and adds no access in the
region keeps every share. A join is such a step: it marks the joined thread and grows the
joiner's clock. -/
theorem keep (hs : ReadShared R m) (ht : m'.threads.size = m.threads.size)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, R e → e ∈ m.footprint) : ReadShared R m' := by
  intro e he hr
  rcases hs e (hfp e he hr) hr with ⟨hk, u, hu, hle⟩ | h
  · exact .inl ⟨hk, u, by omega, VClock.le_trans hle (hcl u hu)⟩
  · exact .inr fun u hu => VClock.le_trans (h u (by omega)) (hcl u (by omega))

/-- A spawn: the new thread `m.threads.size`, whose clock is above its spawner `t`'s, holds a
share too. -/
theorem fork (hs : ReadShared R m) {t : ThreadId} (htl : t < m.threads.size)
    (hsz : m'.threads.size = m.threads.size + 1)
    (hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hnew : VClock.le (m.clocks[t]!) (m'.clocks[m.threads.size]!) = true)
    (hfp : ∀ e ∈ m'.footprint, R e → e ∈ m.footprint) : ReadShared R m' := by
  intro e he hr
  rcases hs e (hfp e he hr) hr with ⟨hk, u, hu, hle⟩ | h
  · exact .inl ⟨hk, u, by omega, VClock.le_trans hle (hcl u hu)⟩
  · refine .inr fun u hu => ?_
    by_cases hu' : u < m.threads.size
    · exact VClock.le_trans (h u hu') (hcl u hu')
    · have : u = m.threads.size := by omega
      subst this
      exact VClock.le_trans (h t htl) hnew

/-- **Join before free.** Once every thread's clock is below `t`'s (every reader was joined), all
read shares are back: `t` owns the region alone. -/
theorem reclaim (hs : ReadShared R m) {t : ThreadId} (ht : t < m.threads.size)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true) :
    RegionOwned R m (m.clocks[t]!) := fun e he hr => by
  rcases hs e he hr with ⟨-, u, hu, hle⟩ | h
  · exact VClock.le_trans hle (hall u hu)
  · exact h t ht

end ReadShared

namespace RegionOwned

theorem mono {c c' : VClock} (ho : RegionOwned R m c) (hle : VClock.le c c' = true) :
    RegionOwned R m c' := fun e he hr => VClock.le_trans (ho e he hr) hle

/-- Exclusive ownership of the region's heap (`Mem.OwnsC`) is full ownership of the region. -/
theorem of_ownsC {c : VClock} {h : Heap} (ho : m.OwnsC c h) (hR : ∀ e, R e → e.Touches h) :
    RegionOwned R m c := fun e he hr => ho e he (.inl (hR e hr))

/-- The owner's own access keeps its ownership. -/
theorem recordAt {t : ThreadId} (ho : RegionOwned R m (m.clocks[t]!)) (hc : m.current = t)
    (ht : t < m.clocks.size) (b o len : Nat) (k : AccessKind) :
    RegionOwned R (m.recordAt b o len k) ((m.recordAt b o len k).clocks[t]!) := by
  subst hc
  intro e he hr
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact VClock.le_trans (ho e he hr) (Lock.recordAt_le m b o len k m.current)
  · rw [recordAt_clock ht]
    exact VClock.le_refl _

/-- Full ownership: no access of any kind to a covered range races, including a write, such as
`std`'s poison write before `free`. -/
theorem noRace (ho : RegionOwned R m (m.clocks[m.current]!)) {b o len : Nat}
    (hc : Covers R b o len) (k : AccessKind) : NoRace m b o len k :=
  noRace_of fun e he hb h1 h2 => .inl (ho e he (hc e hb h1 h2))

end RegionOwned

/-! ## Freeing with a share outstanding -/

/-- The race check reports only `.illegal`. -/
theorem raceAt_illegal {fp : Array FootprintEntry} {c : VClock} {b o len : Nat} {k : AccessKind}
    {err : Error} (h : raceAt fp c b o len k = some err) : err = .illegal := by
  obtain ⟨e, -, he⟩ := Array.exists_of_findSome?_eq_some h
  split at he
  · unfold racePair at he
    split at he
    · cases he; rfl
    · cases he
  · cases he

/-- The race check of `recordAccess` reports only `.illegal`. -/
theorem raceCheck_illegal {m : Mem} {c : VClock} {b o len : Nat} {k : AccessKind}
    {err : Error} (h : raceCheck m c b o len k = some err) : err = .illegal := by
  unfold raceCheck at h
  split at h
  · cases h
  · exact raceAt_illegal h

/-- An outstanding read share: a read that overlaps the bytes and did not happen before the
current thread. A write over it races. -/
theorem outstanding_races {e : FootprintEntry} (he : e ∈ m.footprint) (hk : e.kind = .read)
    {b o len : Nat} (hb : e.block = b) (h1 : o < e.off + e.len) (h2 : e.off < o + len)
    (hc : VClock.concurrent e.clock (VClock.bump (m.clocks[m.current]!) m.current) = true)
    (hs : m.solo = false) : ¬ NoRace m b o len .write :=
  race_of (err := .illegal) he hb h1 h2 hc (by rw [hk]; rfl) hs

/-- `std`'s `free` of a heap region (poison write, then `rawFree`) with a racing access, such as
an outstanding read share (`outstanding_races`), throws `.illegal`. -/
theorem poisonFree_outstanding {p : Ptr} {n b o : Nat} {blk : Block}
    (ha : m.access p n 1 = pure (b, blk, o)) (hk : blk.kind = .heap ∧ o = 0 ∧ blk.bytes.size = n)
    (hnr : ¬ NoRace m b o n .write) :
    ((poisonFree p n).run m).run = some (.error .illegal) := by
  unfold NoRace at hnr
  obtain ⟨err, herr⟩ := Option.ne_none_iff_exists'.mp hnr
  obtain rfl := raceCheck_illegal herr
  obtain ⟨hk1, rfl, hk3⟩ := hk
  simp [poisonFree, recordAccess, zig_unfold, ha, hk1, hk3, herr, ExceptT.bindCont, StateT.lift, ExceptT.run]

/-- An access to a dead block throws `.illegal`. -/
theorem access_dead {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = false) (off : Int) (n a : Nat) :
    m.access ⟨some b, off⟩ n a = throw .illegal := by
  unfold Mem.access
  simp [hb, hl]

/-- **No use after free.** After `free` of block `b`, every access to it throws `.illegal`: a
read share that is still outstanding cannot read the region. -/
theorem access_freed {b : BlockId} {x : Unit} (h : ((free ⟨some b, 0⟩).run m).run = some (.ok (x, m')))
    (off : Int) (n a : Nat) : m'.access ⟨some b, off⟩ n a = throw .illegal := by
  obtain ⟨b', blk, hb', hblk, rfl⟩ := free_ok h
  cases hb'
  refine access_dead (blk := { blk with live := false }) ?_ rfl off n a
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
    (Array.getElem?_eq_some_iff.mp hblk).1]

end Conc
end Zig
