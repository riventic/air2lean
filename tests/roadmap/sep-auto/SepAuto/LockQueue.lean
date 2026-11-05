import ZigLean.Sep.Full.LockWord

/-!
# A lock step queues only its own thread (`LockWord.Step.newQ`)

Two locks `A` and `B` at different words. A step of `B`'s code by thread `t` that puts another
thread `u` in the futex queue at `B`'s word:

- meets every other field of `LockWord.Step` (`queue_other_admitted`). Before `newQ`, `Step`
  constrained only the entries at the other futexes (`Step.waiters`), so `Step` admitted this step;
- breaks `A`'s invariant when `u` is at `A`'s place `out` (`queue_other_breaks`): `A`'s `Queue`
  places a thread queued at another futex at `away` or `holdsAway`. So a lemma "a step of `B`
  keeps `A`'s invariant" (the two-lock product) would be false;
- is not a `Step` (`queue_other_rejected`): `newQ` says a new entry is the stepping thread's. The
  futex wait of the lock's code queues only its caller (`WInv.wait`), so every implementation
  meets it.
-/

open Zig Zig.Conc Zig.Full

namespace SepAuto.LockQueue

/-- `B`'s step that queues `u` at `B`'s word. -/
def queued (B : LockWord) (u : ThreadId) (m : Mem) : Mem :=
  { m with waiters := m.waiters.push (u, B.ptr) }

/-- **The step meets every field of `Step` but `newQ`**: given `newQ`, the step is a `Step`
(`Step.same`: threads, clocks, blocks, footprint, locations and the other futexes' entries
stay). -/
theorem queue_other_admitted (B : LockWord) (t u : ThreadId) (m : Mem)
    (hq : ∀ w ∈ (queued B u m).waiters, w ∉ m.waiters → w.1 = t) :
    B.Step t m (queued B u m) :=
  LockWord.Step.same rfl rfl rfl rfl rfl rfl
    (by
      simp only [queued]
      rw [Array.filter_push_of_neg (p := fun x : ThreadId × Ptr => x.2 != B.ptr)
        (a := (u, B.ptr)) (by simp)]
      simp)
    (hq := hq)

/-- **`A`'s invariant fails after it** when `u` is at `A`'s place `out`. -/
theorem queue_other_breaks (A B : LockWord) (P : ThreadId → LPh) (u : ThreadId) (m : Mem)
    (hp : B.ptr ≠ A.ptr) (hu : P u = .out) : ¬ A.WInv P (queued B u m) := fun hw => by
  rcases hw.fq (u, B.ptr) (Array.mem_push.mpr (.inr rfl)) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩
  · exact hp h
  · rw [hu] at h; cases h
  · rw [hu] at h; cases h

/-- **`newQ` rejects it**: a step of `t` does not queue another thread. -/
theorem queue_other_rejected (B : LockWord) (t u : ThreadId) (m : Mem) (hut : u ≠ t)
    (hn : (u, B.ptr) ∉ m.waiters) : ¬ B.Step t m (queued B u m) := fun hs =>
  hut (hs.newQ (u, B.ptr) (Array.mem_push.mpr (.inr rfl)) hn)

/-- A step that queues the stepping thread itself stays a `Step`. -/
theorem queue_self (B : LockWord) (t : ThreadId) (m : Mem) : B.Step t m (queued B t m) :=
  queue_other_admitted B t t m fun w hw hn => by
    rcases Array.mem_push.mp hw with hw | rfl
    · exact absurd hw hn
    · rfl

end SepAuto.LockQueue
