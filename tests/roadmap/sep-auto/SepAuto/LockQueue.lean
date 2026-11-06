import ZigLean.Sep.Full.LockWord

/-!
# A lock step queues only its own thread (`LockWord.Step.newQ`)

Two locks `A` and `B` at different words. A step of `B`'s code by thread `t` that puts another
thread `u` in the futex queue at `B`'s word:

- meets every field of `LockWord.Step` but `newQ` (`queue_other_admitted`: with `newQ` given, the
  rest is `Step.same`). Without `newQ`, `Step` constrained only the entries at the other futexes
  (`Step.waiters`), which this step keeps;
- leaves `A`'s invariant false whenever `u` is at `A`'s place `out` (`queue_other_breaks`): `A`'s
  `Queue` places a thread queued at another futex at `away` or `holdsAway`. So the two-lock
  product's lemma "a step of `B` keeps `A`'s invariant" needs `newQ`;
- is a `Step` exactly when it queues `t` itself or an entry already queued (`queue_step_iff`):
  `newQ` rejects it for a new `u ≠ t`, and is the only field that does.

`newQ` is necessary for the product, not sufficient: `B`'s own futex wait by `t` queues `t` at
`B`'s word, which `A`'s `Queue` admits only with `t` at `A`'s `away` (or `holdsAway` at a futex of
`A`'s nest). `newQ` is a membership fact: a duplicate of an entry already queued passes it, which
the membership-based `Queue` does not see.

Every producer of `Step` in `LockWord.lean` meets `newQ`: the futex wait pushes only its caller
(`newQ_push`, `WInv.wait`), the wake only removes entries and the other steps keep the queue
(`newQ_of_sub`). A step that queues the stepping thread itself stays a `Step` (`queue_self`).
-/

open Zig Zig.Conc Zig.Full

namespace SepAuto.LockQueue

/-- `B`'s step that queues `u` at `B`'s word. -/
def queued (B : LockWord) (u : ThreadId) (m : Mem) : Mem :=
  { m with waiters := m.waiters.push (u, B.key m) }

/-- **The step meets every field of `Step` but `newQ`**: given `newQ`, it is a `Step`
(`Step.same`: threads, clocks, blocks, footprint, locations and the other futexes' entries
stay). -/
theorem queue_other_admitted (B : LockWord) (t u : ThreadId) (m : Mem)
    (hq : ∀ w ∈ (queued B u m).waiters, w ∉ m.waiters → w.1 = t) :
    B.Step t m (queued B u m) :=
  LockWord.Step.same rfl rfl rfl rfl rfl rfl
    (by
      simp only [queued]
      rw [Array.filter_push_of_neg (p := fun x : ThreadId × FutexKey => x.2 != B.key m)
        (a := (u, B.key m)) (by simp)]
      simp)
    (hq := hq)

/-- **`A`'s invariant is false after it** when `u` is at `A`'s place `out`. -/
theorem queue_other_breaks (A B : LockWord) (P : ThreadId → LPh) (u : ThreadId) (m : Mem)
    (hp : B.key m ≠ A.key m) (hu : P u = .out) : ¬ A.WInv P (queued B u m) := fun hw => by
  rcases hw.fq (u, B.key m) (Array.mem_push.mpr (.inr rfl)) with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩
  · exact hp h
  · rw [hu] at h; cases h
  · rw [hu] at h; cases h

/-- A step that queues the stepping thread itself stays a `Step`. -/
theorem queue_self (B : LockWord) (t : ThreadId) (m : Mem) : B.Step t m (queued B t m) :=
  queue_other_admitted B t t m LockWord.newQ_push

/-- **`newQ` is the only obstruction**: the step is a `Step` exactly when it queues the stepping
thread itself or an entry already in the queue. -/
theorem queue_step_iff (B : LockWord) (t u : ThreadId) (m : Mem) :
    B.Step t m (queued B u m) ↔ u = t ∨ (u, B.key m) ∈ m.waiters := by
  constructor
  · intro hs
    by_cases hn : (u, B.key m) ∈ m.waiters
    · exact .inr hn
    · exact .inl (hs.newQ (u, B.key m) (Array.mem_push.mpr (.inr rfl)) hn)
  · rintro (rfl | h)
    · exact queue_self B _ m
    · refine queue_other_admitted B t u m (LockWord.newQ_of_sub fun w hw => ?_)
      rcases Array.mem_push.mp hw with hw | rfl
      · exact hw
      · exact h

end SepAuto.LockQueue
