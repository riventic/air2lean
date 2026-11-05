import ZigLean.Sep.Full.LockRules

/-!
# A lock order: a holder asleep at an inner lock

A lock `A` whose holder may go to the futex wait of another object names those futexes in its
nest (`LockWord.nest`; a lock without one has none). At the word, the holder is then at
`holdsAway` (`WInv.nap`), may sleep at a nest futex (`WInv.waitNest`), and is at `holds` again
after it (`WInv.unnap`). The protocol's one obligation for that case is `FLock.Fits.holdLive`:
such a holder is not in a deadlock.

* `holdLive_none` (`Lock.lean`): a lock without a nest discharges it at once.
* `holdLive_inners`: a lock whose nest futexes are the words of inner locks `B i` of the same
  protocol discharges it from their `Fits` (a waiter of `B i` is live, `Fits.live`); `holdLive_inner`
  is the case of one inner lock. Each `B i`'s `Fits` exists before `A`'s, so the nest relation of
  locks discharged this way is acyclic: that is the lock order.
* A nest futex of another kind of object (the condition of a semaphore, as in the RwLock writer's
  wait) is discharged from that object's own liveness (`FSem.Fits.live`) and the protocol's
  reason that its waiter is served.
* `Fits.noDeadlock`, `Fits.not_ABBA`: corollaries of `holdLive`. A holder of `A` asleep at another
  futex is in no stuck state of a protocol with `A`'s `Fits`; in particular the AB/BA state of two
  threads is not in its invariant. They hold for any discharge of `holdLive`; the acyclicity is
  the discharge's (`holdLive_inners`), not theirs. `LockWord.WInv.held_notQ_off` rules out the
  second thread's sleep at `A` while it holds `B` when `A` is not in `B`'s nest.
-/

namespace Zig
namespace Full

open Conc Proto LockWord

namespace FLock

variable {γ : Type} {Tgt : Type} {P : Proto Tgt γ}

/-- **The lock order's discharge**: if every futex of `A`'s nest is the word of one of the locks
`B i` that fit the same protocol, a holder of `A` asleep at a nest futex sleeps at some `B i`'s,
as its waiter, and that waiter is live (`B i`'s `Fits.live`). -/
theorem holdLive_inners {ι : Type} {A : FLock γ} {B : ι → FLock γ} {K : ι → FPrim γ}
    {U : ι → (ThreadId → γ) → Res → Mem → Prop} {ok : ι → γ → Prop}
    (hB : ∀ i, (B i).Fits (K i) P (U i) (ok i)) (hnest : ∀ p, A.nest p → ∃ i, p = (B i).ptr)
    {UA : (ThreadId → γ) → Res → Mem → Prop}
    (hinv : ∀ G rX m, A.Inv G rX m → UA G rX m → P.inv G m) :
    ∀ G rX m v, A.Inv G rX m → UA G rX m → A.ph (G v) = .holdsAway → P.Live v G m := by
  intro G rX m v hi hU hv hq hall
  obtain ⟨p, hpm, -, hpn⟩ := hi.w.nestQ hv hq
  obtain ⟨i, rfl⟩ := hnest p hpn
  obtain ⟨rY, hiB, hUB⟩ := ((hB i).inv G m).mp (hinv G rX m hi hU)
  have hw : (B i).ph (G v) = .wait := by
    rcases hiB.w.fq _ hpm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd rfl h
    · exact absurd rfl h
  exact (hB i).live hiB hUB hw hq hall

/-- **The lock order's discharge for one inner lock** `B` (`holdLive_inners`). -/
theorem holdLive_inner {A B : FLock γ} {K : FPrim γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (hB : B.Fits K P U ok) (hnest : ∀ p, A.nest p → p = B.ptr)
    {UA : (ThreadId → γ) → Res → Mem → Prop}
    (hinv : ∀ G rX m, A.Inv G rX m → UA G rX m → P.inv G m) :
    ∀ G rX m v, A.Inv G rX m → UA G rX m → A.ph (G v) = .holdsAway → P.Live v G m :=
  holdLive_inners (ι := Unit) (fun _ => hB) (fun p h => ⟨(), hnest p h⟩) hinv

/-- **No deadlock at a nested lock**: in a protocol with `A`'s `Fits`, a holder of `A` that sleeps
at another object's futex is not in a state where every thread has ended, sleeps or waits at a
join. -/
theorem Fits.noDeadlock {A : FLock γ} {K : FPrim γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (hA : A.Fits K P U ok) {G : ThreadId → γ} {m : Mem} {v : ThreadId}
    (hi : P.inv G m) (hv : A.ph (G v) = .holdsAway) (hq : m.waiters.any (·.1 == v) = true)
    (hall : ∀ u < m.threads.size, P.fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ P.joins (G u)) :
    False := by
  obtain ⟨rX, hiA, hU⟩ := (hA.inv G m).mp hi
  exact hA.holdLive G rX m v hiA hU hv hq hall

/-- **The AB/BA state is not in the invariant** (`Fits.noDeadlock` for two threads): thread `0`
holds `A` and sleeps at a futex `b` (another lock `B`'s word) while thread `1` sleeps at `A`'s.
No protocol with `A`'s `Fits` has this state in its invariant, whatever `b` is. -/
theorem Fits.not_ABBA {A : FLock γ} {K : FPrim γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (hA : A.Fits K P U ok) {G : ThreadId → γ} {m : Mem} {b : Ptr}
    (hsz : m.threads.size = 2) (h0 : A.ph (G 0) = .holdsAway)
    (hq0 : (0, b) ∈ m.waiters) (hq1 : (1, A.ptr) ∈ m.waiters) : ¬ P.inv G m := fun hi => by
  have hq : ∀ u p, (u, p) ∈ m.waiters → m.waiters.any (·.1 == u) = true := fun u p h =>
    Array.any_eq_true'.mpr ⟨_, h, by simp⟩
  refine hA.noDeadlock hi h0 (hq _ _ hq0) fun u hu => .inr (.inl ?_)
  rw [hsz] at hu
  match u, hu with
  | 0, _ => exact hq _ _ hq0
  | 1, _ => exact hq _ _ hq1

end FLock

end Full
end Zig
