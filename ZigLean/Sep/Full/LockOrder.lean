import ZigLean.Sep.Full.LockRules

/-!
# A lock order: a holder asleep at an inner lock

A lock `A` whose holder may go to the futex wait of another object names those futexes in its
nest (`LockWord.nest`; a lock without one has none). The holder is then at `holdsAway`
(`WInv.nap`), may sleep at a nest futex (`WInv.waitNest`), and is at `holds` again after it
(`WInv.unnap`). The protocol's one obligation for that case is `FLock.Fits.holdLive`: such a holder
is not in a deadlock.

* `holdLive_none` (`Lock.lean`): a lock without a nest discharges it at once.
* `holdLive_inner`: a lock whose nest is the futex of an inner lock `B` of the same protocol
  discharges it from `B`'s `Fits` (`B`'s waiter is live, `Fits.live`). `B`'s `Fits` exists before
  `A`'s, so the nest relation is acyclic: that is the lock order.
* `Fits.noDeadlock`, `Fits.not_ABBA`: the deadlock of two threads that take `A` then `B` and `B`
  then `A` is in no protocol's invariant with `A`'s `Fits`; and `WInv.held_notQ_off` rules out the
  second thread's sleep at `A` while it holds `B` when `A` is not in `B`'s nest.
-/

namespace Zig
namespace Full

open Conc Proto LockWord

namespace FLock

variable {γ : Type} {Tgt : Type} {P : Proto Tgt γ}

/-- **The lock order's discharge**: if `A`'s nest is the futex of a lock `B` that fits the same
protocol, a holder of `A` asleep at a nest futex sleeps at `B`'s, as `B`'s waiter, and that waiter
is live (`B`'s `Fits.live`). -/
theorem holdLive_inner {A B : FLock γ} {K : FPrim γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (hB : B.Fits K P U ok) (hnest : ∀ p, A.nest p → p = B.ptr)
    {UA : (ThreadId → γ) → Res → Mem → Prop}
    (hinv : ∀ G rX m, A.Inv G rX m → UA G rX m → P.inv G m) :
    ∀ G rX m v, A.Inv G rX m → UA G rX m → A.ph (G v) = .holdsAway → P.Live v G m := by
  intro G rX m v hi hU hv hq hall
  obtain ⟨p, hpm, -, hpn⟩ := hi.w.nestQ hv hq
  have hp := hnest p hpn; subst hp
  obtain ⟨rY, hiB, hUB⟩ := (hB.inv G m).mp (hinv G rX m hi hU)
  have hw : B.ph (G v) = .wait := by
    rcases hiB.w.fq _ hpm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd rfl h
    · exact absurd rfl h
  exact hB.live hiB hUB hw hq hall

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

/-- **The AB/BA deadlock is rejected**: two threads, `0` holds `A` and sleeps at `B`'s futex while
`1` holds `B` and sleeps at `A`'s. No protocol with `A`'s `Fits` has this state in its invariant,
whatever `B` is and whatever nests `A` and `B` name. -/
theorem Fits.not_ABBA {A B : FLock γ} {K : FPrim γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} (hA : A.Fits K P U ok) {G : ThreadId → γ} {m : Mem}
    (hsz : m.threads.size = 2) (h0 : A.ph (G 0) = .holdsAway)
    (hq0 : (0, B.ptr) ∈ m.waiters) (hq1 : (1, A.ptr) ∈ m.waiters) : ¬ P.inv G m := fun hi => by
  have hq : ∀ u p, (u, p) ∈ m.waiters → m.waiters.any (·.1 == u) = true := fun u p h =>
    Array.any_eq_true'.mpr ⟨_, h, by simp⟩
  refine hA.noDeadlock hi h0 (hq _ _ hq0) fun u hu => .inr (.inl ?_)
  rw [hsz] at hu
  match u, hu with
  | 0, _ => exact hq _ _ hq0
  | 1, _ => exact hq _ _ hq1

/-- **The lock order at the word**: a holder of `B` is never in the futex queue at an address
outside `B`'s nest (other than `B`'s word). So with `B`'s nest empty, the second thread of the
AB/BA deadlock cannot sleep at `A`'s futex while it holds `B`: no rule moves it there. -/
theorem _root_.Zig.Full.LockWord.WInv.held_notQ_off {B : LockWord} {Pl : ThreadId → LPh}
    {m : Mem} {t : ThreadId} {p : Ptr} (hi : B.WInv Pl m) (hh : (Pl t).held = true)
    (hp : p ≠ B.ptr) (hn : ¬ B.nest p) (hq : (t, p) ∈ m.waiters) : False := by
  rcases hi.fq _ hq with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
  · exact hp h
  · rw [h] at hh; cases hh
  · exact hn h

end FLock

end Full
end Zig
