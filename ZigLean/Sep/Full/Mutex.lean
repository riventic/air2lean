import ZigLean.Sep.Full.LockRules

/-!
# The mutex contract, over full-state resources

What a client of a mutex may assume, for every implementation proved against it (CLAUDE.md "Build
generic, prove individual items against it"): `MutexImpl Tgt` is a mutex's code in a program's
generated code (its `lock` and `unlock`, translated from the std code of the Zig version and
target) with the two rules that a client uses:

- `lock_wp`: a thread out of the lock's code that runs `lock` holds the lock afterwards, with a
  resource `rL` in its part (`FLock.Inv.res`: `rL` has the lock's resource `R`);
- `unlock_wp`: the holder that runs `unlock` is out of the lock's code afterwards; the resource is
  back in the protocol's rest.

Both hold for **every protocol that has the lock** (`FLock.FitsOn`): its invariant is
`FLock.Inv` and a rest `U` that every step of the lock's code (`LockWord.Step`, a futex-word lock's
step: only the word's bytes, atomic accesses to them, the futex queue) keeps. The places of a
thread inside the lock's code (`spin`, `wait`, `wake`) are the implementation's; a client sees
`out` and `holds` (and `gone`, `away`), and the protocol's `U` must be stable under every lock step,
so a client proof holds for each implementation of the family. A client takes the implementation
of its program (`Proofs/Sync/Lock.lean`: `Io.Mutex` of 0.16.0; `Proofs/Threadsync/Lock.lean`:
`Thread.Mutex` of 0.15.2) and uses only these two rules.
-/

namespace Zig
namespace Full

open Conc Proto

/-- A mutex implementation in generated code with the contended value `c` (module doc). -/
structure MutexImpl (Tgt : Type) where
  /-- `lock(p, io)`. -/
  lock : Ptr → Io → ConcM Tgt Unit
  /-- `unlock(p, io)`. -/
  unlock : Ptr → Io → ConcM Tgt Unit
  /-- The word's value while a thread can wait (`LockWord.c`). -/
  c : Nat
  lock_wp : ∀ {γ : Type} {L : FLock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop}, L.FitsOn P U ok → ∀ {p : Ptr}, p = L.ptr → L.c = c →
    ∀ (t : ThreadId) (g : γ), L.ph g = .out → ok g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat), P.inv (upd G t g) m →
    P.WP t (lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d
  unlock_wp : ∀ {γ : Type} {L : FLock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop}, L.FitsOn P U ok → ∀ {p : Ptr}, p = L.ptr → L.c = c →
    ∀ (t : ThreadId) (g : γ), L.ph g = .holds → ok g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat), P.inv (upd G t g) m →
    P.WP t (unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d

end Full
end Zig
