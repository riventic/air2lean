import ZigLean.Sep.Full.LockRules

/-!
# The mutex contract, over full-state resources

What a client of a mutex may assume, for every implementation proved against it (CLAUDE.md "Build
generic, prove individual items against it"): `MutexImpl Tgt` is a mutex's code in a program's
generated code (its `lock` and `unlock`, translated from the std code of the Zig version and
target) with the two rules that a client uses:

- `lock_wp`: a thread out of the lock's code, at an entry place of the primitive next to the lock
  (`FPrim.enter`: where the client's code calls `lock`), that runs `lock` holds the lock
  afterwards, with a resource `rL` in its part (`FLock.Inv.res`: `rL` has the lock's resource `R`);
- `unlock_wp`: the holder that runs `unlock` is out of the lock's code afterwards; the resource is
  back in the protocol's rest. The holder is the running thread (`m.current = t`): an unlock
  from a thread that does not hold the mutex is illegal in Zig, and `Thread.Mutex`'s `unlock`
  checks it (`Thread.mutexOwnerCheck`, which reads the current thread). So the premise is the
  contract of every Zig mutex, not a restriction of this one.

Both hold for **every protocol that has the lock** (`FLock.Fits`, with any primitive `K` next to
the lock) and counts no turns
(`P.cost = none`, as `Proofs/Sync`'s `MutexContract`: a futex wait has no turn charge): its invariant is
`FLock.Inv` and a rest `U` that every step of the lock's code (`LockWord.Step`, a futex-word lock's
step: only the word's bytes, atomic accesses to them, the futex queue) keeps. The places of a
thread inside the lock's code (`spin`, `wait`, `wake`) are the implementation's; a client sees
`out` and `holds` (and `gone`, `away`, `holdsAway`), and the protocol's `U` must be stable under
every lock step of a thread in the lock's code along the code's place transitions (`LPh.next`,
entering from `out` at the primitive's entry places: `FLock.Fits.stable`),
so a client proof holds for each implementation of the family. A client takes the implementation
of its program (`Io.Mutex` of 0.16.0: `IoMutexCode.impl`, `ZigLean/Sep/Full/IoMutex.lean`, once for
every program, instantiated by `Proofs/Iogroup/Lock.lean` and `Proofs/Sync/IoMutex.lean`;
`Thread.Mutex` of 0.15.2: `Proofs/Threadsync/ThreadMutex.lean`) and uses only these two rules.

The primary resource contract exposes the actual caller-resource pre/post assertions. Each
implementation proves payment only at its actual tick sites: an unticked native operation
needs none, while an unbounded emitted retry needs a real invariant that supplies each tick.
Every implementation admits a caller part with a positive unmetered fragment and returns it
exactly (`lock_unmetered_pre`, `lock_unmetered_post`), so `lock_wp` is the exact-part rule for
such a caller; a Plain part has one (`Res.Plain.unmetered`). Counting no turns provides no
resource mode, and this interface claims no numerical tick or retry bound.
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
  /-- The caller part that admits `lock` in this implementation's actual code
  (`LockRules`, "Caller parts of composite operations"). -/
  lock_pre : ThreadId → FAssn
  /-- The caller part `lock` returns, from the one it was called with. -/
  lock_post : ThreadId → Res → FAssn
  /-- A caller part with a positive unmetered fragment admits `lock` (the minimal resource of
  an emitted retry loop that ticks). -/
  lock_unmetered_pre : ∀ (t : ThreadId) (r : Res), 0 < r.gh.ac.frag .unmetered → lock_pre t r
  /-- `lock` returns such a caller part exactly. -/
  lock_unmetered_post : ∀ (t : ThreadId) (r r' : Res), 0 < r.gh.ac.frag .unmetered →
    lock_post t r r' → r' = r
  lock_wp_resource : ∀ {γ : Type} {L : FLock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} {K : FPrim γ}, L.Fits K P U ok → P.cost = none → ∀ {p : Ptr}, p = L.ptr → L.c = c →
    ∀ (t : ThreadId) (g : γ), L.ph g = .out → ok g → K.enter (K.pl.ph g) → lock_pre t (L.part g) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat), P.inv (upd G t g) m →
    P.WP t (lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r rL, lock_post t (L.part g) r ∧
        P.inv (upd G' t (L.set (L.setPart g r) .holds rL)) m') G m d
  unlock_wp : ∀ {γ : Type} {L : FLock γ} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} {K : FPrim γ}, L.Fits K P U ok → P.cost = none → ∀ {p : Ptr}, p = L.ptr → L.c = c →
    ∀ (t : ThreadId) (g : γ), L.ph g = .holds → ok g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d

namespace MutexImpl

/-- The exact-part rule for a caller part with a positive unmetered fragment, derived from the
implementation's actual resource contract and its verified compatibility entailments. -/
theorem lock_wp (C : MutexImpl Tgt) {γ : Type} {L : FLock γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {K : FPrim γ}
    (hP : L.Fits K P U ok) (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr)
    (hS : L.c = C.c) (t : ThreadId) (g : γ) (hg : L.ph g = .out) (hok : ok g)
    (hen : K.enter (K.pl.ph g))
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (C.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  refine WP.mono ?_ (C.lock_wp_resource hP hcost hp hS t g hg hok hen
    (C.lock_unmetered_pre t (L.part g) hu) io G m d hi)
  rintro _ G' m' d' ⟨hd, hc, r, rL, hr, hi'⟩
  have he := C.lock_unmetered_post t (L.part g) r hu hr
  subst r
  exact ⟨hd, hc, rL, by simpa only [L.setPart_self] using hi'⟩

/-- **The holder's `unlock`** by the mutex's contract, back to its ghost value `g` out of the
mutex's code with no held resource. -/
theorem unlock_wp_to (mi : MutexImpl Tgt) {γ : Type} {L : FLock γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop} {K : FPrim γ}
    (hF : L.Fits K P U ok)
    (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr) (hLc : L.c = mi.c) (t : ThreadId) (g : γ)
    (rh : Res) (hgo : L.ph g = .out) (hgh : L.held g = rnil) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t (L.set g .holds rh)) m)
    (hc : m.current = t) :
    P.WP t (mi.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧ P.inv (upd G' t g) m')
      G m d := by
  have hg : L.set (L.set g .holds rh) .out rnil = g := by
    rw [L.set_set, ← hgo, ← hgh, L.set_self]
  refine WP.mono (fun _ G' m' d' ⟨hd, hc', hi'⟩ => ⟨hd, hc', ?_⟩)
    (mi.unlock_wp hF hcost hp hLc t _ (L.ph_set _ _ _) ((hF.ok_set _ _ _).mpr hok) io G m d hi hc)
  rwa [hg] at hi'

end MutexImpl

end Full
end Zig
