import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.Mutex

/-!
# The semaphore, over full-state resources

A semaphore (`Io.Semaphore`'s `waitUncancelable` and `post`, the same code in 0.16.0 and 0.17.0,
translated from its std code; the futex under it is the model) is a permit count, a mutex and a
condition next to it: `wait` locks the mutex, waits at the condition while the count is 0, takes a
permit (`count -= 1`), signals the condition if permits are left, and unlocks; `post` locks, gives
a permit back (`count += 1`), signals and unlocks. This module is the component once for every
protocol that has such a semaphore (`FSem`, its primitive `FSem.prim` next to the mutex, the
protocol `FSem.Fits`), and the contract of a semaphore's code (`SemImpl`); an implementation of a
Zig version walks its code with the rules of its mutex and condition (`MutexImpl`, `CondImpl`).
Any number of threads may wait and post: the condition is the multi-waiter one
(`ZigLean/Sep/Full/Cond.lean`).

- **The semaphore** (`FSem γ L C`): the mutex `L` owns the count (`pv`, a function of the threads'
  ghost values) and the resource of the free permits (`Pool`): `L.R G = count ⋆ Pool G`. A
  thread's place in the semaphore's own code is `SPh`: `wt` from its `wait`'s lock to its take of
  a permit (the thread is in the semaphore's wait loop, around the condition's wait), `pst h c`
  from the store of the count to the end of its signal, holding the mutex, with the state's writes
  `h` and its clock `c` at the store (its snapshot). The condition's signallers are exactly the
  threads at `pst` (`sx_iff`): a semaphore signals while it holds the mutex.
- **The no-lost-wakeup argument.** A waiter that sleeps at the condition with no pending signal
  and no signaller in the condition's code (`CondImpl.wait_wp`'s `hlive`) is not deadlocked if
  the count is not 0: then a thread at `pst` (it holds the mutex and will signal) or a *taker*
  (`Tk`: at `wt`, out of the condition's code: a waiter that took a signal and relocks the mutex
  to take a permit) runs (`Inv.live`, `Fits.live`). Without takers the claim is false: two
  waiters asleep, a post wakes one, which takes the signal; now the count is 1, no signal is
  pending, nobody is at `pst`, and only the woken waiter, on its way back to the mutex, will take
  the permit. The count of the client's own sleep at count 0 is the client's (`SemImpl`'s
  `hlive`).
- **The invariant** (`FSem.Inv`), next to the condition's (`FCond.Inv`): a thread at `pst` holds
  the mutex; a thread in the condition's critical code saw the count 0; a waiter at the condition
  is at `wt`; a taker sleeps only at the mutex's futex; every state write keeps `waiters` and does
  not lower `signals` (`FCond.SUp`, a post), happened before the mutex's holder, its newest release
  or every thread that has not ended (`FLock.HB`: registrations and posts, made holding the
  mutex), or before a taker (its consume); for a thread at `pst h c`, every write of `h` is a post,
  happened before `c` or there is a taker, and every later write is a post or there is a taker;
  and the no-lost-wakeup fact above. It holds at a fresh semaphore (`Inv.start`), and a client's
  protocol keeps it over the lock's steps out of `pst` (`Inv.lstep`) and over ticks
  (`Inv.partTick`).
- **The end of `pst`.** After its signal (`CondImpl.signal_wp`'s history post `FCond.SigPost`: a
  write `k` at or after every write that happened before the call is served or a post), every
  later write is a post (or there is a taker), so with a registered waiter a signal is pending
  (`Inv.afterSig`): the thread leaves `pst` keeping the invariant (`Go`).
- **The primitive** (`FSem.prim`): the condition's places with the semaphore's, the condition's
  steps (`FCond.prim`) and the semaphore's own steps (`Move`: the waiter's entry into the
  condition at count 0; the holder's step on the mutex's resource, a load or store of the count,
  with its move in the semaphore's code, `Go`), each with both invariants after it. A protocol
  with the semaphore is `S.Fits P U ok`: `FLock.Fits` with the semaphore as its primitive, its
  `ok` out of `pst`, and the condition's window (`Fits.win`, PR397 ruling 6264821278, maintainer
  decision 6625654179: the protocol's obligation). It has the condition (`Fits.toC`), so the
  condition's contract applies to it.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- Where a thread is in the semaphore's own code (module doc). -/
inductive SPh where
  | out
  | wt
  | pst (h : Array Word.Entry) (c : VClock)

namespace SPh

/-- At `pst`. -/
def isPst : SPh → Bool
  | .pst _ _ => true
  | _ => false

end SPh

/-- **A semaphore** next to the mutex `L` and the condition `C` (module doc): its place, its
pointer `p` (the count at `p`, the mutex at `p + 8`, the condition at `p + 12`), the count `pv`
and the free permits' resource `Pool`, which the mutex owns. -/
structure FSem (γ X : Type) (L : FLock γ) (C : FCond γ) extends FPlace γ SPh where
  p : Ptr
  /-- The layout: the mutex at `p + 8`, the condition at `p + 12`, in the mutex's block. -/
  ptr_l : L.ptr = p.add 8
  ptr_c : C.S.ptr = p.add 12
  off : 8 ≤ L.o
  /-- The client's part of a ghost value, which the count and the pool read. -/
  x : γ → X
  pv : (ThreadId → X) → BitVec 64
  Pool : (ThreadId → X) → FAssn
  R_eq : ∀ G, L.R G = (up (pts p 8 (pv fun u => x (G u))) ⋆ Pool fun u => x (G u))
  /-- The client's part is not the places in the mutex, the condition or the semaphore, nor the
  thread's part and held resource. -/
  x_l : ∀ g q h, x (L.set g q h) = x g
  x_part : ∀ g r, x (L.setPart g r) = x g
  x_c : ∀ g c, x (C.set g c) = x g
  x_s : ∀ g s, x (set g s) = x g
  /-- The semaphore's place and the condition's are independent parts of a ghost value. -/
  cph_set : ∀ g s, C.ph (set g s) = C.ph g
  ph_cset : ∀ g c, ph (C.set g c) = ph g
  set_cset : ∀ g c s, set (C.set g c) s = C.set (set g s) c
  /-- The condition's signallers are the threads at `pst`. -/
  sx_iff : ∀ g, C.sx g ↔ (ph g).isPst = true

namespace FSem

variable {γ X : Type} {L : FLock γ} {C : FCond γ} (S : FSem γ X L C)

/-- The client's parts of the ghost values. -/
def xs (G : ThreadId → γ) : ThreadId → X := fun u => S.x (G u)

/-- The count. -/
def cnt (G : ThreadId → γ) : BitVec 64 := S.pv (S.xs G)

theorem R_cnt (G : ThreadId → γ) : L.R G = (up (pts S.p 8 (S.cnt G)) ⋆ S.Pool (S.xs G)) :=
  S.R_eq G

/-- **A taker** (module doc): a thread in the semaphore's wait (`wt`) out of the condition's
code: back from the condition's wait (a waiter that took a signal and relocks the mutex), or
holding the mutex before its next look at the count. -/
def Tk (G : ThreadId → γ) (u : ThreadId) : Prop := S.ph (G u) = .wt ∧ C.ph (G u) = .out

/-- The semaphore's invariant (module doc). -/
structure Inv (G : ThreadId → γ) (m : Mem) : Prop where
  /-- A thread in the semaphore's code exists. -/
  ex : ∀ u, S.ph (G u) ≠ .out → u < m.threads.size
  /-- A thread at `pst` holds the mutex. -/
  pst : ∀ u, (S.ph (G u)).isPst → L.ph (G u) = .holds
  /-- A thread in the condition's critical code saw the count 0 (it holds the mutex). -/
  crit : ∀ u, (C.ph (G u)).crit → S.cnt G = 0
  /-- A waiter at the condition is in the semaphore's wait. -/
  wt : ∀ u, (C.ph (G u)).waits → S.ph (G u) = .wt
  /-- No thread is in the condition's critical code while one is at `pst` (both hold the
  mutex). -/
  cp : ∀ u v, (C.ph (G u)).crit → (S.ph (G v)).isPst → False
  /-- A taker sleeps only at the mutex's futex. -/
  tq : ∀ w ∈ m.waiters, S.Tk G w.1 → w.2 = L.ptr
  /-- Every state write is a post, or happened before the mutex's holder, its newest release or
  every thread that has not ended (registrations and posts), or before a taker (a consume). -/
  hw : ∀ p, 0 < p → p < (C.S.hist m).size → FCond.SUp (C.S.hist m) p ∨
    L.HB G m (C.S.hist m)[p]!.clock ∨
    ∃ u, S.Tk G u ∧ VClock.le (C.S.hist m)[p]!.clock (m.clocks[u]!) = true
  /-- The snapshot of a thread at `pst` is a prefix of the state's writes, its clock below the
  thread's. -/
  sp : ∀ u h c, S.ph (G u) = .pst h c → C.S.Prefix h m ∧ VClock.le c (m.clocks[u]!) = true
  /-- Every write of the snapshot is a post or happened before its clock, or there is a taker. -/
  sb : ∀ u h c, S.ph (G u) = .pst h c → ∀ p, 0 < p → p < h.size →
    FCond.SUp h p ∨ VClock.le h[p]!.clock c = true ∨ ∃ v, S.Tk G v
  /-- Every write after the snapshot is a post, or there is a taker. -/
  sa : ∀ u h c, S.ph (G u) = .pst h c → ∀ p, h.size ≤ p → p < (C.S.hist m).size →
    FCond.SUp (C.S.hist m) p ∨ ∃ v, S.Tk G v
  /-- **No lost wakeup**: with permits and a registered waiter, a signal is pending, or a thread
  at `pst` or a taker runs. -/
  live : S.cnt G ≠ 0 → 0 < FCond.wOf (C.lastS m) →
    0 < FCond.sOf (C.lastS m) ∨ (∃ u, (S.ph (G u)).isPst) ∨ ∃ v, S.Tk G v

/-- The condition's and the semaphore's places of a thread. -/
def place : FPlace γ (CPh × SPh) where
  ph g := (C.ph g, S.ph g)
  set g q := S.set (C.set g q.1) q.2
  ph_set g q := by
    show (C.ph (S.set (C.set g q.1) q.2), S.ph (S.set (C.set g q.1) q.2)) = q
    rw [S.cph_set, C.ph_set, S.ph_set]
  set_set g q q' := by
    show S.set (C.set (S.set (C.set g q.1) q.2) q'.1) q'.2 = S.set (C.set g q'.1) q'.2
    rw [← S.set_cset, S.set_set, C.set_set]
  set_self g := by
    show S.set (C.set g (C.ph g)) (S.ph g) = g
    rw [C.set_self, S.set_self]

theorem place_set (g : γ) (q : CPh × SPh) : S.place.set g q = S.set (C.set g q.1) q.2 := rfl

/-- The condition's place alone. -/
theorem place_c (g : γ) (p : CPh) : S.place.set g (p, S.ph g) = C.set g p := by
  rw [place_set]
  have : S.ph g = S.ph (C.set g p) := (S.ph_cset g p).symm
  simp only; rw [this, S.set_self]

/-- The semaphore's place alone. -/
theorem place_s (g : γ) (s : SPh) : S.place.set g (C.ph g, s) = S.set g s := by
  rw [place_set]; simp only; rw [C.set_self]

/-- The places thread `t` enters `pst` from: `out` (`post`'s store of the count), or `wt` at a
count not 0 (`wait`'s take). -/
def PstFrom (G : ThreadId → γ) (t : ThreadId) : Prop :=
  S.ph (G t) = .out ∨ (S.ph (G t) = .wt ∧ S.cnt G ≠ 0)

/-- **The holder's moves in the semaphore's own code** (module doc), between the places the code
moves between (ledger row `sem-go-code-moves`): thread `t` stays; enters the wait (`wt`) from `out`
(`wait`'s lock); enters `pst` with the state's writes and its clock (its snapshot) from `PstFrom`;
or leaves `pst` when, with permits and a registered waiter, a signal is pending or there is a
taker. It constrains the places, not the step (the count is the client's ghost). -/
def Go (G : ThreadId → γ) (m : Mem) (t : ThreadId) (s : SPh) : Prop :=
  s = S.ph (G t) ∨ (s = .wt ∧ S.ph (G t) = .out) ∨
    (s = .pst (C.S.hist m) (m.clocks[t]!) ∧ S.PstFrom G t) ∨
    (s = .out ∧ (S.ph (G t)).isPst = true ∧ (S.cnt G ≠ 0 → 0 < FCond.wOf (C.lastS m) →
      0 < FCond.sOf (C.lastS m) ∨ ∃ v, S.Tk G v))

/-- The steps of the semaphore's own code by thread `t` (module doc): the entry of the waiter
into the condition's wait at count 0, and a step of the holder on the mutex's resource (a load or
a store of the count; `FStepIn` with the mutex's word and the rest in its frame, which keeps the
condition's cells) with a move in the semaphore's code (`Go`; the same memory for a move alone). -/
inductive Move (t : ThreadId) (G : ThreadId → γ) (rX : Res) (m : Mem) :
    (ThreadId → γ) → Res → Mem → Prop
  | enter : L.ph (G t) = .holds → C.ph (G t) = .out → S.ph (G t) = .wt → S.cnt G = 0 →
      Move t G rX m (upd G t (C.set (G t) .en)) rX m
  | hold {m' : Mem} (s : SPh) (h : Res) : L.ph (G t) = .holds → C.ph (G t) = .out →
      L.Inv G rX m → m.current = t → FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      (∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
        (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) →
      S.Go G m t s →
      Move t G rX m (upd G t (S.set (L.set (G t) .holds h) s)) rX m'

/-- **The semaphore as a primitive next to its mutex `L`** (module doc; a protocol keeps it:
`S.Fits P U ok`). Its places are the condition's with the semaphore's; the calm places are those
out of the condition's busy code and out of `pst` (a thread at `wt` runs the mutex's code); the
role is the condition's `sx`; the rest keeps the condition (`FCond.prim`'s `Sub`) and the
semaphore's invariant; a step is a step of the condition's code, with both invariants after it,
or of the semaphore's own code (`Move`), with the condition's invariant and the semaphore's
after it (the rest's cells of the words after a step of the holder are the protocol's to show,
as after a step of the lock's code). -/
abbrev prim : FPrim γ where
  Ph := CPh × SPh
  pl := S.place
  out := (.out, .out)
  calm q := q.1.busy = false ∧ (q.2 = .out ∨ q.2 = .wt)
  Role := Unit
  role _ g := C.sx g
  Sub G rX m := (C.prim L).Sub G rX m ∧ S.Inv G m
  Apart := (C.prim L).Apart
  Step t G rX m G' rX' m' := S.Inv G' m' ∧ ((C.prim L).Step t G rX m G' rX' m' ∨
    (C.Inv L G' m' ∧ S.Move t G rX m G' rX' m'))

/-- **A protocol that keeps the semaphore** next to its mutex `L` (module doc): `FLock.Fits` with
the semaphore as its primitive, its `ok` out of `pst` (a thread in `ok` runs the mutex's code),
and the condition's window (`FCond.Fits.win`): every registered waiter on its way to its futex
wait (`reg i jr false e`, not queued at the epoch) has fewer than `2^32` epoch writes after its
saved one, in every state the rest allows. -/
structure Fits {Tgt : Type} (P : Proto Tgt γ) (U : (ThreadId → γ) → Res → Mem → Prop)
    (ok : γ → Prop) : Prop extends L.Fits S.prim P U ok where
  ok_s : ∀ g, ok g → S.ph g = .out ∨ S.ph g = .wt
  win : ∀ G rX m, U G rX m → ∀ u i jr e, C.ph (G u) = .reg i jr false e → C.qd m u = false →
    (C.Ep.hist m).size ≤ i + 4294967296

/-! ## A protocol with the semaphore

The compatibility laws of `FLock.Fits` for the condition's and the semaphore's places alone, and
the protocol with the condition that a protocol with the semaphore is (`Fits.toC`). -/

variable {S} {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
  {ok : γ → Prop}

section Laws

variable (hS : L.Fits S.prim P U ok) (g : γ) (q : LPh) (h r : Res) (p : CPh) (s : SPh)
include hS

theorem cph_l : C.ph (L.set g q h) = C.ph g := congrArg Prod.fst (hS.ph_l g q h)
theorem sph_l : S.ph (L.set g q h) = S.ph g := congrArg Prod.snd (hS.ph_l g q h)
theorem cph_part : C.ph (L.setPart g r) = C.ph g := congrArg Prod.fst (hS.ph_part g r)
theorem sph_part : S.ph (L.setPart g r) = S.ph g := congrArg Prod.snd (hS.ph_part g r)

theorem lph_c : L.ph (C.set g p) = L.ph g := by
  have := hS.lph g (p, S.ph g); rwa [place_c] at this
theorem lph_s : L.ph (S.set g s) = L.ph g := by
  have := hS.lph g (C.ph g, s); rwa [place_s] at this
theorem lpart_c : L.part (C.set g p) = L.part g := by
  have := hS.lpart g (p, S.ph g); rwa [place_c] at this
theorem lpart_s : L.part (S.set g s) = L.part g := by
  have := hS.lpart g (C.ph g, s); rwa [place_s] at this
theorem lheld_c : L.held (C.set g p) = L.held g := by
  have := hS.lheld g (p, S.ph g); rwa [place_c] at this
theorem lheld_s : L.held (S.set g s) = L.held g := by
  have := hS.lheld g (C.ph g, s); rwa [place_s] at this

theorem lset_c : C.set (L.set g q h) p = L.set (C.set g p) q h := by
  have := hS.set_l g (p, S.ph g) q h
  rwa [place_c, ← sph_l hS g q h, place_c] at this
theorem lset_s : S.set (L.set g q h) s = L.set (S.set g s) q h := by
  have := hS.set_l g (C.ph g, s) q h
  rwa [place_s, ← cph_l hS g q h, place_s] at this
theorem pset_c : C.set (L.setPart g r) p = L.setPart (C.set g p) r := by
  have := hS.set_part g (p, S.ph g) r
  rwa [place_c, ← sph_part hS g r, place_c] at this
theorem pset_s : S.set (L.setPart g r) s = L.setPart (S.set g s) r := by
  have := hS.set_part g (C.ph g, s) r
  rwa [place_s, ← cph_part hS g r, place_s] at this

theorem lR_c (G : ThreadId → γ) (t : ThreadId) (r : Res) (hr : L.R G r) :
    L.R (upd G t (C.set (G t) p)) r := by
  have := hS.lR G t (p, S.ph (G t)) r hr; rwa [place_c] at this
theorem lR_s (G : ThreadId → γ) (t : ThreadId) (r : Res) (hr : L.R G r) :
    L.R (upd G t (S.set (G t) s)) r := by
  have := hS.lR G t (C.ph (G t), s) r hr; rwa [place_s] at this

end Laws

/-- The client's parts with `t` at `g'`, whose client part is `g`'s. -/
theorem xs_upd {G : ThreadId → γ} {t : ThreadId} {g g' : γ} (h : S.x g' = S.x g) :
    S.xs (upd G t g') = S.xs (upd G t g) := by
  funext u; unfold xs upd; split
  · exact h
  · rfl

theorem xs_lupd (G : ThreadId → γ) (t : ThreadId) (g : γ) (q : LPh) (h : Res) :
    S.xs (upd G t (L.set g q h)) = S.xs (upd G t g) := S.xs_upd (S.x_l g q h)
theorem xs_cupd (G : ThreadId → γ) (t : ThreadId) (g : γ) (p : CPh) :
    S.xs (upd G t (C.set g p)) = S.xs (upd G t g) := S.xs_upd (S.x_c g p)
theorem xs_supd (G : ThreadId → γ) (t : ThreadId) (g : γ) (s : SPh) :
    S.xs (upd G t (S.set g s)) = S.xs (upd G t g) := S.xs_upd (S.x_s g s)
theorem xs_pupd (G : ThreadId → γ) (t : ThreadId) (g : γ) (r : Res) :
    S.xs (upd G t (L.setPart g r)) = S.xs (upd G t g) := S.xs_upd (S.x_part g r)

theorem pv_lupd (G : ThreadId → γ) (t : ThreadId) (g : γ) (q : LPh) (h : Res) :
    S.cnt (upd G t (L.set g q h)) = S.cnt (upd G t g) := by unfold cnt; rw [xs_lupd]
theorem pv_cupd (G : ThreadId → γ) (t : ThreadId) (g : γ) (p : CPh) :
    S.cnt (upd G t (C.set g p)) = S.cnt (upd G t g) := by unfold cnt; rw [xs_cupd]
theorem pv_supd (G : ThreadId → γ) (t : ThreadId) (g : γ) (s : SPh) :
    S.cnt (upd G t (S.set g s)) = S.cnt (upd G t g) := by unfold cnt; rw [xs_supd]
theorem pv_pupd (G : ThreadId → γ) (t : ThreadId) (g : γ) (r : Res) :
    S.cnt (upd G t (L.setPart g r)) = S.cnt (upd G t g) := by unfold cnt; rw [xs_pupd]

/-- **The count is the value in the holder's resource**: while `t` holds the mutex with the
resource `rL`, which has the count `v`, the count of the ghost values is `v` (whatever the other
threads' ghost values). -/
theorem cnt_held (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    {g : γ} {rL : Res} {v : BitVec 64} {B : FAssn} (hi : P.inv (upd G t (L.set g .holds rL)) m)
    (hv : (up (pts S.p 8 v) ⋆ B) rL) : S.cnt (upd G t (L.set g .holds rL)) = v := by
  obtain ⟨rX, hL, -⟩ := (hS.inv _ m).mp hi
  have hR := hL.res t (by rw [upd_self, L.ph_set])
  rw [upd_self, L.held_set, R_cnt] at hR
  exact pts_agree hR hv

/-- A thread in `ok` runs the mutex's code at `wt` too (its places are calm). -/
theorem Fits.ok_wt (hS : S.Fits P U ok) {g : γ} (hok : ok g) (hgx : C.ph g = .out) :
    ok (S.set g .wt) := by
  have hc : (S.prim).calm (C.ph g, S.ph g) := ⟨by rw [hgx]; rfl, hS.ok_s g hok⟩
  have := (hS.ok_calm g (C.ph g, S.ph g) (C.ph g, .wt) hc ⟨by rw [hgx]; rfl, .inr rfl⟩).mp
    (by rw [place_s, S.set_self]; exact hok)
  rwa [place_s] at this

/-! ## The invariant over the steps -/

/-- **`S.Inv` stays** over a step that keeps every thread's places, the count, the holders at
`pst`, the threads, the state's writes, and the queue but for entries at the mutex, grows the
clocks and keeps `HB` (the holders, or a release, the newest release of the mutex's word). -/
theorem Inv.mono {G G' : ThreadId → γ} {m m' : Mem} (hI : S.Inv G m)
    (hsph : ∀ u, S.ph (G' u) = S.ph (G u)) (hcph : ∀ u, C.ph (G' u) = C.ph (G u))
    (hpv : S.cnt G' = S.cnt G)
    (hpst : ∀ u, (S.ph (G u)).isPst → L.ph (G' u) = .holds)
    (hhold : ∀ u, L.ph (G u) = .holds → L.ph (G' u) = .holds ∨
      ∀ c, VClock.le c (m.clocks[u]!) = true → L.Before m' c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) (ht : m'.threads = m.threads)
    (hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone)
    (hwq : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨ w.2 = L.ptr)
    (hS : C.S.hist m' = C.S.hist m) : S.Inv G' m' := by
  have hTk : ∀ v, S.Tk G' v ↔ S.Tk G v := fun v => by unfold Tk; rw [hsph, hcph]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  refine ⟨fun u hu => ?_, fun u hu => hpst u (by rw [← hsph u]; exact hu),
    fun u hu => by rw [hpv]; exact hI.crit u (by rw [← hcph u]; exact hu),
    fun u hu => by rw [hsph]; exact hI.wt u (by rw [← hcph u]; exact hu),
    fun u v hu hv => hI.cp u v (by rw [← hcph u]; exact hu) (by rw [← hsph v]; exact hv),
    fun w hw hk => ?_, fun p h0 hp => ?_, fun u h c hu => ?_, fun u h c hu p h0 hp => ?_,
    fun u h c hu p h0 hp => ?_, fun hc hpw => ?_⟩
  · rw [ht]; exact hI.ex u (by rw [← hsph u]; exact hu)
  · rcases hwq w hw with hw | hw
    · exact hI.tq w hw ((hTk _).mp hk)
    · exact hw
  · rw [hS] at hp ⊢
    rcases hI.hw p h0 hp with h | h | ⟨u, hu, hle⟩
    · exact .inl h
    · exact .inr (.inl (h.mono hhold hcl hbef ht hgone))
    · exact .inr (.inr ⟨u, (hTk u).mpr hu, VClock.le_trans hle (hcl u)⟩)
  · obtain ⟨⟨r, hr⟩, hc⟩ := hI.sp u h c (by rw [← hsph u]; exact hu)
    exact ⟨⟨r, by rw [hS]; exact hr⟩, VClock.le_trans hc (hcl u)⟩
  · rcases hI.sb u h c (by rw [← hsph u]; exact hu) p h0 hp with h | h | ⟨v, hv⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)
  · rw [hS] at hp ⊢
    rcases hI.sa u h c (by rw [← hsph u]; exact hu) p h0 hp with h | ⟨v, hv⟩
    · exact .inl h
    · exact .inr ⟨v, (hTk v).mpr hv⟩
  · rw [hlast] at hpw ⊢
    rcases hI.live (by rwa [← hpv]) hpw with h | ⟨u, hu⟩ | ⟨v, hv⟩
    · exact .inl h
    · exact .inr (.inl ⟨u, by rw [hsph]; exact hu⟩)
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)

/-- **The semaphore at its start**: every thread out of the semaphore's and the condition's code,
the condition's state at its first write `(0, 0)` (`FCond.Inv.start`'s premises on the state).
Every write fact, the takers' queue, the snapshots and the no-lost-wakeup fact hold vacuously. -/
theorem Inv.start {G : ThreadId → γ} {m : Mem} (hS : (C.S.hist m).size = 1)
    (hS0 : (C.S.hist m)[0]!.Val (0 : BitVec 32)) (hout : ∀ u, C.ph (G u) = .out)
    (hsout : ∀ u, S.ph (G u) = .out) : S.Inv G m where
  ex u hu := absurd (hsout u) hu
  pst u hu := by rw [hsout u] at hu; cases hu
  crit u hu := by rw [hout u] at hu; cases hu
  wt u hu := by rw [hout u] at hu; cases hu
  cp u _ hu _ := by rw [hout u] at hu; cases hu
  tq _ _ hk := by have h1 := hk.1; rw [hsout] at h1; cases h1
  hw p h0 hp := by omega
  sp u _ _ hu := by rw [hsout u] at hu; cases hu
  sb u _ _ hu := by rw [hsout u] at hu; cases hu
  sa u _ _ hu := by rw [hsout u] at hu; cases hu
  live _ hw := by
    have : FCond.wOf (C.lastS m) = 0 := by
      unfold FCond.lastS; rw [hS]; simp [FCond.wOf, FCond.val_of hS0]
    omega

/-- **A tick keeps the semaphore's invariant** (`FLock.PartTick`: the ticking thread's part
changes, its places, the count and the memory but for the tick count stay; for a client's
`FLock.Fits.kstep`). -/
theorem Inv.partTick {G G' : ThreadId → γ} {rX rX' : Res} {m m' : Mem} {t : ThreadId}
    (hI : S.Inv G m) (hcp : ∀ g r, C.ph (L.setPart g r) = C.ph g)
    (hsp : ∀ g r, S.ph (L.setPart g r) = S.ph g) (h : L.PartTick t G rX m G' rX' m') :
    S.Inv G' m' := by
  obtain ⟨-, -, -, r, -, rfl, rfl, rfl, -⟩ := h
  have hph : ∀ (f : γ → Prop), (∀ g r, f (L.setPart g r) ↔ f g) → ∀ u,
      f (upd G t (L.setPart (G t) r) u) ↔ f (G u) := fun f hf u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hf]
    · rw [upd_ne _ _ e]
  exact hI.mono (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, hsp]
      · rw [upd_ne _ _ e])
    (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, hcp]
      · rw [upd_ne _ _ e])
    (by rw [pv_pupd, upd_same])
    (fun u hu => (hph (fun g => L.ph g = .holds) (fun g r => by rw [L.ph_setPart]) u).mpr
      (hI.pst u hu))
    (fun u hu => .inl ((hph (fun g => L.ph g = .holds) (fun g r => by rw [L.ph_setPart]) u).mpr
      hu))
    (fun _ => VClock.le_refl _) (fun _ h => h) rfl
    (fun u => (hph (fun g => L.ph g ≠ .gone) (fun g r => by rw [L.ph_setPart]) u).mp)
    (fun w hw => .inl hw) rfl

/-- **A step of the condition's code keeps the semaphore's invariant** (for `Fits.toC`). A new
state write is classified by the stepping thread's registration: kept (then it is a post,
`FCond.Inv.push_sup`), gained (a registration, from the critical code: the thread holds the mutex,
`HB`), or lost (a consume: the thread is a taker after it). -/
theorem Inv.cstep (hS : L.Fits S.prim P U ok) {G G' : ThreadId → γ} {rX rX' : Res}
    {m m' : Mem} {t : ThreadId} (hI : S.Inv G m) (hC : C.Inv L G m)
    (hsub : (C.prim L).Sub G rX m) (hst : (C.prim L).Step t G rX m G' rX' m') :
    S.Inv G' m' := by
  have hap : ∀ W, (W = C.S ∨ W = C.Ep) → W.ApartL L.toLockWord := hS.apart
  obtain ⟨W, rY, hW, rfl, rfl, hY, hC', hmv | hown⟩ := hst
  · obtain ⟨p, q, h, ⟨hn, hq, hms, -, -⟩, -, rfl⟩ := hmv
    have hqh : L.ph (G t) = .holds → q = .holds := fun hh => by
      rcases hq with ⟨rfl, -⟩ | ⟨ho, -, -⟩
      · exact hh
      · rw [hh] at ho; rcases ho with ho | ⟨ho, -⟩ <;> cases ho
    have hsph : ∀ u, S.ph (upd G t (L.set (C.set (G t) p) q h) u) = S.ph (G u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, sph_l hS, S.ph_cset]
      · rw [upd_ne _ _ e]
    have hpv : S.cnt (upd G t (L.set (C.set (G t) p) q h)) = S.cnt G := by
      rw [pv_lupd, pv_cupd, upd_same]
    have hhold : ∀ u, L.ph (G u) = .holds →
        L.ph (upd G t (L.set (C.set (G t) p) q h) u) = .holds := fun u hu => by
      by_cases e : u = t
      · subst e; rw [upd_self, L.ph_set]; exact hqh hu
      · rw [upd_ne _ _ e]; exact hu
    have hgone : ∀ u, L.ph (upd G t (L.set (C.set (G t) p) q h) u) ≠ .gone →
        L.ph (G u) ≠ .gone := fun u hu => by
      by_cases e : u = t
      · subst e; rw [upd_self, L.ph_set] at hu
        rcases hq with ⟨rfl, -⟩ | ⟨ho, -, -⟩
        · exact hu
        · rcases ho with ho | ⟨ho, -⟩ <;> rw [ho] <;> decide
      · rwa [upd_ne _ _ e] at hu
    have hbef : ∀ c, L.Before m c → L.Before m' c := fun _ ⟨i, l, hl, hc⟩ =>
      ⟨i, l, hms.lockLoc (hap W hW) (hap C.Ep (.inr rfl)) hl, hc⟩
    have hmono : ∀ c, L.HB G m c → L.HB (upd G t (L.set (C.set (G t) p) q h)) m' c :=
      fun c hc => hc.mono (fun u hu => .inl (hhold u hu)) hms.clocks hbef hms.threads hgone
    have hcpt : C.ph (upd G t (L.set (C.set (G t) p) q h) t) = p := by
      rw [upd_self, cph_l hS, C.ph_set]
    have hcph : ∀ u, u ≠ t → C.ph (upd G t (L.set (C.set (G t) p) q h) u) = C.ph (G u) :=
      fun u e => by rw [upd_ne _ _ e]
    have hGu : ∀ u, u ≠ t → upd G t (L.set (C.set (G t) p) q h) u = G u :=
      fun u e => upd_ne _ _ e
    -- the state's writes: the same, or one new write, at the stepping thread's clock
    have hx : C.S.hist m' = C.S.hist m ∨ ∃ x : Word.Entry,
        C.S.hist m' = (C.S.hist m).push x ∧ x.clock = m'.clocks[t]! := by
      rcases (hms.word_rmw (hsub.2 C.S (.inl rfl)).1 (FCond.words_apart (.inl rfl) hW)
        (FCond.words_apart (.inl rfl) (.inr rfl))).2 with h | ⟨-, ord, v, h⟩
      · exact .inl h
      · exact .inr ⟨_, h, rfl⟩
    have hext : C.S.Extends m m' := by
      rcases hx with h | ⟨x, h, -⟩
      · exact ⟨#[], by rw [h, Array.append_empty]⟩
      · exact ⟨#[x], by rw [h, Array.push_eq_append]⟩
    -- the stepping thread's registration: kept, gained (from the critical code), or lost
    have hcase : (C.ph (upd G t (L.set (C.set (G t) p) q h) t)).isReg = (C.ph (G t)).isReg ∨
        ((C.ph (G t)).crit = true ∧ L.ph (upd G t (L.set (C.set (G t) p) q h) t) = .holds) ∨
        S.Tk (upd G t (L.set (C.set (G t) p) q h)) t := by
      rw [hcpt]
      cases hr : (C.ph (G t)).isReg <;> cases hr' : p.isReg
      · exact .inl rfl
      · have hcr := hn.crit_of_reg hr' hr
        exact .inr (.inl ⟨hcr, by rw [upd_self, L.ph_set]; exact hqh (hC.crit t hcr)⟩)
      · refine .inr (.inr ⟨by rw [hsph]; exact hI.wt t (CPh.isReg_waits hr), ?_⟩)
        rw [hcpt]; exact hn.out_of_reg hr hr'
      · exact .inl rfl
    -- a taker stays one (it does not enter the signal code: it is not at `pst`)
    have hTk : ∀ v, S.Tk G v → S.Tk (upd G t (L.set (C.set (G t) p) q h)) v := fun v hv => by
      refine ⟨by rw [hsph]; exact hv.1, ?_⟩
      by_cases e : v = t
      · subst e
        rw [hcpt]
        have hn' := hn; rw [hv.2] at hn'
        rcases CPh.Next.of_out hn' with h' | h'
        · exact h'
        · exfalso
          have hsx := hC'.sx v (by rw [hcpt]; exact h')
          rw [S.sx_iff, hsph, hv.1] at hsx; cases hsx
      · rw [hcph v e]; exact hv.2
    have hcl := hms.clocks
    -- an old write: its index and `SUp` stay
    have hold : ∀ j, j < (C.S.hist m).size → (C.S.hist m')[j]! = (C.S.hist m)[j]! :=
      fun j hj => Word.Prefix.get hext hj
    have hsupOld : ∀ j, j < (C.S.hist m).size →
        (FCond.SUp (C.S.hist m') j ↔ FCond.SUp (C.S.hist m) j) := fun j hj => by
      unfold FCond.SUp; rw [hold j hj, hold (j - 1) (by omega)]
    have hsz : (C.S.hist m).size ≤ (C.S.hist m').size := Word.Prefix.size_le hext
    -- a new write is at index `(C.S.hist m).size`
    have hnew : ∀ j, (C.S.hist m).size ≤ j → j < (C.S.hist m').size → ∃ x : Word.Entry,
        C.S.hist m' = (C.S.hist m).push x ∧ x.clock = m'.clocks[t]! ∧ j = (C.S.hist m).size :=
      fun j h1 h2 => by
        rcases hx with h | ⟨x, h, hc⟩
        · rw [h] at h2; omega
        · rw [h, Array.size_push] at h2; exact ⟨x, h, hc, by omega⟩
    have hgetx : ∀ x : Word.Entry, C.S.hist m' = (C.S.hist m).push x →
        (C.S.hist m')[(C.S.hist m).size]! = x := fun x h => by rw [h]; exact Word.get_push_eq
    refine ⟨fun u hu => ?_, fun u hu => hhold u (hI.pst u (by rw [← hsph u]; exact hu)),
      fun u hu => ?_, fun u hu => ?_, fun u v hu hv => ?_, fun w hw hk => ?_,
      fun j h0 hj => ?_, fun u sh c hu => ?_, fun u sh c hu j h0 hj => ?_,
      fun u sh c hu j h0 hj => ?_, fun hc hpw => ?_⟩
    · -- ex
      rw [hms.threads]; exact hI.ex u (by rw [← hsph u]; exact hu)
    · -- crit
      rw [hpv]
      by_cases e : u = t
      · subst e; rw [hcpt] at hu; exact hI.crit u (hn.crit hu)
      · rw [hcph u e] at hu; exact hI.crit u hu
    · -- wt
      rw [hsph]
      by_cases e : u = t
      · subst e; rw [hcpt] at hu; exact hI.wt u (hn.waits hu)
      · rw [hcph u e] at hu; exact hI.wt u hu
    · -- cp
      rw [hsph] at hv
      by_cases e : u = t
      · subst e; rw [hcpt] at hu; exact hI.cp u v (hn.crit hu) hv
      · rw [hcph u e] at hu; exact hI.cp u v hu hv
    · -- tq
      rcases hms.waiters hw with hw0 | rfl
      · by_cases e : w.1 = t
        · have hk2 := hk.2
          rw [e, hcpt] at hk2
          have hn' := hn; rw [hk2] at hn'
          rcases CPh.Next.to_out hn' with h' | h' | h'
          · exact hI.tq w hw0 ⟨by rw [← hsph]; exact hk.1, by rw [e]; exact h'⟩
          · rcases hC.qw w hw0 (by rw [e]; exact CPh.isReg_waits h') with h'' | h''
            · obtain ⟨i, jr, ee, hreg, -⟩ := hC'.q w hw h''
              rw [e, hcpt, hk2] at hreg; cases hreg
            · exact h''
          · exfalso
            have hsx := (S.sx_iff _).mp (hC.sx t h')
            have h1 := hk.1
            rw [hsph, e] at h1
            rw [h1] at hsx; cases hsx
        · exact hI.tq w hw0 ⟨by rw [← hsph]; exact hk.1, by rw [← hcph w.1 e]; exact hk.2⟩
      · obtain ⟨i, jr, ee, hreg, -⟩ := hC'.q _ hw rfl
        rw [hk.2] at hreg; cases hreg
    · -- hw: every state write
      by_cases hjo : j < (C.S.hist m).size
      · rw [hold j hjo]
        rcases hI.hw j h0 hjo with h' | h' | ⟨u, hu, hle⟩
        · exact .inl ((hsupOld j hjo).mpr h')
        · exact .inr (.inl (hmono _ h'))
        · exact .inr (.inr ⟨u, hTk u hu, VClock.le_trans hle (hcl u)⟩)
      · obtain ⟨x, hxe, hxc, rfl⟩ := hnew j (by omega) hj
        rcases hcase with hr | ⟨-, hh⟩ | hk
        · exact .inl (FCond.Inv.push_sup hC hC' hGu hr hxe)
        · refine .inr (.inl (FLock.HB.of_holder hh ?_))
          rw [hgetx x hxe, hxc]; exact VClock.le_refl _
        · refine .inr (.inr ⟨t, hk, ?_⟩)
          rw [hgetx x hxe, hxc]; exact VClock.le_refl _
    · -- sp
      obtain ⟨hp, hc⟩ := hI.sp u sh c (by rw [← hsph u]; exact hu)
      exact ⟨hp.extend hext, VClock.le_trans hc (hcl u)⟩
    · -- sb
      rcases hI.sb u sh c (by rw [← hsph u]; exact hu) j h0 hj with h' | h' | ⟨v, hv⟩
      · exact .inl h'
      · exact .inr (.inl h')
      · exact .inr (.inr ⟨v, hTk v hv⟩)
    · -- sa
      have hu0 : S.ph (G u) = .pst sh c := by rw [← hsph u]; exact hu
      by_cases hjo : j < (C.S.hist m).size
      · rcases hI.sa u sh c hu0 j h0 hjo with h' | ⟨v, hv⟩
        · exact .inl ((hsupOld j hjo).mpr h')
        · exact .inr ⟨v, hTk v hv⟩
      · obtain ⟨x, hxe, -, rfl⟩ := hnew j (by omega) hj
        rcases hcase with hr | ⟨hcr, -⟩ | hk
        · exact .inl (FCond.Inv.push_sup hC hC' hGu hr hxe)
        · exact absurd (hI.cp t u hcr (by rw [hu0]; rfl)) id
        · exact .inr ⟨t, hk⟩
    · -- live
      rw [hpv] at hc
      rcases hcase with hr | ⟨hcr, -⟩ | hk
      · have hJ : 0 < FCond.wOf (C.lastS m) → 0 < FCond.sOf (C.lastS m) ∨
            (∃ u, (S.ph (upd G t (L.set (C.set (G t) p) q h) u)).isPst) ∨
            ∃ v, S.Tk (upd G t (L.set (C.set (G t) p) q h)) v := fun hw0 => by
          rcases hI.live hc hw0 with h' | ⟨u, hu⟩ | ⟨v, hv⟩
          · exact .inl h'
          · exact .inr (.inl ⟨u, by rw [hsph]; exact hu⟩)
          · exact .inr (.inr ⟨v, hTk v hv⟩)
        rcases hx with he | ⟨x, hxe, -⟩
        · have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [he]
          rw [hlast] at hpw ⊢; exact hJ hpw
        · have hsup := FCond.Inv.push_sup hC hC' hGu hr hxe
          have hsz' : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hxe]; simp
          have hpos := hC.spos
          have hlast : C.lastS m' = (C.S.hist m')[(C.S.hist m).size]! := by
            unfold FCond.lastS; rw [hsz', Nat.add_sub_cancel]
          have hprev : (C.S.hist m')[(C.S.hist m).size - 1]! = C.lastS m := hold _ (by omega)
          obtain ⟨hws, hss⟩ := hsup
          rw [hprev] at hws hss
          rw [hlast] at hpw ⊢
          rw [hws] at hpw
          rcases hJ hpw with h' | h' | h'
          · exact .inl (by omega)
          · exact .inr (.inl h')
          · exact .inr (.inr h')
      · exact absurd (hI.crit t hcr) hc
      · exact .inr (.inr ⟨t, hk⟩)
  · obtain ⟨r, -, hL0, hc, hfs, hcW, -, hh, hL', rfl⟩ := hown
    have hY' : ∀ V, (V = C.S ∨ V = C.Ep) → V.hist m' = V.hist m := by
      intro V hV
      rcases FCond.words_apart hV hW with rfl | hapW
      · exact hh
      · obtain ⟨hwV, rV, hrV, -⟩ := hsub.2 V hV
        have hcell : ∀ l, V.In l → ∃ fc, (rsum (W.cellsR m) rY).heap l = some fc ∧
            rY.heap l = some fc := by
          intro l hl
          have hnW : ¬ W.In l := Word.notIn_apart hapW hl
          have hsome : (rsum (W.cellsR m) rY).heap l ≠ none := by
            rw [hrV]; simp only [FHeap.union_apply, Word.cellsR]
            have := cellsAt_some (W := V.In) hl (hwV.cellIn hl) (m := m)
            cases e : (cellsAt V.In m).heap l <;> simp_all
          have heq : (rsum (W.cellsR m) rY).heap l = rY.heap l := by
            simp only [FHeap.union_apply, Word.cellsR, cellsAt_none hnW, Option.none_or]
          cases e : (rsum (W.cellsR m) rY).heap l with
          | none => exact absurd e hsome
          | some fc => exact ⟨fc, rfl, heq ▸ e⟩
        refine Word.hist_fstep hwV hfs (fun l hl => ?_) (fun l hl => ?_)
        · obtain ⟨fc, -, hy⟩ := hcell l hl
          simp [FHeap.erase, FHeap.union_apply, hy]
        · obtain ⟨fc, hfc, hy⟩ := hcell l hl
          have hnW : (W.cellsR m').heap l = none := cellsAt_none (Word.notIn_apart hapW hl)
          have h' : (rsum (W.cellsR m') rY).heap l = some fc := by
            simp only [FHeap.union_apply, hnW, Option.none_or, hy]
          rw [hL'.restCell h', hL0.restCell hfc]
    have hsph : ∀ u, S.ph (upd G t (L.setPart (G t) r) u) = S.ph (G u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, sph_part hS]
      · rw [upd_ne _ _ e]
    have hcph : ∀ u, C.ph (upd G t (L.setPart (G t) r) u) = C.ph (G u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, cph_part hS]
      · rw [upd_ne _ _ e]
    have hlph : ∀ u, L.ph (upd G t (L.setPart (G t) r) u) = L.ph (G u) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, L.ph_setPart]
      · rw [upd_ne _ _ e]
    exact hI.mono hsph hcph (by rw [pv_pupd, upd_same])
      (fun u hu => by rw [hlph]; exact hI.pst u hu) (fun u hu => .inl (by rw [hlph]; exact hu))
      hfs.clock (FLock.Inv.before_fstep hL0 hfs) hfs.threads (fun u hu => by rwa [hlph] at hu)
      (fun w hw => .inl (by rwa [hfs.waiters] at hw)) (hY' C.S (.inl rfl))

/-- **A lock step of a thread out of `pst`** keeps the semaphore's invariant (for a client's
`FLock.Fits.stable`, whose `ok` excludes `pst`; the component facts are the ones that
structure's other fields give: the state word's `Ok` and apartness, and the places' laws). -/
theorem Inv.lstep {G : ThreadId → γ} {m m' : Mem}
    {t : ThreadId} {q : LPh} {h : Res} (hI : S.Inv G m) (hwS : C.S.Ok m)
    (hapS : C.S.ApartL L.toLockWord) (hcl : ∀ g q h, C.ph (L.set g q h) = C.ph g)
    (hsl : ∀ g q h, S.ph (L.set g q h) = S.ph g)
    (hst : (S.ph (G t)).isPst = false) (hg : L.ph (G t) ≠ .gone)
    (hs : L.Step t m m') (hrel : L.ph (G t) = .holds → q ≠ .holds → L.Before m' (m.clocks[t]!)) :
    S.Inv (upd G t (L.set (G t) q h)) m' := by
  have hsph : ∀ u, S.ph (upd G t (L.set (G t) q h) u) = S.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hsl]
    · rw [upd_ne _ _ e]
  have hcph : ∀ u, C.ph (upd G t (L.set (G t) q h) u) = C.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hcl]
    · rw [upd_ne _ _ e]
  refine hI.mono hsph hcph (by rw [pv_lupd, upd_same])
    (fun u hu => ?_) (FLock.lstep_hold hrel) hs.clocks hs.before hs.threads
    (FLock.lstep_live hg)
    (fun w hw => by
      by_cases hl : w.2 = L.ptr
      · exact .inr hl
      · exact .inl ((hs.waiters_mem w hl).mp hw))
    (hwS.lockStep hs hapS).2
  by_cases e : u = t
  · subst e; rw [hst] at hu; cases hu
  · rw [upd_ne _ _ e]; exact hI.pst u hu

/-- No other thread is at `pst` while the mutex's holder `t` is (`pst` holds the mutex). -/
theorem no_pst {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hI : S.Inv G m)
    (hL : L.Inv G rX m) (hh : L.ph (G t) = .holds) :
    ∀ v, v ≠ t → (S.ph (G v)).isPst = false := fun v hv => by
  cases hp : (S.ph (G v)).isPst
  · rfl
  · exact absurd (hL.w.one v t (hI.pst v hp) hh) hv

/-- **A step of the holder in the semaphore's own code keeps its invariant** (`Move.hold`). -/
theorem Inv.hold (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {s : SPh} {h : Res} (hI : S.Inv G m) (hsub : (C.prim L).Sub G rX m)
    (hh : L.ph (G t) = .holds) (hcx : C.ph (G t) = .out) (hL : L.Inv G rX m)
    (hfs : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hcells : ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hgo : S.Go G m t s) :
    S.Inv (upd G t (S.set (L.set (G t) .holds h) s)) m' := by
  have hcph : ∀ u, C.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = C.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, S.cph_set, cph_l hS]
    · rw [upd_ne _ _ e]
  have hlph : ∀ u, L.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = L.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, lph_s hS, L.ph_set, hh]
    · rw [upd_ne _ _ e]
  have hsph : ∀ u, u ≠ t → S.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = S.ph (G u) :=
    fun u e => by rw [upd_ne _ _ e]
  have hspt : S.ph (upd G t (S.set (L.set (G t) .holds h) s) t) = s := by rw [upd_self, S.ph_set]
  have hpv : S.cnt (upd G t (S.set (L.set (G t) .holds h) s)) = S.cnt G := by
    rw [pv_supd, pv_lupd, upd_same]
  have hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hfs.clock
  have hbef := FLock.Inv.before_fstep hL hfs
  have hmono : ∀ c, L.HB G m c → L.HB (upd G t (S.set (L.set (G t) .holds h) s)) m' c :=
    fun c hc => hc.mono (fun u hu => .inl (by rw [hlph]; exact hu)) hcl hbef hfs.threads
      (fun u hu => by rwa [hlph] at hu)
  have hhS := FCond.hist_hold hsub hfs hcells (.inl rfl)
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hhS]
  have hnq : ∀ w ∈ m.waiters, w.1 ≠ t := FLock.notQ_mem (hL.w.notQ
    (by show L.ph (G t) ≠ _; rw [hh]; decide) (by show L.ph (G t) ≠ _; rw [hh]; decide))
  have hnp := no_pst hI hL hh
  have hTk : ∀ v, v ≠ t → (S.Tk (upd G t (S.set (L.set (G t) .holds h) s)) v ↔ S.Tk G v) :=
    fun v e => by unfold Tk; rw [hsph v e, hcph]
  have hTkt : s = .wt → S.Tk (upd G t (S.set (L.set (G t) .holds h) s)) t :=
    fun e => ⟨by rw [hspt, e], by rw [hcph]; exact hcx⟩
  -- a thread at `pst` after the move is `t`, at the snapshot it had or took
  have hpst' : ∀ u sh c, S.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = .pst sh c →
      u = t ∧ (S.ph (G t) = .pst sh c ∨ (sh = C.S.hist m ∧ c = m.clocks[t]!)) := by
    intro u sh c hu
    by_cases e : u = t
    · subst e
      rw [hspt] at hu; subst hu
      refine ⟨rfl, ?_⟩
      rcases hgo with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
      · exact .inl h'.symm
      · cases h'
      · cases h'; exact .inr ⟨rfl, rfl⟩
      · cases h'
    · rw [hsph u e] at hu
      have := hnp u e; rw [hu] at this; cases this
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun u v hu hv => ?_,
    fun w hw hk => ?_, fun p h0 hp => ?_, fun u sh c hu => ?_, fun u sh c hu p h0 hp => ?_,
    fun u sh c hu p h0 hp => ?_, fun hc hpw => ?_⟩
  · -- ex
    rw [hfs.threads]
    by_cases e : u = t
    · subst e; exact (hL.ht (by rw [hh]; decide)).1
    · rw [hsph u e] at hu; exact hI.ex u hu
  · -- pst
    rw [hlph]
    by_cases e : u = t
    · subst e; exact hh
    · rw [hsph u e] at hu; exact hI.pst u hu
  · -- crit
    rw [hpv]; rw [hcph] at hu; exact hI.crit u hu
  · -- wt
    rw [hcph] at hu
    by_cases e : u = t
    · subst e; rw [hcx] at hu; cases hu
    · rw [hsph u e]; exact hI.wt u hu
  · -- cp
    rw [hcph] at hu
    by_cases e : v = t
    · subst e
      obtain rfl := hL.w.one u v (hsub.1.crit u hu) hh
      rw [hcx] at hu; exact absurd hu (by decide)
    · rw [hsph v e] at hv; exact hI.cp u v hu hv
  · -- tq
    rw [hfs.waiters] at hw
    have e := hnq w hw
    exact hI.tq w hw ((hTk w.1 e).mp hk)
  · -- hw
    rw [hhS] at hp ⊢
    rcases hI.hw p h0 hp with h' | h' | ⟨u, hu, hle⟩
    · exact .inl h'
    · exact .inr (.inl (hmono _ h'))
    · by_cases e : u = t
      · subst e
        exact .inr (.inl (FLock.HB.of_holder (by rw [hlph]; exact hh)
          (VClock.le_trans hle (hcl u))))
      · exact .inr (.inr ⟨u, (hTk u e).mpr hu, VClock.le_trans hle (hcl u)⟩)
  · -- sp
    obtain ⟨rfl, h' | ⟨rfl, rfl⟩⟩ := hpst' u sh c hu
    · obtain ⟨⟨r, hr⟩, hc⟩ := hI.sp u sh c h'
      exact ⟨⟨r, by rw [hhS]; exact hr⟩, VClock.le_trans hc (hcl u)⟩
    · exact ⟨⟨#[], by rw [hhS, Array.append_empty]⟩, hcl u⟩
  · -- sb
    obtain ⟨rfl, h' | ⟨rfl, rfl⟩⟩ := hpst' u sh c hu
    · rcases hI.sb u sh c h' p h0 hp with h'' | h'' | ⟨v, hv⟩
      · exact .inl h''
      · exact .inr (.inl h'')
      · have e : v ≠ u := fun e => by
          subst e; have h1 := hv.1; rw [h'] at h1; exact SPh.noConfusion h1
        exact .inr (.inr ⟨v, (hTk v e).mpr hv⟩)
    · rcases hI.hw p h0 hp with h'' | h'' | ⟨v, hv, hle⟩
      · exact .inl h''
      · exact .inr (.inl (h''.le hL.w hh))
      · by_cases e : v = u
        · subst e; exact .inr (.inl hle)
        · exact .inr (.inr ⟨v, (hTk v e).mpr hv⟩)
  · -- sa
    obtain ⟨rfl, h' | ⟨rfl, rfl⟩⟩ := hpst' u sh c hu
    · rw [hhS] at hp ⊢
      rcases hI.sa u sh c h' p h0 hp with h'' | ⟨v, hv⟩
      · exact .inl h''
      · have e : v ≠ u := fun e => by
          subst e; have h1 := hv.1; rw [h'] at h1; exact SPh.noConfusion h1
        exact .inr ⟨v, (hTk v e).mpr hv⟩
    · rw [hhS] at hp; omega
  · -- live
    rw [hpv] at hc; rw [hlast] at hpw ⊢
    rcases hgo with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, hp, hJ⟩
    · rcases hI.live hc hpw with h'' | ⟨u, hu⟩ | ⟨v, hv⟩
      · exact .inl h''
      · by_cases e : u = t
        · subst e; exact .inr (.inl ⟨u, by rw [hspt, h']; exact hu⟩)
        · exact .inr (.inl ⟨u, by rw [hsph u e]; exact hu⟩)
      · by_cases e : v = t
        · subst e; exact .inr (.inr ⟨v, by rw [hspt, h']; exact hv.1, by rw [hcph]; exact hv.2⟩)
        · exact .inr (.inr ⟨v, (hTk v e).mpr hv⟩)
    · exact .inr (.inr ⟨t, hTkt h'⟩)
    · exact .inr (.inl ⟨t, by rw [hspt, h']; rfl⟩)
    · rcases hJ hc hpw with h'' | ⟨v, hv⟩
      · exact .inl h''
      · have e : v ≠ t := fun e => by
          subst e; rw [hv.1] at hp; cases hp
        exact .inr (.inr ⟨v, (hTk v e).mpr hv⟩)

/-- **A step of the holder in the semaphore's own code keeps the condition's invariant**
(`Move.hold`: the holder is out of the condition's code). -/
theorem condHold (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {s : SPh} {h : Res} (hC : C.Inv L G m) (hsub : (C.prim L).Sub G rX m)
    (hL : L.Inv G rX m) (hh : L.ph (G t) = .holds)
    (hcx : C.ph (G t) = .out) (hfs : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hcells : ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    C.Inv L (upd G t (S.set (L.set (G t) .holds h) s)) m' := by
  have hcp : C.ph (S.set (L.set (G t) .holds h) s) = .out := by
    rw [S.cph_set, cph_l hS, hcx]
  have hnq : ∀ w ∈ m.waiters, w.1 ≠ t := FLock.notQ_mem (hL.w.notQ
    (by show L.ph (G t) ≠ _; rw [hh]; decide) (by show L.ph (G t) ≠ _; rw [hh]; decide))
  exact hC.quiet (by rw [hcx]; trivial) (by rw [hcp]; trivial)
    (FCond.hist_hold hsub hfs hcells (.inl rfl)) (FCond.hist_hold hsub hfs hcells (.inr rfl)) hfs.waiters
    hfs.woken hfs.threads hfs.clock hnq (fun i e h' => by rw [hcp] at h'; cases h')
    (fun h' => by rw [hcp] at h'; exact absurd h' (by decide)) (fun h' => absurd hcp h')
    (fun sh c h' => by rw [hcp] at h'; cases h')

/-- **The waiter's entry into the condition at count 0 keeps the semaphore's invariant**
(`Move.enter`). -/
theorem Inv.enter (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    (hI : S.Inv G m) (hh : L.ph (G t) = .holds) (hcx : C.ph (G t) = .out)
    (hwt : S.ph (G t) = .wt) (h0 : S.cnt G = 0)
    (hnp : ∀ v, (S.ph (G v)).isPst = false) : S.Inv (upd G t (C.set (G t) .en)) m := by
  have hpv : S.cnt (upd G t (C.set (G t) .en)) = S.cnt G := by rw [pv_cupd, upd_same]
  have hsph : ∀ u, S.ph (upd G t (C.set (G t) .en) u) = S.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, S.ph_cset]
    · rw [upd_ne _ _ e]
  have hlph : ∀ u, L.ph (upd G t (C.set (G t) .en) u) = L.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, lph_c hS]
    · rw [upd_ne _ _ e]
  have hcpt : C.ph (upd G t (C.set (G t) .en) t) = .en := by rw [upd_self, C.ph_set]
  have hcph : ∀ u, u ≠ t → C.ph (upd G t (C.set (G t) .en) u) = C.ph (G u) :=
    fun u e => by rw [upd_ne _ _ e]
  have hTk : ∀ v, S.Tk (upd G t (C.set (G t) .en)) v → v ≠ t ∧ S.Tk G v := fun v hv => by
    by_cases e : v = t
    · subst e; have h2 := hv.2; rw [hcpt] at h2; exact CPh.noConfusion h2
    · exact ⟨e, by rw [← hsph v]; exact hv.1, by rw [← hcph v e]; exact hv.2⟩
  have hmono : ∀ c, L.HB G m c → L.HB (upd G t (C.set (G t) .en)) m c :=
    fun c hc => hc.mono (fun u hu => .inl (by rw [hlph]; exact hu))
      (fun _ => VClock.le_refl _) (fun _ h => h) rfl (fun u hu => by rwa [hlph] at hu)
  refine ⟨fun u hu => hI.ex u (by rw [← hsph u]; exact hu),
    fun u hu => (by rw [hsph, hnp u] at hu; cases hu),
    fun u _ => by rw [hpv]; exact h0, fun u hu => ?_,
    fun _ v _ hv => (by rw [hsph, hnp v] at hv; cases hv),
    fun w hw hk => hI.tq w hw (hTk w.1 hk).2, fun p h0 hp => ?_,
    fun u sh c hu => (by have h1 := hnp u; rw [← hsph u, hu] at h1; cases h1),
    fun u sh c hu => (by have h1 := hnp u; rw [← hsph u, hu] at h1; cases h1),
    fun u sh c hu => (by have h1 := hnp u; rw [← hsph u, hu] at h1; cases h1),
    fun hc => absurd (hpv.trans h0) hc⟩
  · rw [hsph]
    by_cases e : u = t
    · subst e; exact hwt
    · rw [hcph u e] at hu; exact hI.wt u hu
  · rcases hI.hw p h0 hp with h' | h' | ⟨u, hu, hle⟩
    · exact .inl h'
    · exact .inr (.inl (hmono _ h'))
    · by_cases e : u = t
      · subst e; exact .inr (.inl (FLock.HB.of_holder (by rw [hlph]; exact hh) hle))
      · exact .inr (.inr ⟨u, ⟨by rw [hsph]; exact hu.1, by rw [hcph u e]; exact hu.2⟩, hle⟩)

/-- **`S.Inv` with the holder `t` at `pst`** after a change of its ghost value (its client part,
its part, its held resource) with the same memory and the same place: the count may change,
since `t` will signal. -/
theorem Inv.atPst {G G' : ThreadId → γ} {m : Mem} {t : ThreadId} (hI : S.Inv G m)
    (hC : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u) (hh : L.ph (G' t) = .holds)
    (hht : L.ph (G t) = .holds) (hp : S.ph (G' t) = S.ph (G t))
    (hpst : (S.ph (G t)).isPst = true) (hcx : C.ph (G' t) = .out) (hcx0 : C.ph (G t) = .out)
    (hw : L.WInv (L.pl G') m) : S.Inv G' m := by
  have hsph : ∀ u, S.ph (G' u) = S.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; exact hp
    · rw [hG u e]
  have hcph : ∀ u, C.ph (G' u) = C.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [hcx, hcx0]
    · rw [hG u e]
  have hTk : ∀ v, S.Tk G' v ↔ S.Tk G v := fun v => by unfold Tk; rw [hsph, hcph]
  have hhold : ∀ u, L.ph (G u) = .holds → L.ph (G' u) = .holds := fun u hu => by
    by_cases e : u = t
    · subst e; exact hh
    · rw [hG u e]; exact hu
  have hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone := fun u hu => by
    by_cases e : u = t
    · subst e; rw [hht]; decide
    · rwa [hG u e] at hu
  have hmono : ∀ c, L.HB G m c → L.HB G' m c := fun c h =>
    h.mono (fun u hu => .inl (hhold u hu)) (fun _ => VClock.le_refl _) (fun _ h => h) rfl hgone
  have hcrit : ∀ u, (C.ph (G' u)).crit → False := fun u hu => by
    rw [hcph] at hu
    by_cases e : u = t
    · subst e; rw [hcx0] at hu; exact absurd hu (by decide)
    · exact absurd (hw.one u t (by show L.ph (G' u) = _; rw [hG u e]; exact hC.crit u hu) hh) e
  refine ⟨fun u hu => hI.ex u (by rw [← hsph u]; exact hu), fun u hu => ?_,
    fun u hu => absurd hu (fun h' => hcrit u h'),
    fun u hu => (by rw [hsph]; exact hI.wt u (by rw [← hcph u]; exact hu)),
    fun u v hu _ => hcrit u hu,
    fun w hw hk => hI.tq w hw ((hTk _).mp hk), fun p h0 hp => ?_, fun u sh c hu => ?_,
    fun u sh c hu p h0 hp => ?_, fun u sh c hu p h0 hp => ?_,
    fun _ _ => .inr (.inl ⟨t, by rw [hp]; exact hpst⟩)⟩
  · by_cases e : u = t
    · subst e; exact hh
    · rw [hG u e]; rw [hG u e] at hu; exact hI.pst u hu
  · rcases hI.hw p h0 hp with h' | h' | ⟨u, hu, hle⟩
    · exact .inl h'
    · exact .inr (.inl (hmono _ h'))
    · exact .inr (.inr ⟨u, (hTk u).mpr hu, hle⟩)
  · exact hI.sp u sh c (by rw [← hsph u]; exact hu)
  · rcases hI.sb u sh c (by rw [← hsph u]; exact hu) p h0 hp with h' | h' | ⟨v, hv⟩
    · exact .inl h'
    · exact .inr (.inl h')
    · exact .inr (.inr ⟨v, (hTk v).mpr hv⟩)
  · rcases hI.sa u sh c (by rw [← hsph u]; exact hu) p h0 hp with h' | ⟨v, hv⟩
    · exact .inl h'
    · exact .inr ⟨v, (hTk v).mpr hv⟩

/-- **After the signal at `pst`** (module doc): thread `t` at `pst sh sc` and the history post of
its signal for the call's writes `sh'` (which extend `sh`) and clock `sc'` (at least `sc`): with
a registered waiter a signal is pending, or there is a taker. Every write after the history post's
write `k` is a post (`sb`: an older write of the snapshot happened before the call, so `k` is at
or after it; `sa`: a later write is a post), so `signals` did not fall from `k`, where it was at
least `waiters` (served) or positive (a post). -/
theorem Inv.afterSig {G : ThreadId → γ} {m : Mem} {t : ThreadId} {sh sh' : Array Word.Entry}
    {sc sc' : VClock} (hI : S.Inv G m) (ht : S.ph (G t) = .pst sh sc)
    (hpre : ∀ j < sh.size, j < sh'.size ∧ sh'[j]! = sh[j]!) (hcc : VClock.le sc sc' = true)
    (hsig : C.SigPost sh' sc' false m) :
    0 < FCond.wOf (C.lastS m) → 0 < FCond.sOf (C.lastS m) ∨ ∃ v, S.Tk G v := by
  intro hw
  by_cases hk : ∃ v, S.Tk G v
  · exact .inr hk
  left
  obtain ⟨-, k, hkl, hfl, hs⟩ := hsig
  obtain ⟨hpS, -⟩ := hI.sp t sh sc ht
  have hall : ∀ p, k < p → p < (C.S.hist m).size → FCond.SUp (C.S.hist m) p := by
    intro p hkp hp
    by_cases hps : p < sh.size
    · rcases hI.sb t sh sc ht p (by omega) hps with h | h | h
      · exact FCond.SUp.prefix hpS hps h
      · obtain ⟨hp', he⟩ := hpre p hps
        have := hfl p hp' (by rw [he]; exact VClock.le_trans h hcc)
        omega
      · exact absurd h hk
    · exact (hI.sa t sh sc ht p (by omega) hp).resolve_right hk
  obtain ⟨hwk, hsk⟩ := FCond.SUp.chain (C.S.hist m).size hkl hall
  show 0 < FCond.sOf (C.S.hist m)[(C.S.hist m).size - 1]!
  change 0 < FCond.wOf (C.S.hist m)[(C.S.hist m).size - 1]! at hw
  rcases hs with hs | ⟨-, -, hlt⟩
  · unfold FCond.Served at hs; omega
  · omega

/-- **No deadlock at a sleep with permits** (module doc): a registered waiter `t` with no pending
signal, while the count is not 0, has a thread that runs: one at `pst` (it holds the mutex) or a
taker (it sleeps at most at the mutex's futex, which then has a waiter, `Fits.noWaits`). -/
theorem Fits.live (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    (hi : P.inv G m) (ht : (C.ph (G t)).isReg = true) (h0 : FCond.sOf (C.lastS m) = 0)
    (hz : S.cnt G ≠ 0) : P.Live t G m := by
  obtain ⟨rX, hL, hU⟩ := (hS.inv _ m).mp hi
  have hsub := hS.sub _ rX m hU
  have hC := hsub.1.1
  have hI := hsub.2
  have hw : 0 < FCond.wOf (C.lastS m) := by
    obtain ⟨T, hT, hwT, -⟩ := hC.cnt
    rw [hwT]
    have htT : t < T := Nat.lt_of_not_le fun hc => by
      have := hT t hc; rw [this] at ht; cases ht
    have := le_tsum (fun u => if (C.ph (G u)).isReg then 1 else 0) htT
    simp only [ht, ↓reduceIte] at this
    exact Nat.lt_of_lt_of_le Nat.one_pos this
  intro _ hall
  have hnw := hS.noWaits hL hall
  rcases hI.live hz hw with h | ⟨u, hu⟩ | ⟨v, hv⟩
  · omega
  · have huh := hI.pst u hu
    obtain ⟨hut, -⟩ := hL.ht (t := u) (by rw [huh]; decide)
    rcases hall u hut with hf | hq | hj
    · have := hS.fin _ hf; rw [huh] at this; cases this
    · have := hL.w.notQ (t := u) (by show L.ph (G u) ≠ _; rw [huh]; decide)
        (by show L.ph (G u) ≠ _; rw [huh]; decide)
      rw [this] at hq; cases hq
    · have := hS.joins _ hj; rw [huh] at this; cases this
  · have hvt := hI.ex v (by rw [hv.1]; exact SPh.noConfusion)
    rcases hall v hvt with hf | hq | hj
    · have : S.ph (G v) = .out := congrArg Prod.snd (hS.kfin _ hf)
      rw [hv.1] at this; cases this
    · obtain ⟨w, hwm, hwe⟩ := Array.any_eq_true'.mp hq
      have e : w.1 = v := by simpa using hwe
      have hwp := hI.tq w hwm (by rw [e]; exact hv)
      exact hnw (Array.any_eq_true'.mpr ⟨w, hwm, by simp [hwp]⟩)
    · have : S.ph (G v) = .out := congrArg Prod.snd (hS.kjoins _ hj)
      rw [hv.1] at this; cases this

/-- **The holder's move in the semaphore's own code without a memory step** (`Move.hold` with the
same memory, `Go`): the protocol's invariant holds at the new place. -/
theorem Fits.move (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    {g : γ} (s : SPh) (hi : P.inv (upd G t g) m) (hc : m.current = t) (hh : L.ph g = .holds)
    (hcx : C.ph g = .out) (hgo : S.Go (upd G t g) m t s) :
    P.inv (upd G t (S.set g s)) m := by
  obtain ⟨rX, hL, hU⟩ := (hS.inv _ m).mp hi
  have hsub := hS.sub _ rX m hU
  have hfs := FStepIn.refl m (rsum (L.wordR m) rX).heap.erase
  have hg : L.set (upd G t g t) .holds (L.held g) = g := by
    rw [upd_self, ← hh, L.set_self]
  have hcells : ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m.heap l).map Cell.norm = (m.heap l).map Cell.norm := fun _ _ _ _ => rfl
  have hht : L.ph (upd G t g t) = .holds := by rw [upd_self]; exact hh
  have hcxt : C.ph (upd G t g t) = .out := by rw [upd_self]; exact hcx
  have hst : S.prim.Step t (upd G t g) rX m
      (upd (upd G t g) t (S.set (L.set (upd G t g t) .holds (L.held g)) s)) rX m :=
    ⟨Inv.hold hS hsub.2 hsub.1 hht hcxt hL hfs hcells hgo,
      .inr ⟨condHold hS hsub.1.1 hsub.1 hL hht hcxt hfs hcells,
        .hold s (L.held g) hht hcxt hL hc hfs hcells hgo⟩⟩
  rw [hg, upd_upd] at hst
  have hL' : L.Inv (upd G t (S.set g s)) rX m := by
    have := hL.relabel (t := t) (g := S.set g s) (by rw [lph_s hS, upd_self])
      (by rw [lpart_s hS, upd_self]) (by rw [lheld_s hS, upd_self])
      (fun r hr => by
        have := lR_s hS s (upd G t g) t r hr
        rw [upd_self] at this; exact this)
    rwa [upd_upd] at this
  exact (hS.inv _ m).mpr ⟨rX, hL', hS.kstep _ _ _ _ _ _ _ (.inl hst) hU⟩

/-- **A protocol with the semaphore has its condition** (module doc): the condition's contract
(`CondImpl`) applies to it. -/
theorem Fits.toC (hS : S.Fits P U ok) : C.Fits L P U ok where
  win := hS.win
  inv := hS.inv
  fin := hS.fin
  joins := hS.joins
  ok_set := hS.ok_set
  ok_setPart := hS.ok_setPart
  stable := hS.stable
  atStop := hS.atStop
  kfin g h := congrArg Prod.fst (hS.kfin g h)
  kjoins g h := congrArg Prod.fst (hS.kjoins g h)
  sub G rX m h := (hS.sub G rX m h).1
  apart := hS.apart
  lph g p := lph_c hS.toFits g p
  lpart g p := lpart_c hS.toFits g p
  lheld g p := lheld_c hS.toFits g p
  lR G t p r hr := lR_c hS.toFits p G t r hr
  ph_l g q h := cph_l hS.toFits g q h
  set_l g p q h := lset_c hS.toFits g q h p
  ph_part g r := cph_part hS.toFits g r
  set_part g p r := pset_c hS.toFits g r p
  role_l _ g q h := hS.role_l () g q h
  role_part _ g r := hS.role_part () g r
  ok_calm g p q hp hq := by
    by_cases hs : S.ph g = .out ∨ S.ph g = .wt
    · have := hS.ok_calm g (p, S.ph g) (q, S.ph g) ⟨hp, hs⟩ ⟨hq, hs⟩
      rwa [place_c, place_c] at this
    · constructor <;> intro h <;>
        exact absurd (by have := hS.ok_s _ h; rwa [S.ph_cset] at this) hs
  kstep t G rX m G' rX' m' hst hU := by
    rcases hst with hst | htk
    · have hsub := hS.sub G rX m hU
      exact hS.kstep t G rX m G' rX' m'
        (.inl ⟨hsub.2.cstep hS.toFits hsub.1.1 hsub.1 hst, .inl hst⟩) hU
    · exact hS.kstep t G rX m G' rX' m' (.inr htk) hU

/-! ## The rules of a semaphore's code

The steps of a semaphore's code in a protocol with it, once for every protocol and every
implementation (`SemImpl`): the field pointers (`projI`), the lock of `wait` into the semaphore's
wait (`wp_lockWt`), the holder's access to the count that keeps it (`Fits.wp_cnt`), the waiter's
take and the poster's give at the store of the count, which move the holder to `pst` with its
snapshot (`Fits.wp_take`, `Fits.wp_give`), the condition's wait at count 0 and its signal at
`pst` by the condition's contract (`wp_cwait`, `wp_csignal`), the end of `pst` at count 0
(`Fits.unpst`, `Fits.wp_unlockPst`); the `unlock` out of `pst` is the mutex's
(`MutexImpl.unlock_wp_to`). -/

theorem p_block (S : FSem γ X L C) : S.p.block = some L.b := by
  have := congrArg Ptr.block S.ptr_l
  simp only [LockWord.ptr, Ptr.add] at this
  exact this.symm

theorem p_off (S : FSem γ X L C) : S.p.off = (L.o : Int) - 8 := by
  have := congrArg Ptr.off S.ptr_l
  simp only [LockWord.ptr, Ptr.add] at this
  omega

/-- **The semaphore's field pointers** (`&sem.mutex`, `&sem.cond`): the mutex's block is live and
holds them (`LockWord.BlkOk`). -/
theorem projI {K : FPrim γ} (hF : L.Fits K P U ok) {G : ThreadId → γ} {m : Mem}
    (hi : P.inv G m) {k : Int} (h0 : 0 ≤ k) (hk : k ≤ 12) :
    (ptrProject S.p (·.add k)).run m = pure (S.p.add k, m) := by
  obtain ⟨rX, hL, -⟩ := (hF.inv G m).mp hi
  obtain ⟨blk, hblk, -, hsz, -⟩ := hL.w.blk
  have h8 := S.off
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  exact ptrProject_block_run hblk S.p_block (by rw [S.p_off]; omega)
    (by rw [S.p_off]; omega)

/-- **The end of `pst` at count 0** (no signal owed): the holder with the resource `rh` back at
`g`'s place in the semaphore. -/
theorem Fits.unpst (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    {g : γ} {rh : Res} {sh : Array Word.Entry} {sc : VClock}
    (hi : P.inv (upd G t (L.set (S.set g (.pst sh sc)) .holds rh)) m)
    (hc : m.current = t) (hcx : C.ph g = .out) (hgs : S.ph g = .out)
    (h0 : S.cnt (upd G t g) = 0) : P.inv (upd G t (L.set g .holds rh)) m := by
  rw [← lset_s hS] at hi
  have := Fits.move hS .out hi hc (by rw [lph_s hS, L.ph_set])
    (by rw [S.cph_set, cph_l hS]; exact hcx)
    (.inr (.inr (.inr ⟨rfl, by rw [upd_self, S.ph_set]; rfl, fun hne =>
      absurd (by rw [pv_supd, pv_lupd]; exact h0) hne⟩)))
  rwa [S.set_set, ← hgs, ← sph_l hS g .holds rh, S.set_self] at this

/-- **The holder's `unlock` at `pst` at count 0** (no signal owed): the end of `pst`
(`Fits.unpst`), then the `unlock` by the mutex's contract (`MutexImpl.unlock_wp_to`). -/
theorem Fits.wp_unlockPst (mi : MutexImpl Tgt) (hS : L.Fits S.prim P U ok)
    (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr) (hLc : L.c = mi.c) (t : ThreadId) (g : γ)
    (rh : Res) (sh : Array Word.Entry) (sc : VClock) (hgo : L.ph g = .out) (hgh : L.held g = rnil)
    (hcx : C.ph g = .out) (hgs : S.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat) (hi : P.inv (upd G t (L.set (S.set g (.pst sh sc)) .holds rh)) m)
    (hc : m.current = t) (h0 : S.cnt (upd G t g) = 0) :
    P.WP t (mi.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧ P.inv (upd G' t g) m')
      G m d :=
  mi.unlock_wp_to hS hcost hp hLc t g rh hgo hgh hok io G m d (Fits.unpst hS hi hc hcx hgs h0) hc

/-- **`wait`'s lock** by the mutex's contract (`MutexImpl`), into the semaphore's wait (`wt`): the
waiter, out of the semaphore's code, holds the mutex at `wt` (a ghost move, `Go`). -/
theorem wp_lockWt (mi : MutexImpl Tgt) (hS : L.Fits S.prim P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = L.ptr) (hLc : L.c = mi.c) (t : ThreadId) (g : γ) (hgo : L.ph g = .out)
    (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (mi.lock p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set (S.set g .wt) .holds rL)) m') G m d := by
  refine WP.mono (fun _ G' m' d' ⟨hd, hc, rL, hi'⟩ => ⟨hd, hc, rL, ?_⟩)
    (mi.lock_wp hS hcost hp hLc t g hgo hok hu io G m d hi)
  have := Fits.move hS .wt hi' hc (L.ph_set _ _ _) (by rw [cph_l hS]; exact hgx)
    (.inr (.inl ⟨rfl, by rw [upd_self, sph_l hS]; exact hgs⟩))
  rwa [lset_s hS] at this

/-- **The holder's access to the count that keeps it** (a load): the holder `t`, out of the
condition's code, keeps its places; the step's post has the same count and pool (`hR`). -/
theorem Fits.wp_cnt (hS : L.Fits S.prim P U ok) (hcost : P.cost = none) {α : Type}
    {x : MemM α} {G : ThreadId → γ}
    {t : ThreadId} {g : γ} {rL : Res} {m : Mem} {d : Nat} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv (upd G t (L.set g .holds rL)) m) (hc : m.current = t) (hgx : C.ph g = .out)
    (htt : FTTriple (up (pts S.p 8 (S.cnt (upd G t g))) ⋆ S.Pool (S.xs (upd G t g))) x Qa)
    (hR : ∀ a r, Qa a r → (up (pts S.p 8 (S.cnt (upd G t g))) ⋆ S.Pool (S.xs (upd G t g))) r)
    (h : ∀ a m' r, m'.current = t → m'.threads = m.threads → Qa a r →
      P.inv (upd G t (L.set g .holds r)) m' → Q a G m' d) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  have hRe : ∀ r', L.R (upd G t (L.set g .holds r')) =
      (up (pts S.p 8 (S.cnt (upd G t g))) ⋆ S.Pool (S.xs (upd G t g))) := fun r' => by
    rw [R_cnt, pv_lupd, xs_lupd]
  refine hS.wp_hold (G' := upd G t (L.set g .holds rL)) (g' := fun r => L.set g .holds r) hi hc
    (by rw [upd_self, L.ph_set]) htt (fun r hr => by rwa [hRe] at hr)
    (fun a r hq => by
      show L.R (upd (upd G t (L.set g .holds rL)) t (L.set g .holds r)) r
      rw [upd_upd, hRe]; exact hR a r hq)
    (fun r => ⟨L.ph_set _ _ _, by
      show L.part (L.set g .holds r) = L.part (upd G t (L.set g .holds rL) t)
      rw [upd_self, L.part_set, L.part_set], L.held_set _ _ _⟩)
    (fun rX m' r hL hU _ hfs _ hL' => ?_)
    (fun a m' r hc' ht hq hi' => h a m' r hc' ht hq (by rwa [upd_upd] at hi')) (.inr hcost)
  -- `U`: a step of the semaphore's own code that keeps the places
  have hsub := hS.sub _ rX m hU
  have hht : L.ph (upd G t (L.set g .holds rL) t) = .holds := by rw [upd_self, L.ph_set]
  have hcxt : C.ph (upd G t (L.set g .holds rL) t) = .out := by
    rw [upd_self, cph_l hS]; exact hgx
  have hcells := FCond.cells_of_inv hsub.1 hL'
  have hgo : S.Go (upd G t (L.set g .holds rL)) m t (S.ph g) :=
    .inl (by rw [upd_self, sph_l hS])
  have hst : S.prim.Step t (upd G t (L.set g .holds rL)) rX m
      (upd (upd G t (L.set g .holds rL)) t
        (S.set (L.set (upd G t (L.set g .holds rL) t) .holds r) (S.ph g))) rX m' :=
    ⟨Inv.hold hS hsub.2 hsub.1 hht hcxt hL hfs hcells hgo,
      .inr ⟨condHold hS hsub.1.1 hsub.1 hL hht hcxt hfs hcells,
        .hold _ r hht hcxt hL hc hfs hcells hgo⟩⟩
  have hgg : S.set (L.set (upd G t (L.set g .holds rL) t) .holds r) (S.ph g) =
      L.set g .holds r := by
    rw [upd_self, L.set_set, ← sph_l hS g .holds r, S.set_self]
  have := hS.kstep _ _ _ _ _ _ _ (.inl hst) hU
  rw [hgg] at this; exact this

/-- **The holder's step to `pst` with a new ghost value `gf`** (the take and the give, at the
store of the count): a step of the semaphore's own code to `pst` with its snapshot (`Move.hold`,
`Go`: from `PstFrom`, `hsrc`), then the client's move (`hUc`) with both invariants at `gf`. -/
theorem U_pst (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {t : ThreadId} {g gf : γ}
    {rL rX : Res} {m m' : Mem} (hgx : C.ph g = .out) (hsrc : S.PstFrom (upd G t g) t)
    (hfx : C.ph gf = .out)
    (hfs : S.ph gf = .pst (C.S.hist m) (m.clocks[t]!)) (hfh : L.ph gf = .holds)
    (hUc : U (upd G t (S.set (L.set g .holds rL) (.pst (C.S.hist m) (m.clocks[t]!)))) rX m' →
      L.Inv (upd G t gf) rX m' → S.Inv (upd G t gf) m' → C.Inv L (upd G t gf) m' →
      U (upd G t gf) rX m')
    (hL : L.Inv (upd G t (L.set g .holds rL)) rX m) (hU : U (upd G t (L.set g .holds rL)) rX m)
    (hc : m.current = t) (hst : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hL' : L.Inv (upd G t gf) rX m') : U (upd G t gf) rX m' := by
  have hsub := hS.sub _ rX m hU
  have hht : L.ph (upd G t (L.set g .holds rL) t) = .holds := by rw [upd_self, L.ph_set]
  have hcxt : C.ph (upd G t (L.set g .holds rL) t) = .out := by
    rw [upd_self, cph_l hS]; exact hgx
  have hcells := FCond.cells_of_inv hsub.1 hL'
  have hgo : S.Go (upd G t (L.set g .holds rL)) m t (.pst (C.S.hist m) (m.clocks[t]!)) :=
    .inr (.inr (.inl ⟨rfl, by
      unfold PstFrom at hsrc ⊢; rw [upd_self] at hsrc; rw [upd_self, sph_l hS, pv_lupd]; exact hsrc⟩))
  have hgi : upd (upd G t (L.set g .holds rL)) t
      (S.set (L.set (upd G t (L.set g .holds rL) t) .holds rL) (.pst (C.S.hist m) (m.clocks[t]!))) =
      upd G t (S.set (L.set g .holds rL) (.pst (C.S.hist m) (m.clocks[t]!))) := by
    rw [upd_upd, upd_self, L.set_set]
  have hI₁ := Inv.hold (h := rL) hS hsub.2 hsub.1 hht hcxt hL hst hcells hgo
  have hC₁ := condHold (s := .pst (C.S.hist m) (m.clocks[t]!)) (h := rL) hS hsub.1.1 hsub.1 hL
    hht hcxt hst hcells
  have hU₁ := hS.kstep _ _ _ _ _ _ _
    (.inl ⟨hI₁, .inr ⟨hC₁, .hold _ rL hht hcxt hL hc hst hcells hgo⟩⟩) hU
  rw [hgi] at hI₁ hC₁ hU₁
  have hIf : S.Inv (upd G t gf) m' :=
    Inv.atPst hI₁ hC₁ (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
      (by rw [upd_self]; exact hfh) (by rw [upd_self, lph_s hS, L.ph_set])
      (by rw [upd_self, upd_self, hfs, S.ph_set]) (by rw [upd_self, S.ph_set]; rfl)
      (by rw [upd_self]; exact hfx) (by rw [upd_self, S.cph_set, cph_l hS]; exact hgx) hL'.w
  have hCf : C.Inv L (upd G t gf) m' := by
    have hnq : ∀ w ∈ m'.waiters, w.1 ≠ t := FLock.notQ_mem (hL'.w.notQ
      (by show L.ph (upd G t gf t) ≠ _; rw [upd_self, hfh]; decide)
      (by show L.ph (upd G t gf t) ≠ _; rw [upd_self, hfh]; decide))
    have := hC₁.quiet (t := t) (g' := gf) (m' := m')
      (by rw [upd_self, S.cph_set, cph_l hS, hgx]; trivial) (by rw [hfx]; trivial)
      rfl rfl rfl rfl rfl (fun _ => VClock.le_refl _) hnq
      (fun i e h' => by rw [hfx] at h'; cases h') (fun h' => by rw [hfx] at h'; exact absurd h' (by decide))
      (fun h' => absurd hfx h') (fun sh c h' => by rw [hfx] at h'; cases h')
    rwa [upd_upd] at this
  exact hUc hU₁ hL' hIf hCf

/-- **The waiter's take of a permit** at the store of the count (count not 0, `hnz`), from the
semaphore's wait (`wt`): its part gains a resource `r` with `T` from the pool (`hpool`), the count
goes down by one to `gx`'s (`hcnt`, `hR`), and the waiter moves to `pst` with its snapshot and the
client's rest's move (`hU`). The premises `hcnt`, `hpool`, `hU` are `SemImpl`'s wait's; the step's
triple is on the count alone, which is not 0. -/
theorem Fits.wp_take (hS : L.Fits S.prim P U ok) (hcost : P.cost = none) {α : Type}
    {x : MemM α} {G : ThreadId → γ} {t : ThreadId} {g gx : γ} {rL : Res} {m : Mem} {d : Nat}
    {T : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      S.cnt (upd G t gx) = S.cnt (upd G t g) - 1)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → ∀ r, S.Pool (S.xs (upd G t g)) r → (S.Pool (S.xs (upd G t gx)) ⋆ T) r)
    (hU : ∀ G rX m h₁ h₂ r sh sc, S.cnt (upd G t g) ≠ 0 → T r →
      FHeap.Disjoint (L.part g).heap r.heap →
      U (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc))) rX m)
    (hgx : C.ph g = .out) (hxx : C.ph gx = .out)
    (hi : P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m) (hc : m.current = t)
    (hnz : S.cnt (upd G t g) ≠ 0)
    (htt : FTTriple (⟪S.cnt (upd G t g) ≠ 0⟫ ⋆ up (pts S.p 8 (S.cnt (upd G t g)))) x Qa)
    (hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t g) - 1)) r)
    (h : ∀ a m' r rh, m'.current = t → m'.threads = m.threads → (∃ rc, Qa a rc) → T r →
      FHeap.Disjoint (L.part g).heap r.heap → S.cnt (upd G t gx) = S.cnt (upd G t g) - 1 →
      P.inv (upd G t (L.set (S.set (L.setPart gx (rsum (L.part g) r))
        (.pst (C.S.hist m) (m.clocks[t]!))) .holds rh)) m' →
      Q a G m' d) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  have hc₁ := hcnt G rL m hi hnz
  have hpool := hpool G rL m hi hnz
  have htt := FTTriple.conseq htt (fun r h => sep_lift.mpr ⟨hnz, h⟩) (fun _ _ h => h)
  have hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t gx))) r := fun a r hq => by
    rw [hc₁]; exact hR a r hq
  have hpw : L.part (S.set g .wt) = L.part g := lpart_s hS g .wt
  have hcw : C.ph (S.set g .wt) = .out := by rw [S.cph_set]; exact hgx
  refine hS.wp_holdParts (G' := upd G t (L.set (S.set g .wt) .holds rL))
    (Pa := (fun r => r = L.part g) ⋆
      (up (pts S.p 8 (S.cnt (upd G t g))) ⋆ S.Pool (S.xs (upd G t g))))
    (Qp := fun _ rp => ∃ r, T r ∧ FHeap.Disjoint (L.part g).heap r.heap ∧ rp = rsum (L.part g) r)
    (Qh := fun a => Qa a ⋆ S.Pool (S.xs (upd G t gx)))
    (g' := fun rp rh => S.set (L.set (L.setPart gx rp) .holds rh)
      (.pst (C.S.hist m) (m.clocks[t]!)))
    hi hc (by rw [upd_self, L.ph_set]) ?_ ?_ ?_ ?_ ?_ ?_ (.inr hcost)
  · refine FTTriple.conseq ((FTTriple.frame (R := S.Pool (S.xs (upd G t g))) htt).frameL
      (R := fun r => r = L.part g)) (fun _ h => h) (fun a r hq => ?_)
    have h1 := sep_mono_right (fun _ => sep_mono_right hpool) hq
    have h2 := sep_assoc' (sep_mono_right (fun _ h => sep_comm (sep_assoc' h)) h1)
    refine sep_mono_left (fun r' hr' => ?_) h2
    obtain ⟨r₁, r₂, hd, he, rfl, hT⟩ := hr'
    exact ⟨r₂, hT, hd, he⟩
  · intro r hr hd
    rw [upd_self, L.part_set, hpw] at hd ⊢
    rw [R_cnt, pv_lupd, xs_lupd, pv_supd, xs_supd] at hr
    exact ⟨L.part g, r, hd, rfl, rfl, hr⟩
  · intro a rp rh _ hq
    rw [upd_upd, R_cnt, pv_supd, pv_lupd, pv_pupd, xs_supd, xs_lupd, xs_pupd]
    exact sep_mono_left (hR a) hq
  · intro a rp rh _ _
    exact ⟨by rw [lph_s hS, L.ph_set], by rw [lpart_s hS, L.part_set, L.part_setPart],
      by rw [lheld_s hS, L.held_set]⟩
  · rintro _ rX m' rp rh ⟨r, hT, hd, rfl⟩ _ hL hU' _ hfs _ hL'
    rw [upd_upd] at hL' ⊢
    have hsrc : S.set (L.set (S.set g .wt) .holds rL) (.pst (C.S.hist m) (m.clocks[t]!)) =
        S.set (L.set g .holds rL) (.pst (C.S.hist m) (m.clocks[t]!)) := by
      rw [lset_s hS, S.set_set, ← lset_s hS]
    exact U_pst hS hcw (.inr ⟨by rw [upd_self, S.ph_set], by rw [pv_supd]; exact hnz⟩)
      (by rw [S.cph_set, cph_l hS, cph_part hS]; exact hxx) (S.ph_set _ _)
      (by rw [lph_s hS, L.ph_set])
      (fun hU₁ => by rw [hsrc] at hU₁; exact hU G rX m' rL rh r _ _ hnz hT hd hU₁) hL hU' hc hfs hL'
  · rintro a m' rp rh hc' ht ⟨r, hT, hd, rfl⟩ hq hi'
    rw [upd_upd, lset_s hS] at hi'
    obtain ⟨rc, -, -, -, hqa, -⟩ := hq
    exact h a m' r rh hc' ht ⟨rc, hqa⟩ hT hd hc₁ hi'

/-- **The poster's give of a permit** at the store of the count: its part `L.part g` loses `rT`
(`hsplit`) to the pool (`hpool`), the count goes up by one to `gx`'s without overflow (`hcnt`,
`hR`), and the poster moves to `pst` with its snapshot and the client's rest's move (`hU`). The
premises `hsplit`, `hcnt`, `hpool`, `hU` are `SemImpl`'s post's; the step's triple is on the count
alone, whose increment does not overflow. -/
theorem Fits.wp_give (hS : L.Fits S.prim P U ok) (hcost : P.cost = none) {α : Type}
    {x : MemM α} {G : ThreadId → γ} {t : ThreadId} {g gx : γ} {rL rT : Res} {m : Mem} {d : Nat}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r)
    (hU : ∀ G rX m h₁ h₂ sh sc, U (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) rX m)
    (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hxx : C.ph gx = .out)
    (hsplit : L.part g = rsum (L.part gx) rT) (hdj : FHeap.Disjoint (L.part gx).heap rT.heap)
    (hi : P.inv (upd G t (L.set g .holds rL)) m) (hc : m.current = t)
    (htt : FTTriple (⟪(S.cnt (upd G t g)).toNat + 1 < 2 ^ 64⟫ ⋆
      up (pts S.p 8 (S.cnt (upd G t g)))) x Qa)
    (hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t g) + 1)) r)
    (h : ∀ a m' rh, m'.current = t → m'.threads = m.threads → (∃ rc, Qa a rc) →
      P.inv (upd G t (L.set (S.set gx (.pst (C.S.hist m) (m.clocks[t]!))) .holds rh)) m' →
      Q a G m' d) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  obtain ⟨hc₁, hb⟩ := hcnt G rL m hi
  have hpool := hpool G rL m hi
  have htt := FTTriple.conseq htt (fun r h => sep_lift.mpr ⟨hb, h⟩) (fun _ _ h => h)
  have hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t gx))) r := fun a r hq => by
    rw [hc₁]; exact hR a r hq
  refine hS.wp_holdParts (G' := upd G t (L.set g .holds rL))
    (Pa := (fun r => r = L.part gx) ⋆ ((fun r => r = rT) ⋆
      (up (pts S.p 8 (S.cnt (upd G t g))) ⋆ S.Pool (S.xs (upd G t g)))))
    (Qp := fun _ rp => rp = L.part gx) (Qh := fun a => Qa a ⋆ S.Pool (S.xs (upd G t gx)))
    (g' := fun _ rh => S.set (L.set gx .holds rh) (.pst (C.S.hist m) (m.clocks[t]!)))
    hi hc (by rw [upd_self, L.ph_set]) ?_ ?_ ?_ ?_ ?_ ?_ (.inr hcost)
  · refine FTTriple.conseq (((FTTriple.frame (R := S.Pool (S.xs (upd G t g))) htt).frameL
      (R := fun r => r = rT)).frameL (R := fun r => r = L.part gx)) (fun _ h => h)
      (fun a r hq => sep_mono_right (fun r' hr' => sep_mono_right hpool
        (sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' hr')))) hq)
  · intro r hr hd
    rw [upd_self, L.part_set, hsplit] at hd ⊢
    rw [R_cnt, pv_lupd, xs_lupd] at hr
    obtain ⟨d1, d2⟩ := FHeap.disjoint_union_left.mp hd
    rw [rsum_assoc]
    exact ⟨L.part gx, rsum rT r, FHeap.disjoint_union_right.mpr ⟨hdj, d1⟩, rfl, rfl,
      rT, r, d2, rfl, rfl, hr⟩
  · intro a rp rh _ hq
    rw [upd_upd, R_cnt, pv_supd, pv_lupd, xs_supd, xs_lupd]
    exact sep_mono_left (hR a) hq
  · intro a rp rh hp _
    exact ⟨by rw [lph_s hS, L.ph_set], by rw [lpart_s hS, L.part_set]; exact hp.symm,
      by rw [lheld_s hS, L.held_set]⟩
  · intro _ rX m' rp rh _ _ hL hU' _ hfs _ hL'
    rw [upd_upd] at hL' ⊢
    exact U_pst hS hgx (.inl (by rw [upd_self]; exact hgs)) (by rw [S.cph_set, cph_l hS]; exact hxx) (S.ph_set _ _)
      (by rw [lph_s hS, L.ph_set]) (hU G rX m' rL rh _ _) hL hU' hc hfs hL'
  · intro a m' rp rh hc' ht _ hq hi'
    rw [upd_upd, lset_s hS] at hi'
    obtain ⟨rc, -, -, -, hqa, -⟩ := hq
    exact h a m' rh hc' ht ⟨rc, hqa⟩ hi'

/-- **The waiter's wait at the condition at count 0** by the condition's contract (`CondImpl`):
the holder `t` at the semaphore's wait (`wt`), out of the condition's code, at count 0, returns
holding the mutex at the same places. The condition's call keeps its part (`hpre`, `hpost`), fewer
than `65535` waiters are registered at its entry (`hroom`), and its sleep is no deadlock: with
permits a thread at `pst` or a taker runs (`Fits.live`); at count 0 the client shows it
(`hlive`). -/
theorem wp_cwait (ci : CondImpl Tgt) (hS : S.Fits P U ok) (hcost : P.cost = none)
    (hLc : L.c = ci.c) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (t : ThreadId) (g : γ)
    (hgx : C.ph g = .out) (hokg : ok g) (hpre : ci.wait_pre t (L.part g))
    (hpost : ∀ r', ci.wait_post t (L.part g) r' → r' = L.part g)
    (hroom : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set (S.set g .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ T, (∀ u, T ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) T < 65535)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (rL : Res) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m) (hc : m.current = t)
    (h0 : S.cnt (upd G t g) = 0) :
    P.WP t (ci.wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL', P.inv (upd G' t (L.set (S.set g .wt) .holds rL')) m') G m d := by
  have hF := hS.toFits
  have hcw : C.ph (L.set (S.set g .wt) .holds rL) = .out := by
    rw [cph_l hF, S.cph_set]; exact hgx
  have hcph : ∀ u, C.ph (upd G t (L.set (S.set g .wt) .holds rL) u) = C.ph (upd G t g u) :=
    fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self, cph_l hF, S.cph_set]
      · rw [upd_ne _ _ e, upd_ne _ _ e]
  have hpw : L.part (L.set (S.set g .wt) .holds rL) = L.part g := by
    rw [L.part_set, lpart_s hF]
  obtain ⟨rX₀, hL₀, hU₀⟩ := (hS.inv _ m).mp hi
  have hsub₀ := hS.sub _ rX₀ m hU₀
  have hht : L.ph (upd G t (L.set (S.set g .wt) .holds rL) t) = .holds := by
    rw [upd_self, L.ph_set]
  have h0' : S.cnt (upd G t (L.set (S.set g .wt) .holds rL)) = 0 := by
    rw [pv_lupd, pv_supd]; exact h0
  have hnp : ∀ v, (S.ph (upd G t (L.set (S.set g .wt) .holds rL) v)).isPst = false := fun v => by
    by_cases e : v = t
    · subst e; rw [upd_self, sph_l hF, S.ph_set]; rfl
    · exact no_pst hsub₀.2 hL₀ hht v e
  have hent : ∀ rX, U (upd G t (L.set (S.set g .wt) .holds rL)) rX m →
      C.Inv L (upd G t (C.set (L.set (S.set g .wt) .holds rL) .en)) m →
      U (upd G t (C.set (L.set (S.set g .wt) .holds rL) .en)) rX m := by
    -- the entry: a step of the semaphore's own code
    intro rX hU hC'
    have hsub := hS.sub _ rX m hU
    have hcxt : C.ph (upd G t (L.set (S.set g .wt) .holds rL) t) = .out := by
      rw [upd_self]; exact hcw
    have hwt : S.ph (upd G t (L.set (S.set g .wt) .holds rL) t) = .wt := by
      rw [upd_self, sph_l hF, S.ph_set]
    have hst : S.prim.Step t (upd G t (L.set (S.set g .wt) .holds rL)) rX m
        (upd (upd G t (L.set (S.set g .wt) .holds rL)) t
          (C.set (upd G t (L.set (S.set g .wt) .holds rL) t) .en)) rX m :=
      ⟨Inv.enter hF hsub.2 hht hcxt hwt h0' hnp,
        .inr ⟨by rw [upd_upd, upd_self]; exact hC', .enter hht hcxt hwt h0'⟩⟩
    have := hS.kstep _ _ _ _ _ _ _ (.inl hst) hU
    rw [upd_upd, upd_self] at this; exact this
  have hlv : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁ := by
    rintro G₁ m₁ ⟨i, jr, e, hr⟩ haw hi₁ hs0 hns
    by_cases hz : S.cnt G₁ = 0
    · exact hlive G₁ m₁ ⟨i, jr, e, hr⟩ haw hi₁ hs0 hns hz
    · exact Fits.live hF hi₁ (by rw [hr]; rfl) hs0 hz
  refine WP.mono ?_
    (ci.wait_wp_resource (Fits.toC hS) hcost hp hq hLc t (L.set (S.set g .wt) .holds rL) hcw
      (L.ph_set _ _ _) ((hS.ok_set _ _ _).mpr (hS.ok_wt hokg hgx)) io G m d
      (fun T hT => by
        rw [FCond.nreg_congr hcph]
        exact hroom G rL m hi h0 T (fun u hu => by rw [← hcph u]; exact hT u hu))
      hent hlv (by rw [hpw]; exact hpre) hi hc)
  rintro _ G' m' d' ⟨hd, hc', r', rL', hr', hi'⟩
  refine ⟨hd, hc', rL', ?_⟩
  rw [hpw] at hr'
  have := hpost r' hr'
  subst this
  rwa [← hpw, L.setPart_self, L.set_set] at hi'

/-- **The signal at `pst`** by the condition's contract (`CondImpl`), and the end of `pst`: after
the signal (its history post), with permits and a registered waiter a signal is pending or there
is a taker (`Inv.afterSig`, from the snapshot `sh sc`, a prefix of the call's writes below its
clock), so the thread leaves `pst` (`Go`). The signal's ticks are paid from the part (`hu`). -/
theorem wp_csignal (ci : CondImpl Tgt) (hS : S.Fits P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g₀ : γ) (rh : Res) (sh : Array Word.Entry)
    (sc : VClock) (hgx : C.ph g₀ = .out) (hgs : S.ph g₀ = .out)
    (hu : 0 < (L.part g₀).gh.ac.frag .unmetered) (io : Io) (G : ThreadId → γ) (m : Mem)
    (d : Nat) (hi : P.inv (upd G t (L.set (S.set g₀ (.pst sh sc)) .holds rh)) m) :
    P.WP t (ci.signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g₀ .holds rh)) m') G m d := by
  have hF := hS.toFits
  rw [← lset_s hF] at hi
  have hgx' : C.ph (S.set (L.set g₀ .holds rh) (.pst sh sc)) = .out := by
    rw [S.cph_set, cph_l hF]; exact hgx
  have hgh' : L.ph (S.set (L.set g₀ .holds rh) (.pst sh sc)) = .holds := by
    rw [lph_s hF, L.ph_set]
  have hgo : S.set (S.set (L.set g₀ .holds rh) (.pst sh sc)) .out = L.set g₀ .holds rh := by
    rw [S.set_set, ← hgs, ← sph_l hF g₀ .holds rh, S.set_self]
  have hpt : ∀ G' : ThreadId → γ,
      S.ph (upd G' t (S.set (L.set g₀ .holds rh) (.pst sh sc)) t) = .pst sh sc :=
    fun _ => by rw [upd_self, S.ph_set]
  -- the snapshot at the call: a prefix of the call's writes, its clock below the caller's
  obtain ⟨rX, -, hU⟩ := (hS.inv _ m).mp hi
  have hsp := (hS.sub _ rX m hU).2.sp t sh sc (hpt G)
  refine WP.mono (fun _ G' m' d' ⟨hd, hc, hi', hsig⟩ => ⟨hd, hc, ?_⟩)
    (ci.signal_wp (Fits.toC hS) hcost hp t (S.set (L.set g₀ .holds rh) (.pst sh sc)) hgx'
      (.inr hgh') ((S.sx_iff _).mpr (by rw [S.ph_set]; rfl)) io G m d
      (by rw [lpart_s hF, L.part_set]; exact hu) hi)
  rw [← hgo]
  refine Fits.move hF .out hi' hc hgh' hgx'
    (.inr (.inr (.inr ⟨rfl, by rw [hpt]; rfl, fun _ hw => ?_⟩)))
  obtain ⟨rX', -, hU'⟩ := (hS.inv _ m').mp hi'
  exact Inv.afterSig (hS.sub _ rX' m' hU').2 (hpt G')
    (fun j hj => ⟨by have := Word.Prefix.size_le hsp.1; omega, Word.Prefix.get hsp.1 hj⟩)
    hsp.2 hsig hw

end FSem

/-- **A semaphore implementation** in generated code: `wait(sem, io)` and `post(sem, io)` with the
rules that a client uses, for every protocol that keeps the semaphore (`S.Fits P U ok`, with the
condition's window; the mutex's contended value `c`; the mutex at `S.p + 8`, the condition at
`S.p + 12`) and that counts no turns. Any number of threads may wait and post. A thread runs
either op out of the mutex's, the condition's and the semaphore's code, and returns out of them.

- `wait_wp_resource`: the thread takes a permit. Its client part goes from `x g` to `x gx` while
  the count goes down by one (`hcnt`), and a resource `r` with `T` moves from the pool into its
  part (`hpool`: the pool's split); the client's rest allows the move at the store of the count,
  with the moved resource `r` and the count before it not 0 (`hU`, with both invariants after it;
  the thread goes to `pst` with a snapshot). At count 0 it waits at the condition: fewer than
  `65535` waiters are registered at its entry (`hroom`, the condition's `u16` count, as
  `CondImpl.wait_wp`), and its sleep at count 0 with no pending signal and no signaller in the
  condition's code is no deadlock (`hlive`); with permits the semaphore shows it (module doc).
- `post_wp_resource`: the thread gives a permit back. Its part loses `rT` to the pool (`hpool`),
  the count goes up by one without overflow (`hcnt`), and the client's rest allows the move
  (`hU`).

The premises on the count and the pool are for the ghost values of a reachable state in which
the thread holds the mutex. The caller parts follow the mutex and the condition (`LockRules`,
"Caller parts of composite operations"): `wait_pre`/`post_pre` admit the call, `wait_during`/
`post_during` are the parts at the premises' states (the take, the give, the condition's wait),
`wait_post`/`post_post` the returned ones; `post`'s profile is on the part the poster keeps
(`L.part gx`), which pays its ticks. A Plain caller admits `wait` and keeps its part exactly
(`wait_plain_*`), a caller with a positive unmetered fragment admits `post`
(`post_unmetered_*`): `SemImpl.wait_wp` and `SemImpl.post_wp` are derived. The waiter is the
running thread (`m.current = t`), as for `MutexImpl.unlock_wp`. -/
structure SemImpl (Tgt : Type) where
  wait : Ptr → Io → ConcM Tgt Unit
  post : Ptr → Io → ConcM Tgt Unit
  /-- The contended value of the semaphore's mutex. -/
  c : Nat
  wait_pre : ThreadId → FAssn
  wait_during : ThreadId → Res → FAssn
  wait_post : ThreadId → Res → FAssn
  wait_plain_pre : ∀ (t : ThreadId) (r : Res), r.Plain → wait_pre t r
  wait_plain_during : ∀ (t : ThreadId) (r rᵢ : Res), r.Plain → wait_during t r rᵢ → rᵢ = r
  wait_plain_post : ∀ (t : ThreadId) (r r' : Res), r.Plain → wait_post t r r' → r' = r
  post_pre : ThreadId → FAssn
  post_during : ThreadId → Res → FAssn
  post_post : ThreadId → Res → FAssn
  post_unmetered_pre : ∀ (t : ThreadId) (r : Res), 0 < r.gh.ac.frag .unmetered → post_pre t r
  post_unmetered_during : ∀ (t : ThreadId) (r rᵢ : Res), 0 < r.gh.ac.frag .unmetered →
    post_during t r rᵢ → rᵢ = r
  post_unmetered_post : ∀ (t : ThreadId) (r r' : Res), 0 < r.gh.ac.frag .unmetered →
    post_post t r r' → r' = r
  wait_wp_resource : ∀ {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C}
    {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, S.Fits P U ok →
    P.cost = none → L.c = c → ∀ {p : Ptr}, p = S.p →
    ∀ (t : ThreadId) (g gx : γ) (T : FAssn),
    L.ph g = .out → C.ph g = .out → S.ph g = .out → ok g →
    L.ph gx = .out → L.held gx = rnil → C.ph gx = .out → S.ph gx = .out → ok gx →
    (∀ rᵢ, wait_during t (L.part g) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (S.set (L.setPart g rᵢ) .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → S.cnt (upd G t gx) = S.cnt (upd G t g) - 1) →
    (∀ rᵢ, wait_during t (L.part g) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (S.set (L.setPart g rᵢ) .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → ∀ r, S.Pool (S.xs (upd G t g)) r →
      (S.Pool (S.xs (upd G t gx)) ⋆ T) r) →
    (∀ rᵢ, wait_during t (L.part g) rᵢ → ∀ G rX m h₁ h₂ r sh sc, S.cnt (upd G t g) ≠ 0 → T r →
      FHeap.Disjoint rᵢ.heap r.heap →
      U (upd G t (S.set (L.set (L.setPart g rᵢ) .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx (rsum rᵢ r)) .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx (rsum rᵢ r)) .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx (rsum rᵢ r)) .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set (L.setPart gx (rsum rᵢ r)) .holds h₂) (.pst sh sc))) rX m) →
    (∀ rᵢ, wait_during t (L.part g) rᵢ → ∀ G₁ rL m₁,
      P.inv (upd G₁ t (L.set (S.set (L.setPart g rᵢ) .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ T, (∀ u, T ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) T < 65535) →
    (∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), wait_pre t (L.part g) →
    P.inv (upd G t g) m → m.current = t →
    P.WP t (wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r' r,
      wait_post t (L.part g) r' ∧ T r ∧ FHeap.Disjoint r'.heap r.heap ∧
      P.inv (upd G' t (L.setPart gx (rsum r' r))) m') G m d
  post_wp_resource : ∀ {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C}
    {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, S.Fits P U ok →
    P.cost = none → L.c = c → ∀ {p : Ptr}, p = S.p →
    ∀ (t : ThreadId) (g gx : γ) (rT : Res),
    L.ph g = .out → C.ph g = .out → S.ph g = .out → ok g →
    L.ph gx = .out → L.held gx = rnil → C.ph gx = .out → S.ph gx = .out → ok gx →
    L.part g = rsum (L.part gx) rT → FHeap.Disjoint (L.part gx).heap rT.heap →
    (∀ rᵢ, post_during t (L.part gx) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (L.setPart g (rsum rᵢ rT)) .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64) →
    (∀ rᵢ, post_during t (L.part gx) rᵢ → ∀ G rL m,
      P.inv (upd G t (L.set (L.setPart g (rsum rᵢ rT)) .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r) →
    (∀ rᵢ, post_during t (L.part gx) rᵢ → ∀ G rX m h₁ h₂ sh sc,
      U (upd G t (S.set (L.set (L.setPart g (rsum rᵢ rT)) .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set (L.setPart gx rᵢ) .holds h₂) (.pst sh sc))) rX m) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), post_pre t (L.part gx) →
    P.inv (upd G t g) m → m.current = t →
    P.WP t (post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r',
      post_post t (L.part gx) r' ∧ P.inv (upd G' t (L.setPart gx r')) m') G m d

namespace SemImpl

variable {Tgt : Type}

/-- **The wait rule for a Plain caller**: the implementation keeps its part exactly
(`wait_plain_*`), so the premises are at its ghost value `g`. -/
theorem wait_wp (I : SemImpl Tgt) {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C}
    {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}
    (hS : S.Fits P U ok) (hcost : P.cost = none) (hLc : L.c = I.c) {p : Ptr} (hp : p = S.p)
    (t : ThreadId) (g gx : γ) (T : FAssn)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g)
    (hxo : L.ph gx = .out) (hxh : L.held gx = rnil) (hxx : C.ph gx = .out) (hxs : S.ph gx = .out)
    (hokx : ok gx)
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → S.cnt (upd G t gx) = S.cnt (upd G t g) - 1)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set (S.set g .wt) .holds rL)) m →
      S.cnt (upd G t g) ≠ 0 → ∀ r, S.Pool (S.xs (upd G t g)) r →
      (S.Pool (S.xs (upd G t gx)) ⋆ T) r)
    (hU : ∀ G rX m h₁ h₂ r sh sc, S.cnt (upd G t g) ≠ 0 → T r →
      FHeap.Disjoint (L.part g).heap r.heap →
      U (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc)))
        rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc)))
        m →
      U (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) (.pst sh sc))) rX m)
    (hroom : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set (S.set g .wt) .holds rL)) m₁ →
      S.cnt (upd G₁ t g) = 0 → ∀ T, (∀ u, T ≤ u → C.ph (upd G₁ t g u) = .out) →
      C.nreg (upd G₁ t g) T < 65535)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hpl : (L.part g).Plain)
    (hi : P.inv (upd G t g) m) (hc : m.current = t) :
    P.WP t (I.wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r, T r ∧
      FHeap.Disjoint (L.part g).heap r.heap ∧
      P.inv (upd G' t (L.setPart gx (rsum (L.part g) r))) m') G m d := by
  have hd : ∀ rᵢ, I.wait_during t (L.part g) rᵢ → rᵢ = L.part g :=
    fun rᵢ h => I.wait_plain_during t _ rᵢ hpl h
  refine WP.mono ?_ (I.wait_wp_resource hS hcost hLc hp t g gx T hgo hgx hgs hokg hxo hxh hxx
    hxs hokx
    (fun rᵢ h => by rw [hd rᵢ h, L.setPart_self]; exact hcnt)
    (fun rᵢ h => by rw [hd rᵢ h, L.setPart_self]; exact hpool)
    (fun rᵢ h => by rw [hd rᵢ h, L.setPart_self]; exact hU)
    (fun rᵢ h => by rw [hd rᵢ h, L.setPart_self]; exact hroom)
    hlive io G m d (I.wait_plain_pre t _ hpl) hi hc)
  rintro _ G' m' d' ⟨hd', hc', r', r, hr', hT, hdj, hi'⟩
  have := I.wait_plain_post t _ r' hpl hr'
  subst this
  exact ⟨hd', hc', r, hT, hdj, hi'⟩

/-- **The post rule for a caller whose kept part has a positive unmetered fragment** (it pays the
lock's and the signal's ticks): the implementation keeps that part exactly
(`post_unmetered_*`), so the premises are at the ghost value `g`. -/
theorem post_wp (I : SemImpl Tgt) {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C}
    {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}
    (hS : S.Fits P U ok) (hcost : P.cost = none) (hLc : L.c = I.c) {p : Ptr} (hp : p = S.p)
    (t : ThreadId) (g gx : γ) (rT : Res)
    (hgo : L.ph g = .out) (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hokg : ok g)
    (hxo : L.ph gx = .out) (hxh : L.held gx = rnil) (hxx : C.ph gx = .out) (hxs : S.ph gx = .out)
    (hokx : ok gx)
    (hsplit : L.part g = rsum (L.part gx) rT) (hdj : FHeap.Disjoint (L.part gx).heap rT.heap)
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r)
    (hU : ∀ G rX m h₁ h₂ sh sc, U (upd G t (S.set (L.set g .holds h₁) (.pst sh sc))) rX m →
      L.Inv (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) rX m →
      S.Inv (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) m →
      C.Inv L (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) m →
      U (upd G t (S.set (L.set gx .holds h₂) (.pst sh sc))) rX m)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : 0 < (L.part gx).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m)
    (hc : m.current = t) :
    P.WP t (I.post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t gx) m')
      G m d := by
  have hd : ∀ rᵢ, I.post_during t (L.part gx) rᵢ → rᵢ = L.part gx :=
    fun rᵢ h => I.post_unmetered_during t _ rᵢ hu h
  have hg : L.setPart g (rsum (L.part gx) rT) = g := by rw [← hsplit, L.setPart_self]
  refine WP.mono ?_ (I.post_wp_resource hS hcost hLc hp t g gx rT hgo hgx hgs hokg hxo hxh hxx
    hxs hokx hsplit hdj
    (fun rᵢ h => by rw [hd rᵢ h, hg]; exact hcnt)
    (fun rᵢ h => by rw [hd rᵢ h, hg]; exact hpool)
    (fun rᵢ h => by rw [hd rᵢ h, hg, L.setPart_self]; exact hU)
    io G m d (I.post_unmetered_pre t _ hu) hi hc)
  rintro _ G' m' d' ⟨hd', hc', r', hr', hi'⟩
  have := I.post_unmetered_post t _ r' hu hr'
  subst this
  exact ⟨hd', hc', by rwa [L.setPart_self] at hi'⟩

end SemImpl

end Full
end Zig
