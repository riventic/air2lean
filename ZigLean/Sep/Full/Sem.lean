import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.Mutex

/-!
# The semaphore, over full-state resources

A semaphore (`Io.Semaphore`'s `waitUncancelable` and `post`, the same code in 0.16.0 and 0.17.0,
translated from its std code; the futex under it is the model) is a permit count, a mutex and a condition next to it: `wait` locks the mutex,
waits at the condition while the count is 0, takes a permit (`count -= 1`), signals the
condition if permits are left, and unlocks; `post` locks, gives a permit back (`count += 1`),
signals and unlocks. This module is the component once for every protocol that has such a
semaphore (`FSem`, its primitive `FSem.prim` next to the mutex), and the contract of a
semaphore's code (`SemImpl`); an implementation of a Zig version walks its code with the rules of
its mutex and condition (`MutexImpl`, `CondImpl`).

- **The semaphore** (`FSem γ L C`): the mutex `L` owns the count (`pv`, a function of the threads'
  ghost values) and the resource of the free permits (`Pool`): `L.R G = count ⋆ Pool G`. A
  thread's place in the semaphore's own code is `SPh`: `pst` from the store of the count to the
  end of its signal, holding the mutex. The condition's signallers are exactly the threads at `pst`
  (`sx_iff`): a semaphore signals while it holds the mutex.
- **The invariant** (`FSem.Inv`), next to the condition's (`FCond.Inv`): a thread at `pst` holds
  the mutex; a thread in the condition's critical code saw the count 0; every write of the epoch
  and every waiter's registration happened before the mutex's holder, before the newest release
  of the mutex, or before every thread that has not ended (`FLock.HB`); and while a registered
  waiter is not signalled the count is 0 or a thread at `pst` will signal it (no lost wakeup).
- **The primitive** (`FSem.prim`): the condition's places with the semaphore's, the condition's
  steps (`FCond.prim`) and the semaphore's own steps (`Move`: the waiter's entry into the
  condition at count 0; the holder's step on the mutex's resource, a load or store of the count,
  with its move to or from `pst`), each with both invariants after it. A protocol with the
  semaphore is `L.Fits S.prim P U ok`; it has the condition (`Fits.toC`), so the condition's
  contract applies to it.

**Scope (one waiter).** The condition's contract admits one waiter at a time (`CondImpl`, the
module doc of `ZigLean/Sep/Full/Cond.lean`): `SemImpl.wait_wp` asks the client, as the legacy
`Sem.wait_spec` did, that no other thread is registered at the condition while the waiter holds
the mutex at count 0 (`hone`). `hone` is the condition's one-waiter workaround, removed with it
(engine ledger `seen-floor-sync-retirement`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- Where a thread is in the semaphore's own code (module doc). -/
inductive SPh where
  | out
  | pst
  deriving DecidableEq

namespace FLock

variable {γ : Type} (L : FLock γ)

/-- The clock `c` happened before the lock's holder, before the release clock of the newest
message of the lock's word, or before every thread that has not ended. -/
def HB (G : ThreadId → γ) (m : Mem) (c : VClock) : Prop :=
  (∃ u, L.ph (G u) = .holds ∧ VClock.le c (m.clocks[u]!) = true) ∨ L.Before m c ∨
    LockWord.LiveLe (L.pl G) m c

variable {L}

/-- A clock that happened before the lock's holder `t` (with the word's invariant). -/
theorem HB.le {G : ThreadId → γ} {m : Mem} {c : VClock} (hw : L.WInv (L.pl G) m)
    (h : L.HB G m c) {t : ThreadId} (ht : L.ph (G t) = .holds) :
    VClock.le c (m.clocks[t]!) = true := by
  rcases h with ⟨u, hu, hle⟩ | ⟨i, l, hl, hle⟩ | hlive
  · obtain rfl := hw.one u t hu ht; exact hle
  · exact VClock.le_trans hle ((hw.rel i l hl).2 t ht)
  · exact hlive t (hw.live t (by show L.ph (G t) ≠ .gone; rw [ht]; decide)).1
      (by show L.ph (G t) ≠ .gone; rw [ht]; decide)

/-- A clock below `c'`. -/
theorem HB.of_le {G : ThreadId → γ} {m : Mem} {c c' : VClock} (h : L.HB G m c')
    (hle : VClock.le c c' = true) : L.HB G m c := by
  rcases h with ⟨u, hu, h'⟩ | hb | hlive
  · exact .inl ⟨u, hu, VClock.le_trans hle h'⟩
  · exact .inr (.inl (L.before_le hb hle))
  · exact .inr (.inr (LockWord.LiveLe.le hle hlive))

/-- **`HB` stays** over a step that keeps the holders (or releases with the release fact), grows
the clocks, keeps the word's newest release and the threads that have not ended. -/
theorem HB.mono {G G' : ThreadId → γ} {m m' : Mem} {c : VClock} (h : L.HB G m c)
    (hhold : ∀ u, L.ph (G u) = .holds → L.ph (G' u) = .holds ∨
      ∀ c, VClock.le c (m.clocks[u]!) = true → L.Before m' c)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) (ht : m'.threads = m.threads)
    (hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone) : L.HB G' m' c := by
  rcases h with ⟨u, hu, hle⟩ | hb | hlive
  · rcases hhold u hu with h' | hrel
    · exact .inl ⟨u, h', VClock.le_trans hle (hcl u)⟩
    · exact .inr (.inl (hrel c hle))
  · exact .inr (.inl (hbef c hb))
  · exact .inr (.inr (fun u hu hg =>
      VClock.le_trans (hlive u (ht ▸ hu) (hgone u hg)) (hcl u)))

/-- A clock that happened before thread `t`, which holds the lock. -/
theorem HB.of_holder {G : ThreadId → γ} {m : Mem} {c : VClock} {t : ThreadId}
    (ht : L.ph (G t) = .holds) (hle : VClock.le c (m.clocks[t]!) = true) : L.HB G m c :=
  .inl ⟨t, ht, hle⟩

end FLock

/-- **Two typed values at the same pointer of one resource are the same**: their bytes are the
resource's cells there. -/
theorem pts_agree {T : Type} [Enc T] {p : Ptr} {a a' : Nat} {v v' : T} {A B : FAssn} {r : Res}
    (h : (up (pts p a v) ⋆ A) r) (h' : (up (pts p a' v') ⋆ B) r) : v = v' := by
  have key : ∀ {a : Nat} {v : T} {A : FAssn}, (up (pts p a v) ⋆ A) r → ∃ bs b,
      p.block = some b ∧ bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧
      ∀ j < bs.size, ∃ fc, r.heap (b, p.off.toNat + j) = some fc ∧ fc.cell.byte = bs[j]! := by
    intro a v A hA
    obtain ⟨r₁, r₂, -, hr, h₁, -⟩ := hA
    obtain ⟨A', S', K', bs, ⟨-, hs, hv, -⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp h₁
    obtain ⟨⟨b, hpb, -⟩, -, -⟩ := id hb
    refine ⟨bs, b, hpb, hs, hv, fun j hj => ?_⟩
    obtain ⟨fc, hfc, hcell⟩ := up_bytesAt_cell hb hpb hj
    refine ⟨fc, ?_, by rw [hcell]⟩
    rw [hr]; show (r₁.heap _).or _ = _; rw [hfc]; rfl
  obtain ⟨bs, b, hpb, hs, hv, hc⟩ := key h
  obtain ⟨bs', b', hpb', hs', hv', hc'⟩ := key h'
  rw [hpb] at hpb'; cases hpb'
  have hbs : bs = bs' := Array.ext (by rw [hs, hs']) fun j hj hj' => by
    obtain ⟨fc, h1, h2⟩ := hc j hj
    obtain ⟨fc', h1', h2'⟩ := hc' j hj'
    rw [h1] at h1'; cases h1'
    rw [← getElem!_pos bs j hj, ← getElem!_pos bs' j hj', ← h2, ← h2']
  subst hbs
  have e := hv.symm.trans hv'
  simp only [pure, ExceptT.pure, ExceptT.mk] at e
  exact Except.ok.inj (Option.some.inj e)

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
  sx_iff : ∀ g, C.sx g ↔ ph g = .pst

namespace FSem

variable {γ X : Type} {L : FLock γ} {C : FCond γ} (S : FSem γ X L C)

/-- The client's parts of the ghost values. -/
def xs (G : ThreadId → γ) : ThreadId → X := fun u => S.x (G u)

/-- The count. -/
def cnt (G : ThreadId → γ) : BitVec 64 := S.pv (S.xs G)

theorem R_cnt (G : ThreadId → γ) : L.R G = (up (pts S.p 8 (S.cnt G)) ⋆ S.Pool (S.xs G)) :=
  S.R_eq G

/-- The semaphore's invariant (module doc). -/
structure Inv (G : ThreadId → γ) (m : Mem) : Prop where
  pst : ∀ u, S.ph (G u) = .pst → L.ph (G u) = .holds
  crit : ∀ u, (C.ph (G u)).crit → S.cnt G = 0
  hbE : ∀ j < (C.Ep.hist m).size, L.HB G m (C.Ep.hist m)[j]!.clock
  hbR : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → L.HB G m (C.S.hist m)[jr]!.clock
  pz : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → (C.S.hist m).size = jr + 1 →
    S.cnt G = 0 ∨ ∃ v, S.ph (G v) = .pst
  /-- A thread at `pst` does not wait at the condition, and no thread is in the condition's
  critical code meanwhile (both would hold the mutex). -/
  pw : ∀ u, S.ph (G u) = .pst → (C.ph (G u)).waits = false
  cp : ∀ u v, (C.ph (G u)).crit → S.ph (G v) = .pst → False
  /-- Every registration happened before every thread at `pst` (its signal's `hseen`). -/
  rp : ∀ u v i jr sn e, C.ph (G u) = .reg i jr sn e → S.ph (G v) = .pst →
    VClock.le (C.S.hist m)[jr]!.clock (m.clocks[v]!) = true

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

/-- The steps of the semaphore's own code by thread `t` (module doc): the entry of the waiter
into the condition's wait at count 0, and a step of the holder on the mutex's resource (a load or
a store of the count; `FStepIn` with the mutex's word and the rest in its frame, which keeps the
condition's cells) or its move to or from `pst` (the same memory). A move from `pst`
to `out` comes after the signal: then a registered waiter that was not signalled sees the count
0. -/
inductive Move (t : ThreadId) (G : ThreadId → γ) (rX : Res) (m : Mem) :
    (ThreadId → γ) → Res → Mem → Prop
  | enter : L.ph (G t) = .holds → C.ph (G t) = .out → S.cnt G = 0 →
      (∀ v, S.ph (G v) ≠ .pst) → Move t G rX m (upd G t (C.set (G t) .en)) rX m
  | hold {m' : Mem} (s : SPh) (h : Res) : L.ph (G t) = .holds → C.ph (G t) = .out →
      L.Inv G rX m → m.current = t → FStepIn (rsum (L.wordR m) rX).heap.erase m m' →
      (∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
        (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) →
      (S.ph (G t) = .pst → s = .out → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
        (C.S.hist m).size = jr + 1 → S.cnt G = 0) →
      Move t G rX m (upd G t (S.set (L.set (G t) .holds h) s)) rX m'

/-- **The semaphore as a primitive next to its mutex `L`** (module doc; a protocol keeps it:
`L.Fits S.prim P U ok`). Its places are the condition's with the semaphore's; the calm places
are those out of the condition's busy code and out of the semaphore's own code; the role is the
condition's `sx`; the rest keeps the condition (`FCond.prim`'s `Sub`) and the semaphore's
invariant; a step is a step of the condition's code, with both invariants after it, or of the
semaphore's own code (`Move`), with the condition's invariant and the semaphore's after it (the
rest's cells of the words after a step of the holder are the protocol's to show, as after a step
of the lock's code). -/
abbrev prim : FPrim γ where
  Ph := CPh × SPh
  pl := S.place
  out := (.out, .out)
  calm q := q.1.busy = false ∧ q.2 = .out
  Role := Unit
  role _ g := C.sx g
  Sub G rX m := (C.prim L).Sub G rX m ∧ S.Inv G m
  Apart := (C.prim L).Apart
  Step t G rX m G' rX' m' := S.Inv G' m' ∧ ((C.prim L).Step t G rX m G' rX' m' ∨
    (C.Inv L G' m' ∧ S.Move t G rX m G' rX' m'))

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

/-- **`S.Inv` stays** over a step that keeps every thread's semaphore place, the count, the
holders, the threads that have not ended and the writes of both words, and grows the clocks. -/
theorem Inv.mono {G G' : ThreadId → γ} {m m' : Mem} (hI : S.Inv G m)
    (hsph : ∀ u, S.ph (G' u) = S.ph (G u)) (hcph : ∀ u, C.ph (G' u) = C.ph (G u))
    (hpv : S.cnt G' = S.cnt G)
    (hhold : ∀ u, L.ph (G u) = .holds → L.ph (G' u) = .holds)
    (hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) (ht : m'.threads = m.threads)
    (hgone : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone)
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m) : S.Inv G' m' where
  pst u h := hhold u (hI.pst u (by rw [← hsph u]; exact h))
  crit u h := by rw [hpv]; exact hI.crit u (by rw [← hcph u]; exact h)
  hbE j hj := by
    rw [hE] at hj ⊢
    exact (hI.hbE j hj).mono (fun u hu => .inl (hhold u hu)) hcl hbef ht hgone
  hbR u i jr sn e h := by
    rw [hS]
    exact (hI.hbR u i jr sn e (by rw [← hcph u]; exact h)).mono (fun u hu => .inl (hhold u hu))
      hcl hbef ht hgone
  pz u i jr sn e h hs := by
    rw [hS] at hs
    rcases hI.pz u i jr sn e (by rw [← hcph u]; exact h) hs with h' | ⟨v, hv⟩
    · exact .inl (by rw [hpv]; exact h')
    · exact .inr ⟨v, by rw [hsph v]; exact hv⟩
  pw u h := by rw [hcph]; exact hI.pw u (by rw [← hsph u]; exact h)
  cp u v hu hv := hI.cp u v (by rw [← hcph u]; exact hu) (by rw [← hsph v]; exact hv)
  rp u v i jr sn e hu hv := by
    rw [hS]
    exact VClock.le_trans (hI.rp u v i jr sn e (by rw [← hcph u]; exact hu)
      (by rw [← hsph v]; exact hv)) (hcl v)

/-- A step of the code into a registration comes from the critical code or from the same
registration. -/
theorem _root_.Zig.Full.CPh.Next.to_reg {a : CPh} {i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : CPh.Next a (.reg i jr sn e)) :
    (∃ i' e', a = .ld i' e') ∨ ∃ sn', a = .reg i jr sn' e := by
  cases a with
  | ld i' e' => exact .inl ⟨i', e', rfl⟩
  | reg i' jr' sn' e' =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .inr ⟨sn', rfl⟩
  | _ => simp [CPh.Next] at h

/-- A cell of a word is not a cell of a word apart from it. -/
theorem notIn_apart {V W : Word 32 4} (h : W.b ≠ V.b ∨ W.o + 4 ≤ V.o ∨ V.o + 4 ≤ W.o)
    {l : Zig.Loc} (hl : V.In l) : ¬ W.In l := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨h1', h2', h3'⟩ := hl
  rcases h with h | h | h
  · exact h (h1.symm.trans h1')
  · have : W.o + 4 ≤ V.o := h
    have h3 : l.2 < W.o + 4 := h3
    have h2' : V.o ≤ l.2 := h2'
    omega
  · have : V.o + 4 ≤ W.o := h
    have h3' : l.2 < V.o + 4 := h3'
    have h2 : W.o ≤ l.2 := h2
    omega

/-- The two words of the condition apart or the same. -/
theorem words_apart {V W : Word 32 4} (hV : V = C.S ∨ V = C.Ep) (hW : W = C.S ∨ W = C.Ep) :
    V = W ∨ W.b ≠ V.b ∨ W.o + 4 ≤ V.o ∨ V.o + 4 ≤ W.o := by
  have hb := C.ep_b; have ho := C.ep_o
  rcases hV with rfl | rfl <;> rcases hW with rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr (.inr (by omega)))
  · exact .inr (.inr (.inl (by omega)))
  · exact .inl rfl

/-- **A step of the condition's code keeps the semaphore's invariant** (for `Fits.toC`). -/
theorem Inv.cstep (hS : L.Fits S.prim P U ok) {G G' : ThreadId → γ} {rX rX' : Res}
    {m m' : Mem} {t : ThreadId} (hI : S.Inv G m) (hC : C.Inv L G m)
    (hsub : (C.prim L).Sub G rX m) (hst : (C.prim L).Step t G rX m G' rX' m') :
    S.Inv G' m' := by
  have hap : ∀ W, (W = C.S ∨ W = C.Ep) → W.ApartL L.toLockWord := hS.apart
  obtain ⟨W, rY, hW, rfl, rfl, hY, hC', hmv | hown⟩ := hst
  · obtain ⟨p, q, h, ⟨hn, hq, hms, hEp⟩, rfl⟩ := hmv
    have hqh : L.ph (G t) = .holds → q = .holds := fun hh => by
      rcases hq with ⟨rfl, -⟩ | ⟨ho, -, -⟩
      · exact hh
      · rw [hh] at ho; rcases ho with ho | ho <;> cases ho
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
        · rcases ho with ho | ho <;> rw [ho] <;> decide
      · rwa [upd_ne _ _ e] at hu
    have hbef : ∀ c, L.Before m c → L.Before m' c := fun _ ⟨i, l, hl, hc⟩ =>
      ⟨i, l, hms.lockLoc (hap W hW) (hap C.Ep (.inr rfl)) hl, hc⟩
    have hmono : ∀ c, L.HB G m c → L.HB (upd G t (L.set (C.set (G t) p) q h)) m' c :=
      fun c hc => hc.mono (fun u hu => .inl (hhold u hu)) hms.clocks hbef hms.threads hgone
    have hword : ∀ V, (V = C.S ∨ V = C.Ep) → V.hist m' = V.hist m ∨
        (V = W ∧ ∃ x, V.hist m' = (V.hist m).push x ∧ x.clock = m'.clocks[t]!) := fun V hV =>
      (hms.word_clock (hsub.2 V hV).1 (words_apart hV hW) (words_apart hV (.inr rfl))).2
    have hcpt : C.ph (upd G t (L.set (C.set (G t) p) q h) t) = p := by
      rw [upd_self, cph_l hS, C.ph_set]
    have hcph : ∀ u, u ≠ t → C.ph (upd G t (L.set (C.set (G t) p) q h) u) = C.ph (G u) :=
      fun u e => by rw [upd_ne _ _ e]
    -- the stepping thread holds the lock afterwards if it held it
    refine ⟨fun u hu => hhold u (hI.pst u (by rw [← hsph u]; exact hu)), fun u hu => ?_,
      fun j hj => ?_, fun u i jr sn e hu => ?_, fun u i jr sn e hu hsz => ?_,
      fun u hu => ?_, fun u v hu hv => ?_, fun u v i jr sn e hu hv => ?_⟩
    rotate_left 4
    · -- pw
      rw [hsph] at hu
      by_cases e : u = t
      · subst e; rw [hcpt]
        cases hp : p.waits
        · rfl
        · have := hn.waits hp; rw [hI.pw u hu] at this; cases this
      · rw [hcph u e]; exact hI.pw u hu
    · -- cp
      rw [hsph] at hv
      by_cases e : u = t
      · subst e; rw [hcpt] at hu; exact hI.cp u v (hn.crit hu) hv
      · rw [hcph u e] at hu; exact hI.cp u v hu hv
    · -- rp
      rw [hsph] at hv
      have hold : ∀ i' sn' e', C.ph (G u) = .reg i' jr sn' e' →
          VClock.le (C.S.hist m')[jr]!.clock (m'.clocks[v]!) = true := by
        intro i' sn' e' hr
        have hlt : jr < (C.S.hist m).size := by
          rcases (hC.era u i' jr sn' e' hr).ssz with h1 | h1 <;> omega
        have h0 := VClock.le_trans (hI.rp u v i' jr sn' e' hr hv) (hms.clocks v)
        rcases hword C.S (.inl rfl) with hs | ⟨-, x, hs, -⟩
        · rw [hs]; exact h0
        · rw [hs, FEvent.get_push_lt hlt]; exact h0
      by_cases e' : u = t
      · subst e'
        rw [hcpt] at hu; subst hu
        rcases hn.to_reg with ⟨i', e'', hld⟩ | ⟨sn', hr⟩
        · exact absurd hv (fun hv => hI.cp u v (by rw [hld]; rfl) hv)
        · exact hold i sn' e hr
      · rw [hcph u e'] at hu; exact hold i sn e hu
    · -- crit
      rw [hpv]
      by_cases e : u = t
      · subst e; rw [hcpt] at hu; exact hI.crit u (hn.crit hu)
      · rw [upd_ne _ _ e] at hu; exact hI.crit u hu
    · -- the epoch's writes
      rcases hword C.Ep (.inr rfl) with he | ⟨-, x, he, hx⟩
      · rw [he] at hj ⊢; exact hmono _ (hI.hbE j hj)
      · rw [he] at hj ⊢
        rw [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [FEvent.get_push_lt hj]; exact hmono _ (hI.hbE j hj)
        · rw [FEvent.get_push_eq, hx]
          have hinc : C.ph (G t) = .inc := by
            rcases hEp with he' | he'
            · have := congrArg Array.size (he.symm.trans he')
              rw [Array.size_push] at this; omega
            · exact he'
          have hpst : S.ph (G t) = .pst :=
            (S.sx_iff _).mp (hC.sx t (by rw [hinc]; rfl))
          exact FLock.HB.of_holder (hhold t (hI.pst t hpst)) (VClock.le_refl _)
    · -- the registrations
      have hold : ∀ i' sn' e', C.ph (G u) = .reg i' jr sn' e' →
          L.HB (upd G t (L.set (C.set (G t) p) q h)) m' (C.S.hist m')[jr]!.clock := by
        intro i' sn' e' hr
        have hlt : jr < (C.S.hist m).size := by
          rcases (hC.era u i' jr sn' e' hr).ssz with h1 | h1 <;> omega
        rcases hword C.S (.inl rfl) with hs | ⟨-, x, hs, -⟩
        · rw [hs]; exact hmono _ (hI.hbR u i' jr sn' e' hr)
        · rw [hs, FEvent.get_push_lt hlt]; exact hmono _ (hI.hbR u i' jr sn' e' hr)
      by_cases e' : u = t
      · subst e'
        rw [hcpt] at hu; subst hu
        rcases hn.to_reg with ⟨i', e'', hld⟩ | ⟨sn', hr⟩
        · -- the registration: `t` holds the mutex (critical code)
          have hh : L.ph (G u) = .holds := hC.crit u (by rw [hld]; rfl)
          refine FLock.HB.of_holder (hhold u hh) ?_
          exact (hC'.era u i jr sn e hcpt).cs
        · exact hold i sn' e hr
      · rw [upd_ne _ _ e'] at hu; exact hold i sn e hu
    · -- a registered waiter that is not signalled
      have hsz' : ∀ i' sn' e', C.ph (G u) = .reg i' jr sn' e' → (C.S.hist m).size = jr + 1 := by
        intro i' sn' e' hr
        have h1 := (hC.era u i' jr sn' e' hr).ssz
        rcases hword C.S (.inl rfl) with hs | ⟨-, x, hs, -⟩
        · rw [hs] at hsz; exact hsz
        · rw [hs, Array.size_push] at hsz; omega
      have hold : ∀ i' sn' e', C.ph (G u) = .reg i' jr sn' e' →
          S.cnt (upd G t (L.set (C.set (G t) p) q h)) = 0 ∨
            ∃ v, S.ph (upd G t (L.set (C.set (G t) p) q h) v) = .pst := by
        intro i' sn' e' hr
        rcases hI.pz u i' jr sn' e' hr (hsz' i' sn' e' hr) with h0 | ⟨v, hv⟩
        · exact .inl (by rw [hpv]; exact h0)
        · exact .inr ⟨v, by rw [hsph v]; exact hv⟩
      by_cases e' : u = t
      · subst e'
        rw [hcpt] at hu; subst hu
        rcases hn.to_reg with ⟨i', e'', hld⟩ | ⟨sn', hr⟩
        · exact .inl (by rw [hpv]; exact hI.crit u (by rw [hld]; rfl))
        · exact hold i sn' e hr
      · rw [upd_ne _ _ e'] at hu; exact hold i sn e hu
  · obtain ⟨r, -, hL0, hc, hfs, hcW, -, hh, hL', rfl⟩ := hown
    have hY' : ∀ V, (V = C.S ∨ V = C.Ep) → V.hist m' = V.hist m := by
      intro V hV
      rcases words_apart hV hW with rfl | hapW
      · exact hh
      · obtain ⟨hwV, rV, hrV, -⟩ := hsub.2 V hV
        have hcell : ∀ l, V.In l → ∃ fc, (rsum (W.cellsR m) rY).heap l = some fc ∧
            rY.heap l = some fc := by
          intro l hl
          have hnW : ¬ W.In l := notIn_apart hapW hl
          have hsome : (rsum (W.cellsR m) rY).heap l ≠ none := by
            rw [hrV]; simp only [rsum, FHeap.union_apply, Word.cellsR]
            have := cellsAt_some (W := V.In) hl (hwV.cellIn hl) (m := m)
            cases e : (cellsAt V.In m).heap l <;> simp_all
          have heq : (rsum (W.cellsR m) rY).heap l = rY.heap l := by
            simp only [rsum, FHeap.union_apply, Word.cellsR, cellsAt_none hnW, Option.none_or]
          cases e : (rsum (W.cellsR m) rY).heap l with
          | none => exact absurd e hsome
          | some fc => exact ⟨fc, rfl, heq ▸ e⟩
        refine Word.hist_fstep hwV hfs (fun l hl => ?_) (fun l hl => ?_)
        · obtain ⟨fc, -, hy⟩ := hcell l hl
          simp [rsum, FHeap.erase, FHeap.union_apply, hy]
        · obtain ⟨fc, hfc, hy⟩ := hcell l hl
          have hnW : (W.cellsR m').heap l = none := cellsAt_none (notIn_apart hapW hl)
          have h' : (rsum (W.cellsR m') rY).heap l = some fc := by
            simp only [rsum, FHeap.union_apply, hnW, Option.none_or, hy]
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
    have hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hfs.clock
    have hbef : ∀ c, L.Before m c → L.Before m' c := by
      rintro c ⟨i, l, hl, hle⟩
      obtain ⟨i', hl'⟩ := (LockWord.loc_fstep (L := L.toLockWord) hfs
        (fun x h1 h2 => by
          have := LockWord.wordR_some hL0.w.blk (L := L.toLockWord) (l := (L.b, x)) ⟨rfl, h1, h2⟩
          simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
            Option.or_eq_none_iff, not_and]
          intro h; exact absurd h this)
        (fun i l hl => (hL0.w.loc.ok i l hl).1) l).mpr ⟨i, hl⟩
      exact ⟨i', l, hl', hle⟩
    exact hI.mono hsph hcph (by rw [pv_pupd, upd_same]) (fun u hu => by rw [hlph]; exact hu) hcl hbef
      hfs.threads (fun u hu => by rwa [hlph] at hu) (hY' C.S (.inl rfl)) (hY' C.Ep (.inr rfl))

/-- **A lock step of a thread out of the condition's busy code and the semaphore's code** keeps
the semaphore's invariant (for a client's `FLock.Fits.stable`, whose `ok` excludes them). -/
theorem Inv.lstep (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {q : LPh} {h : Res} (hI : S.Inv G m) (hsub : (C.prim L).Sub G rX m)
    (hb : (C.ph (G t)).busy = false) (hst : S.ph (G t) = .out) (hg : L.ph (G t) ≠ .gone)
    (hs : L.Step t m m') (hrel : L.ph (G t) = .holds → q ≠ .holds → L.Before m' (m.clocks[t]!)) :
    S.Inv (upd G t (L.set (G t) q h)) m' := by
  have hap : ∀ W, (W = C.S ∨ W = C.Ep) → W.ApartL L.toLockWord := hS.apart
  have hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hs.clocks
  have hnc : (C.ph (G t)).crit = false := by
    unfold CPh.busy at hb; revert hb; cases (C.ph (G t)).crit <;> simp
  have hsph : ∀ u, S.ph (upd G t (L.set (G t) q h) u) = S.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, sph_l hS]
    · rw [upd_ne _ _ e]
  have hcph : ∀ u, C.ph (upd G t (L.set (G t) q h) u) = C.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, cph_l hS]
    · rw [upd_ne _ _ e]
  have hpv : S.cnt (upd G t (L.set (G t) q h)) = S.cnt G := by
    rw [pv_lupd, upd_same]
  have hhold : ∀ u, L.ph (G u) = .holds → L.ph (upd G t (L.set (G t) q h) u) = .holds ∨
      ∀ c, VClock.le c (m.clocks[u]!) = true → L.Before m' c := fun u hu => by
    by_cases e : u = t
    · subst e
      by_cases hq : q = .holds
      · exact .inl (by rw [upd_self, L.ph_set, hq])
      · exact .inr fun c hc => L.before_le (hrel hu hq) hc
    · exact .inl (by rw [upd_ne _ _ e]; exact hu)
  have hgone : ∀ u, L.ph (upd G t (L.set (G t) q h) u) ≠ .gone → L.ph (G u) ≠ .gone :=
    fun u _ => by
      by_cases e : u = t
      · subst e; exact hg
      · rwa [upd_ne _ _ e] at *
  have hmono : ∀ c, L.HB G m c → L.HB (upd G t (L.set (G t) q h)) m' c :=
    fun c hc => hc.mono hhold hcl hs.before hs.threads hgone
  have hhS := ((hsub.2 C.S (.inl rfl)).1.lockStep hs (hap C.S (.inl rfl))).2
  have hhE := ((hsub.2 C.Ep (.inr rfl)).1.lockStep hs (hap C.Ep (.inr rfl))).2
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun j hj => ?_, fun u i jr sn e hu => ?_,
    fun u i jr sn e hu hsz => ?_, fun u hu => ?_, fun u v hu hv => ?_,
    fun u v i jr sn e hu hv => ?_⟩
  rotate_left 5
  · rw [hcph]; rw [hsph] at hu; exact hI.pw u hu
  · rw [hcph] at hu; rw [hsph] at hv; exact hI.cp u v hu hv
  · rw [hcph] at hu; rw [hsph] at hv; rw [hhS]
    exact VClock.le_trans (hI.rp u v i jr sn e hu hv) (hcl v)
  · rw [hsph] at hu
    by_cases e : u = t
    · subst e; rw [hst] at hu; cases hu
    · rw [upd_ne _ _ e]; exact hI.pst u hu
  · rw [hpv]; rw [hcph] at hu; exact hI.crit u hu
  · rw [hhE] at hj ⊢; exact hmono _ (hI.hbE j hj)
  · rw [hhS]; rw [hcph] at hu; exact hmono _ (hI.hbR u i jr sn e hu)
  · rw [hhS] at hsz; rw [hcph] at hu
    rcases hI.pz u i jr sn e hu hsz with h0 | ⟨v, hv⟩
    · exact .inl (by rw [hpv]; exact h0)
    · exact .inr ⟨v, by rw [hsph]; exact hv⟩

/-- The condition's cells stay (up to `Cell.norm`) over a step with the lock's invariant before
and after it, with the same rest (the cells are in the rest: `FCond.prim`'s `Sub`). -/
theorem cells_of_inv {G G' : ThreadId → γ} {rX : Res} {m m' : Mem}
    (hsub : (C.prim L).Sub G rX m) (hL : L.Inv G rX m) (hL' : L.Inv G' rX m') :
    ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
  intro W hW l hl
  obtain ⟨hw, rY, hrX, -⟩ := hsub.2 W hW
  have := cellsAt_some (W := W.In) hl (hw.cellIn hl) (m := m)
  obtain ⟨fc, hfc⟩ : ∃ fc, rX.heap l = some fc := by
    rw [hrX]; simp only [rsum, FHeap.union_apply, Word.cellsR]
    cases e : (cellsAt W.In m).heap l with
    | none => exact absurd e this
    | some fc => exact ⟨fc, rfl⟩
  rw [hL'.restCell hfc, hL.restCell hfc]

/-- The words' writes stay over a holder's step with the condition's cells. -/
theorem hist_hold {G : ThreadId → γ} {rX : Res} {m m' : Mem} (hsub : (C.prim L).Sub G rX m)
    (hfs : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hcells : ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    {W : Word 32 4} (hW : W = C.S ∨ W = C.Ep) : W.hist m' = W.hist m := by
  obtain ⟨hw, rY, hrX, -⟩ := hsub.2 W hW
  refine Word.hist_fstep hw hfs (fun l hl => ?_) (hcells W hW)
  have := cellsAt_some (W := W.In) hl (hw.cellIn hl) (m := m)
  rw [hrX]
  simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and, Word.cellsR] at this ⊢
  intro _ h; exact absurd h this

/-- **A step of the holder in the semaphore's own code keeps its invariant** (`Move.hold`). -/
theorem Inv.hold (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {s : SPh} {h : Res} (hI : S.Inv G m) (hsub : (C.prim L).Sub G rX m)
    (hh : L.ph (G t) = .holds) (hcx : C.ph (G t) = .out) (hL : L.Inv G rX m)
    (hc : m.current = t) (hfs : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hcells : ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hpz : S.ph (G t) = .pst → s = .out → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
      (C.S.hist m).size = jr + 1 → S.cnt G = 0) :
    S.Inv (upd G t (S.set (L.set (G t) .holds h) s)) m' := by
  have hcph : ∀ u, C.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = C.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, S.cph_set, cph_l hS]
    · rw [upd_ne _ _ e]
  have hlph : ∀ u, L.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = L.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, lph_s hS, L.ph_set, hh]
    · rw [upd_ne _ _ e]
  have hpv : S.cnt (upd G t (S.set (L.set (G t) .holds h) s)) = S.cnt G := by
    rw [pv_supd, pv_lupd, upd_same]
  have hcl : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hfs.clock
  have hbef : ∀ c, L.Before m c → L.Before m' c := by
    rintro c ⟨i, l, hl, hle⟩
    obtain ⟨i', hl'⟩ := (LockWord.loc_fstep (L := L.toLockWord) hfs
      (fun x h1 h2 => by
        have := LockWord.wordR_some hL.w.blk (L := L.toLockWord) (l := (L.b, x)) ⟨rfl, h1, h2⟩
        simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
          Option.or_eq_none_iff, not_and]
        intro h; exact absurd h this)
      (fun i l hl => (hL.w.loc.ok i l hl).1) l).mpr ⟨i, hl⟩
    exact ⟨i', l, hl', hle⟩
  have hmono : ∀ c, L.HB G m c → L.HB (upd G t (S.set (L.set (G t) .holds h) s)) m' c :=
    fun c hc => hc.mono (fun u hu => .inl (by rw [hlph]; exact hu)) hcl hbef hfs.threads
      (fun u hu => by rwa [hlph] at hu)
  have hhS := hist_hold hsub hfs hcells (.inl rfl)
  have hhE := hist_hold hsub hfs hcells (.inr rfl)
  have hsph : ∀ u, u ≠ t → S.ph (upd G t (S.set (L.set (G t) .holds h) s) u) = S.ph (G u) :=
    fun u e => by rw [upd_ne _ _ e]
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun j hj => ?_, fun u i jr sn e hu => ?_,
    fun u i jr sn e hu hsz => ?_, fun u hu => ?_, fun u v hu hv => ?_,
    fun u v i jr sn e hu hv => ?_⟩
  rotate_left 5
  · rw [hcph]
    by_cases e : u = t
    · subst e; rw [hcx]; rfl
    · rw [hsph u e] at hu; exact hI.pw u hu
  · rw [hcph] at hu
    by_cases e : v = t
    · subst e
      obtain rfl := hL.w.one u v (hsub.1.crit u hu) hh
      rw [hcx] at hu; exact absurd hu (by decide)
    · rw [hsph v e] at hv; exact hI.cp u v hu hv
  · rw [hcph] at hu; rw [hhS]
    by_cases e' : v = t
    · subst e'
      exact VClock.le_trans ((hI.hbR u i jr sn e hu).le hL.w hh) (hcl v)
    · rw [hsph v e'] at hv
      exact VClock.le_trans (hI.rp u v i jr sn e hu hv) (hcl v)
  · rw [hlph]
    by_cases e : u = t
    · subst e; exact hh
    · rw [hsph u e] at hu; exact hI.pst u hu
  · rw [hpv]; rw [hcph] at hu; exact hI.crit u hu
  · rw [hhE] at hj ⊢; exact hmono _ (hI.hbE j hj)
  · rw [hhS]; rw [hcph] at hu; exact hmono _ (hI.hbR u i jr sn e hu)
  · rw [hhS] at hsz; rw [hcph] at hu; rw [hpv]
    rcases hI.pz u i jr sn e hu hsz with h0 | ⟨v, hv⟩
    · exact .inl h0
    · by_cases e' : v = t
      · subst e'
        cases s with
        | pst => exact .inr ⟨v, by rw [upd_self, S.ph_set]⟩
        | out => exact .inl (hpz hv rfl u i jr sn e hu hsz)
      · exact .inr ⟨v, by rw [hsph v e']; exact hv⟩

/-- **A step of the holder in the semaphore's own code keeps the condition's invariant**
(`Move.hold`: the holder is out of the condition's code). -/
theorem condHold (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {rX : Res} {m m' : Mem}
    {t : ThreadId} {s : SPh} {h : Res} (hC : C.Inv L G m) (hsub : (C.prim L).Sub G rX m)
    (hcx : C.ph (G t) = .out) (hfs : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hcells : ∀ W, (W = C.S ∨ W = C.Ep) → ∀ l, W.In l →
      (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    C.Inv L (upd G t (S.set (L.set (G t) .holds h) s)) m' := by
  have hcp : C.ph (S.set (L.set (G t) .holds h) s) = .out := by
    rw [S.cph_set, cph_l hS, hcx]
  have hapE : C.Ep.ApartL L.toLockWord := hS.apart C.Ep (.inr rfl)
  refine hC.moveT rfl (hist_hold hsub hfs hcells (.inl rfl)) (hist_hold hsub hfs hcells (.inr rfl))
    hapE.ptr_ne (fun w _ hw => by rwa [hfs.waiters] at hw) hfs.clock
    (fun h' => by rw [hcp] at h'; exact absurd h' (by decide))
    (fun h' => by rw [hcp] at h'; exact absurd h' (by decide))
    (fun h' => by rw [hcp, hcx] at h'; rcases h' with h' | h' <;> exact absurd h' (by decide))
    (fun h' => by rw [hcp] at h'; cases h') (fun _ _ h' => by rw [hcp] at h'; cases h')
    (fun _ _ _ _ h' => by rw [hcp] at h'; cases h') (fun _ _ _ _ h' => by rw [hcx] at h'; cases h')
    (fun w hw e => ⟨fun h' => by rw [hcp] at h'; exact absurd h' (by decide),
      fun hp => ?_⟩)
  obtain ⟨i, jr, e', h1, -⟩ := hC.q w hw hp
  rw [e, hcx] at h1; cases h1

/-- **The others are out of the condition's code** while the holder `t` sees no other registered
thread (the scope of one waiter, module doc): a waiter in the critical code and a signaller (at
`pst`) would hold the mutex, which `t` holds. -/
theorem others_out {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hC : C.Inv L G m)
    (hI : S.Inv G m) (hL : L.Inv G rX m) (hh : L.ph (G t) = .holds)
    (hone : ∀ u, u ≠ t → ∀ i jr sn e, C.ph (G u) ≠ .reg i jr sn e) :
    ∀ u, u ≠ t → C.ph (G u) = .out := by
  have hhold : ∀ u, L.ph (G u) = .holds → u = t := fun u hu => hL.w.one u t hu hh
  intro u hu
  cases hu' : C.ph (G u) with
  | out => rfl
  | en => exact absurd (hhold u (hC.crit u (by rw [hu']; rfl))) hu
  | ld i e => exact absurd (hhold u (hC.crit u (by rw [hu']; rfl))) hu
  | reg i jr sn e => exact absurd hu' (hone u hu i jr sn e)
  | inc => exact absurd (hhold u (hI.pst u ((S.sx_iff _).mp (hC.sx u (by rw [hu']; rfl))))) hu
  | wk => exact absurd (hhold u (hI.pst u ((S.sx_iff _).mp (hC.sx u (by rw [hu']; rfl))))) hu

/-- No thread is at `pst` while the holder `t` is out of the semaphore's code. -/
theorem no_pst {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hI : S.Inv G m)
    (hL : L.Inv G rX m) (hh : L.ph (G t) = .holds) (hst : S.ph (G t) = .out) :
    ∀ v, S.ph (G v) ≠ .pst := fun v hv => by
  obtain rfl := hL.w.one v t (hI.pst v hv) hh
  rw [hst] at hv; cases hv

/-- **The waiter's entry into the condition at count 0 keeps the semaphore's invariant**
(`Move.enter`). -/
theorem Inv.enter (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    (hI : S.Inv G m) (hcx : C.ph (G t) = .out) (h0 : S.cnt G = 0)
    (hnp : ∀ v, S.ph (G v) ≠ .pst) : S.Inv (upd G t (C.set (G t) .en)) m := by
  have hpv : S.cnt (upd G t (C.set (G t) .en)) = S.cnt G := by rw [pv_cupd, upd_same]
  have hsph : ∀ u, S.ph (upd G t (C.set (G t) .en) u) = S.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, S.ph_cset]
    · rw [upd_ne _ _ e]
  have hlph : ∀ u, L.ph (upd G t (C.set (G t) .en) u) = L.ph (G u) := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, lph_c hS]
    · rw [upd_ne _ _ e]
  have hreg : ∀ u i jr sn e, C.ph (upd G t (C.set (G t) .en) u) = .reg i jr sn e →
      C.ph (G u) = .reg i jr sn e := fun u i jr sn e hu => by
    by_cases e' : u = t
    · subst e'; rw [upd_self, C.ph_set] at hu; cases hu
    · rwa [upd_ne _ _ e'] at hu
  have hmono : ∀ c, L.HB G m c → L.HB (upd G t (C.set (G t) .en)) m c :=
    fun c hc => hc.mono (fun u hu => .inl (by rw [hlph]; exact hu))
      (fun _ => VClock.le_refl _) (fun _ h => h) rfl (fun u hu => by rwa [hlph] at hu)
  refine ⟨fun u hu => ?_, fun u _ => by rw [hpv]; exact h0, fun j hj => hmono _ (hI.hbE j hj),
    fun u i jr sn e hu => hmono _ (hI.hbR u i jr sn e (hreg u i jr sn e hu)),
    fun u i jr sn e hu hsz => ?_, fun u hu => absurd (by rwa [hsph] at hu) (hnp u),
    fun _ v _ hv => absurd (by rwa [hsph] at hv) (hnp v),
    fun _ v _ _ _ _ _ hv => absurd (by rwa [hsph] at hv) (hnp v)⟩
  · rw [hlph]; rw [hsph] at hu; exact hI.pst u hu
  · rw [hpv]
    rcases hI.pz u i jr sn e (hreg u i jr sn e hu) hsz with h' | ⟨v, hv⟩
    · exact .inl h'
    · exact .inr ⟨v, by rw [hsph]; exact hv⟩

/-- **`S.Inv` with the holder `t` at `pst`** after a change of its ghost value (its client part,
its part, its held resource) with the same memory: the count may change, since `t` will signal
a registered waiter that was not signalled. -/
theorem Inv.atPst {G G' : ThreadId → γ} {m : Mem} {t : ThreadId} (hI : S.Inv G m)
    (hC : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u) (hh : L.ph (G' t) = .holds)
    (hht : L.ph (G t) = .holds) (hp : S.ph (G' t) = .pst) (hp0 : S.ph (G t) = .pst)
    (hcx : C.ph (G' t) = .out) (hw : L.WInv (L.pl G') m) : S.Inv G' m := by
  have hsph : ∀ v, S.ph (G' v) = .pst → S.ph (G v) = .pst := fun v hv => by
    by_cases e : v = t
    · subst e; exact hp0
    · rwa [hG v e] at hv
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
  have hreg : ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.ph (G u) = .reg i jr sn e :=
    fun u i jr sn e hu => by
      by_cases e' : u = t
      · subst e'; rw [hcx] at hu; cases hu
      · rwa [hG u e'] at hu
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun j hj => hmono _ (hI.hbE j hj),
    fun u i jr sn e hu => hmono _ (hI.hbR u i jr sn e (hreg u i jr sn e hu)),
    fun _ _ _ _ _ _ _ => .inr ⟨t, hp⟩, fun u hu => ?_, fun u v hu hv => ?_,
    fun u v i jr sn e hu hv => ?_⟩
  rotate_left 2
  · by_cases e : u = t
    · subst e; rw [hcx]; rfl
    · rw [hG u e] at hu ⊢; exact hI.pw u hu
  · have hcu : (C.ph (G u)).crit := by
      by_cases e : u = t
      · subst e; rw [hcx] at hu; exact absurd hu (by decide)
      · rwa [hG u e] at hu
    exact hI.cp u v hcu (hsph v hv)
  · exact hI.rp u v i jr sn e (hreg u i jr sn e hu) (hsph v hv)
  · by_cases e : u = t
    · subst e; exact hh
    · rw [hG u e] at hu ⊢; exact hI.pst u hu
  · by_cases e : u = t
    · subst e; rw [hcx] at hu; exact absurd hu (by decide)
    · rw [hG u e] at hu
      exact absurd (hw.one u t (by show L.ph (G' u) = _; rw [hG u e]; exact hC.crit u hu) hh) e

/-- **The holder's move in the semaphore's own code without a memory step** (to or from `pst`;
`Move.hold` with the same memory): the protocol's invariant holds at the new place. -/
theorem Fits.move (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {m : Mem} {t : ThreadId}
    {g : γ} (s : SPh) (hi : P.inv (upd G t g) m) (hc : m.current = t) (hh : L.ph g = .holds)
    (hcx : C.ph g = .out)
    (hpz : S.ph g = .pst → s = .out → ∀ u i jr sn e, C.ph (upd G t g u) = .reg i jr sn e →
      (C.S.hist m).size = jr + 1 → S.cnt (upd G t g) = 0) :
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
    ⟨Inv.hold hS hsub.2 hsub.1 hht hcxt hL hc hfs hcells (by rw [upd_self]; exact hpz),
      .inr ⟨condHold hS hsub.1.1 hsub.1 hcxt hfs hcells,
        .hold s (L.held g) hht hcxt hL hc hfs hcells (by rw [upd_self]; exact hpz)⟩⟩
  rw [hg, upd_upd] at hst
  have hL' : L.Inv (upd G t (S.set g s)) rX m := by
    have := hL.relabel (t := t) (g := S.set g s) (by rw [lph_s hS, upd_self])
      (by rw [lpart_s hS, upd_self]) (by rw [lheld_s hS, upd_self])
      (fun r hr => by
        have := lR_s hS s (upd G t g) t r hr
        rw [upd_self] at this; exact this)
    rwa [upd_upd] at this
  exact (hS.inv _ m).mpr ⟨rX, hL', hS.kstep _ _ _ _ _ _ _ hst hU⟩

/-- **A protocol with the semaphore has its condition** (module doc), when its `ok` excludes the
semaphore's own code: the condition's contract (`CondImpl`) applies to it. -/
theorem Fits.toC (hS : L.Fits S.prim P U ok) (hok : ∀ g, ok g → S.ph g = .out) :
    L.Fits (C.prim L) P U ok where
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
  lph g p := lph_c hS g p
  lpart g p := lpart_c hS g p
  lheld g p := lheld_c hS g p
  lR G t p r hr := lR_c hS p G t r hr
  ph_l g q h := cph_l hS g q h
  set_l g p q h := lset_c hS g q h p
  ph_part g r := cph_part hS g r
  set_part g p r := pset_c hS g r p
  role_l _ g q h := hS.role_l () g q h
  role_part _ g r := hS.role_part () g r
  ok_calm g p q hp hq := by
    by_cases hs : S.ph g = .out
    · have := hS.ok_calm g (p, .out) (q, .out) ⟨hp, rfl⟩ ⟨hq, rfl⟩
      rwa [← hs, place_c, place_c] at this
    · constructor <;> intro h <;>
        exact absurd ((S.ph_cset g _).symm.trans (hok _ h)) hs
  kstep t G rX m G' rX' m' hst hU := by
    have hsub := hS.sub G rX m hU
    exact hS.kstep t G rX m G' rX' m'
      ⟨hsub.2.cstep hS hsub.1.1 hsub.1 hst, .inl hst⟩ hU

/-! ## The rules of a semaphore's code

The steps of a semaphore's code in a protocol with it, once for every protocol and every
implementation (`SemImpl`): the field pointers (`projI`), the holder's access to the count that
keeps it (`Fits.wp_cnt`), the waiter's take and the poster's give at the store of the count, which
move the holder to `pst` (`Fits.wp_take`, `Fits.wp_give`), the condition's wait at count 0 and its
signal at `pst` by the condition's contract (`wp_cwait`, `wp_csignal`), the end of `pst` at count
0 (`Fits.unpst`), and the `unlock` by the mutex's contract (`wp_unlock`). -/

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
    {g : γ} {rh : Res} (hi : P.inv (upd G t (L.set (S.set g .pst) .holds rh)) m)
    (hc : m.current = t) (hcx : C.ph g = .out) (hgs : S.ph g = .out)
    (h0 : S.cnt (upd G t g) = 0) : P.inv (upd G t (L.set g .holds rh)) m := by
  rw [← lset_s hS] at hi
  have := Fits.move hS .out hi hc (by rw [lph_s hS, L.ph_set])
    (by rw [S.cph_set, cph_l hS]; exact hcx)
    fun _ _ _ _ _ _ _ _ _ => by rw [pv_supd, pv_lupd]; exact h0
  rwa [S.set_set, ← hgs, ← sph_l hS g .holds rh, S.set_self] at this

/-- **The holder's `unlock`** by the mutex's contract (`MutexImpl`), back to its ghost value `g`
out of the mutex's code with no held resource. -/
theorem wp_unlock {K : FPrim γ} (mi : MutexImpl Tgt) (hF : L.Fits K P U ok)
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

/-- **The holder's `unlock` at `pst` at count 0** (no signal owed): the end of `pst`
(`Fits.unpst`), then the `unlock` by the mutex's contract (`wp_unlock`). -/
theorem Fits.wp_unlockPst (mi : MutexImpl Tgt) (hS : L.Fits S.prim P U ok)
    (hcost : P.cost = none) {p : Ptr} (hp : p = L.ptr) (hLc : L.c = mi.c) (t : ThreadId) (g : γ)
    (rh : Res) (hgo : L.ph g = .out) (hgh : L.held g = rnil) (hcx : C.ph g = .out)
    (hgs : S.ph g = .out) (hok : ok g) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set (S.set g .pst) .holds rh)) m) (hc : m.current = t)
    (h0 : S.cnt (upd G t g) = 0) :
    P.WP t (mi.unlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧ P.inv (upd G' t g) m')
      G m d :=
  wp_unlock mi hS hcost hp hLc t g rh hgo hgh hok io G m d (Fits.unpst hS hi hc hcx hgs h0) hc

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
  have hcells := cells_of_inv hsub.1 hL hL'
  have hpz : S.ph (upd G t (L.set g .holds rL) t) = .pst → S.ph g = .out →
      ∀ u i jr sn e, C.ph (upd G t (L.set g .holds rL) u) = .reg i jr sn e →
      (C.S.hist m).size = jr + 1 → S.cnt (upd G t (L.set g .holds rL)) = 0 := by
    intro hp hs; rw [upd_self, sph_l hS, hs] at hp; cases hp
  have hst : S.prim.Step t (upd G t (L.set g .holds rL)) rX m
      (upd (upd G t (L.set g .holds rL)) t
        (S.set (L.set (upd G t (L.set g .holds rL) t) .holds r) (S.ph g))) rX m' :=
    ⟨Inv.hold hS hsub.2 hsub.1 hht hcxt hL hc hfs hcells hpz,
      .inr ⟨condHold hS hsub.1.1 hsub.1 hcxt hfs hcells,
        .hold _ r hht hcxt hL hc hfs hcells hpz⟩⟩
  have hgg : S.set (L.set (upd G t (L.set g .holds rL) t) .holds r) (S.ph g) =
      L.set g .holds r := by
    rw [upd_self, L.set_set, ← sph_l hS g .holds r, S.set_self]
  have := hS.kstep _ _ _ _ _ _ _ hst hU
  rw [hgg] at this; exact this

/-- **The holder's step to `pst` with a new ghost value `gf`** (the take and the give, at the
store of the count): a step of the semaphore's own code to `pst` (`Move.hold`), then the client's
move (`hUc`) with both invariants at `gf`. -/
theorem U_pst (hS : L.Fits S.prim P U ok) {G : ThreadId → γ} {t : ThreadId} {g gf : γ}
    {rL rX : Res} {m m' : Mem} (hgx : C.ph g = .out) (hgs : S.ph g = .out)
    (hfx : C.ph gf = .out) (hfs : S.ph gf = .pst) (hfh : L.ph gf = .holds)
    (hUc : U (upd G t (S.set (L.set g .holds rL) .pst)) rX m' → L.Inv (upd G t gf) rX m' →
      S.Inv (upd G t gf) m' → C.Inv L (upd G t gf) m' → U (upd G t gf) rX m')
    (hL : L.Inv (upd G t (L.set g .holds rL)) rX m) (hU : U (upd G t (L.set g .holds rL)) rX m)
    (hc : m.current = t) (hst : FStepIn (rsum (L.wordR m) rX).heap.erase m m')
    (hL' : L.Inv (upd G t gf) rX m') : U (upd G t gf) rX m' := by
  have hsub := hS.sub _ rX m hU
  have hht : L.ph (upd G t (L.set g .holds rL) t) = .holds := by rw [upd_self, L.ph_set]
  have hcxt : C.ph (upd G t (L.set g .holds rL) t) = .out := by
    rw [upd_self, cph_l hS]; exact hgx
  have hcells := cells_of_inv hsub.1 hL hL'
  have hpz : S.ph (upd G t (L.set g .holds rL) t) = .pst → SPh.pst = .out →
      ∀ u i jr sn e, C.ph (upd G t (L.set g .holds rL) u) = .reg i jr sn e →
      (C.S.hist m).size = jr + 1 → S.cnt (upd G t (L.set g .holds rL)) = 0 :=
    fun _ h => by cases h
  have hgi : upd (upd G t (L.set g .holds rL)) t
      (S.set (L.set (upd G t (L.set g .holds rL) t) .holds rL) .pst) =
      upd G t (S.set (L.set g .holds rL) .pst) := by rw [upd_upd, upd_self, L.set_set]
  have hI₁ := Inv.hold (h := rL) hS hsub.2 hsub.1 hht hcxt hL hc hst hcells hpz
  have hC₁ := condHold (s := .pst) (h := rL) hS hsub.1.1 hsub.1 hcxt hst hcells
  have hU₁ := hS.kstep _ _ _ _ _ _ _ ⟨hI₁, .inr ⟨hC₁, .hold _ rL hht hcxt hL hc hst hcells hpz⟩⟩ hU
  rw [hgi] at hI₁ hC₁ hU₁
  have hIf : S.Inv (upd G t gf) m' :=
    Inv.atPst hI₁ hC₁ (fun u hu => by rw [upd_ne _ _ hu, upd_ne _ _ hu])
      (by rw [upd_self]; exact hfh) (by rw [upd_self, lph_s hS, L.ph_set])
      (by rw [upd_self]; exact hfs) (by rw [upd_self, S.ph_set]) (by rw [upd_self]; exact hfx)
      hL'.w
  have hCf : C.Inv L (upd G t gf) m' := by
    have := hC₁.frame (t := t) (g' := gf)
      (by rw [upd_self, S.cph_set, cph_l hS, hfx, hgx]) (by rw [upd_self, lph_s hS, L.ph_set, hfh])
      (fun _ => (S.sx_iff gf).mpr hfs) rfl rfl (hS.apart C.Ep (.inr rfl)).ptr_ne rfl
      (fun _ => VClock.le_refl _)
    rwa [upd_upd] at this
  exact hUc hU₁ hL' hIf hCf

/-- **The waiter's take of a permit** at the store of the count (count not 0, `hnz`): its part
gains a resource `r` with `T` from the pool (`hpool`), the count goes down by one to `gx`'s
(`hcnt`, `hR`), and the waiter moves to `pst` with the client's rest's move (`hU`). The premises
`hcnt`, `hpool`, `hU` are `SemImpl.wait_wp`'s; the step's triple is on the count alone, which is
not 0. -/
theorem Fits.wp_take (hS : L.Fits S.prim P U ok) (hcost : P.cost = none) {α : Type}
    {x : MemM α} {G : ThreadId → γ} {t : ThreadId} {g gx : γ} {rL : Res} {m : Mem} {d : Nat}
    {T : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      S.cnt (upd G t gx) = S.cnt (upd G t g) - 1)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      ∀ r, S.Pool (S.xs (upd G t g)) r → (S.Pool (S.xs (upd G t gx)) ⋆ T) r)
    (hU : ∀ G rX m h₁ h₂ r, S.cnt (upd G t g) ≠ 0 → T r →
      FHeap.Disjoint (L.part g).heap r.heap → U (upd G t (S.set (L.set g .holds h₁) .pst)) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) m →
      U (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) rX m)
    (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hxx : C.ph gx = .out)
    (hi : P.inv (upd G t (L.set g .holds rL)) m) (hc : m.current = t)
    (hnz : S.cnt (upd G t g) ≠ 0)
    (htt : FTTriple (⟪S.cnt (upd G t g) ≠ 0⟫ ⋆ up (pts S.p 8 (S.cnt (upd G t g)))) x Qa)
    (hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t g) - 1)) r)
    (h : ∀ a m' r rh, m'.current = t → m'.threads = m.threads → (∃ rc, Qa a rc) → T r →
      FHeap.Disjoint (L.part g).heap r.heap → S.cnt (upd G t gx) = S.cnt (upd G t g) - 1 →
      P.inv (upd G t (L.set (S.set (L.setPart gx (rsum (L.part g) r)) .pst) .holds rh)) m' →
      Q a G m' d) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  have hc₁ := hcnt G rL m hi hnz
  have hpool := hpool G rL m hi hnz
  have htt := FTTriple.conseq htt (fun r h => sep_lift.mpr ⟨hnz, h⟩) (fun _ _ h => h)
  have hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t gx))) r := fun a r hq => by
    rw [hc₁]; exact hR a r hq
  refine hS.wp_holdParts (G' := upd G t (L.set g .holds rL))
    (Pa := (fun r => r = L.part g) ⋆
      (up (pts S.p 8 (S.cnt (upd G t g))) ⋆ S.Pool (S.xs (upd G t g))))
    (Qp := fun _ rp => ∃ r, T r ∧ FHeap.Disjoint (L.part g).heap r.heap ∧ rp = rsum (L.part g) r)
    (Qh := fun a => Qa a ⋆ S.Pool (S.xs (upd G t gx)))
    (g' := fun rp rh => S.set (L.set (L.setPart gx rp) .holds rh) .pst)
    hi hc (by rw [upd_self, L.ph_set]) ?_ ?_ ?_ ?_ ?_ ?_ (.inr hcost)
  · refine FTTriple.conseq ((FTTriple.frame (R := S.Pool (S.xs (upd G t g))) htt).frameL
      (R := fun r => r = L.part g)) (fun _ h => h) (fun a r hq => ?_)
    have h1 := sep_mono_right (fun _ => sep_mono_right hpool) hq
    have h2 := sep_assoc' (sep_mono_right (fun _ h => sep_comm (sep_assoc' h)) h1)
    refine sep_mono_left (fun r' hr' => ?_) h2
    obtain ⟨r₁, r₂, hd, he, rfl, hT⟩ := hr'
    exact ⟨r₂, hT, hd, he⟩
  · intro r hr hd
    rw [upd_self, L.part_set] at hd ⊢
    rw [R_cnt, pv_lupd, xs_lupd] at hr
    exact ⟨L.part g, r, hd, rfl, rfl, hr⟩
  · intro a rp rh _ hq
    rw [upd_upd, R_cnt, pv_supd, pv_lupd, pv_pupd, xs_supd, xs_lupd, xs_pupd]
    exact sep_mono_left (hR a) hq
  · intro a rp rh _ _
    exact ⟨by rw [lph_s hS, L.ph_set], by rw [lpart_s hS, L.part_set, L.part_setPart],
      by rw [lheld_s hS, L.held_set]⟩
  · rintro _ rX m' rp rh ⟨r, hT, hd, rfl⟩ _ hL hU' _ hfs _ hL'
    rw [upd_upd] at hL' ⊢
    exact U_pst hS hgx hgs (by rw [S.cph_set, cph_l hS, cph_part hS]; exact hxx) (S.ph_set _ _)
      (by rw [lph_s hS, L.ph_set]) (hU G rX m' rL rh r hnz hT hd) hL hU' hc hfs hL'
  · rintro a m' rp rh hc' ht ⟨r, hT, hd, rfl⟩ hq hi'
    rw [upd_upd, lset_s hS] at hi'
    obtain ⟨rc, -, -, -, hqa, -⟩ := hq
    exact h a m' r rh hc' ht ⟨rc, hqa⟩ hT hd hc₁ hi'

/-- **The poster's give of a permit** at the store of the count: its part `L.part g` loses `rT`
(`hsplit`) to the pool (`hpool`), the count goes up by one to `gx`'s without overflow (`hcnt`,
`hR`), and the poster moves to `pst` with the client's rest's move (`hU`). The premises `hsplit`,
`hcnt`, `hpool`, `hU` are `SemImpl.post_wp`'s; the step's triple is on the count alone, whose
increment does not overflow. -/
theorem Fits.wp_give (hS : L.Fits S.prim P U ok) (hcost : P.cost = none) {α : Type}
    {x : MemM α} {G : ThreadId → γ} {t : ThreadId} {g gx : γ} {rL rT : Res} {m : Mem} {d : Nat}
    {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hcnt : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64)
    (hpool : ∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r)
    (hU : ∀ G rX m h₁ h₂, U (upd G t (S.set (L.set g .holds h₁) .pst)) rX m →
      L.Inv (upd G t (S.set (L.set gx .holds h₂) .pst)) rX m →
      S.Inv (upd G t (S.set (L.set gx .holds h₂) .pst)) m →
      C.Inv L (upd G t (S.set (L.set gx .holds h₂) .pst)) m →
      U (upd G t (S.set (L.set gx .holds h₂) .pst)) rX m)
    (hgx : C.ph g = .out) (hgs : S.ph g = .out) (hxx : C.ph gx = .out)
    (hsplit : L.part g = rsum (L.part gx) rT) (hdj : FHeap.Disjoint (L.part gx).heap rT.heap)
    (hi : P.inv (upd G t (L.set g .holds rL)) m) (hc : m.current = t)
    (htt : FTTriple (⟪(S.cnt (upd G t g)).toNat + 1 < 2 ^ 64⟫ ⋆
      up (pts S.p 8 (S.cnt (upd G t g)))) x Qa)
    (hR : ∀ a r, Qa a r → up (pts S.p 8 (S.cnt (upd G t g) + 1)) r)
    (h : ∀ a m' rh, m'.current = t → m'.threads = m.threads → (∃ rc, Qa a rc) →
      P.inv (upd G t (L.set (S.set gx .pst) .holds rh)) m' → Q a G m' d) :
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
    (g' := fun _ rh => S.set (L.set gx .holds rh) .pst)
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
    exact U_pst hS hgx hgs (by rw [S.cph_set, cph_l hS]; exact hxx) (S.ph_set _ _)
      (by rw [lph_s hS, L.ph_set]) (hU G rX m' rL rh) hL hU' hc hfs hL'
  · intro a m' rp rh hc' ht _ hq hi'
    rw [upd_upd, lset_s hS] at hi'
    obtain ⟨rc, -, -, -, hqa, -⟩ := hq
    exact h a m' rh hc' ht ⟨rc, hqa⟩ hi'

/-- **The waiter's wait at the condition at count 0** by the condition's contract (`CondImpl`):
the holder `t`, out of the condition's and the semaphore's code, at count 0, with no other
registered thread (`hone`), returns holding the mutex again. Its sleep is no deadlock when the
client shows it at count 0 (`hlive`); otherwise a thread at `pst` holds the mutex and signals. -/
theorem wp_cwait (ci : CondImpl Tgt) (hS : L.Fits S.prim P U ok) (hcost : P.cost = none)
    (hok : ∀ g, ok g → S.ph g = .out) (hLc : L.c = ci.c) {p q : Ptr} (hp : p = C.S.ptr)
    (hq : q = L.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgs : S.ph g = .out) (hokg : ok g) (hpl : (L.part g).Plain)
    (hone : ∀ G₁ rL m₁, P.inv (upd G₁ t (L.set g .holds rL)) m₁ → S.cnt (upd G₁ t g) = 0 →
      ∀ u, u ≠ t → ∀ i jr sn e, C.ph (G₁ u) ≠ .reg i jr sn e)
    (hlive : ∀ G₁ m₁, P.inv G₁ m₁ → (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) →
      L.ph (G₁ t) = .away → ¬ C.Signalled m₁ → S.cnt G₁ = 0 → P.Live t G₁ m₁)
    (rL : Res) (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set g .holds rL)) m) (hc : m.current = t)
    (h0 : S.cnt (upd G t g) = 0) :
    P.WP t (ci.wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL', P.inv (upd G' t (L.set g .holds rL')) m') G m d := by
  have hone := hone G rL m hi h0
  have hcx : C.ph (L.set g .holds rL) = .out := by rw [cph_l hS]; exact hgx
  have hsx : S.ph (L.set g .holds rL) = .out := by rw [sph_l hS]; exact hgs
  obtain ⟨rX₀, hL₀, hU₀⟩ := (hS.inv _ m).mp hi
  have hsub₀ := hS.sub _ rX₀ m hU₀
  have hht : L.ph (upd G t (L.set g .holds rL) t) = .holds := by rw [upd_self, L.ph_set]
  have hone' : ∀ u, u ≠ t → C.ph (G u) = .out := fun u hu => by
    have := others_out hsub₀.1.1 hsub₀.2 hL₀ hht
      (fun u hu i jr sn e => by rw [upd_ne _ _ hu]; exact hone u hu i jr sn e) u hu
    rwa [upd_ne _ _ hu] at this
  have hhb : ∀ j < (C.Ep.hist m).size,
      VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true := fun j hj =>
    (hsub₀.2.hbE j hj).le hL₀.w hht
  have h0' : S.cnt (upd G t (L.set g .holds rL)) = 0 := by rw [pv_lupd]; exact h0
  have hnp := no_pst hsub₀.2 hL₀ hht (by rw [upd_self]; exact hsx)
  refine WP.mono (fun _ G' m' d' hw => ⟨hw.1, hw.2.1, by
      obtain ⟨rL', hi'⟩ := hw.2.2; exact ⟨rL', by rwa [L.set_set] at hi'⟩⟩)
    (ci.wait_wp (Fits.toC hS hok) hcost hp hq hLc t (L.set g .holds rL) hcx (L.ph_set _ _ _)
      ((hS.ok_set _ _ _).mpr hokg) io G m d hone' hhb (fun rX hU hC' => ?hent)
      (fun G₁ m₁ hreg haw hi₁ hns => ?hlive) (by rw [L.part_set]; exact hpl) hi hc)
  case hent =>
    -- the entry: a step of the semaphore's own code
    have hsub := hS.sub _ rX m hU
    have hcxt : C.ph (upd G t (L.set g .holds rL) t) = .out := by rw [upd_self]; exact hcx
    have hst : S.prim.Step t (upd G t (L.set g .holds rL)) rX m
        (upd (upd G t (L.set g .holds rL)) t (C.set (upd G t (L.set g .holds rL) t) .en)) rX m :=
      ⟨Inv.enter hS hsub.2 hcxt h0' hnp,
        .inr ⟨by rw [upd_upd, upd_self]; exact hC', .enter hht hcxt h0' hnp⟩⟩
    have := hS.kstep _ _ _ _ _ _ _ hst hU
    rw [upd_upd, upd_self] at this; exact this
  case hlive =>
    -- the waiter's sleep: count 0, or a thread at `pst` holds the mutex
    obtain ⟨i, jr, e, hr⟩ := hreg
    obtain ⟨rX₁, hL₁, hU₁⟩ := (hS.inv _ m₁).mp hi₁
    have hsub₁ := hS.sub _ rX₁ m₁ hU₁
    have hera := hsub₁.1.1.era t i jr false e hr
    have hsz : (C.S.hist m₁).size = jr + 1 := by
      rcases hera.ssz with h | h
      · exact h
      · exfalso; apply hns
        show ((C.S.hist m₁)[(C.S.hist m₁).size - 1]!).Val _
        rw [h, show jr + 2 - 1 = jr + 1 by omega]; exact hera.s1 h
    rcases hsub₁.2.pz t i jr false e hr hsz with hz | ⟨v, hv⟩
    · exact hlive G₁ m₁ hi₁ ⟨i, jr, e, hr⟩ haw hns hz
    · intro _ hall
      have hvh := hsub₁.2.pst v hv
      obtain ⟨hvt, -⟩ := hL₁.ht (t := v) (by rw [hvh]; decide)
      rcases hall v hvt with hf | hw | hj
      · have := hS.fin _ hf; rw [hvh] at this; cases this
      · have := hL₁.w.notQ (t := v) (by show L.ph (G₁ v) ≠ _; rw [hvh]; decide)
          (by show L.ph (G₁ v) ≠ _; rw [hvh]; decide)
        rw [this] at hw; cases hw
      · have := hS.joins _ hj; rw [hvh] at this; cases this

/-- **The signal at `pst`** by the condition's contract (`CondImpl`), and the end of `pst`: every
registration happened before the thread at `pst` (`Inv.rp`), and after the signal every
registered waiter is signalled, so none is owed a signal. -/
theorem wp_csignal (ci : CondImpl Tgt) (hS : L.Fits S.prim P U ok) (hcost : P.cost = none)
    (hok : ∀ g, ok g → S.ph g = .out) {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g₀ : γ)
    (rh : Res) (hgx : C.ph g₀ = .out) (hgs : S.ph g₀ = .out) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hi : P.inv (upd G t (L.set (S.set g₀ .pst) .holds rh)) m) :
    P.WP t (ci.signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g₀ .holds rh)) m') G m d := by
  rw [← lset_s hS] at hi
  have hgx' : C.ph (S.set (L.set g₀ .holds rh) .pst) = .out := by
    rw [S.cph_set, cph_l hS]; exact hgx
  have hgh' : L.ph (S.set (L.set g₀ .holds rh) .pst) = .holds := by rw [lph_s hS, L.ph_set]
  have hgo : S.set (S.set (L.set g₀ .holds rh) .pst) .out = L.set g₀ .holds rh := by
    rw [S.set_set, ← hgs, ← sph_l hS g₀ .holds rh, S.set_self]
  refine WP.mono (fun _ G' m' d' ⟨hd, hc, hi', hsig⟩ => ⟨hd, hc, ?_⟩)
    (ci.signal_wp (Fits.toC hS hok) hcost hp t (S.set (L.set g₀ .holds rh) .pst) hgx'
      (.inr hgh')
      ((S.sx_iff _).mpr (S.ph_set _ _)) io G m d
      (fun G₁ rX m₁ hg hU u i jr sn e hr =>
        (hS.sub G₁ rX m₁ hU).2.rp u t i jr sn e hr (by rw [hg]; exact S.ph_set _ _)) hi)
  rw [← hgo]
  refine Fits.move hS .out hi' hc hgh' hgx' fun _ _ u i jr sn e hr hsz => ?_
  obtain ⟨rX, -, hU⟩ := (hS.inv _ m').mp hi'
  have hera := (hS.sub _ rX m' hU).1.1.era u i jr sn e hr
  have hut : u ≠ t := fun e' => by rw [e', upd_self, hgx'] at hr; cases hr
  have hs := hsig u i jr sn e (by rw [upd_ne _ _ hut] at hr; exact hr)
  have hs' : (C.S.hist m')[jr]!.Val (0x10001 : BitVec 32) := by
    have : ((C.S.hist m')[(C.S.hist m').size - 1]!).Val (0x10001 : BitVec 32) := hs
    rwa [hsz, Nat.add_sub_cancel] at this
  exact absurd (FEvent.val_eq hs' hera.s0) (by decide)

end FSem

/-- **A semaphore implementation** in generated code: `wait(sem, io)` and `post(sem, io)` with the
rules that a client uses, for every protocol that has the semaphore (`L.Fits S.prim P U ok`; the
mutex's contended value `c`; the mutex at `S.p + 8`, the condition at `S.p + 12`) whose `ok`
excludes the semaphore's own code and that counts no turns. A thread runs either op out of the
mutex's, the condition's and the semaphore's code, and returns out of them.

- `wait_wp`: the thread takes a permit. Its client part goes from `x g` to `x gx` while the count
  goes down by one (`hcnt`), and a resource `r` with `T` moves from the pool into its part
  (`hpool`: the pool's split); the client's rest allows the move at the store of the count, with
  the moved resource `r` and the count before it not 0 (`hU`, with both invariants after it). At count 0 it waits at the
  condition: no other thread is registered there while it holds the mutex (`hone`, the
  condition's one-waiter scope) and its sleep at count 0 is no deadlock (`hlive`). Its part holds
  the plain mode, as for `CondImpl.wait_wp` (the condition's code may keep its state on the
  waiter's stack).
- `post_wp`: the thread gives a permit back. Its part loses `rT` to the pool (`hpool`), the count
  goes up by one without overflow (`hcnt`), and the client's rest allows the move (`hU`).

The premises on the count and the pool are for the ghost values of a reachable state in which
the thread holds the mutex. The waiter is the running thread (`m.current = t`), as for
`MutexImpl.unlock_wp`. -/
structure SemImpl (Tgt : Type) where
  wait : Ptr → Io → ConcM Tgt Unit
  post : Ptr → Io → ConcM Tgt Unit
  /-- The contended value of the semaphore's mutex. -/
  c : Nat
  wait_wp : ∀ {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits S.prim P U ok →
    P.cost = none → (∀ g, ok g → S.ph g = .out) → L.c = c → ∀ {p : Ptr}, p = S.p →
    ∀ (t : ThreadId) (g gx : γ) (T : FAssn),
    L.ph g = .out → C.ph g = .out → S.ph g = .out → ok g → (L.part g).Plain →
    L.ph gx = .out → L.held gx = rnil → C.ph gx = .out → S.ph gx = .out → ok gx →
    (∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      S.cnt (upd G t gx) = S.cnt (upd G t g) - 1) →
    (∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → S.cnt (upd G t g) ≠ 0 →
      ∀ r, S.Pool (S.xs (upd G t g)) r → (S.Pool (S.xs (upd G t gx)) ⋆ T) r) →
    (∀ G rX m h₁ h₂ r, S.cnt (upd G t g) ≠ 0 → T r → FHeap.Disjoint (L.part g).heap r.heap →
      U (upd G t (S.set (L.set g .holds h₁) .pst)) rX m →
      L.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) rX m →
      S.Inv (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) m →
      C.Inv L (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) m →
      U (upd G t (S.set (L.set (L.setPart gx (rsum (L.part g) r)) .holds h₂) .pst)) rX m) →
    (∀ G₁ rL m₁, P.inv (upd G₁ t (L.set g .holds rL)) m₁ → S.cnt (upd G₁ t g) = 0 →
      ∀ u, u ≠ t → ∀ i jr sn e, C.ph (G₁ u) ≠ .reg i jr sn e) →
    (∀ G₁ m₁, P.inv G₁ m₁ → (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) →
      L.ph (G₁ t) = .away → ¬ C.Signalled m₁ → S.cnt G₁ = 0 → P.Live t G₁ m₁) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (wait p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ ∃ r, T r ∧
      FHeap.Disjoint (L.part g).heap r.heap ∧
      P.inv (upd G' t (L.setPart gx (rsum (L.part g) r))) m') G m d
  post_wp : ∀ {γ X : Type} {L : FLock γ} {C : FCond γ} {S : FSem γ X L C} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits S.prim P U ok →
    P.cost = none → (∀ g, ok g → S.ph g = .out) → L.c = c → ∀ {p : Ptr}, p = S.p →
    ∀ (t : ThreadId) (g gx : γ) (rT : Res),
    L.ph g = .out → C.ph g = .out → S.ph g = .out → ok g →
    L.ph gx = .out → L.held gx = rnil → C.ph gx = .out → S.ph gx = .out → ok gx →
    L.part g = rsum (L.part gx) rT → FHeap.Disjoint (L.part gx).heap rT.heap →
    (∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m →
      S.cnt (upd G t gx) = S.cnt (upd G t g) + 1 ∧ (S.cnt (upd G t g)).toNat + 1 < 2 ^ 64) →
    (∀ G rL m, P.inv (upd G t (L.set g .holds rL)) m → ∀ r,
      ((fun r => r = rT) ⋆ S.Pool (S.xs (upd G t g))) r → S.Pool (S.xs (upd G t gx)) r) →
    (∀ G rX m h₁ h₂, U (upd G t (S.set (L.set g .holds h₁) .pst)) rX m →
      L.Inv (upd G t (S.set (L.set gx .holds h₂) .pst)) rX m →
      S.Inv (upd G t (S.set (L.set gx .holds h₂) .pst)) m →
      C.Inv L (upd G t (S.set (L.set gx .holds h₂) .pst)) m →
      U (upd G t (S.set (L.set gx .holds h₂) .pst)) rX m) →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (post p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t gx) m')
      G m d

end Full
end Zig
