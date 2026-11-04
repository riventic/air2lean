import ZigLean.Sep.Full.CondInv

/-!
# The futex-epoch condition, over full-state resources

A condition variable with a futex epoch (`Io.Condition` of 0.16.0 and 0.17.0,
`Thread.Condition.FutexImpl` of 0.15.2), for any number of waiters and signallers. The places
(`CPh`), the condition's words and roles (`FCond`) and its invariant (`FCond.Inv`, the history
fields H1–H3 and the count) are in `ZigLean/Sep/Full/CondInv.lean`; this module is the
condition as a primitive next to its mutex (`FCond.prim`, `FPrim.ofWords`), the protocol that
keeps it (`FCond.Fits`: `FLock.Fits` with the condition as its primitive, and the window), the
rules of the condition's ops in generated code, and the contract that an implementation of a
Zig version proves (`CondImpl`).

**The window** (PR397 ruling 6264821278): a waiter's futex compare is against its saved epoch
value, so it can miss its wake if exactly a multiple of `2^32` epoch increments happen inside
its save-to-enqueue window. The contract asks the protocol for fewer: every registered waiter
`reg i …` has `(C.Ep.hist m).size ≤ i + 2^32` in every state its rest allows (`Fits.win`). A
client with a bounded run discharges it from its cost or admission accounting; a singleton
client (one increment per registration) trivially. It is not a premise ID and not a global cap.

**The client's part.** Roles: `FCond.sx` are the ghost values that may signal (`Inv.sx`). A
thread in the condition's critical code (`en`, `ld`) holds the mutex (`Inv.crit`); one between
its post and its wake (`inc`, `wk`) is outside or holding the mutex (`Inv.lp`); both run no lock
code, so a client's `Fits` `ok` excludes them (`CPh.busy`, `Fits.ok_calm`) and a lock step keeps
the invariant (`Inv.lstep`). A step of the condition's code keeps the client's rest `U` given
the code's transition (`CPh.Next`; the entry `out → en` is the client's `hent` of
`CondImpl.wait_wp`) and the epoch's writes (they change only at a signaller's `epoch += 1`,
`FCond.prim`, `Fits.wStep`).

WORK IN PROGRESS (PR #599): the step lemmas of the singleton module and the `wp_*` rules are
being ported onto `CondInv` (git history of this file on `main`); the clients
(`Proofs/Sync/Cond.lean`, `Proofs/Threadsync/Cond.lean`, `Proofs/Handoff/*`,
`SepAuto.WPCond`) move in the same PR.
-/

namespace Zig
namespace Full

open Conc Proto

namespace FCond

variable {γ : Type} (C : FCond γ)

/-- A step of thread `t` in the condition's code, as the protocol's rest sees it: no change, an
op at the word `W` (the state or the epoch: a read, or an RMW of the newest write), the futex
wait's sleep at the epoch, the return of a futex wait, or a futex wake at the epoch. -/
inductive MStep (W : Word 32 4) (t : ThreadId) (m : Mem) : Mem → Prop
  | same : MStep W t m m
  | op {m' : Mem} : W.Ok { m with current := t } →
      t < m.clocks.size →
      ((∃ (c : Nat) (ord : AtomicOrder) (v : BitVec 32),
          ((atomicLoadAt c ord 4 W.ptr).run { m with current := t }).run =
            some (.ok (v, m'))) ∨
        (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
            (v old : BitVec 32),
          ((atomicRmwAt c op signed ord 4 W.ptr v).run { m with current := t }).run =
            some (.ok (old, m'))) ∨
        (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec 32)
            (r : Option (BitVec 32)),
          ((cmpxchgAt c succ fail 4 W.ptr expected new).run { m with current := t }).run =
            some (.ok (r, m'))) ∨
        (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec 32)
            (r : Option (BitVec 32)),
          ((cmpxchgWeakAt c succ fail 4 W.ptr expected new).run { m with current := t }).run =
            some (.ok (r, m'))) ∨
        m' = ({ m with current := t } : Mem).recordAt W.b W.o 4 .atomicRead) →
      W.Ok m' →
      (W.hist m' = W.hist m ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
        W.hist m' = (W.hist m).push
          (Word.rmwEnt m' t ord (W.hist m)[(W.hist m).size - 1]! v)) →
      MStep W t m m'
  | sleep {M : Mem} : C.Ep.Ok { m with current := t } →
      t < m.clocks.size →
      M = ({ m with current := t } : Mem).recordAt C.Ep.b C.Ep.o 4 .atomicRead →
      C.Ep.hist M = C.Ep.hist m → C.Ep.Ok M →
      MStep W t m { M with waiters := M.waiters.push (t, C.Ep.ptr) }
  | woken : MStep W t m { m with current := t, woken := m.woken.erase t }
  | resume : MStep W t m { m with current := t }
  | wake {m' : Mem} (c : Nat) (cs : List Nat) :
      ((Thread.futexWake C.Ep.ptr c cs).run { m with current := t }).run =
        some (.ok ((), m')) → MStep W t m m'

/-- **The condition as a primitive next to its mutex `L`** (`FPrim.ofWords`; a protocol keeps it:
`C.Fits L P U ok`). Its words are the state and the epoch; the role is `sx`; the calm places are
those out of the busy code (`ok` reads no other place: a thread out of the busy code runs lock
code). A step of its code at a word `W` is an `MStep` with the stepping thread's transition
(`CPh.Next`), its lock place and resource (the same, or `out`/`away` around a futex wait: only a
waiter goes `away`), and the epoch's writes (they change only at a signaller's `epoch += 1`, at
`inc`). A thread steps on its own part (a stack block of the condition's code) out of the lock's
code or holding the lock. -/
abbrev prim (L : FLock γ) : FPrim γ :=
  FPrim.ofWords L C.toFPlace .out (fun p => p.busy = false) (fun (_ : Unit) g => C.sx g)
    (fun W => W = C.S ∨ W = C.Ep) (C.Inv L)
    (fun W t g p q h m m' => CPh.Next (C.ph g) p ∧
      ((q = L.ph g ∧ h = L.held g) ∨
        ((L.ph g = .out ∨ L.ph g = .away) ∧ (q = .out ∨ (q = .away ∧ p.waits = true)) ∧
          h = rnil)) ∧
      C.MStep W t m m' ∧ (C.Ep.hist m' = C.Ep.hist m ∨ ∃ q n, C.ph g = .inc q n))
    (fun q => q = .out ∨ q = .holds)

/-- **A protocol that keeps the condition** next to its mutex `L`: `FLock.Fits` with the
condition as its primitive, and the window (module doc): every registered waiter has fewer than
`2^32` epoch writes after its saved one, in every state the rest allows. -/
structure Fits (L : FLock γ) {Tgt : Type} (P : Proto Tgt γ)
    (U : (ThreadId → γ) → Res → Mem → Prop) (ok : γ → Prop) : Prop
    extends FLock.Fits L (C.prim L) P U ok where
  win : ∀ G rX m, U G rX m → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
    (C.Ep.hist m).size ≤ i + 4294967296

variable {C}

/-! ## A step of the condition's code, as the memory sees it

As for the event (`FEvent.MStep.threads`, …), with the op at the word `W` and the futex wait and
wake at the epoch: only `W`'s bytes change, a new access is at `W` or at the epoch, a lock's word
apart from both keeps its location, a new waiter is the stepping thread at the epoch, and a word
at or apart from each of them stays valid, with a new write only at `W`. -/

namespace MStep

variable {W : Word 32 4} {t : ThreadId} {m m' : Mem}

theorem nextMsg (hs : C.MStep W t m m') : m.nextMsg ≤ m'.nextMsg := by
  cases hs with
  | @op M hw hc hop _ _ =>
    have hs : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    exact hs.nextMsg
  | @sleep M _ _ hr _ _ =>
    subst M
    exact Nat.le_refl _
  | wake c cs h => rw [Proto.modify_ok h]; exact Nat.le_refl _
  | _ => exact Nat.le_refl _

/-- An op changes views only at `W`; a scheduler wait keeps atomic locations and views exactly.
The map always names the actual actor explicitly. -/
theorem atomics (hs : C.MStep W t m m') (hF : Heap)
    (hW : ∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) :
    ∃ σ, AMap hF { m with current := t } { m' with current := t } σ := by
  cases hs with
  | @op M hw hc hop _ _ =>
    have hs : FStepIn hF { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc hW hop
    obtain ⟨σ, ha⟩ := hs.atomics
    exact ⟨σ, ha.withCurrent (t := t) rfl⟩
  | @sleep M _ _ hr _ _ =>
    subst M
    exact ⟨some, AMap.of_eq rfl rfl⟩
  | wake c cs h => rw [Proto.modify_ok h]; exact ⟨some, AMap.of_eq rfl rfl⟩
  | _ => exact ⟨some, AMap.of_eq rfl rfl⟩

theorem threads (hs : C.MStep W t m m') : m'.threads = m.threads := by
  cases hs with
  | @op M hw hc hop _ _ =>
    have hs : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    exact hs.threads
  | @sleep M _ _ hr _ _ =>
    subst M
    rfl
  | wake c cs h => rw [Proto.modify_ok h]
  | _ => rfl

theorem clocks (hs : C.MStep W t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  cases hs with
  | @op M hw hc hop _ _ =>
    have hs : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hw hc (fun _ _ _ => rfl) hop
    exact hs.clock u
  | @sleep M hw hc hr _ _ =>
    subst M
    exact (Word.record_fstep (hF := fun _ => none) (k := .atomicRead)
      hw hc (fun _ _ _ => rfl)).clock u
  | wake c cs h => rw [Proto.modify_ok h]; exact VClock.le_refl _
  | _ => exact VClock.le_refl _

theorem cells (hs : C.MStep W t m m') {l : Zig.Loc} (hl : ¬ W.In l) : m'.heap l = m.heap l := by
  cases hs with
  | @op M hw hc hop _ _ =>
    exact (Word.actualRun_rest hw hc hop).heap l hl
  | @sleep M _ _ hr _ _ =>
    subst M
    rfl
  | wake c cs h => rw [Proto.modify_ok h]; rfl
  | _ => rfl

theorem fp (hs : C.MStep W t m m') {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) ∨ (e.block = C.Ep.b ∧ e.off = C.Ep.o) := by
  cases hs with
  | @op M hw _ hop _ _ =>
    exact (Word.actualRun_fpAt hw hop he).imp_right .inl
  | @sleep M _ _ hr _ _ =>
    rw [hr] at he
    exact (Word.record_fpAt (W := C.Ep) (m := { m with current := t }) he).imp_right .inr
  | wake c cs h => rw [Proto.modify_ok h] at he; exact .inl he
  | _ => exact .inl he

theorem block (hs : C.MStep W t m m') {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  cases hs with
  | @op M hw _ hop _ _ =>
    exact Word.actualRun_block hw hop hb
  | @sleep M _ _ hr _ _ =>
    subst M
    exact ⟨blk, hb, rfl, rfl, rfl⟩
  | wake c cs h => rw [Proto.modify_ok h]; exact ⟨blk, hb, rfl, rfl, rfl⟩
  | _ => exact ⟨blk, hb, rfl, rfl, rfl⟩

theorem lockLoc (hs : C.MStep W t m m') {L : LockWord} (hW : W.ApartL L) (hE : C.Ep.ApartL L)
    {i : Nat} {l : ALoc} (hl : L.Loc m i l) : L.Loc m' i l := by
  cases hs with
  | @op M hw _ hop _ _ =>
    exact Word.actualRun_lockLoc hw hop hW hl
  | @sleep M _ _ hr _ _ =>
    subst M
    exact hl
  | wake c cs h => rw [Proto.modify_ok h]; exact hl
  | _ => exact hl

theorem waiters (hs : C.MStep W t m m') {w : ThreadId × Ptr} (hw : w ∈ m'.waiters) :
    w ∈ m.waiters ∨ w = (t, C.Ep.ptr) := by
  cases hs with
  | @op M hv hc hop _ _ =>
    have hstep : FStepIn (fun _ => none) { m with current := t } m' := by
      exact Word.actualRun_fstep hv hc (fun _ _ _ => rfl) hop
    exact .inl (hstep.waiters ▸ hw)
  | @sleep M _ _ hr _ _ =>
    rw [hr] at hw
    rcases Array.mem_push.mp hw with hw | hw
    · exact .inl hw
    · exact .inr hw
  | wake c cs h => rw [Proto.modify_ok h] at hw; exact .inl (Array.mem_filter.mp hw).1
  | _ => exact .inl hw

theorem word {W' : Word 32 4} (hs : C.MStep W t m m') (hok : W'.Ok m)
    (hW : W' = W ∨ W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o)
    (hE : W' = C.Ep ∨ C.Ep.b ≠ W'.b ∨ C.Ep.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ C.Ep.o) :
    W'.Ok m' ∧ (W'.hist m' = W'.hist m ∨ (W' = W ∧ ∃ x, W'.hist m' = (W'.hist m).push x)) := by
  have hmem : ∀ l, ¬ W.In l → m'.heap l = m.heap l := fun _ hl => hs.cells hl
  have hk : ∀ {m₁ : Mem}, m₁.blocks = m.blocks → m₁.atomics = m.atomics →
      m₁.footprint = m.footprint → m₁.threads = m.threads → m₁.clocks = m.clocks →
      W'.Ok m₁ ∧ (W'.hist m₁ = W'.hist m ∨
        (W' = W ∧ ∃ x, W'.hist m₁ = (W'.hist m).push x)) :=
    fun hb ha hf ht hc => by
      obtain ⟨hw', hh⟩ := hok.fields_native hb ha hf ht
        (fun u => by rw [hc]; exact VClock.le_refl _)
      exact ⟨hw', .inl hh⟩
  cases hs with
  | same => exact hk rfl rfl rfl rfl rfl
  | @op M hw hc hop hw' hh =>
    rcases hW with rfl | hap
    · exact ⟨hw', hh.imp id fun ⟨ord, v, h⟩ =>
        ⟨rfl, Word.rmwEnt m' t ord ((W'.hist m)[(W'.hist m).size - 1]!) v, h⟩⟩
    · obtain ⟨hv, hvHist⟩ := hok.fields_native (m' := { m with current := t })
        rfl rfl rfl rfl (fun _ => VClock.le_refl _)
      have hsteps : ∀ hF : Heap,
          (∀ x, W.o ≤ x → x < W.o + 4 → hF (W.b, x) = none) →
          FStepIn hF { m with current := t } m' := by
        intro hF hoff
        exact Word.actualRun_fstep hw hc hoff hop
      have hpres := Word.preserve_apart (W := W) hv hsteps hmem hap
      exact ⟨hpres.1, .inl (hpres.2.trans hvHist)⟩
  | @sleep M hw hc hr hh hw' =>
    have hM : W'.Ok M ∧ W'.hist M = W'.hist m := by
      rcases hE with rfl | hap
      · exact ⟨hw', hh⟩
      · obtain ⟨hv, hvHist⟩ := hok.fields_native (m' := { m with current := t })
          rfl rfl rfl rfl (fun _ => VClock.le_refl _)
        have hsteps : ∀ hF : Heap,
            (∀ x, C.Ep.o ≤ x → x < C.Ep.o + 4 → hF (C.Ep.b, x) = none) →
            FStepIn hF { m with current := t } M := by
          intro hF hoff
          rw [hr]
          exact Word.record_fstep (k := .atomicRead) hw hc hoff
        have hcells : ∀ l, ¬ C.Ep.In l →
            M.heap l = ({ m with current := t } : Mem).heap l :=
          fun l _ => by rw [hr]; rfl
        have hpres := Word.preserve_apart (W := C.Ep) hv hsteps hcells hap
        exact ⟨hpres.1, hpres.2.trans hvHist⟩
    obtain ⟨hw'', hh'⟩ := hM.1.fields_native
      (m' := { M with waiters := M.waiters.push (t, C.Ep.ptr) })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)
    exact ⟨hw'', .inl (hh'.trans hM.2)⟩
  | woken => exact hk rfl rfl rfl rfl rfl
  | resume => exact hk rfl rfl rfl rfl rfl
  | wake c cs h => rw [Proto.modify_ok h]; exact hk rfl rfl rfl rfl rfl

end MStep

/-! ## Generic facts of the words -/

variable {L : FLock γ} {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop}
  {ok : γ → Prop} {t : ThreadId}

/-- An op at a word of the condition: its `MStep`. -/
theorem mstep_op {W : Word 32 4} {m₁ m' : Mem} (hc : m₁.current = t)
    (hw : W.Ok m₁) (hct : t < m₁.clocks.size)
    (hop : ((∃ (c : Nat) (ord : AtomicOrder) (v : BitVec 32),
          ((atomicLoadAt c ord 4 W.ptr).run m₁).run =
            some (.ok (v, m'))) ∨
        (∃ (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder)
            (v old : BitVec 32),
          ((atomicRmwAt c op signed ord 4 W.ptr v).run m₁).run =
            some (.ok (old, m'))) ∨
        (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec 32)
            (r : Option (BitVec 32)),
          ((cmpxchgAt c succ fail 4 W.ptr expected new).run m₁).run =
            some (.ok (r, m'))) ∨
        (∃ (c : Nat) (succ fail : AtomicOrder) (expected new : BitVec 32)
            (r : Option (BitVec 32)),
          ((cmpxchgWeakAt c succ fail 4 W.ptr expected new).run m₁).run =
            some (.ok (r, m'))) ∨
        m' = (m₁ : Mem).recordAt W.b W.o 4 .atomicRead)) (hw' : W.Ok m')
    (hh : W.hist m' = W.hist m₁ ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
      W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]! v)) :
    C.MStep W t m₁ m' :=
  .op (by rw [FEvent.cur_eq hc]; exact hw) hct (by rw [FEvent.cur_eq hc]; exact hop) hw' hh

theorem add_one_ne (e : BitVec 32) : e + 1 ≠ e := by bv_omega

/-- `g` at the place it has. -/
theorem set_of {g : γ} {p : CPh} (h : C.ph g = p) : C.set g p = g := h ▸ C.set_self g

/-- The epoch's pointer is the condition's plus 4. -/
theorem ptr_ep : C.S.ptr.add 4 = C.Ep.ptr := by
  simp only [Word.ptr, Ptr.add, C.ep_b, C.ep_o]; congr 1

/-- A byte of the epoch is not the state's. -/
theorem ep_notS {l : Zig.Loc} (hl : C.Ep.In l) : ¬ C.S.In l := by
  obtain ⟨-, h2, -⟩ := hl
  rintro ⟨-, -, h3⟩
  have := C.ep_o
  omega

/-- The epoch's pointer is formed from the condition's (`&cond.epoch`, MM-3). -/
theorem _root_.Zig.Full.FLock.Fits.projE (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {m : Mem}
    (hi : P.inv G m) : (ptrProject C.S.ptr (·.add 4)).run m = pure (C.S.ptr.add 4, m) := by
  obtain ⟨rX, -, hU⟩ := (hC.inv _ _).mp hi
  obtain ⟨blk, hblk, -, hsz, -⟩ := ((hC.wRest (.inr rfl)) _ _ _ hU).1.blk
  rw [C.ep_b] at hblk
  have := C.ep_o
  exact ptrProject_add_run (inBounds_of (b := C.S.b) rfl hblk (by simp [Word.ptr])
    (by simp [Word.ptr]; omega)) (inBounds_of (b := C.S.b) rfl hblk
    (by simp [Word.ptr, Ptr.add]; omega) (by simp [Word.ptr, Ptr.add]; omega))

/-- `&cond.epoch` as a step (`projE`): no stop, the epoch's pointer, the memory unchanged. The
invariant may hold at other ghost values than the step's (`upd G t g` at a stop). -/
theorem _root_.Zig.Full.FLock.Fits.wp_projE (hC : L.Fits (C.prim L) P U ok)
    {G₀ G : ThreadId → γ} {m : Mem} {n : Nat} {Q : Ptr → (ThreadId → γ) → Mem → Nat → Prop}
    (hi : P.inv G₀ m) (h : Q (C.S.ptr.add 4) G m n) :
    P.WP t (ConcM.liftMem (ptrProject C.S.ptr (·.add 4)) : ConcM Tgt Ptr) Q G m n := by
  have hr : ((ptrProject C.S.ptr (·.add 4)).run m).run = some (.ok (C.S.ptr.add 4, m)) := by
    rw [hC.projE hi]; rfl
  refine WP.liftMem (fun e he => ?_) (fun a m' he => ?_) fun hn => ?_
  · rw [hr] at he; cases he
  · rw [hr] at he; cases he; exact ⟨rfl, h⟩
  · rw [hr] at hn; cases hn

end FCond

/-- **A condition implementation** in generated code: `wait(cond, io, mutex)` and
`signal(cond, io)` with the rules that a client uses, for every protocol that keeps the condition
next to its mutex (`C.Fits L P U ok`, with the window; the mutex's contended value `c`) and
counts no turns. Any number of threads may wait and signal.

- `wait_wp`: the mutex's holder, out of the condition's code, that waits returns holding the
  mutex again (after it took a signal). The client's rest allows its entry (`hent`), and the
  client shows that its sleep is not a deadlock when no signal is pending and no signaller is
  between its post and its wake (`hlive`); otherwise the library shows it from the count
  (`Inv.noDeadlock`). The waiter is the running thread (`m.current = t`), the same premise and
  reason as `MutexImpl.unlock_wp`: the waiter holds the mutex, which only the running thread can
  (Zig's `Thread.mutexOwnerCheck`), and every client has the fact from its previous step (the
  lock's post). `Thread.Condition.wait` (0.15.2) needs it: it allocates its deadline block, a
  memory step with no stop before it, first. For the same block the waiter's part holds the
  plain mode (`Res.Plain`, `docs/sep-full-state.md` §Plain mode).
- `signal_wp`: a thread out of the condition's code, outside or holding the mutex, that may
  signal, returns with its exact initial ghost value, including the complete caller part and
  held resource, and the state has a write `k` at or after every state write that happened
  before the call at which no registered waiter lacks a signal (`waiters ≤ signals`), or which
  is a post (`signals` rose). A client with one waiter reads "the waiter is signalled" from it
  and its own history fact (the derived `_one` lemma, maintainer decision 6625654179). -/
structure CondImpl (Tgt : Type) where
  wait : Ptr → Io → Ptr → ConcM Tgt Unit
  signal : Ptr → Io → ConcM Tgt Unit
  /-- The contended value of the mutex that `wait` unlocks and locks. -/
  c : Nat
  wait_wp : ∀ {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, C.Fits L P U ok →
    P.cost = none → ∀ {p q : Ptr}, p = C.S.ptr → q = L.ptr → L.c = c →
    ∀ (t : ThreadId) (g : γ), C.ph g = .out → L.ph g = .holds → ok g →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    (∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m) →
    (∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁) →
    (L.part g).Plain → P.inv (upd G t g) m → m.current = t →
    P.WP t (wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d
  signal_wp : ∀ {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, C.Fits L P U ok →
    P.cost = none → ∀ {p : Ptr}, p = C.S.ptr → ∀ (t : ThreadId) (g : γ), C.ph g = .out →
    (L.ph g = .out ∨ L.ph g = .holds) → C.sx g →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    P.inv (upd G t g) m →
    P.WP t (signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t g) m' ∧
      ∃ k, k < (C.S.hist m').size ∧
        (∀ j, j < (C.S.hist m).size →
          VClock.le (C.S.hist m)[j]!.clock (m.clocks[t]!) = true → j ≤ k) ∧
        (FCond.wOf (C.S.hist m')[k]! ≤ FCond.sOf (C.S.hist m')[k]! ∨
          (0 < k ∧ FCond.sOf (C.S.hist m')[k - 1]! < FCond.sOf (C.S.hist m')[k]!))) G m d

end Full
end Zig
