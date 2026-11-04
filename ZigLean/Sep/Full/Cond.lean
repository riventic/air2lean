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
      C.MStep W t m m' ∧ (C.Ep.hist m' = C.Ep.hist m ∨ ∃ q n h, C.ph g = .inc q n h))
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

/-! ## The protocol after a step -/

/-- An op at the state keeps the epoch's writes. -/
theorem _root_.Zig.Full.FLock.Fits.keepE (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {rX : Res} {m m' : Mem} (hU : U G rX m) (hms : C.MStep C.S t m m') :
    C.Ep.hist m' = C.Ep.hist m := by
  obtain ⟨_, hh⟩ := hms.word ((hC.wRest (.inr rfl)) _ _ _ hU).1
    (.inr (.inr (.inl (by have := C.ep_o; omega)))) (.inl rfl)
  rcases hh with hh | ⟨he, _⟩
  · exact hh
  · have ho := congrArg (fun w : Word 32 4 => w.o) he
    have := C.ep_o
    omega

/-- An op at the epoch keeps the state's writes. -/
theorem _root_.Zig.Full.FLock.Fits.keepS (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {rX : Res} {m m' : Mem} (hU : U G rX m) (hms : C.MStep C.Ep t m m') :
    C.S.hist m' = C.S.hist m := by
  obtain ⟨_, hh⟩ := hms.word ((hC.wRest (.inl rfl)) _ _ _ hU).1
    (.inr (.inr (.inr (by have := C.ep_o; omega)))) (.inr (.inr (.inr (by have := C.ep_o; omega))))
  rcases hh with hh | ⟨he, _⟩
  · exact hh
  · have ho := congrArg (fun w : Word 32 4 => w.o) he
    have := C.ep_o
    omega

/-- After a step of the condition's code by `t` (`g`, new place `p`) that keeps `t`'s lock
place: the protocol's invariant, from the lock's invariant after the step, the rest before it,
and the condition's invariant after it. -/
theorem _root_.Zig.Full.FLock.Fits.backC (hC : L.Fits (C.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {g : γ} {p : CPh} {W : Word 32 4}
    (hW : W = C.S ∨ W = C.Ep) (hg₁ : G₁ t = g) (hn : CPh.Next (C.ph g) p)
    (hU : U G₁ (rsum (W.cellsR m₁) rY) m₁) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : C.MStep W t m₁ m') (hEp : C.Ep.hist m' = C.Ep.hist m₁ ∨ ∃ q n h, C.ph g = .inc q n h)
    (hL : L.Inv G₁ (rsum (W.cellsR m') rY) m') (hI : C.Inv L (upd G₁ t (C.set g p)) m') :
    P.inv (upd G₁ t (C.set g p)) m' :=
  hC.back hW hg₁ ⟨hn, .inl ⟨rfl, rfl⟩, hs, hEp⟩ hU hY hL hI

/-- **A thread enters the wait** (`out` → `en`) holding the mutex: `hroom`, fewer than `65535`
waiters are registered (the state's `u16` count; a protocol bounds its waiters); `hent`, the
client's rest allows the entry. No other thread need be out of the condition's code. -/
theorem _root_.Zig.Full.FLock.Fits.enterEn (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {m : Mem} {g : γ} (hgx : C.ph g = .out) (hgh : L.ph g = .holds)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (C.set g .en)) m := by
  obtain ⟨rX, hL, hU⟩ := (hC.inv _ _).mp hi
  have hnq : ∀ w ∈ m.waiters, w.1 ≠ t := by
    have := hL.w.notQ (t := t) (show L.ph (upd G t g t) ≠ .wait by rw [upd_self, hgh]; decide)
      (show L.ph (upd G t g t) ≠ .away by rw [upd_self, hgh]; decide)
    exact FLock.notQ_mem this
  have hI₀ := hC.wInv _ _ _ hU
  have hI := hI₀.quiet (t := t) (g' := C.set g .en) (m' := m)
    (by rw [upd_self, hgx]; trivial) (by rw [C.ph_set]; trivial) rfl rfl rfl rfl
    rfl (fun _ => VClock.le_refl _) hnq (fun i e h => by rw [C.ph_set] at h; cases h)
    (fun _ => ⟨by rw [hC.lph]; exact hgh, by
      obtain ⟨T, hT, hw, -⟩ := hI₀.cnt; rw [hw]; exact hroom T hT, fun u hu => by
      cases hc : (C.ph (upd G t g u)).crit
      · rfl
      · have h1 := hI₀.crit u hc
        have h2 : L.ph (upd G t g t) = .holds := by rw [upd_self, hgh]
        exact absurd (hL.w.one u t h1 h2) hu⟩)
    (fun _ => (hL.ht (t := t) (by rw [upd_self, hgh]; decide)).1)
    (fun _ _ h => by rw [C.ph_set] at h; cases h)
  rw [upd_upd] at hI
  have hL' := hL.relabel (t := t) (g := C.set g .en) (by rw [upd_self, hC.lph])
    (by rw [upd_self, hC.lpart]) (by rw [upd_self, hC.lheld]) (fun r hr => by
      have := hC.lR (upd G t g) t .en r hr; rwa [upd_self] at this)
  rw [upd_upd] at hL'
  exact (hC.inv _ _).mpr ⟨rX, hL', hent rX hU hI⟩

/-! ## The ops of the condition's code in generated code (`WP`) -/

variable {σ : Type} {s : σ} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}

/-- The waiter's acquire load of the epoch at `en` (holding the mutex): it reads a write `i` its
view allows (not only the newest), `ld i b`, and acquires it. -/
theorem wp_ldEp (hC : L.Fits (C.prim L) P U ok) (hg : C.ph g = .en)
    (hgh : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b i, m'.current = t →
      P.inv (upd G₁ t (C.set g (.ld i b))) m' → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .acquire 4 C.Ep.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hC (hC.wRest (.inr rfl)) (hC.wAp (.inr rfl)) (by rw [hgh]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv _hfl hacq hh hw' hw₀ hct hrun hA _hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      have hms : C.MStep C.Ep t m₁ m' := mstep_op hc₁ hw₀ hct (by rcases hrun with ⟨c, hr⟩; exact .inl ⟨c, _, _, hr⟩) hw' (.inl hh)
      obtain ⟨hI, hnq⟩ := hC.atOp hU (by rw [hg₁, hgh]; decide) (by rw [hg₁, hgh]; decide) hop.waiters hL
      have hcr : (C.ph (G₁ t)).crit = true := by rw [hg₁, hg]; rfl
      refine h k hk G₁ m' b j (hop.current.trans hc₁) (hC.backC (.inr rfl) hg₁
        (by rw [hg]; exact True.intro) hU hY hms (.inl hh) hL ?_)
      have hI' := hI.quiet (t := t) (g' := C.set g (.ld j b)) (m' := m')
        (by rw [hg₁, hg]; trivial) (by rw [C.ph_set]; trivial)
        (hC.keepS hU hms) hh hop.waiters hop.woken hop.threads hop.clock hnq
        (fun i e h' => by rw [C.ph_set] at h'; cases h'; exact ⟨hj, hv, hacq rfl⟩)
        (fun _ => ⟨by rw [hC.lph]; exact hgh, hI.room t hcr, fun u hu => by
          cases hc : (C.ph (G₁ u)).crit
          · rfl
          · exact absurd (hI.crit1 u t hc hcr) hu⟩)
        (fun _ => hI.ex t (by rw [hg₁, hg]; exact nofun))
        (fun _ _ h => by rw [C.ph_set] at h; cases h)
      exact hI'

/-- The `waiters` and `signals` of a state value with `s ≤ w < 65535` (the facts `wp_reg` gives
for the value it read; Zig's `assert(prev_state.waiters < maxInt(u16))`). -/
def RegOld (b : BitVec 32) : Prop := b.toNat % 65536 < 65535 ∧ b.toNat / 65536 ≤ b.toNat % 65536

/-- The waiter's `waiters += 1` at `ld i e` (after it, `reg i jr false e` with `jr` the new
write): it reads the newest state, with room for one more waiter (`RegOld`). -/
theorem _root_.Zig.Full.FLock.Fits.afterReg (hC : L.Fits (C.prim L) P U ok)
    {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {i : Nat} {e : BitVec 32} {ord : AtomicOrder} {old : BitVec 32}
    (hg₁ : G₁ t = g) (hg : C.ph g = .ld i e) (hgh : L.ph g = .holds)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hms : C.MStep C.S t m₁ m')
    (hA : ∀ hF, (∀ x, C.S.o ≤ x → x < C.S.o + 4 → hF (C.S.b, x) = none) →
      FStepIn hF m₁ m')
    (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hv : (C.lastS m₁).Val old)
    (hh : C.S.hist m' = (C.S.hist m₁).push (Word.rmwEnt m' t ord (C.lastS m₁) (old + 1))) :
    RegOld old ∧ P.inv (upd G₁ t (C.set g (.reg i (C.S.hist m₁).size false e))) m' := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  obtain ⟨hI, -⟩ := hC.atOp hU (by rw [hg₁, hgh]; decide) (by rw [hg₁, hgh]; decide) hop.waiters hL
  have hcr : (C.ph (G₁ t)).crit = true := by rw [hg₁, hg]; rfl
  have hold : val (C.lastS m₁) = old := val_of hv
  have hroom := hI.room t hcr
  have hsw := hI.s_le_w
  unfold wOf at hroom hsw; unfold sOf at hsw
  rw [hold] at hroom hsw
  refine ⟨⟨hroom, hsw⟩, hC.backC (.inl rfl) hg₁ (by rw [hg]; exact ⟨rfl, rfl, rfl⟩) hU hY hms
    (.inl (hC.keepE hU hms)) hL ?_⟩
  exact hI.register (by rw [hg₁]; exact hg) (by rw [C.ph_set]) hh
    (by rw [hold]; exact FEvent.rmwEnt_val) (VClock.le_refl _) (hC.keepE hU hms) hop.waiters
    hop.woken hop.threads hop.clock

/-- The waiter's `waiters += 1` on bits (`atomicRmwC`, `Thread.Condition`). -/
theorem wp_reg (hC : L.Fits (C.prim L) P U ok) {i : Nat} {e : BitVec 32}
    (hg : C.ph g = .ld i e) (hgh : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' jr old, m'.current = t → RegOld old →
      P.inv (upd G₁ t (C.set g (.reg i jr false e))) m' → Q (old, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .add false .relaxed 4 C.S.ptr (1 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n :=
  FLock.wp_wordRmw hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgh]; decide) hi
    fun k hk G₁ rY m₁ m' old hg₁ hc₁ hU hY hv _ hh _ hw' hw₀ hct hrun hA _hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      obtain ⟨hro, hi'⟩ := hC.afterReg hg₁ hg hgh hU hY (mstep_op hc₁ hw₀ hct (by rcases hrun with ⟨c, hr⟩; exact .inr (.inl ⟨c, _, _, _, _, _, hr⟩)) hw' (.inr ⟨_, _, hh⟩)) hA hL hv hh
      exact h k hk G₁ m' _ old (hop.current.trans hc₁) hro hi'

/-- The waiter's `waiters += 1` with a decode (`atomicRmwAsC`, `Io.Condition`): `v` encodes one
waiter, and every state value with room decodes (`hdec`). -/
theorem wp_regAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok) {i : Nat}
    {e : BitVec 32} {v : α} (hv1 : Packed.toBits v = (1 : BitVec 32))
    (hdec : ∀ b : BitVec 32, RegOld b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (hg : C.ph g = .ld i e) (hgh : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' jr old r, m'.current = t → RegOld old →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      P.inv (upd G₁ t (C.set g (.reg i jr false e))) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .add .relaxed 4 C.S.ptr v : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordRmwAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgh]; decide) hi
    (fun G₁ rY m₁ hg₁ hc₁ hU b hb => by
      have hI := hC.wInv _ _ _ hU
      have hcr : (C.ph (G₁ t)).crit = true := by rw [hg₁, hg]; rfl
      have hroom := hI.room t hcr
      have hsw := hI.s_le_w
      unfold wOf at hroom hsw; unfold sOf at hsw
      rw [val_of hb] at hroom hsw
      exact hdec b ⟨hroom, hsw⟩)
    fun k hk G₁ rY m₁ m' old r hg₁ hc₁ hU hY hd hv _ hh _ hw' hw₀ hct hrun hA _hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      rw [hv1] at hh
      obtain ⟨hro, hi'⟩ := hC.afterReg hg₁ hg hgh hU hY (mstep_op hc₁ hw₀ hct (by rcases hrun with ⟨c, hr⟩; exact .inr (.inl ⟨c, _, _, _, _, _, hr⟩)) hw' (.inr ⟨_, _, hh⟩)) hA hL hv hh
      exact h k hk G₁ m' _ old r (hop.current.trans hc₁) hro hd hi'

/-- A state value `(w, s)` with `s ≤ w` (H1: every state write has one). -/
def SOk (b : BitVec 32) : Prop := b.toNat / 65536 ≤ b.toNat % 65536

/-- The waiter's place after it read the state value `b` at `reg i jr true e`: it goes back to
its futex wait (`sn := false`, the loop-back) when `b` has no signal. -/
abbrev afterRead (i jr : Nat) (e b : BitVec 32) : CPh := .reg i jr (decide (b.toNat / 65536 ≠ 0)) e

/-- **The waiter's read of the state** at `reg i jr true e` (a relaxed load, or a failed
`cmpxchg`), of a write `j` at or after its floor, with no write: with no signal it loops back
(`Inv.loopBack`), else it stays. -/
theorem _root_.Zig.Full.FLock.Fits.afterReadS (hC : L.Fits (C.prim L) P U ok)
    {G₁ : ThreadId → γ} {rY : Res} {m₁ m' : Mem} {i jr j : Nat} {e b : BitVec 32}
    (hg₁ : G₁ t = g) (hg : C.ph g = .reg i jr true e)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hms : C.MStep C.S t m₁ m')
    (hA : ∀ hF, (∀ x, C.S.o ≤ x → x < C.S.o + 4 → hF (C.S.b, x) = none) →
      FStepIn hF m₁ m')
    (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hj : j < (C.S.hist m₁).size) (hv : (C.S.hist m₁)[j]!.Val b)
    (hfl : Word.Floor (C.S.hist m₁) (m₁.clocks[t]!) j) (hh : C.S.hist m' = C.S.hist m₁) :
    SOk b ∧ P.inv (upd G₁ t (C.set g (afterRead i jr e b))) m' := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  have hI := hC.wInv _ _ _ hU
  have hE := hC.keepE hU hms
  have hsv := (hI.sv j hj).2
  unfold sOf wOf at hsv
  rw [val_of hv] at hsv
  refine ⟨hsv, ?_⟩
  by_cases hs : b.toNat / 65536 = 0
  · have hp : afterRead i jr e b = .reg i jr false e := by simp [afterRead, hs]
    rw [hp]
    exact hC.backC (.inl rfl) hg₁ (by rw [hg]; exact ⟨rfl, Nat.le_refl _⟩) hU hY hms (.inl hE) hL
      (hI.loopBack (by rw [hg₁]; exact hg) (by rw [C.ph_set]) hh hE hop.waiters hop.woken
        hop.threads hop.clock hj hfl (by unfold sOf; rw [val_of hv]; exact hs))
  · have hp : afterRead i jr e b = .reg i jr true e := by simp [afterRead, hs]
    rw [hp, ← hg, set_of rfl]
    have hI' := hI.stay hh hE (by rw [hop.waiters]) (fun w hw _ => by rw [hop.waiters] at hw; exact hw)
      (fun u _ hw => by rw [hop.woken]; exact hw) (by rw [hop.threads]; exact Nat.le_refl _) hop.clock
    have := hC.backC (p := C.ph g) (.inl rfl) hg₁ (CPh.Next.refl _) hU hY hms (.inl hE) hL
      (by rw [set_of rfl, ← hg₁, upd_same]; exact hI')
    rwa [set_of rfl] at this

/-- The waiter's relaxed load of the state at `reg i jr true e` (`atomicLoadC`,
`Thread.Condition`). -/
theorem wp_loadS (hC : L.Fits (C.prim L) P U ok) {i jr : Nat}
    {e : BitVec 32} (hg : C.ph g = .reg i jr true e) (hgo : L.ph g = .out)
    (hi : P.inv (upd G t g) m) {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t → SOk b →
      P.inv (upd G₁ t (C.set g (afterRead i jr e b))) m' → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .relaxed 4 C.S.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv hfl _ hh hw' hw₀ hct hrun hA _hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      obtain ⟨hok, hi'⟩ := hC.afterReadS hg₁ hg hU hY (mstep_op hc₁ hw₀ hct (by rcases hrun with ⟨c, hr⟩; exact .inl ⟨c, _, _, hr⟩) hw' (.inl hh)) hA hL hj hv hfl hh
      exact h k hk G₁ m' b (hop.current.trans hc₁) hok hi'

/-- The decode of every state value (`SOk`, H1). -/
theorem dec_of {α : Type} [Packed α 32]
    (hdec : ∀ b : BitVec 32, SOk b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {G₁ : ThreadId → γ} {m₁ : Mem} (hI : C.Inv L G₁ m₁) :
    ∀ j < (C.S.hist m₁).size, ∀ b, (C.S.hist m₁)[j]!.Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r) :=
  fun j hj b hv => hdec b (by
    have hsv := (hI.sv j hj).2
    unfold sOf wOf at hsv; rw [val_of hv] at hsv; exact hsv)

/-- The waiter's relaxed load of the state with a decode (`atomicLoadAsC`, `Io.Condition`). -/
theorem wp_loadSAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok)
    (hdec : ∀ b : BitVec 32, SOk b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {i jr : Nat} {e : BitVec 32} (hg : C.ph g = .reg i jr true e) (hgo : L.ph g = .out)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b r, m'.current = t →
      (Packed.ofBits? (α := α) b).run = some (.ok r) → SOk b →
      P.inv (upd G₁ t (C.set g (afterRead i jr e b))) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α .relaxed 4 C.S.ptr : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordLoadAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    (fun _ _ _ _ _ hU => dec_of hdec (hC.wInv _ _ _ hU))
    fun k hk G₁ rY m₁ m' b r j hg₁ hc₁ hU hY hd hj hv hfl _ hh hw' hw₀ hct hrun hA _hS _hR hL => by
      have hop := hA (fun _ => none) (fun _ _ _ => rfl)
      obtain ⟨hok, hi'⟩ := hC.afterReadS hg₁ hg hU hY (mstep_op hc₁ hw₀ hct (by rcases hrun with ⟨c, hr⟩; exact .inl ⟨c, _, _, hr⟩) hw' (.inl hh)) hA hL hj hv hfl hh
      exact h k hk G₁ m' b r (hop.current.trans hc₁) hd hok hi'

/-- A consume's value: `(w, s) - (1, 1)` with `0 < s ≤ w`. -/
theorem consume_val {b : BitVec 32} (hs : 0 < b.toNat / 65536) (hok : SOk b) :
    (b - 0x10001).toNat % 65536 + 1 = b.toNat % 65536 ∧
      (b - 0x10001).toNat / 65536 + 1 = b.toNat / 65536 := by
  unfold SOk at hok
  have h1 : 65537 ≤ b.toNat := by omega
  have h2 : (b - 0x10001).toNat = b.toNat - 65537 := by bv_omega
  rw [h2]; omega

/-- **The waiter takes a signal**: its successful `cmpxchg((w, s) → (w - 1, s - 1))` at
`reg i jr true e` with `0 < s` (the loop's guard): it is out of the condition's code. -/
theorem _root_.Zig.Full.FLock.Fits.afterConsume (hC : L.Fits (C.prim L) P U ok)
    {G₁ : ThreadId → γ} {rY : Res} {m₁ m' : Mem} {i jr : Nat} {e exp : BitVec 32}
    {ord : AtomicOrder}
    (hg₁ : G₁ t = g) (hg : C.ph g = .reg i jr true e) (hgo : L.ph g = .out)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hms : C.MStep C.S t m₁ m')
    (hA : ∀ hF, (∀ x, C.S.o ≤ x → x < C.S.o + 4 → hF (C.S.b, x) = none) →
      FStepIn hF m₁ m')
    (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hs : 0 < exp.toNat / 65536) (hv : (C.lastS m₁).Val exp)
    (hh : C.S.hist m' = (C.S.hist m₁).push (Word.rmwEnt m' t ord (C.lastS m₁) (exp - 0x10001))) :
    P.inv (upd G₁ t (C.set g .out)) m' := by
  have hop := hA (fun _ => none) (fun _ _ _ => rfl)
  have hI := hC.wInv _ _ _ hU
  have hok : SOk exp := by
    have := hI.s_le_w; unfold sOf wOf at this; rw [val_of hv] at this; exact this
  obtain ⟨hw1, hs1⟩ := consume_val hs hok
  have hxv : (Word.rmwEnt m' t ord (C.lastS m₁) (exp - 0x10001)).Val (exp - 0x10001) :=
    FEvent.rmwEnt_val
  exact hC.backC (.inl rfl) hg₁ (by rw [hg]; exact True.intro) hU hY hms (.inl (hC.keepE hU hms)) hL
    (hI.consume (by rw [hg₁]; exact hg) (by rw [C.ph_set]) hh (by rw [val_of hxv]; exact hxv)
      (by unfold wOf; rw [val_of hxv, val_of hv]; exact hw1)
      (by unfold sOf; rw [val_of hxv, val_of hv]; exact hs1)
      (hC.keepE hU hms) hop.waiters hop.woken hop.threads hop.clock)

/-- The waiter's weak `cmpxchg((w, s) → (w - 1, s - 1))` (acquire) at `reg i jr true e` with
`0 < s`, on bits (`Thread.Condition`): on success it is out; on failure it read a state value
(`afterReadS`). -/
theorem wp_consume (hC : L.Fits (C.prim L) P U ok) {succ fail : AtomicOrder}
    {exp new : BitVec 32} (hs : 0 < exp.toNat / 65536) (hnew : new = exp - 0x10001) {i jr : Nat}
    {e : BitVec 32} (hg : C.ph g = .reg i jr true e) (hgo : L.ph g = .out)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (C.set g .out)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b, SOk b → P.inv (upd G₁ t (C.set g (afterRead i jr e b))) m' →
        Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakC (n := 32) succ fail 4 C.S.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  subst hnew
  exact FLock.wp_wordWeakCas hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hw₀ hct hrun hA _hS hL =>
      let hop := hA (fun _ => none) (fun _ _ _ => rfl)
      let hms := mstep_op (C := C) hc₁ hw₀ hct
        (by rcases hrun with ⟨c, r, hr⟩; exact .inr (.inr (.inr (.inl ⟨c, _, _, _, _, r, hr⟩)))) hw'
      ⟨fun hv _ hh _ _hR =>
        (h k hk G₁ m' (hop.current.trans hc₁)).1
          (hC.afterConsume hg₁ hg hgo hU hY (hms (.inr ⟨_, _, hh⟩)) hA hL hs hv hh),
       fun j b hj hv hfl _ hh _hR =>
        let r := hC.afterReadS hg₁ hg hU hY (hms (.inl hh)) hA hL hj hv hfl hh
        (h k hk G₁ m' (hop.current.trans hc₁)).2 b r.1 r.2⟩

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
