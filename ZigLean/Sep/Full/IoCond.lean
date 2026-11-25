import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.AutoWP

/-!
# `Io.Condition` as a condition (`CondImpl`), once for every program and Zig version

`Io.Condition`'s `signal`, `broadcast` and `waitUncancelable` (Zig 0.16.0 and 0.17.1) are the
same code in every program that uses them, up to names and one difference between the versions: 0.16.0's
`waitUncancelable` calls `waitInner(…, true)`, which holds the registration and the loops, and
0.17.1 inlines that code into `waitUncancelable`. `IoCondCode Tgt` is that code passed as
parameters, as `IoMutexCode` (`ZigLean/Sep/Full/IoMutex.lean`) is for `Io.Mutex`: a program's
functions with their unfolding equations over the code's normal form (`bind_assoc`, `pure_bind`,
`ite_bind`), the generated matches on the code's own exits as continuations of which the proof
uses only their values at the exits it takes, and the mutex the wait unlocks and locks as a
`MutexImpl` field. The registration and its two loops are the wait's *core*
(`waitInner(…, true)` of 0.16.0, `waitUncancelable` of 0.17.1); `WaitShape` states the wait as
its core, directly (0.17.1) or through a call that checks the core's return (0.16.0).

`IoCondCode.impl` proves the condition contract (`CondImpl`, `ZigLean/Sep/Full/Cond.lean`) once,
from the rules of the futex-epoch condition: `signal`, `broadcast` and `waitUncancelable`, for
every protocol that has the condition next to its mutex. A program instantiates it with its generated names and
`rfl`/`simp` proofs of the equations, once per translation (`Proofs/Sync/Cond.lean`, and one
instance per golden case in `Proofs/Sync/CondCases.lean`). The wait's walks are rule-by-rule term
proofs: `fsym` cannot yet walk a shape whose continuations are hypotheses (ledger
`fsym-abstract-shape`).

The state `Io.Condition.State` is the packed `(waiters, signals)`: the low and the high 16 bits
of the condition's state word (`FCond`), every bit pattern a value (`ofBits?_ok`).
-/

namespace Zig
namespace Full

open Conc Proto

namespace IoCondCode

variable {Tgt S : Type} [Packed S 32]

/-- `signal`'s loop body, in normal form: the loop-entry tick; if the state has a waiter without
a signal (`waiters > signals`), the `cmpxchg` that adds a signal; on success the epoch increment
and its futex wake, on failure a repeat with the value read. -/
def sbodyOf {σ E : Type} (wa si : S → BitVec 16) (mk : BitVec 16 → BitVec 16 → S)
    (prev : σ → S) (setPrev : σ → S → σ) (rep stop ret : E) (p : Ptr) (io : Io) :
    CM Tgt σ E := do
  callMC tick
  let x ← get
  let x_1 ← get
  if gt false (wa (prev x)) (si (prev x_1)) = true then do
    let x ← get
    let x_2 ← get
    let x_3 ← get
    let x_4 ← add false (si (prev x_3)) (1 : BitVec 16)
    let x ← cmpxchgWeakAsC AtomicOrder.release AtomicOrder.relaxed 4 p (prev x)
      (mk (wa (prev x_2)) x_4)
    if x.isSome = true then do
      let x ← optPayload x
      modify fun s => setPrev s x
      pure rep
    else do
      let i36 ← callMC (ptrProject p fun x => x.add 4)
      let _ ← atomicRmwC RmwOp.add false AtomicOrder.release 4 i36 (1 : BitVec 32)
      let i43 ← callMC (ptrProject p fun x => x.add 4)
      futexWakeC io i43 (1 : BitVec 32)
      pure ret
  else pure stop

/-- `broadcast`'s loop body, in normal form: as `signal`'s (`sbodyOf`), but the `cmpxchg` gives
every waiter its signal (`signals := waiters`) and the wake is of `waiters - signals` threads. -/
def bbodyOf {σ E : Type} (wa si : S → BitVec 16) (mk : BitVec 16 → BitVec 16 → S)
    (prev : σ → S) (setPrev : σ → S → σ) (rep stop ret : E) (p : Ptr) (io : Io) :
    CM Tgt σ E := do
  callMC tick
  let x ← get
  let x_1 ← get
  if gt false (wa (prev x)) (si (prev x_1)) = true then do
    let x ← get
    let x_2 ← get
    let x_3 ← get
    let x ← cmpxchgWeakAsC AtomicOrder.release AtomicOrder.relaxed 4 p (prev x)
      (mk (wa (prev x_2)) (wa (prev x_3)))
    if x.isSome = true then do
      let x ← optPayload x
      modify fun s => setPrev s x
      pure rep
    else do
      let i35 ← callMC (ptrProject p fun x => x.add 4)
      let _ ← atomicRmwC RmwOp.add false AtomicOrder.release 4 i35 (1 : BitVec 32)
      let i40 ← callMC (ptrProject p fun x => x.add 4)
      let x_4 ← get
      let x_5 ← get
      let i47 ← sub false (wa (prev x_4)) (si (prev x_5))
      let i48 ← intCast false false 32 i47 (safe := false)
      futexWakeC io i40 i48
      pure ret
  else pure stop

/-- `signal` and `broadcast` in normal form: the relaxed load of the state, then the loop. `k` is
the generated match after the loop, `fin` the one on the function's exit. -/
def signalOf {σ E : Type} [Inhabited σ] (setPrev : σ → S → σ) (body : Ptr → Io → CM Tgt σ E)
    (again : E → Bool) (k : E → CM Tgt σ E) (fin : E → ConcM Tgt Unit) (p : Ptr) (io : Io) :
    ConcM Tgt Unit := do
  let e ← StateT.run' (do
      let v ← atomicLoadAsC S AtomicOrder.relaxed 4 p
      modify fun s => setPrev s v
      let y ← loop (body p io) again
      k y) default
  fin e

/-- The wait's inner loop body, in normal form: the loop-entry tick; if the state value read last
has a signal, the `cmpxchg` that takes it with the waiter's registration; on success `lock`, on
failure a repeat with the value read; without a signal the loop ends (`stop`). -/
def innerOf {σ E : Type} (wa si : S → BitVec 16) (mk : BitVec 16 → BitVec 16 → S)
    (prev : σ → S) (setPrev : σ → S → σ) (lock : Ptr → Io → ConcM Tgt Unit) (rep stop done : E)
    (p : Ptr) (io : Io) (q : Ptr) : CM Tgt σ E := do
  callMC tick
  let x ← get
  if gt false (si (prev x)) (0 : BitVec 16) = true then do
    let x ← get
    let x_1 ← get
    let x_2 ← sub false (wa (prev x_1)) (1 : BitVec 16)
    let x_3 ← get
    let x_4 ← sub false (si (prev x_3)) (1 : BitVec 16)
    let x ← cmpxchgWeakAsC AtomicOrder.acquire AtomicOrder.relaxed 4 p (prev x) (mk x_2 x_4)
    if x.isSome = true then do
      let x ← optPayload x
      modify fun s => setPrev s x
      pure rep
    else do
      callC (lock q io)
      pure done
  else pure stop

/-- The wait's outer loop body, in normal form: the loop-entry tick, the futex wait on the epoch
the waiter saved, the epoch's and the state's loads, and the inner loop. `k` is the generated
match after the inner loop. -/
def outerOf {σ E : Type} (ep : σ → BitVec 32) (setEp : σ → BitVec 32 → σ) (setPrev : σ → S → σ)
    (inner : Ptr → Io → Ptr → CM Tgt σ E) (again : E → Bool) (k : E → CM Tgt σ E) (p : Ptr)
    (io : Io) (q : Ptr) : CM Tgt σ E := do
  callMC tick
  let x ← callMC (ptrProject p fun x => x.add 4)
  let x_1 ← get
  futexWaitC io x (ep x_1)
  let x ← callMC (ptrProject p fun x => x.add 4)
  let x ← atomicLoadC (n := 32) AtomicOrder.acquire 4 x
  modify fun s => setEp s x
  let x ← atomicLoadAsC S AtomicOrder.relaxed 4 p
  modify fun s => setPrev s x
  let y ← loop (inner p io q) again
  k y

/-- The wait's core in normal form: the epoch's load, the registration (`waiters += 1`, with its
`assert`), `unlock`, and the outer loop. `fin` is the generated match on the function's exit. -/
def coreOf {σ E R : Type} [Inhabited σ] (wa : S → BitVec 16) (setEp : σ → BitVec 32 → σ)
    (dassert : Bool → Result Unit) (unlock : Ptr → Io → ConcM Tgt Unit)
    (outer : Ptr → Io → Ptr → CM Tgt σ E) (again : E → Bool) (fin : E → ConcM Tgt R) (p : Ptr)
    (io : Io) (q : Ptr) : ConcM Tgt R := do
  let e ← StateT.run' (do
      let i6 ← callMC (ptrProject p fun x => x.add 4)
      let v7 ← atomicLoadC (n := 32) AtomicOrder.acquire 4 i6
      modify fun s => setEp s v7
      let x ← atomicRmwAsC RmwOp.add AtomicOrder.relaxed 4 p (Packed.ofBits (1 : BitVec 32) : S)
      callRC (dassert (lt false (wa x) (65535 : BitVec 16)))
      callC (unlock q io)
      loop (outer p io q) again) default
  fin e

end IoCondCode

/-- The uncancelable wait as its core (`IoCondCode`): the core itself (`direct`, Zig 0.17.1), or
a call of the core whose generated code continues with `k` on the core's return and ends with
`fin` (`call`, Zig 0.16.0's `waitInner(…, true)`). -/
inductive IoCondCode.WaitShape {Tgt R : Type} (core : Ptr → Io → Ptr → ConcM Tgt R) (rv : R)
    (wait : Ptr → Io → Ptr → ConcM Tgt Unit) : Prop where
  | direct (h : ∀ p io q, wait p io q = (core p io q >>= fun _ => pure ()))
  | call {σ E : Type} [Inhabited σ] (k : R → CM Tgt σ E) (wret : E) (fin : E → ConcM Tgt Unit)
      (h : ∀ p io q, wait p io q = (do
        let e ← StateT.run' (do let r ← callC (core p io q); k r) default
        fin e))
      (hk : k rv = pure wret) (hfin : fin wret = pure ())

/-- `Io.Condition`'s code in a program's generated code (module doc). -/
structure IoCondCode (Tgt : Type) where
  /-- The mutex the wait unlocks and locks again. -/
  M : MutexImpl Tgt
  /-- `Io.Condition.State`, its fields `waiters` and `signals`, and its constructor. -/
  S : Type
  [pk : Packed S 32]
  wa : S → BitVec 16
  si : S → BitVec 16
  pack : BitVec 16 → BitVec 16 → S
  /- The facts below are definitional for generated code: each defaults to `rfl`. -/
  ofBits?_ok : ∀ b : BitVec 32,
    (Packed.ofBits? (α := S) b).run = some (Except.ok (Packed.ofBits b)) := by intros; rfl
  wa_ofBits : ∀ b : BitVec 32, wa (Packed.ofBits b) = b.extractLsb' 0 16 := by intros; rfl
  si_ofBits : ∀ b : BitVec 32, si (Packed.ofBits b) = b.extractLsb' 16 16 := by intros; rfl
  toBits_pack : ∀ w s : BitVec 16,
    Packed.toBits (pack w s) = (w.setWidth 32 <<< 0) ||| (s.setWidth 32 <<< 16) := by intros; rfl
  pack_eta : ∀ x : S, pack (wa x) (si x) = x := by intros; rfl
  /-- The program's `debug.assert`. -/
  dassert : Bool → Result Unit
  dassert_true : (dassert true).run = some (.ok ()) := by rfl
  /-- `signal`'s locals (`prev_state`) and exits: the return, the loop's end, its repeat. -/
  σs : Type
  [inhs : Inhabited σs]
  Es : Type
  sprev : σs → S
  ssetPrev : σs → S → σs
  sprev_set : ∀ s v, sprev (ssetPrev s v) = v := by intros; rfl
  sret : Es
  sstop : Es
  srep : Es
  sagain : Es → Bool
  sagain_rep : sagain srep = true := by rfl
  sagain_stop : sagain sstop = false := by rfl
  sagain_ret : sagain sret = false := by rfl
  /-- `signal`'s loop body. -/
  sbody : Ptr → Io → CM Tgt σs Es
  sbody_eq : ∀ p io, sbody p io = IoCondCode.sbodyOf wa si pack sprev ssetPrev srep sstop sret p io
  /-- `signal`. -/
  signal : Ptr → Io → ConcM Tgt Unit
  signal_eq : ∃ (k : Es → CM Tgt σs Es) (fin : Es → ConcM Tgt Unit),
    (∀ p io, signal p io = IoCondCode.signalOf ssetPrev sbody sagain k fin p io) ∧
    k sstop = pure sret ∧ k sret = pure sret ∧ fin sret = pure ()
  /-- `broadcast`'s locals (`prev_state`) and exits, as `signal`'s. -/
  σb : Type
  [inhb : Inhabited σb]
  Eb : Type
  bprev : σb → S
  bsetPrev : σb → S → σb
  bprev_set : ∀ s v, bprev (bsetPrev s v) = v := by intros; rfl
  bret : Eb
  bstop : Eb
  brep : Eb
  bagain : Eb → Bool
  bagain_rep : bagain brep = true := by rfl
  bagain_stop : bagain bstop = false := by rfl
  bagain_ret : bagain bret = false := by rfl
  /-- `broadcast`'s loop body. -/
  bbody : Ptr → Io → CM Tgt σb Eb
  bbody_eq : ∀ p io, bbody p io = IoCondCode.bbodyOf wa si pack bprev bsetPrev brep bstop bret p io
  /-- `broadcast`: `signal`'s entry around its own loop. -/
  broadcast : Ptr → Io → ConcM Tgt Unit
  broadcast_eq : ∃ (k : Eb → CM Tgt σb Eb) (fin : Eb → ConcM Tgt Unit),
    (∀ p io, broadcast p io = IoCondCode.signalOf bsetPrev bbody bagain k fin p io) ∧
    k bstop = pure bret ∧ k bret = pure bret ∧ fin bret = pure ()
  /-- The wait core's locals (`epoch`, `prev_state`) and exits: the core's return (`done`), the
  inner loop's end and repeat, the outer loop's repeat. -/
  σ : Type
  [inh : Inhabited σ]
  E : Type
  ep : σ → BitVec 32
  setEp : σ → BitVec 32 → σ
  prev : σ → S
  setPrev : σ → S → σ
  ep_setEp : ∀ s v, ep (setEp s v) = v := by intros; rfl
  ep_setPrev : ∀ s v, ep (setPrev s v) = ep s := by intros; rfl
  prev_setPrev : ∀ s v, prev (setPrev s v) = v := by intros; rfl
  done : E
  istop : E
  irep : E
  orep : E
  iagain : E → Bool
  oagain : E → Bool
  iagain_rep : iagain irep = true := by rfl
  iagain_stop : iagain istop = false := by rfl
  iagain_done : iagain done = false := by rfl
  oagain_rep : oagain orep = true := by rfl
  oagain_done : oagain done = false := by rfl
  /-- The inner loop's body. -/
  inner : Ptr → Io → Ptr → CM Tgt σ E
  inner_eq : ∀ p io q, inner p io q = IoCondCode.innerOf wa si pack prev setPrev M.lock irep istop
    done p io q
  /-- The outer loop's body. -/
  outer : Ptr → Io → Ptr → CM Tgt σ E
  outer_eq : ∃ k : E → CM Tgt σ E,
    (∀ p io q, outer p io q = IoCondCode.outerOf ep setEp setPrev inner iagain k p io q) ∧
    k istop = pure orep ∧ k done = pure done
  /-- The wait's core, with its return value. -/
  R : Type
  rv : R
  core : Ptr → Io → Ptr → ConcM Tgt R
  core_eq : ∃ fin : E → ConcM Tgt R,
    (∀ p io q, core p io q = IoCondCode.coreOf wa setEp dassert M.unlock outer oagain fin p io q) ∧
    fin done = pure rv
  /-- `waitUncancelable`. -/
  wait : Ptr → Io → Ptr → ConcM Tgt Unit
  wait_eq : IoCondCode.WaitShape core rv wait

namespace IoCondCode

attribute [instance] IoCondCode.pk IoCondCode.inhs IoCondCode.inhb IoCondCode.inh

variable {Tgt : Type} (X : IoCondCode Tgt)

/-! ## The state's values

Stated for an abstract value `b`, so that the walks keep `b` abstract. -/

theorem s_dec : ∀ b : BitVec 32, FCond.SOk b →
    ∃ r, (Packed.ofBits? (α := X.S) b).run = some (.ok r) :=
  fun b _ => ⟨_, X.ofBits?_ok b⟩

theorem s_eq {b : BitVec 32} {r : X.S}
    (h : (Packed.ofBits? (α := X.S) b).run = some (.ok r)) : r = Packed.ofBits b := by
  rw [X.ofBits?_ok] at h; cases h; rfl

/-- `waiters` is the low half of the state word. -/
theorem s_w (b : BitVec 32) : (X.wa (Packed.ofBits b)).toNat = b.toNat % 65536 := by
  rw [X.wa_ofBits]
  simp

/-- `signals` is the high half of the state word. -/
theorem s_s (b : BitVec 32) : (X.si (Packed.ofBits b)).toNat = b.toNat / 65536 := by
  rw [X.si_ofBits]
  have := b.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The state word of `(waiters, signals)`. -/
theorem s_mk (w s : BitVec 16) :
    (Packed.toBits (X.pack w s)).toNat = w.toNat + 65536 * s.toNat := by
  rw [X.toBits_pack]
  have hw := w.isLt
  have hs := s.isLt
  rw [BitVec.toNat_or, BitVec.shiftLeft_zero, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : s.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- Every state word is the word of its value. -/
theorem s_bits (b : BitVec 32) : Packed.toBits (Packed.ofBits b : X.S) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← X.pack_eta (Packed.ofBits b), s_mk, s_w, s_s]
  omega

/-- `signal`'s post: one more signal to a state with a waiter lacking one. -/
theorem s_post {b : BitVec 32} {r : BitVec 16}
    (hlt : ¬b.toNat % 65536 ≤ b.toNat / 65536)
    (hr : r.toNat = b.toNat / 65536 + 1) :
    FCond.PostOk (Packed.toBits (Packed.ofBits b : X.S))
      (Packed.toBits (X.pack (X.wa (Packed.ofBits b)) r)) := by
  unfold FCond.PostOk
  rw [s_bits, s_mk, s_w, hr]
  omega

/-- `broadcast`'s post: a signal for every waiter, `(w, s) → (w, w)`, to a state with a waiter
lacking one. -/
theorem s_bpost {b : BitVec 32} (hlt : ¬b.toNat % 65536 ≤ b.toNat / 65536) :
    FCond.PostOk (Packed.toBits (Packed.ofBits b : X.S))
      (Packed.toBits (X.pack (X.wa (Packed.ofBits b)) (X.wa (Packed.ofBits b)))) := by
  unfold FCond.PostOk
  rw [s_bits, s_mk, s_w]
  omega

/-- The state `(w, w)` is served. -/
theorem s_bserved (x : BitVec 16) :
    (Packed.toBits (X.pack x x)).toNat % 65536 ≤ (Packed.toBits (X.pack x x)).toNat / 65536 := by
  rw [s_mk]
  have : x.toNat < 65536 := x.isLt
  omega

/-- The waiter's take of a signal: `(w, s) - (1, 1)`, with `0 < s ≤ w`. -/
theorem s_take {b : BitVec 32} (hok : FCond.SOk b) (hs : b.toNat / 65536 ≠ 0) :
    Packed.toBits (X.pack (X.wa (Packed.ofBits b) - 1) (X.si (Packed.ofBits b) - 1)) =
      Packed.toBits (Packed.ofBits b : X.S) - 0x10001 := by
  unfold FCond.SOk at hok
  rw [s_bits]
  apply BitVec.eq_of_toNat_eq
  have hw := X.s_w b
  have hs' := X.s_s b
  have h1 : (X.wa (Packed.ofBits b) - 1).toNat = (X.wa (Packed.ofBits b)).toNat - 1 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hw]; simp; omega)
  have h2 : (X.si (Packed.ofBits b) - 1).toNat = (X.si (Packed.ofBits b)).toNat - 1 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hs']; simp; omega)
  have h3 : (b - 0x10001).toNat = b.toNat - 65537 := by bv_omega
  rw [s_mk, h1, h2, h3, hw, hs']
  omega

/-- A state value with a signal: `0 < s`. -/
theorem s_sig (b : BitVec 32) :
    gt false (X.si (Packed.ofBits b)) 0 = decide (b.toNat / 65536 ≠ 0) := by
  simp only [gt, lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, s_s]
  by_cases h : b.toNat / 65536 = 0 <;> simp [h] <;> omega

/-- A state value with a waiter lacking a signal: `w > s`. -/
theorem s_gt (b : BitVec 32) :
    gt false (X.wa (Packed.ofBits b)) (X.si (Packed.ofBits b)) =
      decide ¬(b.toNat % 65536 ≤ b.toNat / 65536) := by
  simp only [gt, lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, s_s, s_w]
  by_cases h : b.toNat % 65536 ≤ b.toNat / 65536 <;> simp [h] <;> omega

theorem s_subW {b : BitVec 32} (hok : FCond.SOk b) (hs : b.toNat / 65536 ≠ 0) :
    (sub false (X.wa (Packed.ofBits b)) (1 : BitVec 16)).run =
    some (.ok (X.wa (Packed.ofBits b) - 1)) := by
  unfold FCond.SOk at hok
  rw [Auto.sub_ok (by rw [s_w]; simp; omega)]; rfl

theorem s_subS {b : BitVec 32} (hs : b.toNat / 65536 ≠ 0) :
    (sub false (X.si (Packed.ofBits b)) (1 : BitVec 16)).run =
    some (.ok (X.si (Packed.ofBits b) - 1)) := by
  rw [Auto.sub_ok (by rw [s_s]; simp; omega)]; rfl

/-- `assert(prev_state.waiters < maxInt(u16))` of a registration (`FCond.RegOld`). -/
theorem s_room {b : BitVec 32} (h : FCond.RegOld b) :
    lt false (X.wa (Packed.ofBits b)) (65535 : BitVec 16) = true := by
  unfold FCond.RegOld at h
  simp only [lt, Bool.false_eq_true, ↓reduceIte, BitVec.ult, s_w]
  simp; omega

section
variable {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
  {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-! ## `signal` and `broadcast`

Both are the relaxed load of the state and a loop (`signalOf`) that ends when every waiter has
its signal; they differ in the loop's `cmpxchg` and wake, and in the history post: `signal`'s
for `all = false`, `broadcast`'s for `all = true` (`FCond.SigPost`). -/

/-- The loop invariant of `signal` and `broadcast` (locals `prev_state` read by `prev`), for the
call snapshot `h c` (`FCond.Fits.enterSl`): `t` last read the state value `b`
(`waiters ≥ signals`); a served value (`waiters ≤ signals`) gave the history post and `t` is out,
else `t` is still at `sl h c`. -/
def sigInv {σ : Type} (prev : σ → X.S) (P : Proto Tgt γ) (C : FCond γ) (t : ThreadId) (g : γ)
    (h : Array Word.Entry) (c : VClock) (D : Nat) (s : σ) (G : ThreadId → γ) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ b : BitVec 32, prev s = Packed.ofBits b ∧ FCond.SOk b ∧
    (b.toNat % 65536 ≤ b.toNat / 65536 → ∀ all, C.SigPost h c all m) ∧
    P.inv (upd G t (C.set g (FCond.afterSRead h c b))) m

/-- The loop ends (at `ret` or `stop`) with `t` out and the history post for `all`. -/
def sigPost {σ E : Type} (ret stop : E) (all : Bool) (P : Proto Tgt γ) (C : FCond γ)
    (t : ThreadId) (g : γ) (h : Array Word.Entry) (c : VClock) (D : Nat) (r : E × σ)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  (r.1 = ret ∨ r.1 = stop) ∧ d < D ∧ m.current = t ∧ P.inv (upd G t g) m ∧
    C.SigPost h c all m

/-- **The entry of `signal` and `broadcast`** (`signalOf`) outside or holding the mutex,
preserving its complete resource, with the history post of its call for `all`, from its loop
body's step (`hbody`). -/
theorem entry_wp {σ E : Type} [Inhabited σ] {prev : σ → X.S} {setPrev : σ → X.S → σ}
    (prev_set : ∀ s v, prev (setPrev s v) = v) {body : Ptr → Io → CM Tgt σ E}
    {again : E → Bool} {ret stop : E} {k : E → CM Tgt σ E} {fin : E → ConcM Tgt Unit}
    (hkstop : k stop = pure ret) (hkret : k ret = pure ret) (hfin : fin ret = pure ())
    {all : Bool} (hC : L.Fits (C.prim L) P U ok) {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId)
    (g : γ) (hgx : C.ph g = .out) (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io)
    (hbody : ∀ (h : Array Word.Entry) (c : VClock) (D : Nat) (s : σ) (G : ThreadId → γ)
      (m : Mem) (d : Nat), X.sigInv prev P C t g h c D s G m d →
      P.WP t ((body C.S.ptr io).run s) (fun r G' m' d' =>
        if again r.1 then X.sigInv prev P C t g h c D r.2 G' m' d' ∧
          (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : σ) => 0) s)
        else X.sigPost ret stop all P C t g h c D r G' m' d') G m d)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (signalOf setPrev body again k fin p io) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ P.inv (upd G' t g) m' ∧ C.SigPost (C.S.hist m) (m.clocks[t]!) all m')
      G m d := by
  subst hp
  have hi' := hC.enterSl hgx hgo hsx hi
  generalize C.S.hist m = h at hi' ⊢
  generalize m.clocks[t]! = c at hi' ⊢
  clear hi
  rw [signalOf]
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (FCond.wp_sloadAs hC X.s_dec (C.ph_set _ _) hi'
    fun k₁ hk₁ G₁ m₁ b r hc₁ hd hb hsp hi₁ => ?_)
  obtain rfl := X.s_eq hd
  rw [C.set_set] at hi₁
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (X.sigInv prev P C t g h c d) (fun _ => 0)
    (X.sigPost ret stop all P C t g h c d) (hbody h c d) _ G₁ m₁ k₁
    ⟨by omega, hc₁, b, prev_set _ _, hb, hsp, hi₁⟩))
  rintro ⟨x, s'⟩ G₂ m₂ d₂ ⟨hx, hd₂, hc₂, hi₂, hp₂⟩
  have hkx : k x = pure ret := by rcases hx with rfl | rfl <;> assumption
  rw [hkx, StateT.run_pure]
  refine WP.pure' ?_
  show P.WP t (fin ret) _ G₂ m₂ d₂
  rw [hfin]
  exact WP.pure' ⟨hd₂, hc₂, hi₂, hp₂⟩

theorem sig_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (h : Array Word.Entry) (c : VClock) (D : Nat)
    (io : Io) (s : X.σs) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hs : X.sigInv X.sprev P C t g h c D s G m d) :
    P.WP t ((X.sbody C.S.ptr io).run s) (fun r G' m' d' =>
      if X.sagain r.1 then X.sigInv X.sprev P C t g h c D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : X.σs) => 0) s)
      else X.sigPost X.sret X.sstop false P C t g h c D r G' m' d') G m d := by
  obtain ⟨hd, hcur, b, hb, hok, hsp₀, hi₀⟩ := hs
  rw [X.sbody_eq, sbodyOf, StateT.run_bind]
  refine WP.bind ?_
  -- the loop's tick, paid from the unmetered fragment: the same writes (`m.ticked`)
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hC.wp_tick_unmetered_exact hi₀ hcur
    (by rw [hC.lph]; rcases hgo with hh | hh <;> rw [hh] <;> decide)
    (by rw [hC.lpart]; exact hu) fun hcur hi => WP.pure' ?_)
  have hsp : b.toNat % 65536 ≤ b.toNat / 65536 → ∀ all, C.SigPost h c all m.ticked :=
    fun hsv all => (hsp₀ hsv all).extend (Word.Extends.congr rfl rfl)
  clear hsp₀ hi₀
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hb, s_gt]
  by_cases hsv : b.toNat % 65536 ≤ b.toNat / 65536
  · -- every waiter has its signal: the loop ends, `t` out with the history post
    have hp := hsp hsv false
    rw [show FCond.afterSRead h c b = .out by simp [FCond.afterSRead, hsv],
      FCond.set_of hgx] at hi
    clear hsp
    fsym [X.s_w, X.s_s, FCond.SOk, sigPost, X.sagain_stop, hb]
  · -- a waiter lacks its signal: the `cmpxchg` that adds one; on success the epoch's increment
    -- and its wake, on failure a repeat with the value read
    rw [show FCond.afterSRead h c b = .sl h c by simp [FCond.afterSRead, hsv]] at hi
    clear hsp
    fsym [FCond.wp_postAs hC X.s_dec (sh := h) (c := c), FCond.wp_bump hC, FCond.wp_wakeEp hC,
      hC.wp_projE (t := t), FCond.SigPost.ofPost, X.s_post hsv, X.s_eq, X.s_w, X.s_s, X.s_mk,
      X.s_bits, C.ph_set, hC.lph, C.set_set, FCond.set_of, (FCond.set_of hgx), FCond.ptr_ep,
      FCond.SOk, sigInv, sigPost, X.sagain_ret, X.sagain_rep, X.sprev_set, hb]

/-- **`Io.Condition.signal`** outside or holding the mutex, preserving its complete resource,
with the history post of its call (`FCond.SigPost`). -/
theorem signal_wp_unmetered (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (X.signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ C.SigPost (C.S.hist m) (m.clocks[t]!) false m') G m d := by
  obtain ⟨k, fin, hsig, hkstop, hkret, hfin⟩ := X.signal_eq
  rw [hsig]
  exact X.entry_wp X.sprev_set hkstop hkret hfin hC hp t g hgx hgo hsx io
    (fun h c D => X.sig_body hC hcost t g hgx hgo hu h c D io) G m d hi

/-- The signal contract at its caller part: this implementation's proved profile returns the
part it was called with (`keepPart`). -/
theorem signal_wp_resource (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (X.signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r', keepPart t (L.part g) r' ∧ P.inv (upd G' t (L.setPart g r')) m' ∧
        C.SigPost (C.S.hist m) (m.clocks[t]!) false m') G m d := by
  refine WP.mono ?_ (X.signal_wp_unmetered hC hcost hp t g hgx hgo hsx hu io G m d hi)
  rintro _ G' m' d' ⟨hd, hc, hi', hsig⟩
  exact ⟨hd, hc, L.part g, rfl, by simpa only [L.setPart_self] using hi', hsig⟩

theorem bc_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (h : Array Word.Entry) (c : VClock) (D : Nat)
    (io : Io) (s : X.σb) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hs : X.sigInv X.bprev P C t g h c D s G m d) :
    P.WP t ((X.bbody C.S.ptr io).run s) (fun r G' m' d' =>
      if X.bagain r.1 then X.sigInv X.bprev P C t g h c D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : X.σb) => 0) s)
      else X.sigPost X.bret X.bstop true P C t g h c D r G' m' d') G m d := by
  obtain ⟨hd, hcur, b, hb, hok, hsp₀, hi₀⟩ := hs
  rw [X.bbody_eq, bbodyOf, StateT.run_bind]
  refine WP.bind ?_
  -- the loop's tick, paid from the unmetered fragment: the same writes (`m.ticked`)
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hC.wp_tick_unmetered_exact hi₀ hcur
    (by rw [hC.lph]; rcases hgo with hh | hh <;> rw [hh] <;> decide)
    (by rw [hC.lpart]; exact hu) fun hcur hi => WP.pure' ?_)
  have hsp : b.toNat % 65536 ≤ b.toNat / 65536 → ∀ all, C.SigPost h c all m.ticked :=
    fun hsv all => (hsp₀ hsv all).extend (Word.Extends.congr rfl rfl)
  clear hsp₀ hi₀
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hb, s_gt]
  by_cases hsv : b.toNat % 65536 ≤ b.toNat / 65536
  · -- every waiter has its signal: the loop ends, `t` out with the history post
    have hp := hsp hsv true
    rw [show FCond.afterSRead h c b = .out by simp [FCond.afterSRead, hsv],
      FCond.set_of hgx] at hi
    clear hsp
    fsym [X.s_w, X.s_s, FCond.SOk, sigPost, X.bagain_stop, hb]
  · -- a waiter lacks its signal: the `cmpxchg` that gives every waiter one; on success the
    -- epoch's increment and the wake of `waiters - signals`, on failure a repeat with the value
    rw [show FCond.afterSRead h c b = .sl h c by simp [FCond.afterSRead, hsv]] at hi
    clear hsp
    fsym [FCond.wp_postAs hC X.s_dec (sh := h) (c := c), FCond.wp_bump hC, FCond.wp_wakeEp hC,
      hC.wp_projE (t := t), FCond.SigPost.ofPostAll, X.s_bpost hsv, X.s_bserved,
      Zig.intCast_unsigned_widen, BitVec.toNat_setWidth, X.s_eq, X.s_w, X.s_s, X.s_mk,
      X.s_bits, C.ph_set, hC.lph, C.set_set, FCond.set_of, (FCond.set_of hgx), FCond.ptr_ep,
      FCond.SOk, sigInv, sigPost, X.bagain_ret, X.bagain_rep, X.bprev_set, hb]

/-- **`Io.Condition.broadcast`** outside or holding the mutex, preserving its complete resource,
with the history post of its call for `all = true` (`FCond.SigPost`). -/
theorem broadcast_wp_unmetered (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat) (hi : P.inv (upd G t g) m) :
    P.WP t (X.broadcast p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      P.inv (upd G' t g) m' ∧ C.SigPost (C.S.hist m) (m.clocks[t]!) true m') G m d := by
  obtain ⟨k, fin, hbc, hkstop, hkret, hfin⟩ := X.broadcast_eq
  rw [hbc]
  exact X.entry_wp X.bprev_set hkstop hkret hfin hC hp t g hgx hgo hsx io
    (fun h c D => X.bc_body hC hcost t g hgx hgo hu h c D io) G m d hi

/-- The broadcast contract at its caller part (`keepPart`, as `signal`). -/
theorem broadcast_wp_resource (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    {p : Ptr} (hp : p = C.S.ptr) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hsx : C.sx g)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) :
    P.WP t (X.broadcast p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r', keepPart t (L.part g) r' ∧ P.inv (upd G' t (L.setPart g r')) m' ∧
        C.SigPost (C.S.hist m) (m.clocks[t]!) true m') G m d := by
  refine WP.mono ?_ (X.broadcast_wp_unmetered hC hcost hp t g hgx hgo hsx hu io G m d hi)
  rintro _ G' m' d' ⟨hd, hc, hi', hsig⟩
  exact ⟨hd, hc, L.part g, rfl, by simpa only [L.setPart_self] using hi', hsig⟩

/-! ## `wait`

The waiter's ghost value after its `unlock`: `gR g i jr sn e` (registered, out of the lock's
code). -/

/-- The waiter registered, out of the lock's code. -/
abbrev gR (L : FLock γ) (C : FCond γ) (g : γ) (i jr : Nat) (sn : Bool) (e : BitVec 32) : γ :=
  C.set (L.set g .out rnil) (.reg i jr sn e)

theorem gR_ph {g : γ} {i jr : Nat} {sn : Bool} {e : BitVec 32} :
    C.ph (gR L C g i jr sn e) = .reg i jr sn e := C.ph_set _ _

theorem gR_lph (hC : L.Fits (C.prim L) P U ok) {g : γ} {i jr : Nat} {sn : Bool}
    {e : BitVec 32} : L.ph (gR L C g i jr sn e) = .out := by rw [hC.lph, L.ph_set]

theorem gR_set {g : γ} {i i' jr : Nat} {sn sn' : Bool} {e e' : BitVec 32} :
    C.set (gR L C g i jr sn e) (.reg i' jr sn' e') = gR L C g i' jr sn' e' := C.set_set _ _ _

/-- After the waiter took the signal: `g` out of the lock's code. -/
theorem gR_out (hC : L.Fits (C.prim L) P U ok) {g : γ} (hgx : C.ph g = .out) {i jr : Nat}
    {sn : Bool} {e : BitVec 32} : C.set (gR L C g i jr sn e) .out = L.set g .out rnil := by
  show C.set (C.set (L.set g .out rnil) (.reg i jr sn e)) .out = _
  rw [C.set_set, FCond.set_of (by rw [hC.ph_l]; exact hgx)]

/-- The inner loop's invariant: `t` registered (write `jr`), with its epoch write `i` and value
`e` (the local `epoch`), and the state value `b` it read last (`waiters ≥ signals`), at
`afterRead i jr e b`: it has a signal to take iff `signals ≠ 0`. -/
def innerInv (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (s : X.σ) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ X.ep s = e ∧ ∃ b : BitVec 32, X.prev s = Packed.ofBits b ∧
    FCond.SOk b ∧ P.inv (upd G t (gR L C g i jr (decide (b.toNat / 65536 ≠ 0)) e)) m

/-- The inner loop ends with no signal to take (`istop`), or with `t` holding the mutex again. -/
def innerPost (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (i jr : Nat)
    (e : BitVec 32) (D : Nat) (r : X.E × X.σ) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧
  ((r.1 = X.istop ∧ X.ep r.2 = e ∧ P.inv (upd G t (gR L C g i jr false e)) m) ∨
    (r.1 = X.done ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m))

theorem inner_body (hC : L.Fits (C.prim L) P U ok) (hcost : P.cost = none)
    (hLc : L.c = X.M.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (i jr : Nat) (e : BitVec 32) (D : Nat) (io : Io) (s : X.σ)
    (G : ThreadId → γ) (m : Mem) (d : Nat) (h : X.innerInv P L C t g i jr e D s G m d) :
    P.WP t ((X.inner C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if X.iagain r.1 then X.innerInv P L C t g i jr e D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : X.σ) => 0) s)
      else X.innerPost P L C t g i jr e D r G' m' d') G m d := by
  obtain ⟨hD, hc, hep, b, hps, hb, hi⟩ := h
  rw [X.inner_eq, innerOf, StateT.run_bind]
  -- the loop's tick, paid from the unmetered fragment
  refine WP.bind ?_
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hC.wp_tick_unmetered hi hc (by rw [gR_lph hC]; decide)
    (by simpa only [gR, hC.lpart, L.part_set] using hu) fun m₀ hc hi => WP.pure' ?_)
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hps, s_sig]
  by_cases hs : b.toNat / 65536 = 0
  · -- no signal: back to the futex wait
    simp only [hs, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure] at hi ⊢
    refine WP.pure' ?_
    simp only [X.iagain_stop, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, hc, .inl ⟨rfl, hep, hi⟩⟩
  · -- a signal: take it
    simp only [hs, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, StateT.run_bind,
      StateT.run_get, pure_bind, hps] at hi ⊢
    refine WP.bind (WP.callRC_ok (X.s_subW hb hs) ?_)
    dsimp only
    try simp only [hps]
    refine WP.bind (WP.callRC_ok (X.s_subS hs) ?_)
    dsimp only
    refine WP.bind (FCond.wp_consumeAs hC X.s_dec (by rw [s_bits]; omega)
      (X.s_take hb hs) gR_ph hi
      fun k hk G₁ m₁ hc₁ => ⟨fun hi₁ => ?_, fun b' r hd hb' hi₁ => ?_⟩)
    · -- the signal taken: `lock`
      rw [gR_out hC hgx] at hi₁
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.callC (WP.mono ?_ (X.M.lock_wp hC hcost rfl hLc t _
        (L.ph_set _ _ _) ((hC.ok_set _ _ _).mpr hok) trivial (by simpa only [L.part_set] using hu)
        io G₁ m₁ k hi₁)))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, rL, hi₂⟩
      rw [L.set_set] at hi₂
      rw [StateT.run_pure]
      refine WP.pure' ?_
      simp only [X.iagain_done, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hc₂, .inr ⟨rfl, rL, hi₂⟩⟩
    · -- the `cmpxchg` failed: the read value
      obtain rfl := X.s_eq hd
      rw [FCond.afterRead, gR_set] at hi₁
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.callRC_ok (x := optPayload (some (Packed.ofBits b'))) rfl ?_)
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]
      refine WP.pure' ?_
      simp only [X.iagain_rep, ↓reduceIte]
      exact ⟨⟨by omega, hc₁, by rw [X.ep_setPrev, hep], b', X.prev_setPrev _ _, hb', hi₁⟩,
        .inl (by omega)⟩

/-- The outer loop's invariant: `t` registered (write `jr`), before its futex wait, with an
epoch write `i` and its value, the local `epoch`. -/
def outerInv (P : Proto Tgt γ) (L : FLock γ) (C : FCond γ) (t : ThreadId) (g : γ) (jr : Nat)
    (D : Nat) (s : X.σ) (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ ∃ i, P.inv (upd G t (gR L C g i jr false (X.ep s))) m

/-- The outer loop ends with `t` holding the mutex again. -/
def outerPost (P : Proto Tgt γ) (L : FLock γ) (g : γ) (t : ThreadId) (D : Nat) (r : X.E × X.σ)
    (G : ThreadId → γ) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = X.done ∧ m.current = t ∧ ∃ rL, P.inv (upd G t (L.set g .holds rL)) m

theorem outer_body (hC' : C.Fits L P U ok) (hcost : P.cost = none)
    (hLc : L.c = X.M.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hok : ok g)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (jr : Nat) (D : Nat) (io : Io)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (s : X.σ) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (h : X.outerInv P L C t g jr D s G m d) :
    P.WP t ((X.outer C.S.ptr io L.ptr).run s) (fun r G' m' d' =>
      if X.oagain r.1 then X.outerInv P L C t g jr D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : X.σ) => 0) s)
      else X.outerPost P L g t D r G' m' d') G m d := by
  obtain ⟨hD, hc, i, hi⟩ := h
  have hC := hC'.toFits
  obtain ⟨k, houter, hkstop, hkdone⟩ := X.outer_eq
  rw [houter, outerOf, StateT.run_bind]
  -- the loop's tick, paid from the unmetered fragment
  refine WP.bind ?_
  show P.WP t (ConcM.liftMem Zig.tick >>= fun a => pure (a, s)) _ _ _ _
  refine WP.bind (hC.wp_tick_unmetered hi hc (by rw [gR_lph hC]; decide)
    (by simpa only [gR, hC.lpart, L.part_set] using hu) fun m₀ hc hi => WP.pure' ?_)
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_waitEp hC' (BitVec.setWidth_eq (X.ep s)) gR_ph (gR_lph hC) hi hlive
    fun k₁ hk₁ G₁ m₁ hc₁ hi₁ => ?_)
  rw [FCond.afterWait, gR_set] at hi₁
  dsimp only
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi₁) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_loadEp hC gR_ph hi₁
    fun k₂ hk₂ G₂ m₂ v i' hc₂ hi₂ => ?_)
  rw [gR_set] at hi₂
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_loadSAs hC X.s_dec gR_ph hi₂
    fun k₃ hk₃ G₃ m₃ b r hc₃ hd hb hi₃ => ?_)
  obtain rfl := X.s_eq hd
  rw [FCond.afterRead, gR_set] at hi₃
  simp only
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (X.innerInv P L C t g i' jr v d) (fun _ => 0)
    (X.innerPost P L C t g i' jr v d) (X.inner_body hC hcost hLc t g hgx hok hu i' jr v d io) _
    G₃ m₃ k₃ ⟨by omega, hc₃, by rw [X.ep_setPrev, X.ep_setEp], b, X.prev_setPrev _ _, hb, hi₃⟩))
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, hc₄, ⟨rfl, hep₄, hi₄⟩ | ⟨rfl, rL, hi₄⟩⟩
  · rw [← hep₄] at hi₄
    rw [hkstop, StateT.run_pure]
    refine WP.pure' ?_
    simp only [X.oagain_rep, ↓reduceIte]
    exact ⟨⟨by omega, hc₄, i', hi₄⟩, .inl (by omega)⟩
  · rw [hkdone, StateT.run_pure]
    refine WP.pure' ?_
    simp only [X.oagain_done, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by omega, rfl, hc₄, rL, hi₄⟩

/-- The wait's core by the mutex's holder, out of the condition's code: it returns `rv`,
holding the mutex again. -/
theorem core_wp (hC' : C.Fits L P U ok) (hcost : P.cost = none)
    (hLc : L.c = X.M.c) (t : ThreadId) (g : γ) (hgx : C.ph g = .out)
    (hgh : L.ph g = .holds) (hok : ok g) (hu : 0 < (L.part g).gh.ac.frag .unmetered)
    (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hi : P.inv (upd G t g) m) :
    P.WP t (X.core C.S.ptr io L.ptr) (fun r G' m' d' => d' < d ∧
      r = X.rv ∧ m'.current = t ∧ ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  have hC := hC'.toFits
  have hi0 := hC.enterEn hgx hgh hroom hent hi
  have hgh0 : L.ph (C.set g .en) = .holds := by rw [hC.lph]; exact hgh
  obtain ⟨fin, hcore, hfin⟩ := X.core_eq
  rw [hcore, coreOf]
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (hC.projE hi0) ?_)
  dsimp only
  rw [FCond.ptr_ep]
  refine WP.bind (FCond.wp_ldEp hC (C.ph_set _ _) hgh0 hi0
    fun k₁ hk₁ G₁ m₁ v i hc₁ hi₁ => ?_)
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (FCond.wp_regAs hC (X.s_bits 1) (fun b _ => ⟨_, X.ofBits?_ok b⟩)
    (C.ph_set _ _) (by rw [hC.lph]; exact hgh0) hi₁
    fun k₂ hk₂ G₂ m₂ jr old r hc₂ hro hd hi₂ => ?_)
  obtain rfl := X.s_eq hd
  rw [C.set_set, C.set_set] at hi₂
  simp only
  rw [X.s_room hro]
  refine WP.bind (WP.callRC_ok X.dassert_true ?_)
  dsimp only
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (X.M.unlock_wp hC hcost rfl hLc t _
    (by rw [hC.lph]; exact hgh) (by rw [hC.ok_calm _ _ .out rfl rfl, FCond.set_of hgx]; exact hok)
    io G₂ m₂ k₂ hi₂ hc₂)))
  rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₃⟩
  rw [← hC.set_l] at hi₃
  refine WP.mono ?_ (WP.loop _ _ (X.outerInv P L C t g jr d) (fun _ => 0) (X.outerPost P L g t d)
    (X.outer_body hC' hcost hLc t g hgx hok hu jr d io hlive) _ G₃ m₃ d₃
    ⟨by omega, hc₃, i, by rw [X.ep_setEp]; exact hi₃⟩)
  rintro ⟨x, s'⟩ G₄ m₄ d₄ ⟨hd₄, rfl, hc₄, rL, hi₄⟩
  show P.WP t (fin X.done) _ G₄ m₄ d₄
  rw [hfin]
  exact WP.pure' ⟨by omega, rfl, hc₄, rL, hi₄⟩

/-- **`Io.Condition.waitUncancelable`**, through either shape of its core (`WaitShape`). -/
theorem wait_wp_unmetered (hC : C.Fits L P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = X.M.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hu : 0 < (L.part g).gh.ac.frag .unmetered) (hi : P.inv (upd G t g) m) :
    P.WP t (X.wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d := by
  subst hp hq
  have hcore := X.core_wp hC hcost hLc t g hgx hgh hok hu io G m d hroom hent hlive hi
  cases X.wait_eq with
  | direct h =>
    rw [h]
    refine WP.bind (WP.mono ?_ hcore)
    rintro _ G₁ m₁ d₁ ⟨hd₁, -, hc₁, rL, hi₁⟩
    exact WP.pure' ⟨hd₁, hc₁, rL, hi₁⟩
  | call k wret fin h hk hfin =>
    rw [h]
    refine WP.bind ?_
    rw [StateT.run'_eq]
    refine WP.map ?_
    simp only [StateT.run_bind]
    refine WP.bind (WP.callC (WP.mono ?_ hcore))
    rintro r G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, rL, hi₁⟩
    rw [hk, StateT.run_pure]
    refine WP.pure' ?_
    show P.WP t (fin wret) _ G₁ m₁ d₁
    rw [hfin]
    exact WP.pure' ⟨hd₁, hc₁, rL, hi₁⟩

/-- The wait contract at its caller part: this implementation's proved profile returns the
part it was called with (`keepPart`), with the protected resource returned separately after the
re-lock. -/
theorem wait_wp_resource (hC : C.Fits L P U ok)
    (hcost : P.cost = none) {p q : Ptr} (hp : p = C.S.ptr) (hq : q = L.ptr) (hLc : L.c = X.M.c)
    (t : ThreadId) (g : γ) (hgx : C.ph g = .out) (hgh : L.ph g = .holds) (hok : ok g) (io : Io)
    (G : ThreadId → γ) (m : Mem) (d : Nat)
    (hroom : ∀ T, (∀ u, T ≤ u → C.ph (upd G t g u) = .out) → C.nreg (upd G t g) T < 65535)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hlive : ∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → FCond.sOf (C.lastS m₁) = 0 → (∀ v, (C.ph (G₁ v)).sig = false) →
      P.Live t G₁ m₁)
    (hu : payUnmetered t (L.part g)) (hi : P.inv (upd G t g) m) (_hc : m.current = t) :
    P.WP t (X.wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ r' rL, keepPart t (L.part g) r' ∧
        P.inv (upd G' t (L.set (L.setPart g r') .holds rL)) m') G m d := by
  refine WP.mono ?_ (X.wait_wp_unmetered hC hcost hp hq hLc t g hgx hgh hok
    io G m d hroom hent hlive hu hi)
  rintro _ G' m' d' ⟨hd, hcur, rL, hi'⟩
  exact ⟨hd, hcur, L.part g, rL, rfl, by simpa only [L.setPart_self] using hi'⟩

end

/-- **`Io.Condition` is a condition** (`CondImpl`), with its mutex, in every program and Zig
version whose code it is. -/
def impl : CondImpl Tgt where
  wait := X.wait
  signal := X.signal
  broadcast := X.broadcast
  c := X.M.c
  wait_pre := payUnmetered
  wait_post := keepPart
  wait_plain_pre _ _ := payUnmetered_plain
  wait_plain_post _ _ _ _ hr := hr
  signal_pre := payUnmetered
  signal_post := keepPart
  signal_unmetered_pre _ _ hu := hu
  signal_unmetered_post _ _ _ _ hr := hr
  broadcast_pre := payUnmetered
  broadcast_post := keepPart
  broadcast_unmetered_pre _ _ hu := hu
  broadcast_unmetered_post _ _ _ _ hr := hr
  wait_wp_resource := X.wait_wp_resource
  signal_wp_resource hC := X.signal_wp_resource hC.toFits
  broadcast_wp_resource hC := X.broadcast_wp_resource hC.toFits

end IoCondCode

end Full
end Zig
