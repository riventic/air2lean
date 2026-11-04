import ZigLean.Sep.Full.Event
import ZigLean.Sep.Full.TSum

/-!
# The futex-epoch condition with any number of waiters: places, invariant, counting

WORK IN PROGRESS (lane L10d, PR description): the multi-waiter `FCond.Inv` of
`ZigLean/Sep/Full/Cond.lean`, step 3 of the design on PR #575 (comments 6619561994 and
6625654179). This module replaces the singleton places and invariant of `Cond.lean` in one swap;
until then it is built on its own and nothing imports it.

The condition (`Io.Condition` of 0.16.0 and 0.17.0, `Thread.Condition.FutexImpl` of 0.15.2):
a state word `S` (`waiters` in the low 16 bits, `signals` in the high 16) and an epoch word
`Ep` after it. A waiter, holding the mutex, loads the epoch (acquire), does `waiters += 1`,
unlocks the mutex and loops: a futex wait at the epoch with the saved value, an acquire reload
of the epoch (the new saved value), a relaxed load of the state and, while `signals > 0`, a weak
acquire `cmpxchg` that takes one signal; with `signals = 0` it loops back. `signal` posts one
signal while `waiters > signals` (release `cmpxchg`), then `epoch += 1` (release) and wakes one
waiter; `broadcast` posts `waiters - signals` and wakes as many.

**Places** (`CPh`). `en` a waiter before its epoch load; `ld i e` it loaded epoch write `i`
(any write its view allows, not only the newest) with the value `e`; `reg i jr sn e` it
registered at state write `jr` and saved epoch write `i` (value `e`), and `sn` says it returned
from a futex wait and will read the state before it waits again; `inc q n` a signaller after
its post (state write `q`, `n` signals); `wk n` after its `epoch += 1`, to wake `n`. A waiter's
loop resaves: `CPh.Next`'s `reg` case is `jr' = jr ∧ i ≤ i'`.

**The invariant** (`FCond.Inv`) has the history fields of the design next to the count:

- (H1, `sv`) every state write is a pair `(w, s)` with `s ≤ w`;
- (H3, `ep`) each epoch write is the one before plus one, and the release clocks of the epoch's
  writes grow (all of them after the first are release RMWs, one release sequence);
- (H2, `pub`) a write that raised `signals` (a post) is its signaller's, still at `inc`, or some
  epoch write's release clock covers it (it is published);
- (C, `cnt`) the newest `waiters` is the number of registered threads, and the newest `signals`
  is at most the claims (`claims`): the signals of the signallers at `inc`, the waiters that
  will read the state (`sn`, or not queued at the epoch and their saved write is not the newest
  (stale), or woken), and of the signallers at `wk` as many as are queued at the epoch.

The window (`< 2^32` epoch writes after a registered waiter's save, PR397 ruling 6264821278)
is the field `reg`'s `(C.Ep.hist m).size ≤ i + 2^32`; a protocol supplies it at each
`epoch += 1` (the admission field of `C.Fits`). With it and (H3), a saved value that is not
the newest write's differs from the epoch's value, so a stale waiter does not sleep.

**Why the count is inductive** (design comment 6619561994, completed here):
- a post adds `n` signals and a claim `n`; a consume takes one signal and its taker's claim;
- `epoch += 1` makes every waiter that is not queued stale: either the queued waiters are at
  least the pending wakes (and the claim moves from `inc` to `wk`), or every registered waiter
  is a claim (queued: through `wk`; not queued: stale), and `signals ≤ waiters` (`claims_ge`);
- a wake of `n` wakes `min n q` of the `q` queued waiters; they become claims (`woken`);
- a waiter's loop-back (it read `signals = 0` at write `k`) with the newest saved write: every
  post after `k` is still its signaller's (a published one is covered by the release clock of
  an epoch write at or before the saved one, which the waiter acquired, so its read is at least
  that post), so the newest `signals` is at most the claims at `inc` (`loopBack_bound`).
-/

namespace Zig
namespace Full

open Conc Proto

/-- Where a thread is in a condition's code (module doc). -/
inductive CPh where
  | out
  | en
  | ld (i : Nat) (e : BitVec 32)
  | reg (i jr : Nat) (sn : Bool) (e : BitVec 32)
  | inc (q n : Nat)
  | wk (n : Nat)
  deriving DecidableEq

namespace CPh

/-- A waiter's place. -/
def waits : CPh → Bool
  | .en | .ld _ _ | .reg _ _ _ _ => true
  | _ => false

/-- The critical code: the waiter holds the mutex. -/
def crit : CPh → Bool
  | .en | .ld _ _ => true
  | _ => false

/-- A signaller between its post and its wake. -/
def sig : CPh → Bool
  | .inc _ _ | .wk _ => true
  | _ => false

/-- A place where the thread runs no lock code. -/
def busy (p : CPh) : Bool := p.crit || p.sig

/-- A registered waiter. -/
def isReg : CPh → Bool
  | .reg _ _ _ _ => true
  | _ => false

/-- The signals a signaller at `inc` posted. -/
def incN : CPh → Nat
  | .inc _ n => n
  | _ => 0

/-- The post of a signaller at `inc` (its state write). -/
def incQ : CPh → Option Nat
  | .inc q _ => some q
  | _ => none

/-- The wakes a signaller at `wk` still owes. -/
def wkN : CPh → Nat
  | .wk n => n
  | _ => 0

/-- The transitions of the condition's code, without the entry `out → en` (module doc). A
waiter keeps its registration and resaves a later epoch write; a signaller posts at most the
signals it then wakes. -/
def Next : CPh → CPh → Prop
  | .en, .ld _ _ => True
  | .ld i e, .reg i' _ sn e' => i' = i ∧ sn = false ∧ e' = e
  | .reg i jr _ _, .reg i' jr' _ _ => jr' = jr ∧ i ≤ i'
  | .reg _ _ _ _, .out => True
  | .out, .inc _ _ => True
  | .inc _ n, .wk n' => n' = n
  | .wk _, .out => True
  | a, b => a = b

theorem isReg_eq {p : CPh} (h : p.isReg = true) : ∃ i jr sn e, p = .reg i jr sn e := by
  cases p with
  | reg i jr sn e => exact ⟨i, jr, sn, e, rfl⟩
  | _ => simp [isReg] at h

theorem Next.refl (a : CPh) : Next a a := by
  cases a <;> simp [Next]

/-- A step of the code into a waiter's place comes from one. -/
theorem Next.waits {a b : CPh} (h : Next a b) (hb : b.waits = true) : a.waits = true := by
  cases a <;> cases b <;> first | rfl | exact hb | (simp [Next] at h; done) | (simp [CPh.waits] at hb; done)

/-- A step of the code into the critical code comes from it. -/
theorem Next.crit {a b : CPh} (h : Next a b) (hb : b.crit = true) : a.crit = true := by
  cases a <;> cases b <;> first | rfl | exact hb | (simp [Next] at h; done) | (simp [CPh.crit] at hb; done)

end CPh

/-- A futex-epoch condition (module doc): its state and epoch words, and a thread's place in
its code. -/
structure FCond (γ : Type) extends FPlace γ CPh where
  S : Word 32 4
  Ep : Word 32 4
  ep_b : Ep.b = S.b
  ep_o : Ep.o = S.o + 4
  /-- The ghost values of the threads that may signal (the protocol's roles). -/
  sx : γ → Prop
  sx_set : ∀ g p, sx (set g p) ↔ sx g

namespace FCond

/-! ## The values of the writes -/

/-- The value of a write (`0` if its bytes are not a `u32`). -/
def val (x : Word.Entry) : BitVec 32 :=
  match (intOfBytes 32 x.bytes).run with
  | some (.ok v) => v
  | _ => 0

theorem val_of {x : Word.Entry} {v : BitVec 32} (h : x.Val v) : val x = v := by
  unfold val; unfold Word.Entry.Val at h; rw [h]

/-- `waiters` of a state write. -/
def wOf (x : Word.Entry) : Nat := (val x).toNat % 65536

/-- `signals` of a state write. -/
def sOf (x : Word.Entry) : Nat := (val x).toNat / 65536

variable {γ : Type} (C : FCond γ)

/-- The newest write of the state. -/
abbrev lastS (m : Mem) : Word.Entry := (C.S.hist m)[(C.S.hist m).size - 1]!

/-- The newest write of the epoch. -/
abbrev lastE (m : Mem) : Word.Entry := (C.Ep.hist m)[(C.Ep.hist m).size - 1]!

/-! ## Counting the threads -/

/-- Thread `u` is in the futex queue at the epoch. -/
def qd (m : Mem) (u : ThreadId) : Bool := m.waiters.any fun w => w.1 == u && w.2 == C.Ep.ptr

/-- A registered waiter's claim (module doc): it will read the state. -/
def regCl (m : Mem) (u : ThreadId) : CPh → Nat
  | .reg i _ sn _ =>
    if sn || (!C.qd m u && (decide (i + 1 < (C.Ep.hist m).size) || m.woken.contains u)) then 1 else 0
  | _ => 0

/-- A thread's own claim: its posted signals at `inc`, or its registered claim. -/
def cl (G : ThreadId → γ) (m : Mem) (u : ThreadId) : Nat :=
  (C.ph (G u)).incN + C.regCl m u (C.ph (G u))

/-- The registered threads below `T`. -/
def nreg (G : ThreadId → γ) (T : Nat) : Nat := tsum T fun u => if (C.ph (G u)).isReg then 1 else 0

/-- The registered threads below `T` in the futex queue at the epoch. -/
def nq (G : ThreadId → γ) (m : Mem) (T : Nat) : Nat :=
  tsum T fun u => if (C.ph (G u)).isReg && C.qd m u then 1 else 0

/-- The claims of the threads below `T` (module doc): their own claims, and of the wakes owed
at `wk` as many as there are queued waiters. -/
def claims (G : ThreadId → γ) (m : Mem) (T : Nat) : Nat :=
  tsum T (C.cl G m) + min (tsum T fun u => (C.ph (G u)).wkN) (C.nq G m T)

/-! ## The invariant -/

/-- The condition's invariant, with the lock's places (module doc). -/
structure Inv (L : FLock γ) (G : ThreadId → γ) (m : Mem) : Prop where
  spos : 0 < (C.S.hist m).size
  /-- (H1) Every state write is a `u32` pair `(w, s)` with `s ≤ w`. -/
  sv : ∀ k < (C.S.hist m).size, (C.S.hist m)[k]!.Val (val (C.S.hist m)[k]!) ∧
    sOf (C.S.hist m)[k]! ≤ wOf (C.S.hist m)[k]!
  /-- Every epoch write is a `u32`. -/
  e32 : ∀ k < (C.Ep.hist m).size, (C.Ep.hist m)[k]!.Val (val (C.Ep.hist m)[k]!)
  /-- (H3) Each epoch write is the one before plus one, and its release clock covers the one
  before (one release sequence). -/
  ep : ∀ k, k + 1 < (C.Ep.hist m).size →
    val (C.Ep.hist m)[k + 1]! = val (C.Ep.hist m)[k]! + 1 ∧
    VClock.le (C.Ep.hist m)[k]!.relClock (C.Ep.hist m)[k + 1]!.relClock = true
  /-- (H2) A post is its signaller's, or an epoch write's release clock covers it. -/
  pub : ∀ q, 0 < q → q < (C.S.hist m).size →
    sOf (C.S.hist m)[q - 1]! < sOf (C.S.hist m)[q]! →
    (∃ v n, C.ph (G v) = .inc q n ∧ sOf (C.S.hist m)[q]! - sOf (C.S.hist m)[q - 1]! ≤ n) ∨
    ∃ b < (C.Ep.hist m).size,
      VClock.le (C.S.hist m)[q]!.clock (C.Ep.hist m)[b]!.relClock = true
  /-- A signaller at `inc` made its post, which happened before it. -/
  inc : ∀ v q n, C.ph (G v) = .inc q n → 0 < q ∧ q < (C.S.hist m).size ∧
    VClock.le (C.S.hist m)[q]!.clock (m.clocks[v]!) = true
  /-- The waiter at `ld i e` acquired epoch write `i`. -/
  ld : ∀ u i e, C.ph (G u) = .ld i e → i < (C.Ep.hist m).size ∧ (C.Ep.hist m)[i]!.Val e ∧
    VClock.le (C.Ep.hist m)[i]!.relClock (m.clocks[u]!) = true
  /-- A registered waiter acquired its saved epoch write `i`, its registration happened before
  it, and fewer than `2^32` epoch writes follow its save (the window). -/
  reg : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → i < (C.Ep.hist m).size ∧
    (C.Ep.hist m)[i]!.Val e ∧ VClock.le (C.Ep.hist m)[i]!.relClock (m.clocks[u]!) = true ∧
    jr < (C.S.hist m).size ∧ VClock.le (C.S.hist m)[jr]!.clock (m.clocks[u]!) = true ∧
    (C.Ep.hist m).size ≤ i + 4294967296
  /-- A thread in the futex queue at the epoch is a registered waiter about to read nothing. -/
  q : ∀ w ∈ m.waiters, w.2 = C.Ep.ptr → ∃ i jr e, C.ph (G w.1) = .reg i jr false e
  /-- A waiter in the futex queue is at the epoch or at the mutex. -/
  qw : ∀ w ∈ m.waiters, (C.ph (G w.1)).waits → w.2 = C.Ep.ptr ∨ w.2 = L.ptr
  /-- (C) The count (module doc), for a bound past which every thread is out. -/
  cnt : ∃ T, (∀ u, T ≤ u → C.ph (G u) = .out) ∧ wOf (C.lastS m) = C.nreg G T ∧
    sOf (C.lastS m) ≤ C.claims G m T
  /-- Room for one more waiter while one is in the critical code (`waiters < 65535`). -/
  room : ∀ u, (C.ph (G u)).crit → wOf (C.lastS m) < 65535
  /-- One thread in the critical code (it holds the mutex). -/
  crit1 : ∀ u v, (C.ph (G u)).crit → (C.ph (G v)).crit → u = v
  crit : ∀ u, (C.ph (G u)).crit → L.ph (G u) = .holds
  lp : ∀ u, (C.ph (G u)).sig → L.ph (G u) = .out ∨ L.ph (G u) = .holds
  sx : ∀ u, (C.ph (G u)).sig → C.sx (G u)

/-! ## Counting lemmas -/

variable {C}

/-- A bound past which every thread is out bounds every count. -/
theorem nreg_ext {G : ThreadId → γ} {T T' : Nat} (hT : ∀ u, T ≤ u → C.ph (G u) = .out)
    (h : T ≤ T') : C.nreg G T' = C.nreg G T :=
  tsum_ext h fun u hu => by rw [hT u hu]; rfl

theorem claims_ext {G : ThreadId → γ} {m : Mem} {T T' : Nat}
    (hT : ∀ u, T ≤ u → C.ph (G u) = .out) (h : T ≤ T') : C.claims G m T' = C.claims G m T := by
  unfold claims nq cl
  rw [tsum_ext h fun u hu => by rw [hT u hu]; rfl, tsum_ext h fun u hu => by rw [hT u hu]; rfl,
    tsum_ext h fun u hu => by rw [hT u hu]; rfl]

/-- **Every registered waiter is a claim or queued**: then the claims are at least the
registered waiters (the `epoch += 1` case of the module doc). -/
theorem nreg_le_claims {G : ThreadId → γ} {m : Mem} {T : Nat}
    (h : ∀ u, u < T → (C.ph (G u)).isReg → C.qd m u = false → C.cl G m u ≥ 1)
    (hw : C.nq G m T ≤ tsum T fun u => (C.ph (G u)).wkN) : C.nreg G T ≤ C.claims G m T := by
  unfold claims
  rw [Nat.min_eq_right hw]
  unfold nreg nq
  rw [← tsum_add]
  refine tsum_le fun u hu => ?_
  dsimp only
  by_cases hr : (C.ph (G u)).isReg = true
  · by_cases hq : C.qd m u = true
    · rw [if_pos hr, if_pos (by rw [hr, hq]; rfl)]; omega
    · have := h u hu hr (by simpa using hq)
      rw [if_pos hr, if_neg (by rw [hr]; simpa using hq)]; omega
  · rw [if_neg hr]; exact Nat.zero_le _

/-- **The loop-back bound** (module doc): if every post after write `k` up to the newest is
still its signaller's, the newest `signals` is at most `signals` of write `k` plus the signals
of the signallers at `inc`. -/
theorem loopBack_bound {G : ThreadId → γ} {h : Array Word.Entry} {k T : Nat}
    (hk : k < h.size)
    (hT : ∀ u, T ≤ u → C.ph (G u) = .out)
    (hpub : ∀ q, k < q → q < h.size → sOf h[q - 1]! < sOf h[q]! →
      ∃ v n, C.ph (G v) = .inc q n ∧ sOf h[q]! - sOf h[q - 1]! ≤ n) :
    sOf h[h.size - 1]! ≤ sOf h[k]! + tsum T fun v => (C.ph (G v)).incN := by
  have hle := le_add_tsum_up (fun q => sOf h[q]!) (k := k) (n := h.size - 1) (by omega)
  beta_reduce at hle
  simp only [show h.size - 1 + 1 = h.size by omega] at hle
  refine Nat.le_trans hle (Nat.add_le_add_left (tsum_tag (fun v => (C.ph (G v)).incQ) ?_) _)
  intro q hq hpos
  by_cases hkq : k < q
  · simp only [hkq, if_true] at hpos ⊢
    obtain ⟨v, n, hv, hn⟩ := hpub q hkq hq (by omega)
    refine ⟨v, ?_, by rw [hv]; rfl, by rw [hv]; exact hn⟩
    by_cases hvT : v < T
    · exact hvT
    · have := hT v (by omega); rw [this] at hv; cases hv
  · simp [hkq] at hpos

variable {L : FLock γ}

/-! ## The epoch's values -/

theorem ofNat_succ (d : Nat) : BitVec.ofNat 32 (d + 1) = BitVec.ofNat 32 d + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

/-- (H3) iterated: epoch write `i + d` is write `i` plus `d`. -/
theorem Inv.ep_add {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) {i : Nat} :
    ∀ d, i + d < (C.Ep.hist m).size →
      val (C.Ep.hist m)[i + d]! = val (C.Ep.hist m)[i]! + BitVec.ofNat 32 d
  | 0, _ => by simp
  | d + 1, h => by
    rw [← Nat.add_assoc, (hI.ep (i + d) (by omega)).1, hI.ep_add d (by omega), ofNat_succ,
      BitVec.add_assoc]

theorem add_ofNat_ne (e : BitVec 32) {d : Nat} (h0 : 0 < d) (h1 : d < 4294967296) :
    e + BitVec.ofNat 32 d ≠ e := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- **A stale save is not the epoch's value** (H3 and the window): a registered waiter whose
saved write is not the newest finds another value at the futex, so it does not sleep. -/
theorem Inv.stale_ne {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) {u : ThreadId}
    {i jr : Nat} {sn : Bool} {e : BitVec 32} (hu : C.ph (G u) = .reg i jr sn e)
    (hst : i + 1 < (C.Ep.hist m).size) : ¬ (C.lastE m).Val e := by
  obtain ⟨hi, he, -, -, -, hw⟩ := hI.reg u i jr sn e hu
  intro hv
  have hval := hI.ep_add (i := i) ((C.Ep.hist m).size - 1 - i) (by omega)
  have hv' : val (C.Ep.hist m)[(C.Ep.hist m).size - 1]! = e := val_of hv
  rw [show i + ((C.Ep.hist m).size - 1 - i) = (C.Ep.hist m).size - 1 by omega, hv',
    val_of he] at hval
  exact add_ofNat_ne e (d := (C.Ep.hist m).size - 1 - i) (by omega) (by omega) hval.symm

/-- A registered waiter whose save is the epoch's value saved the newest write. -/
theorem Inv.fresh_of_val {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) {u : ThreadId}
    {i jr : Nat} {sn : Bool} {e : BitVec 32} (hu : C.ph (G u) = .reg i jr sn e)
    (hv : (C.lastE m).Val e) : (C.Ep.hist m).size = i + 1 := by
  have hi := (hI.reg u i jr sn e hu).1
  by_cases hst : i + 1 < (C.Ep.hist m).size
  · exact absurd hv (hI.stale_ne hu hst)
  · omega

/-! ## The count after a step -/

/-- The support bound of the count, for a thread that is not out. -/
theorem Inv.lt_bound {G : ThreadId → γ} {T : Nat} (hT : ∀ u, T ≤ u → C.ph (G u) = .out)
    {t : ThreadId} (ht : C.ph (G t) ≠ .out) : t < T := by
  by_cases h : t < T
  · exact h
  · exact absurd (hT t (by omega)) ht

/-- The newest `signals` is at most the newest `waiters` (H1). -/
theorem Inv.s_le_w {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) :
    sOf (C.lastS m) ≤ wOf (C.lastS m) :=
  (hI.sv _ (by have := hI.spos; omega)).2

/-- **The count after `epoch += 1`** by the signaller `t` at `inc q n` (now `wk n`): the claim
moves from `inc` to the wakes owed, and every registered waiter out of the queue is stale (module
doc). -/
theorem Inv.cnt_bump {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {q n : Nat} {g' : γ}
    (hI : C.Inv L G m) (ht : C.ph (G t) = .inc q n) (hg' : C.ph g' = .wk n)
    (hS : C.S.hist m' = C.S.hist m) (hE : (C.Ep.hist m').size = (C.Ep.hist m).size + 1)
    (hq : ∀ u, C.qd m' u = C.qd m u) (hwk : m'.woken = m.woken) :
    ∃ T, (∀ u, T ≤ u → C.ph (upd G t g' u) = .out) ∧
      wOf (C.lastS m') = C.nreg (upd G t g') T ∧ sOf (C.lastS m') ≤ C.claims (upd G t g') m' T := by
  obtain ⟨T, hT, hw, hs⟩ := hI.cnt
  have htT : t < T := Inv.lt_bound hT (by rw [ht]; exact nofun)
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  have hreg : C.nreg (upd G t g') T = C.nreg G T := tsum_congr fun u _ => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; rfl
    · rw [hph u hu]
  have hnq : C.nq (upd G t g') m' T = C.nq G m T := tsum_congr fun u _ => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; rfl
    · rw [hph u hu, hq]
  have hwkS : (tsum T fun u => (C.ph (upd G t g' u)).wkN) =
      (tsum T fun u => (C.ph (G u)).wkN) + n := by
    have := tsum_upd (g := fun u => (C.ph (G u)).wkN) (g' := fun u => (C.ph (upd G t g' u)).wkN)
      htT (fun u hu => by rw [hph u hu])
    simp only [upd_self, hg', ht, CPh.wkN] at this
    omega
  -- a claim of a registered waiter only grows (its save gets older)
  have hcl : ∀ u, u ≠ t → C.cl G m u ≤ C.cl (upd G t g') m' u := fun u hu => by
    unfold cl; rw [hph u hu]
    refine Nat.add_le_add_left ?_ _
    rcases C.ph (G u) with _ | _ | _ | ⟨i, jr, sn, e⟩ | _ | _
    all_goals try exact Nat.le_refl _
    simp only [regCl, hq, hwk, hE]
    split <;> rename_i h1 <;> split <;> rename_i h2
    all_goals first | exact Nat.le_refl _ | exact Nat.zero_le _ | skip
    exfalso; revert h1 h2
    cases sn <;> cases C.qd m u <;> cases m.woken.contains u <;> simp <;> omega
  refine ⟨T, fun u hu => ?_, by rw [hlast, hreg]; exact hw, ?_⟩
  · by_cases e : u = t
    · subst e; omega
    · rw [hph u e]; exact hT u hu
  rw [hlast]
  unfold claims
  rw [hwkS, hnq]
  have hclS : tsum T (C.cl G m) ≤ tsum T (C.cl (upd G t g') m') + n := by
    have := tsum_le_add_point (g := C.cl G m) (h := C.cl (upd G t g') m') htT
      (fun u _ hu => hcl u hu)
    have hct : C.cl G m t = n := by unfold cl; rw [ht]; simp [CPh.incN, regCl]
    omega
  by_cases hcase : (tsum T fun u => (C.ph (G u)).wkN) + n ≤ C.nq G m T
  · -- the pending wakes move from `inc` to `wk`
    unfold claims at hs
    rw [Nat.min_eq_left hcase]
    rw [Nat.min_eq_left (by omega)] at hs
    omega
  · -- every registered waiter is a claim or queued
    have hall : C.nreg (upd G t g') T ≤ C.claims (upd G t g') m' T := by
      refine nreg_le_claims (fun u hu hr hqd => ?_) (by rw [hwkS, hnq]; omega)
      have hut : u ≠ t := fun h => by subst h; rw [upd_self, hg'] at hr; cases hr
      rw [hph u hut] at hr
      obtain ⟨i, jr, sn, e, hpu⟩ := CPh.isReg_eq hr
      have hi : i + 1 < (C.Ep.hist m).size + 1 := by have := (hI.reg u i jr sn e hpu).1; omega
      unfold cl; rw [hph u hut, hpu]
      simp [CPh.incN, regCl, hqd, hE, hi]
    have := hI.s_le_w
    unfold claims at hall
    rw [hwkS, hnq, hreg, ← hw] at hall
    omega

/-- (H3, clocks) iterated: an older epoch write's release clock is covered by a newer one's. -/
theorem Inv.rel_mono {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) {b : Nat} :
    ∀ d, b + d < (C.Ep.hist m).size →
      VClock.le (C.Ep.hist m)[b]!.relClock (C.Ep.hist m)[b + d]!.relClock = true
  | 0, _ => VClock.le_refl _
  | d + 1, h => VClock.le_trans (hI.rel_mono d (by omega)) (hI.ep (b + d) (by omega)).2

/-- A thread queued at the epoch is a registered waiter about to wait. -/
theorem Inv.qd_reg {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) {u : ThreadId}
    (h : C.qd m u = true) : ∃ i jr e, C.ph (G u) = .reg i jr false e := by
  unfold qd at h
  obtain ⟨w, hw, hwe⟩ := Array.any_eq_true'.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hwe
  obtain ⟨rfl, hp⟩ := hwe
  exact hI.q w hw hp

/-- **The count after a waiter's loop-back** (module doc): waiter `t` at `reg i jr true e`
read state write `k` (at least every write that happened before it) with `signals = 0`, and
goes back to its futex wait (`reg i jr false e`). -/
theorem Inv.cnt_loopBack {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {i jr k : Nat}
    {e : BitVec 32} {g' : γ} (hI : C.Inv L G m) (ht : C.ph (G t) = .reg i jr true e)
    (hg' : C.ph g' = .reg i jr false e)
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hq : ∀ u, C.qd m' u = C.qd m u) (hwk : m'.woken = m.woken)
    (hk : k < (C.S.hist m).size) (hfl : Word.Floor (C.S.hist m) (m.clocks[t]!) k)
    (hs0 : sOf (C.S.hist m)[k]! = 0) :
    ∃ T, (∀ u, T ≤ u → C.ph (upd G t g' u) = .out) ∧
      wOf (C.lastS m') = C.nreg (upd G t g') T ∧ sOf (C.lastS m') ≤ C.claims (upd G t g') m' T := by
  obtain ⟨T, hT, hw, hs⟩ := hI.cnt
  have htT : t < T := Inv.lt_bound hT (by rw [ht]; exact nofun)
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  have htq : C.qd m t = false := by
    cases h : C.qd m t
    · rfl
    · obtain ⟨_, _, _, h'⟩ := hI.qd_reg h; rw [ht] at h'; cases h'
  have hT' : ∀ u, T ≤ u → C.ph (upd G t g' u) = .out := fun u hu => by
    by_cases e' : u = t
    · subst e'; omega
    · rw [hph u e']; exact hT u hu
  have hreg : C.nreg (upd G t g') T = C.nreg G T := tsum_congr fun u _ => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; rfl
    · rw [hph u hu]
  have hnq : C.nq (upd G t g') m' T = C.nq G m T := tsum_congr fun u _ => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht, hq]; rfl
    · rw [hph u hu, hq]
  have hwkS : (tsum T fun u => (C.ph (upd G t g' u)).wkN) = tsum T fun u => (C.ph (G u)).wkN :=
    tsum_congr fun u _ => by
      by_cases hu : u = t
      · subst hu; rw [upd_self, hg', ht]; rfl
      · rw [hph u hu]
  have hcl : ∀ u, u ≠ t → C.cl (upd G t g') m' u = C.cl G m u := fun u hu => by
    unfold cl regCl; rw [hph u hu, hq, hwk, hE]
  refine ⟨T, hT', by rw [hlast, hreg]; exact hw, ?_⟩
  rw [hlast]
  unfold claims; rw [hwkS, hnq]
  by_cases hkeep : i + 1 < (C.Ep.hist m).size ∨ m.woken.contains t = true
  · -- still a claim: nothing changes
    have hct : C.cl (upd G t g') m' t = C.cl G m t := by
      unfold cl regCl; rw [upd_self, hg', ht, hq, hwk, hE, htq]
      rcases hkeep with h | h <;> simp [h, CPh.incN]
    rw [tsum_congr fun u _ => show C.cl (upd G t g') m' u = C.cl G m u by
      by_cases hu : u = t
      · subst hu; exact hct
      · exact hcl u hu]
    exact hs
  · -- the newest save: every post after `k` is still its signaller's
    have hfresh : (C.Ep.hist m).size = i + 1 := by
      have := (hI.reg t i jr true e ht).1; omega
    have hb := loopBack_bound (C := C) (G := G) hk hT fun q hkq hq' hlt => by
      rcases hI.pub q (by omega) hq' hlt with h | ⟨b, hb, hc⟩
      · exact h
      · exfalso
        have h1 := hI.rel_mono (b := b) (i - b) (by omega)
        rw [show b + (i - b) = i by omega] at h1
        have h2 := (hI.reg t i jr true e ht).2.2.1
        have := hfl q hq' (VClock.le_trans hc (VClock.le_trans h1 h2))
        omega
    rw [hs0, Nat.zero_add] at hb
    refine Nat.le_trans hb (Nat.le_trans (tsum_le fun u _ => ?_) (Nat.le_add_right _ _))
    by_cases hu : u = t
    · subst hu; rw [ht]; exact Nat.zero_le _
    · rw [hcl u hu]; unfold cl; exact Nat.le_add_right _ _

/-- **The count after a wake** by the signaller `t` at `wk n` (now out): the waiters it took off
the epoch's queue are woken, so claims, and they are at least `min n` of the queued ones
(`hmin`; module doc). -/
theorem Inv.cnt_wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {n : Nat} {g' : γ}
    (hI : C.Inv L G m) (ht : C.ph (G t) = .wk n) (hg' : C.ph g' = .out)
    (hS : C.S.hist m' = C.S.hist m) (hE : (C.Ep.hist m').size = (C.Ep.hist m).size)
    (hqd : ∀ u, C.qd m' u = true → C.qd m u = true)
    (hwk : ∀ u, C.qd m u = true → C.qd m' u = false → m'.woken.contains u = true)
    (hwk' : ∀ u, m.woken.contains u = true → m'.woken.contains u = true)
    (hmin : ∀ T, (∀ u, T ≤ u → C.ph (G u) = .out) →
      min n (C.nq G m T) + C.nq G m' T ≤ C.nq G m T) :
    ∃ T, (∀ u, T ≤ u → C.ph (upd G t g' u) = .out) ∧
      wOf (C.lastS m') = C.nreg (upd G t g') T ∧ sOf (C.lastS m') ≤ C.claims (upd G t g') m' T := by
  obtain ⟨T, hT, hw, hs⟩ := hI.cnt
  have htT : t < T := Inv.lt_bound hT (by rw [ht]; exact nofun)
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  have hT' : ∀ u, T ≤ u → C.ph (upd G t g' u) = .out := fun u hu => by
    by_cases e' : u = t
    · subst e'; omega
    · rw [hph u e']; exact hT u hu
  have hreg : C.nreg (upd G t g') T = C.nreg G T := tsum_congr fun u _ => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; rfl
    · rw [hph u hu]
  have hnq : C.nq (upd G t g') m' T = C.nq G m' T := tsum_congr fun u _ => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; rfl
    · rw [hph u hu]
  have hwkS : (tsum T fun u => (C.ph (upd G t g' u)).wkN) + n =
      tsum T fun u => (C.ph (G u)).wkN := by
    have := tsum_upd (g := fun u => (C.ph (G u)).wkN) (g' := fun u => (C.ph (upd G t g' u)).wkN)
      htT (fun u hu => by rw [hph u hu])
    simp only [upd_self, hg', ht, CPh.wkN] at this
    omega
  -- a claim grows by one for each waiter taken off the queue
  have hcl : ∀ u, u < T → C.cl G m u +
      ((if (C.ph (G u)).isReg && C.qd m u then 1 else 0) -
        (if (C.ph (G u)).isReg && C.qd m' u then 1 else 0)) ≤ C.cl (upd G t g') m' u := by
    intro u _
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; simp [cl, CPh.incN, regCl, CPh.isReg]
    rw [show C.cl (upd G t g') m' u = C.cl G m' u by unfold cl; rw [hph u hu]]
    unfold cl
    rcases hp : C.ph (G u) with _ | _ | _ | ⟨i, jr, sn, e⟩ | _ | _
    all_goals simp only [regCl, CPh.isReg, CPh.incN, Bool.false_and, if_false, Nat.sub_self,
      Nat.add_zero, Nat.le_refl]
    simp only [Bool.true_and, Nat.zero_add, hE]
    cases h1 : C.qd m u
    · have h2 : C.qd m' u = false := by cases h : C.qd m' u; rfl; exact absurd (hqd u h) (by simp [h1])
      simp only [h2, if_false, Nat.sub_self, Nat.add_zero, Bool.not_false, Bool.true_and]
      cases sn <;> cases hw : m.woken.contains u <;> simp [hwk' u, hw] <;> split <;> simp_all
    · obtain ⟨_, _, _, h'⟩ := hI.qd_reg h1
      rw [hp] at h'; cases h'
      cases h2 : C.qd m' u
      · simp [hwk u h1 h2]
      · simp
  have hsum := tsum_le hcl
  rw [tsum_add] at hsum
  have hflip : (tsum T fun u => (if (C.ph (G u)).isReg && C.qd m u then 1 else 0) -
      (if (C.ph (G u)).isReg && C.qd m' u then 1 else 0)) + C.nq G m' T = C.nq G m T := by
    unfold nq; rw [← tsum_add]
    refine tsum_congr fun u _ => ?_
    by_cases h : ((C.ph (G u)).isReg && C.qd m' u) = true
    · have : ((C.ph (G u)).isReg && C.qd m u) = true := by
        simp only [Bool.and_eq_true] at h ⊢; exact ⟨h.1, hqd u h.2⟩
      simp [h, this]
    · simp only [h, if_false]; split <;> rfl
  have hmn := hmin T hT
  have hn : n ≤ tsum T fun u => (C.ph (G u)).wkN := by
    have := le_tsum (fun u => (C.ph (G u)).wkN) htT
    simp only [ht, CPh.wkN] at this; exact this
  refine ⟨T, hT', by rw [hlast, hreg]; exact hw, ?_⟩
  rw [hlast]
  unfold claims at hs ⊢
  rw [hnq]
  omega

end FCond

end Full
end Zig
