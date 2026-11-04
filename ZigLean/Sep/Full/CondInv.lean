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
  tsum T (C.cl G m) + Min.min (tsum T fun u => (C.ph (G u)).wkN) (C.nq G m T)

/-- The kinds of consecutive state writes (H1): a registration `(w + 1, s)`, a post or broadcast
`(w, s')` with `s < s' ≤ w`, or a consume `(w - 1, s - 1)`. -/
def SStep (a b : Word.Entry) : Prop :=
  (wOf b = wOf a + 1 ∧ sOf b = sOf a) ∨ (wOf b = wOf a ∧ sOf a < sOf b ∧ sOf b ≤ wOf a) ∨
    (wOf b + 1 = wOf a ∧ sOf b + 1 = sOf a)

/-! ## The invariant -/

/-- The condition's invariant, with the lock's places (module doc). -/
structure Inv (L : FLock γ) (G : ThreadId → γ) (m : Mem) : Prop where
  spos : 0 < (C.S.hist m).size
  /-- (H1) Every state write is a `u32` pair `(w, s)` with `s ≤ w`. -/
  sv : ∀ k < (C.S.hist m).size, (C.S.hist m)[k]!.Val (val (C.S.hist m)[k]!) ∧
    sOf (C.S.hist m)[k]! ≤ wOf (C.S.hist m)[k]!
  /-- (H1) Consecutive state writes differ by a registration, a post (`signals` up to at most
  `waiters`) or a consume. The count does not need it (`le_add_tsum_up`); the derived
  singleton lemmas read the newest state from it. -/
  steps : ∀ k, k + 1 < (C.S.hist m).size → SStep (C.S.hist m)[k]! (C.S.hist m)[k + 1]!
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
  /-- A thread in the condition's code exists. -/
  ex : ∀ u, C.ph (G u) ≠ .out → u < m.threads.size
  /-- Room for one more waiter while one is in the critical code (`waiters < 65535`). -/
  room : ∀ u, (C.ph (G u)).crit → wOf (C.lastS m) < 65535
  /-- One thread in the critical code (it holds the mutex). -/
  crit1 : ∀ u v, (C.ph (G u)).crit → (C.ph (G v)).crit → u = v
  crit : ∀ u, (C.ph (G u)).crit → L.ph (G u) = .holds
  lp : ∀ u, (C.ph (G u)).sig → L.ph (G u) = .out ∨ L.ph (G u) = .holds
  sx : ∀ u, (C.ph (G u)).sig → C.sx (G u)

variable {C}

/-- **The condition at its start**: every thread out of its code, no thread in the futex queue,
the state has its first write `(0, 0)` and the epoch its first write. -/
theorem Inv.start {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hS : (C.S.hist m).size = 1)
    (hS0 : (C.S.hist m)[0]!.Val (0 : BitVec 32)) (hE : (C.Ep.hist m).size = 1)
    {e0 : BitVec 32} (hE0 : (C.Ep.hist m)[0]!.Val e0) (hout : ∀ u, C.ph (G u) = .out)
    (hq : m.waiters = #[]) : C.Inv L G m where
  spos := by omega
  sv k hk := by
    obtain rfl : k = 0 := by omega
    rw [val_of hS0]; exact ⟨hS0, by simp [sOf, wOf, val_of hS0]⟩
  steps k hk := by omega
  e32 k hk := by
    obtain rfl : k = 0 := by omega
    rw [val_of hE0]; exact hE0
  ep k hk := by omega
  pub q h0 hq' _ := by omega
  inc v _ _ h := by rw [hout v] at h; cases h
  ld u _ _ h := by rw [hout u] at h; cases h
  reg u _ _ _ _ h := by rw [hout u] at h; cases h
  q w hw := by simp [hq] at hw
  qw w hw := by simp [hq] at hw
  cnt := ⟨0, fun u _ => hout u, by
    show wOf (C.S.hist m)[(C.S.hist m).size - 1]! = tsum 0 _
    rw [hS]; simp [wOf, val_of hS0], by
    show sOf (C.S.hist m)[(C.S.hist m).size - 1]! ≤ _
    rw [hS]; simp [sOf, val_of hS0]⟩
  ex u h := absurd (hout u) h
  room u h := by rw [hout u] at h; exact absurd h (by decide)
  crit1 u _ h := by rw [hout u] at h; exact absurd h (by decide)
  crit u h := by rw [hout u] at h; exact absurd h (by decide)
  lp u h := by rw [hout u] at h; exact absurd h (by decide)
  sx u h := by rw [hout u] at h; exact absurd h (by decide)

/-! ## Counting lemmas -/

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
  simp only [show h.size - 1 + 1 = h.size by omega] at hle
  refine Nat.le_trans hle (Nat.add_le_add_left (tsum_tag (fun v => (C.ph (G v)).incQ) ?_) _)
  intro q hq hpos
  by_cases hkq : k < q
  · simp only [hkq, if_true] at hpos ⊢
    obtain ⟨v, n, hv, hn⟩ := hpub q hkq hq (by omega)
    refine ⟨v, ?_, by rw [hv]; rfl, by rw [hv]; exact hn⟩
    by_cases hvT : v < T
    · exact hvT
    · have := hT v (Nat.le_of_not_lt hvT); rw [this] at hv; cases hv
  · simp [hkq] at hpos

variable {L : FLock γ}

/-! ## The epoch's values -/

theorem ofNat_succ (d : Nat) : BitVec.ofNat 32 (d + 1) = BitVec.ofNat 32 d + 1 := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl]
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
  · exact absurd (hT t (by simp only [ThreadId] at *; omega)) ht

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
    have e1 : (C.ph (upd G t g' t)).wkN = n := by rw [upd_self, hg']; rfl
    have e2 : (C.ph (G t)).wkN = 0 := by rw [ht]; rfl
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
    · subst e; simp only [ThreadId] at *; omega
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
    · subst e'; simp only [ThreadId] at *; omega
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
      rcases hkeep with h | h
      · simp [h, CPh.incN]
      · simp only [Array.contains_iff_mem] at h; simp [h, CPh.incN]
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
      Min.min n (C.nq G m T) + C.nq G m' T ≤ C.nq G m T) :
    ∃ T, (∀ u, T ≤ u → C.ph (upd G t g' u) = .out) ∧
      wOf (C.lastS m') = C.nreg (upd G t g') T ∧ sOf (C.lastS m') ≤ C.claims (upd G t g') m' T := by
  obtain ⟨T, hT, hw, hs⟩ := hI.cnt
  have htT : t < T := Inv.lt_bound hT (by rw [ht]; exact nofun)
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  have hT' : ∀ u, T ≤ u → C.ph (upd G t g' u) = .out := fun u hu => by
    by_cases e' : u = t
    · subst e'; simp only [ThreadId] at *; omega
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
    have e1 : (C.ph (upd G t g' t)).wkN = 0 := by rw [upd_self, hg']; rfl
    have e2 : (C.ph (G t)).wkN = n := by rw [ht]; rfl
    omega
  -- a claim grows by one for each waiter taken off the queue
  have hcl : ∀ u, u < T → C.cl G m u +
      ((if (C.ph (G u)).isReg && C.qd m u then 1 else 0) -
        (if (C.ph (G u)).isReg && C.qd m' u then 1 else 0)) ≤ C.cl (upd G t g') m' u := by
    intro u _
    by_cases hu : u = t
    · subst hu; unfold cl; rw [upd_self, hg', ht]; simp [CPh.incN, regCl, CPh.isReg]
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
      · have h3 := hwk u h1 h2
        simp only [Array.contains_iff_mem] at h3
        simp [h3]
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
    have e2 : (C.ph (G t)).wkN = n := by rw [ht]; rfl
    omega
  refine ⟨T, hT', by rw [hlast, hreg]; exact hw, ?_⟩
  rw [hlast]
  unfold claims at hs ⊢
  rw [hnq]
  omega

/-- **Pending signals have a claim** (no lost wakeup): with a signal pending or a signaller
between its post and its wake, some thread is such a signaller or a registered waiter that is
not queued at the epoch (it will read the state). -/
theorem Inv.claim_of {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m)
    (h : 0 < sOf (C.lastS m) ∨ ∃ v, (C.ph (G v)).sig) :
    ∃ u, (C.ph (G u)).sig ∨ ∃ i jr sn e, C.ph (G u) = .reg i jr sn e ∧ C.qd m u = false := by
  rcases h with h | ⟨v, hv⟩
  · obtain ⟨T, -, -, hs⟩ := hI.cnt
    unfold claims at hs
    by_cases hc : 0 < tsum T (C.cl G m)
    · obtain ⟨u, -, hu⟩ := exists_of_tsum_pos hc
      refine ⟨u, ?_⟩
      unfold cl at hu
      rcases hp : C.ph (G u) with _ | _ | _ | ⟨i, jr, sn, e⟩ | ⟨q, n⟩ | n <;>
        rw [hp] at hu <;> simp [CPh.incN, regCl] at hu
      · right
        refine ⟨i, jr, sn, e, rfl, ?_⟩
        cases hq : C.qd m u
        · rfl
        · obtain ⟨_, _, _, h'⟩ := hI.qd_reg hq
          rw [hp] at h'; cases h'
          simp [hq] at hu
      · left; rfl
    · have hw : 0 < tsum T fun u => (C.ph (G u)).wkN := by omega
      obtain ⟨u, -, hu⟩ := exists_of_tsum_pos hw
      refine ⟨u, .inl ?_⟩
      revert hu; cases C.ph (G u) <;> simp [CPh.wkN, CPh.sig]
  · exact ⟨v, .inl hv⟩

/-- **No deadlock with a pending signal** (no lost wakeup, the memory's part of `P.Live`): with a
signal pending or a signaller between its post and its wake, not every thread has ended, sleeps
at a futex or waits at a join. `hfin`, `hjoins`: such a thread is out of the condition's code;
`hL`: nobody waits at the mutex (all blocked); `hnq`: a thread outside or holding the mutex is
not in the futex queue (the lock's invariant). -/
theorem Inv.noDeadlock {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m) {fin joins : γ → Prop}
    (hfin : ∀ g, fin g → C.ph g = .out) (hjoins : ∀ g, joins g → C.ph g = .out)
    (hL : ∀ w ∈ m.waiters, w.2 ≠ L.ptr)
    (hnq : ∀ u, (L.ph (G u) = .out ∨ L.ph (G u) = .holds) → m.waiters.any (·.1 == u) = false)
    (hall : ∀ u < m.threads.size, fin (G u) ∨ m.waiters.any (·.1 == u) = true ∨ joins (G u))
    (h : 0 < sOf (C.lastS m) ∨ ∃ v, (C.ph (G v)).sig) : False := by
  obtain ⟨u, hu⟩ := hI.claim_of h
  have hne : C.ph (G u) ≠ .out := by
    rcases hu with hu | ⟨i, jr, sn, e, hp, -⟩
    · intro h'; rw [h'] at hu; cases hu
    · rw [hp]; exact nofun
  have hnotq : m.waiters.any (·.1 == u) = false := by
    rcases hu with hu | ⟨i, jr, sn, e, hp, hq⟩
    · exact hnq u (hI.lp u hu)
    · cases hany : m.waiters.any (·.1 == u)
      · rfl
      · obtain ⟨w, hw, hwe⟩ := Array.any_eq_true'.mp hany
        have e' : w.1 = u := by simpa using hwe
        rcases hI.qw w hw (by rw [e', hp]; rfl) with h1 | h1
        · have : C.qd m u = true := by
            unfold qd; exact Array.any_eq_true'.mpr ⟨w, hw, by simp [e', h1]⟩
          rw [hq] at this; cases this
        · exact absurd h1 (hL w hw)
  rcases hall u (hI.ex u hne) with h1 | h1 | h1
  · exact hne (hfin _ h1)
  · rw [hnotq] at h1; cases h1
  · exact hne (hjoins _ h1)

/-- **The count after a post** by `t` (out, now at `inc q n`): the newest `signals` grows by at
most `n`, the claim of `t`. -/
theorem Inv.cnt_post {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {q n : Nat} {g' : γ}
    (hI : C.Inv L G m) (ht : C.ph (G t) = .out) (hg' : C.ph g' = .inc q n)
    (hw : wOf (C.lastS m') = wOf (C.lastS m)) (hs : sOf (C.lastS m') ≤ sOf (C.lastS m) + n)
    (hE : (C.Ep.hist m').size = (C.Ep.hist m).size)
    (hq : ∀ u, C.qd m' u = C.qd m u) (hwk : m'.woken = m.woken) :
    ∃ T, (∀ u, T ≤ u → C.ph (upd G t g' u) = .out) ∧
      wOf (C.lastS m') = C.nreg (upd G t g') T ∧ sOf (C.lastS m') ≤ C.claims (upd G t g') m' T := by
  obtain ⟨T₀, hT₀, hw₀, hs₀⟩ := hI.cnt
  have hT : ∀ u, Max.max T₀ (t + 1) ≤ u → C.ph (G u) = .out := fun u hu => hT₀ u (by simp only [ThreadId] at *; omega)
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  refine ⟨Max.max T₀ (t + 1), fun u hu => ?_, ?_, ?_⟩
  · by_cases e' : u = t
    · subst e'; simp only [ThreadId] at *; omega
    · rw [hph u e']; exact hT u hu
  · rw [hw, hw₀, ← nreg_ext hT₀ (Nat.le_max_left T₀ (t + 1))]
    refine tsum_congr fun u _ => ?_
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg', ht]; rfl
    · rw [hph u hu]
  · rw [← claims_ext hT₀ (Nat.le_max_left T₀ (t + 1))] at hs₀
    have htT : t < Max.max T₀ (t + 1) := by simp only [ThreadId] at *; omega
    unfold claims at hs₀ ⊢
    have hwkS : (tsum (Max.max T₀ (t + 1)) fun u => (C.ph (upd G t g' u)).wkN) =
        tsum (Max.max T₀ (t + 1)) fun u => (C.ph (G u)).wkN := tsum_congr fun u _ => by
      by_cases hu : u = t
      · subst hu; rw [upd_self, hg', ht]; rfl
      · rw [hph u hu]
    have hnq : C.nq (upd G t g') m' (Max.max T₀ (t + 1)) = C.nq G m (Max.max T₀ (t + 1)) :=
      tsum_congr fun u _ => by
        by_cases hu : u = t
        · subst hu; rw [upd_self, hg', ht]; rfl
        · rw [hph u hu, hq]
    have hcl := tsum_upd (g := C.cl G m) (g' := C.cl (upd G t g') m') htT fun u hu => by
      unfold cl regCl; rw [hph u hu, hq, hwk, hE]
    have hct : C.cl G m t = 0 := by unfold cl; rw [ht]; rfl
    have hct' : C.cl (upd G t g') m' t = n := by unfold cl; rw [upd_self, hg']; simp [CPh.incN, regCl]
    rw [hwkS, hnq]
    omega

/-- **The count after a consume** by `t` (registered, now out): one signal and one waiter fewer,
and the claim of `t` (it read the state) goes. -/
theorem Inv.cnt_consume {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {i jr : Nat}
    {e : BitVec 32} {g' : γ} (hI : C.Inv L G m) (ht : C.ph (G t) = .reg i jr true e)
    (hg' : C.ph g' = .out)
    (hw : wOf (C.lastS m') + 1 = wOf (C.lastS m)) (hs : sOf (C.lastS m') + 1 = sOf (C.lastS m))
    (hE : (C.Ep.hist m').size = (C.Ep.hist m).size)
    (hq : ∀ u, C.qd m' u = C.qd m u) (hwk : m'.woken = m.woken) :
    ∃ T, (∀ u, T ≤ u → C.ph (upd G t g' u) = .out) ∧
      wOf (C.lastS m') = C.nreg (upd G t g') T ∧ sOf (C.lastS m') ≤ C.claims (upd G t g') m' T := by
  obtain ⟨T, hT, hw₀, hs₀⟩ := hI.cnt
  have htT : t < T := Inv.lt_bound hT (by rw [ht]; exact nofun)
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have htq : C.qd m t = false := by
    cases h : C.qd m t
    · rfl
    · obtain ⟨_, _, _, h'⟩ := hI.qd_reg h; rw [ht] at h'; cases h'
  refine ⟨T, fun u hu => ?_, ?_, ?_⟩
  · by_cases e' : u = t
    · subst e'; rw [upd_self, hg']
    · rw [hph u e']; exact hT u hu
  · have := tsum_upd (g := fun u => if (C.ph (G u)).isReg then 1 else 0)
      (g' := fun u => if (C.ph (upd G t g' u)).isReg then 1 else 0) htT fun u hu => by
        rw [hph u hu]
    have e1 : (if (C.ph (upd G t g' t)).isReg then 1 else 0) = 0 := by rw [upd_self, hg']; rfl
    have e2 : (if (C.ph (G t)).isReg then 1 else 0) = 1 := by rw [ht]; rfl
    unfold nreg at hw₀ ⊢; omega
  · unfold claims at hs₀ ⊢
    have hwkS : (tsum T fun u => (C.ph (upd G t g' u)).wkN) = tsum T fun u => (C.ph (G u)).wkN :=
      tsum_congr fun u _ => by
        by_cases hu : u = t
        · subst hu; rw [upd_self, hg', ht]; rfl
        · rw [hph u hu]
    have hnq : C.nq (upd G t g') m' T = C.nq G m T := tsum_congr fun u _ => by
      by_cases hu : u = t
      · subst hu; rw [upd_self, hg', ht, htq]; rfl
      · rw [hph u hu, hq]
    have hcl := tsum_upd (g := C.cl G m) (g' := C.cl (upd G t g') m') htT fun u hu => by
      unfold cl regCl; rw [hph u hu, hq, hwk, hE]
    have hct : C.cl G m t = 1 := by unfold cl; rw [ht]; simp [CPh.incN, regCl]
    have hct' : C.cl (upd G t g') m' t = 0 := by unfold cl; rw [upd_self, hg']; rfl
    rw [hwkS, hnq]
    omega

/-- **The claims only grow** when every own claim grows, the wakes owed stay and the queued
waiters do not shrink. -/
theorem claims_mono {G G' : ThreadId → γ} {m m' : Mem} {T : Nat}
    (hcl : ∀ u, u < T → C.cl G m u ≤ C.cl G' m' u)
    (hwk : (tsum T fun u => (C.ph (G' u)).wkN) = tsum T fun u => (C.ph (G u)).wkN)
    (hnq : C.nq G m T ≤ C.nq G' m' T) : C.claims G m T ≤ C.claims G' m' T := by
  unfold claims
  rw [hwk]
  have := tsum_le hcl
  have : Min.min (tsum T fun u => (C.ph (G u)).wkN) (C.nq G m T) ≤
      Min.min (tsum T fun u => (C.ph (G u)).wkN) (C.nq G' m' T) := by omega
  omega

/-- A thread pushed into the futex queue at the epoch. -/
theorem qd_push {M : Mem} {t u : ThreadId} :
    C.qd { M with waiters := M.waiters.push (t, C.Ep.ptr) } u = (C.qd M u || t == u) := by
  unfold qd
  simp

/-- **The waiter's sleep at the epoch** (`reg i jr false e`, the futex compare read its saved
value `e`): it joins the queue. `hwk`: it had no pending wake (`Proto.futexWait_ok`: it sleeps
only then; library prerequisite 3 of the PR); `hnq`: it was not queued. -/
theorem Inv.sleep {G : ThreadId → γ} {M : Mem} {t : ThreadId} {i jr : Nat} {e : BitVec 32}
    (hI : C.Inv L G M) (ht : C.ph (G t) = .reg i jr false e) (hv : (C.lastE M).Val e)
    (hwk : M.woken.contains t = false) (hnq : C.qd M t = false) :
    C.Inv L G { M with waiters := M.waiters.push (t, C.Ep.ptr) } := by
  have hfresh := hI.fresh_of_val ht hv
  refine { hI with
    q := fun w hw hp => ?_, qw := fun w hw hp => ?_, cnt := ?_ }
  · rcases Array.mem_push.mp hw with hw | rfl
    · exact hI.q w hw hp
    · exact ⟨i, jr, e, ht⟩
  · rcases Array.mem_push.mp hw with hw | rfl
    · exact hI.qw w hw hp
    · exact .inl rfl
  · obtain ⟨T, hT, hw, hs⟩ := hI.cnt
    refine ⟨T, hT, hw, Nat.le_trans hs (claims_mono (fun u _ => ?_) rfl ?_)⟩
    · by_cases hu : u = t
      · subst hu
        have : C.cl G M u = 0 := by
          have hwk' : u ∉ M.woken := by simpa using hwk
          unfold cl regCl; rw [ht]; simp [CPh.incN, hnq, hwk', hfresh]
        omega
      · unfold cl regCl
        rw [qd_push, show (t == u) = false from beq_false_of_ne (Ne.symm hu), Bool.or_false]
        exact Nat.le_refl _
    · unfold nq
      refine tsum_le fun u _ => ?_
      rw [qd_push]
      cases (C.ph (G u)).isReg <;> cases C.qd M u <;> cases (t == u) <;> simp

/-- **The waiter's return from its futex wait** (`reg i jr false e` to `reg i jr true e`): after a
pending wake (`woken` loses `t`), a spurious return, or the kernel's read without sleeping. `hnq`:
it is not queued (library prerequisite 3); `hwk`: only `t`'s wake goes; `hE`, `hS`: the writes
stay; `hcl`: the clocks only grow. -/
theorem Inv.ret {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {i jr : Nat} {e : BitVec 32}
    {g' : γ} (hI : C.Inv L G m) (ht : C.ph (G t) = .reg i jr false e)
    (hg' : C.ph g' = .reg i jr true e) (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hwt : m'.waiters = m.waiters) (hth : m'.threads = m.threads)
    (hwk : ∀ u, u ≠ t → m'.woken.contains u = m.woken.contains u)
    (hnq : C.qd m t = false)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L (upd G t g') m' := by
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hqd : ∀ u, C.qd m' u = C.qd m u := fun u => by unfold qd; rw [hwt]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  -- the fields of the other threads, and `t`'s at its new place
  have hreg : ∀ u i' jr' sn' e', C.ph (upd G t g' u) = .reg i' jr' sn' e' →
      C.ph (G u) = .reg i' jr' false e' ∨ (u = t ∧ C.ph (G u) = .reg i' jr' false e') ∨
        C.ph (G u) = .reg i' jr' sn' e' := fun u i' jr' sn' e' h => by
    by_cases hu : u = t
    · subst hu; rw [upd_self, hg'] at h; cases h; exact .inr (.inl ⟨rfl, ht⟩)
    · rw [hph u hu] at h; exact .inr (.inr h)
  have hcrit : ∀ u, (C.ph (upd G t g' u)).crit → u ≠ t := fun u h hu => by
    subst hu; rw [upd_self, hg'] at h; cases h
  have hsig : ∀ u, (C.ph (upd G t g' u)).sig → u ≠ t := fun u h hu => by
    subst hu; rw [upd_self, hg'] at h; cases h
  refine ⟨by rw [hS]; exact hI.spos, by rw [hS]; exact hI.sv, by rw [hS]; exact hI.steps,
    by rw [hE]; exact hI.e32, by rw [hE]; exact hI.ep, fun q h0 hq hlt => ?_,
    fun v q n h => ?_, fun u i' e' h => ?_, fun u i' jr' sn' e' h => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, ?_, fun u h => ?_, fun u h => ?_, fun u v hu hv => ?_,
    fun u h => ?_, fun u h => ?_, fun u h => ?_⟩
  · rw [hS] at hq hlt ⊢; rw [hE]
    rcases hI.pub q h0 hq hlt with ⟨v, n, hv, hn⟩ | h
    · refine .inl ⟨v, n, ?_, hn⟩
      by_cases hvt : v = t
      · subst hvt; rw [ht] at hv; cases hv
      · rw [hph v hvt]; exact hv
    · exact .inr h
  · have hvt : v ≠ t := fun e' => by subst e'; rw [upd_self, hg'] at h; cases h
    rw [hph v hvt] at h
    obtain ⟨h1, h2, h3⟩ := hI.inc v q n h
    rw [hS]; exact ⟨h1, h2, VClock.le_trans h3 (hclk v)⟩
  · have hut : u ≠ t := fun e' => by subst e'; rw [upd_self, hg'] at h; cases h
    rw [hph u hut] at h
    obtain ⟨h1, h2, h3⟩ := hI.ld u i' e' h
    rw [hE]; exact ⟨h1, h2, VClock.le_trans h3 (hclk u)⟩
  · have h' : ∃ sn₀, C.ph (G u) = .reg i' jr' sn₀ e' := by
      rcases hreg u i' jr' sn' e' h with h | ⟨-, h⟩ | h
      · exact ⟨false, h⟩
      · exact ⟨false, h⟩
      · exact ⟨sn', h⟩
    obtain ⟨sn₀, h'⟩ := h'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.reg u i' jr' sn₀ e' h'
    rw [hS, hE]
    exact ⟨h1, h2, VClock.le_trans h3 (hclk u), h4, VClock.le_trans h5 (hclk u), h6⟩
  · rw [hwt] at hw
    have hwt' : w.1 ≠ t := fun e' => by
      have : C.qd m t = true := by
        unfold qd; exact Array.any_eq_true'.mpr ⟨w, hw, by simp [e', hp]⟩
      rw [hnq] at this; cases this
    rw [hph _ hwt']; exact hI.q w hw hp
  · rw [hwt] at hw
    by_cases hwt' : w.1 = t
    · rw [hwt', upd_self, hg'] at hp; rw [← hwt'] at ht
      exact hI.qw w hw (by rw [ht]; rfl)
    · rw [hph _ hwt'] at hp; exact hI.qw w hw hp
  · obtain ⟨T, hT, hw, hs⟩ := hI.cnt
    have hT' : ∀ u, T ≤ u → C.ph (upd G t g' u) = .out := fun u hu => by
      by_cases e' : u = t
      · subst e'; have := Inv.lt_bound hT (t := u) (by rw [ht]; exact nofun)
        simp only [ThreadId] at *; omega
      · rw [hph u e']; exact hT u hu
    refine ⟨T, hT', ?_, ?_⟩
    · rw [hlast, hw]
      refine tsum_congr fun u _ => ?_
      by_cases hu : u = t
      · subst hu; rw [upd_self, hg', ht]; rfl
      · rw [hph u hu]
    · rw [hlast]
      refine Nat.le_trans hs (claims_mono (fun u _ => ?_) (tsum_congr fun u _ => ?_) ?_)
      · by_cases hu : u = t
        · subst hu; unfold cl regCl; rw [upd_self, hg', ht]
          simp [CPh.incN, hqd, hnq]
          split <;> omega
        · unfold cl regCl; rw [hph u hu, hqd, hwk u hu, hE]; exact Nat.le_refl _
      · by_cases hu : u = t
        · subst hu; rw [upd_self, hg', ht]; rfl
        · rw [hph u hu]
      · unfold nq
        refine tsum_le fun u _ => ?_
        by_cases hu : u = t
        · subst hu; rw [upd_self, hg', ht, hqd, hnq]; exact Nat.le_refl _
        · rw [hph u hu, hqd]; exact Nat.le_refl _
  · rw [hth]
    by_cases hu : u = t
    · subst hu; exact hI.ex u (by rw [ht]; exact nofun)
    · rw [hph u hu] at h; exact hI.ex u h
  · have := hcrit u h; rw [hph u this] at h; rw [hlast]; exact hI.room u h
  · have := hcrit u hu; have := hcrit v hv
    rw [hph u (hcrit u hu)] at hu; rw [hph v (hcrit v hv)] at hv
    exact hI.crit1 u v hu hv
  · have hut := hcrit u h; rw [hph u hut] at h; rw [upd_ne _ _ hut]; exact hI.crit u h
  · have hut := hsig u h; rw [hph u hut] at h; rw [upd_ne _ _ hut]; exact hI.lp u h
  · have hut := hsig u h; rw [hph u hut] at h; rw [upd_ne _ _ hut]; exact hI.sx u h

/-- A place that the count does not see (`out`, `en`, `ld`). -/
def quiet (p : CPh) : Prop := p.isReg = false ∧ p.sig = false

theorem quiet_cl {p : CPh} (h : quiet p) (m : Mem) (u : ThreadId) :
    p.incN = 0 ∧ p.wkN = 0 ∧ C.regCl m u p = 0 := by
  obtain ⟨h1, h2⟩ := h
  cases p <;> simp_all [CPh.isReg, CPh.sig, CPh.incN, CPh.wkN, regCl]

/-- **A step of `t` among the places the count does not see** (the wait's entry `out → en`, its
epoch load `en → ld i e`), with no write and the same futex queue: `hld`, the new `ld`'s acquired
write; `hcr`, a new critical place holds the mutex, has room and is the only one (the mutex);
`htn`, a thread in the code exists. -/
theorem Inv.quiet {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g' : γ} (hI : C.Inv L G m)
    (ht : quiet (C.ph (G t))) (hg' : quiet (C.ph g'))
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hwt : m'.waiters = m.waiters) (hwk : m'.woken = m.woken) (hth : m'.threads = m.threads)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (htq : ∀ w ∈ m.waiters, w.1 ≠ t)
    (hld : ∀ i e, C.ph g' = .ld i e → i < (C.Ep.hist m).size ∧ (C.Ep.hist m)[i]!.Val e ∧
      VClock.le (C.Ep.hist m)[i]!.relClock (m'.clocks[t]!) = true)
    (hcr : (C.ph g').crit → L.ph g' = .holds ∧ wOf (C.lastS m) < 65535 ∧
      ∀ u, u ≠ t → (C.ph (G u)).crit = false)
    (htn : C.ph g' ≠ .out → t < m.threads.size) :
    C.Inv L (upd G t g') m' := by
  have hph : ∀ u, u ≠ t → C.ph (upd G t g' u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hqd : ∀ u, C.qd m' u = C.qd m u := fun u => by unfold qd; rw [hwt]
  have hlast : C.lastS m' = C.lastS m := by unfold FCond.lastS; rw [hS]
  have hnreg : ∀ u p, C.ph (upd G t g' u) = p → p.isReg = true → u ≠ t := fun u p h hp hu => by
    subst hu; rw [upd_self] at h; rw [← h, hg'.1] at hp; cases hp
  have hnsig : ∀ u, (C.ph (upd G t g' u)).sig → u ≠ t := fun u h hu => by
    subst hu; rw [upd_self, hg'.2] at h; cases h
  have hnsig₀ : ∀ v, (C.ph (G v)).sig → v ≠ t := fun v h hv => by
    subst hv; rw [ht.2] at h; cases h
  refine ⟨by rw [hS]; exact hI.spos, by rw [hS]; exact hI.sv, by rw [hS]; exact hI.steps,
    by rw [hE]; exact hI.e32, by rw [hE]; exact hI.ep, fun q h0 hq hlt => ?_,
    fun v q n h => ?_, fun u i e h => ?_, fun u i jr sn e h => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, ?_, fun u h => ?_, fun u h => ?_, fun u v hu hv => ?_,
    fun u h => ?_, fun u h => ?_, fun u h => ?_⟩
  · rw [hS] at hq hlt ⊢; rw [hE]
    rcases hI.pub q h0 hq hlt with ⟨v, n, hv, hn⟩ | h
    · refine .inl ⟨v, n, ?_, hn⟩
      rw [hph v (hnsig₀ v (by rw [hv]; rfl))]; exact hv
    · exact .inr h
  · have hvt := hnsig v (by rw [h]; rfl)
    rw [hph v hvt] at h
    obtain ⟨h1, h2, h3⟩ := hI.inc v q n h
    rw [hS]; exact ⟨h1, h2, VClock.le_trans h3 (hclk v)⟩
  · rw [hE]
    by_cases hut : u = t
    · subst hut; rw [upd_self] at h; exact hld i e h
    · rw [hph u hut] at h
      obtain ⟨h1, h2, h3⟩ := hI.ld u i e h
      exact ⟨h1, h2, VClock.le_trans h3 (hclk u)⟩
  · have hut := hnreg u _ h rfl
    rw [hph u hut] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.reg u i jr sn e h
    rw [hS, hE]
    exact ⟨h1, h2, VClock.le_trans h3 (hclk u), h4, VClock.le_trans h5 (hclk u), h6⟩
  · rw [hwt] at hw
    rw [hph _ (htq w hw)]; exact hI.q w hw hp
  · rw [hwt] at hw
    rw [hph _ (htq w hw)] at hp; exact hI.qw w hw hp
  · obtain ⟨T₀, hT₀, hw₀, hs₀⟩ := hI.cnt
    have hT : ∀ u, Max.max T₀ (t + 1) ≤ u → C.ph (G u) = .out := fun u hu =>
      hT₀ u (by simp only [ThreadId] at *; omega)
    have htT : t < Max.max T₀ (t + 1) := by simp only [ThreadId] at *; omega
    refine ⟨Max.max T₀ (t + 1), fun u hu => ?_, ?_, ?_⟩
    · by_cases e' : u = t
      · subst e'; simp only [ThreadId] at *; omega
      · rw [hph u e']; exact hT u hu
    · rw [hlast, hw₀, ← nreg_ext hT₀ (Nat.le_max_left T₀ (t + 1))]
      refine tsum_congr fun u _ => ?_
      by_cases hu : u = t
      · subst hu; rw [upd_self, hg'.1, ht.1]
      · rw [hph u hu]
    · rw [hlast]
      have hs := hs₀
      rw [← claims_ext hT₀ (Nat.le_max_left T₀ (t + 1))] at hs
      refine Nat.le_trans hs (claims_mono (fun u _ => ?_) (tsum_congr fun u _ => ?_) ?_)
      · by_cases hu : u = t
        · subst hu
          obtain ⟨a1, -, a3⟩ := quiet_cl (C := C) ht m u
          have : C.cl G m u = 0 := by unfold cl; rw [a1, a3]
          omega
        · unfold cl regCl; rw [hph u hu, hqd, hwk, hE]; exact Nat.le_refl _
      · by_cases hu : u = t
        · subst hu; rw [upd_self, (quiet_cl (C := C) hg' m u).2.1, (quiet_cl (C := C) ht m u).2.1]
        · rw [hph u hu]
      · unfold nq
        refine tsum_le fun u _ => ?_
        by_cases hu : u = t
        · subst hu; rw [upd_self, hg'.1, ht.1]; exact Nat.le_refl _
        · rw [hph u hu, hqd]; exact Nat.le_refl _
  · rw [hth]
    by_cases hu : u = t
    · subst hu; rw [upd_self] at h; exact htn h
    · rw [hph u hu] at h; exact hI.ex u h
  · rw [hlast]
    by_cases hu : u = t
    · subst hu; rw [upd_self] at h; exact (hcr h).2.1
    · rw [hph u hu] at h; exact hI.room u h
  · by_cases hut : u = t
    · by_cases hvt : v = t
      · rw [hut, hvt]
      · subst hut; rw [hph v hvt] at hv; rw [upd_self] at hu
        rw [(hcr hu).2.2 v hvt] at hv; cases hv
    · by_cases hvt : v = t
      · subst hvt; rw [hph u hut] at hu; rw [upd_self] at hv
        rw [(hcr hv).2.2 u hut] at hu; cases hu
      · rw [hph u hut] at hu; rw [hph v hvt] at hv; exact hI.crit1 u v hu hv
  · by_cases hut : u = t
    · subst hut; rw [upd_self] at h ⊢; exact (hcr h).1
    · rw [hph u hut] at h; rw [upd_ne _ _ hut]; exact hI.crit u h
  · have hut := hnsig u h; rw [hph u hut] at h; rw [upd_ne _ _ hut]; exact hI.lp u h
  · have hut := hnsig u h; rw [hph u hut] at h; rw [upd_ne _ _ hut]; exact hI.sx u h

end FCond

end Full
end Zig
