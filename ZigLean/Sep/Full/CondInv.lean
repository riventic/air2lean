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
    (C.Ep.hist m).size ≤ i + 2 ^ 32
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
  by_cases hr : (C.ph (G u)).isReg
  · by_cases hq : C.qd m u
    · simp [hr, hq]
    · have := h u hu hr (by simpa using hq); simp [hr, hq]; omega
  · simp [hr]

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
    · have := hT v (by omega); rw [this] at hv; cases hv
  · simp [hkq] at hpos

end FCond

end Full
end Zig
