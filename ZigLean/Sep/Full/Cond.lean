import ZigLean.Sep.Full.Event

/-!
# The futex-epoch condition, over full-state resources

A condition variable with a futex epoch (`Io.Condition` of 0.16.0 and 0.17.0,
`Thread.Condition.FutexImpl` of 0.15.2): a `u32` state word `S` (`waiters` in the low 16 bits,
`signals` in the high 16) and a `u32` epoch word `Ep` right after it. A waiter, holding the
mutex, loads the epoch (acquire), does `waiters += 1`, unlocks the mutex and then loops: a futex
wait at the epoch with the loaded value, an acquire load of the epoch, a relaxed load of the
state, and, while `signals > 0`, a weak acquire `cmpxchg` that takes one signal (`waiters -= 1`,
`signals -= 1`); after it took one it locks the mutex again. A signaller loads the state and,
while `waiters > signals`, does a weak release `cmpxchg` with `signals += 1`, then `epoch += 1`
(release) and wakes one waiter at the epoch. This module is the component once for every
protocol that has such a condition next to its mutex (`FLock.Fits` with the condition as a
primitive over its two words: `FCond.prim`, `FPrim.ofWords`), and the rules of the
condition's ops in generated code; an implementation of a Zig version walks its code with them
(`CondImpl`).

`FCond γ` is the two words and a thread's place in the condition's code (`CPh`: `en` a waiter
before its epoch load, `ld i e` it loaded epoch write `i` (the newest) with the value `e`,
`reg i jr sn e` it did `waiters += 1` (state write `jr`; `sn`: it loaded epoch write `i + 1`),
`inc` a signaller after its `signals += 1`, `wk` after its `epoch += 1`). `FCond.Inv` is the
condition's invariant, modelled on the legacy `Proofs/Sync/Semaphore.lean` (`Era`): the state's
writes are `(0, 0)`, `(1, 0)`, `(1, 1)` (`SV`); while a waiter is registered, the state has its
write `jr` (`1`) and at most a signal after it (`0x10001`), and the epoch its write `i` and at
most one more, after the signal (`Era`); a thread asleep at the epoch is the registered waiter,
and the epoch is still write `i` or a signaller will wake it (no lost wakeup).

**Scope (one waiter, the newest epoch).** A waiter enters only when every other thread is out of
the condition's code (`hone`: no other waiter, no signaller between its `signals += 1` and its
wake) and after every epoch write (`hhb`), so that its acquire load reads the newest epoch write
and the futex value cannot be an older write's (ABA). A signaller's stops come after the
registration of a waiter (`hseen`). Reason: as for the event (`ZigLean/Sep/Full/Event.lean`),
the memory model's facts of a read give its happens-before floor, not the read-read coherence of
`Mem.seen`, and a full-state frame does not keep `Mem.seen`. Several waiters are a follow-up.

**The client's part.** Roles: `FCond.sx` are the ghost values that may signal (`Inv.sx`). A
thread in the condition's critical code (`en`, `ld`) holds the mutex (`Inv.crit`); one between
its signal and its wake (`inc`, `wk`) is out of the lock's code (`Inv.lp`); both run no lock
code, so a client's `Fits` `ok` excludes them (`CPh.busy`, `Fits.ok_calm`) and a lock step keeps
the invariant (`Inv.lstep`). A step of the condition's code keeps the client's rest `U` given
the code's transition (`CPh.Next`; the entry `out → en` is the client's `hent` of
`CondImpl.wait_wp`) and the epoch's writes (`FCond.prim`, `Fits.wStep`).
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
  | inc
  | wk
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

/-- A signaller between its `signals += 1` and its wake. -/
def sig : CPh → Bool
  | .inc | .wk => true
  | _ => false

/-- A place where the thread runs no lock code. -/
def busy (p : CPh) : Bool := p.crit || p.sig

/-- The transitions of the condition's code, without the entry `out → en` (module doc). A waiter
registers with the epoch it loaded and keeps its registration until it leaves (only `sn`
changes). -/
def Next : CPh → CPh → Prop
  | .en, .ld _ _ => True
  | .ld i e, .reg i' _ _ e' => i' = i ∧ e' = e
  | .reg i jr _ e, .reg i' jr' _ e' => i' = i ∧ jr' = jr ∧ e' = e
  | .reg _ _ _ _, .out => True
  | .out, .inc => True
  | .inc, .wk => True
  | .wk, .out => True
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

variable {γ : Type} (C : FCond γ)

/-- The newest write of the state. -/
abbrev lastS (m : Mem) : Word.Entry := (C.S.hist m)[(C.S.hist m).size - 1]!

/-- The newest write of the epoch. -/
abbrev lastE (m : Mem) : Word.Entry := (C.Ep.hist m)[(C.Ep.hist m).size - 1]!

/-- A value of the state: `(0, 0)`, `(1, 0)` or `(1, 1)`. -/
def SV (x : Word.Entry) : Prop :=
  x.Val (0 : BitVec 32) ∨ x.Val (1 : BitVec 32) ∨ x.Val (0x10001 : BitVec 32)

/-- A signal is pending: the newest state is `(1, 1)`. -/
def Signalled (m : Mem) : Prop := (C.lastS m).Val (0x10001 : BitVec 32)

/-- The writes of the condition while thread `u` waits (`CPh.reg i jr sn e`). -/
structure Era (G : ThreadId → γ) (m : Mem) (u i jr : Nat) (sn : Bool) (e : BitVec 32) :
    Prop where
  ssz : (C.S.hist m).size = jr + 1 ∨ (C.S.hist m).size = jr + 2
  s0 : (C.S.hist m)[jr]!.Val (1 : BitVec 32)
  s1 : (C.S.hist m).size = jr + 2 → (C.S.hist m)[jr + 1]!.Val (0x10001 : BitVec 32)
  esz : (C.Ep.hist m).size = i + 1 ∨ ((C.Ep.hist m).size = i + 2 ∧ (C.S.hist m).size = jr + 2 ∧
    VClock.le (C.S.hist m)[jr + 1]!.clock (C.Ep.hist m)[i + 1]!.relClock = true)
  eval : (C.Ep.hist m)[i]!.Val e ∧
    ((C.Ep.hist m).size = i + 2 → (C.Ep.hist m)[i + 1]!.Val (e + 1))
  seen : sn = true → (C.Ep.hist m).size = i + 2 ∧
    VClock.le (C.Ep.hist m)[i + 1]!.relClock (m.clocks[u]!) = true
  cs : VClock.le (C.S.hist m)[jr]!.clock (m.clocks[u]!) = true
  ce : VClock.le (C.Ep.hist m)[i]!.clock (m.clocks[u]!) = true
  pend : (C.S.hist m).size = jr + 2 → (C.Ep.hist m).size = i + 1 → ∃ v, C.ph (G v) = .inc

/-- The condition's invariant, with the lock's places (module doc). -/
structure Inv (L : FLock γ) (G : ThreadId → γ) (m : Mem) : Prop where
  sv : ∀ k < (C.S.hist m).size, SV (C.S.hist m)[k]!
  /-- One waiter at a time (module doc, scope). -/
  one : ∀ u v, (C.ph (G u)).waits → (C.ph (G v)).waits → u = v
  /-- Without a registered waiter the state is `(0, 0)`. -/
  idle : (∀ u i jr sn e, C.ph (G u) ≠ .reg i jr sn e) → (C.lastS m).Val (0 : BitVec 32)
  era : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Era G m u i jr sn e
  /-- Every epoch write happened before the waiter at `en`. -/
  en : ∀ u, C.ph (G u) = .en → ∀ j < (C.Ep.hist m).size,
    VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[u]!) = true
  /-- The waiter at `ld i e` loaded the newest epoch write `i`. -/
  ld : ∀ u i e, C.ph (G u) = .ld i e → (C.Ep.hist m).size = i + 1 ∧
    (C.Ep.hist m)[i]!.Val e ∧ VClock.le (C.Ep.hist m)[i]!.clock (m.clocks[u]!) = true
  /-- No signaller between its signal and its wake while a waiter is in the critical code. -/
  nosig : ∀ u v, (C.ph (G u)).crit → (C.ph (G v)).sig = false
  /-- One signaller between its signal and its wake. -/
  sone : ∀ u v, (C.ph (G u)).sig → (C.ph (G v)).sig → u = v
  inc : ∀ u v i jr sn e, C.ph (G u) = .inc → C.ph (G v) = .reg i jr sn e →
    (C.S.hist m).size = jr + 2 ∧ (C.Ep.hist m).size = i + 1 ∧
    VClock.le (C.S.hist m)[jr + 1]!.clock (m.clocks[u]!) = true
  wk : ∀ u v i jr sn e, C.ph (G u) = .wk → C.ph (G v) = .reg i jr sn e →
    (C.Ep.hist m).size = i + 2
  /-- A thread in the futex queue at the epoch is the registered waiter, and the epoch is still
  its write `i` or a signaller will wake it (no lost wakeup). -/
  q : ∀ w ∈ m.waiters, w.2 = C.Ep.ptr → ∃ i jr e, C.ph (G w.1) = .reg i jr false e ∧
    ((C.Ep.hist m).size = i + 1 ∨ ∃ v, C.ph (G v) = .wk)
  /-- A waiter in the futex queue is at the epoch or at the mutex. -/
  qw : ∀ w ∈ m.waiters, (C.ph (G w.1)).waits → w.2 = C.Ep.ptr ∨ w.2 = L.ptr
  crit : ∀ u, (C.ph (G u)).crit → L.ph (G u) = .holds
  lp : ∀ u, (C.ph (G u)).sig → L.ph (G u) = .out
  sx : ∀ u, (C.ph (G u)).sig → C.sx (G u)

/-- **The condition at its start**: every thread out of its code, no thread in the futex queue,
and the state has its first write, `(0, 0)`. -/
theorem Inv.start {L : FLock γ} {G : ThreadId → γ} {m : Mem} (hS : (C.S.hist m).size = 1)
    (hS0 : (C.S.hist m)[0]!.Val (0 : BitVec 32)) (hout : ∀ u, C.ph (G u) = .out)
    (hq : m.waiters = #[]) : C.Inv L G m where
  sv k hk := by obtain rfl : k = 0 := by omega
                exact .inl hS0
  one u _ h := by rw [hout u] at h; exact absurd h (by decide)
  idle _ := by show (C.S.hist m)[(C.S.hist m).size - 1]!.Val _; rw [hS]; exact hS0
  era u _ _ _ _ h := by rw [hout u] at h; cases h
  en u h := by rw [hout u] at h; cases h
  ld u _ _ h := by rw [hout u] at h; cases h
  nosig u _ h := by rw [hout u] at h; exact absurd h (by decide)
  sone u _ h := by rw [hout u] at h; exact absurd h (by decide)
  inc u _ _ _ _ _ h := by rw [hout u] at h; cases h
  wk u _ _ _ _ _ h := by rw [hout u] at h; cases h
  q w hw := by simp [hq] at hw
  qw w hw := by simp [hq] at hw
  crit u h := by rw [hout u] at h; exact absurd h (by decide)
  lp u h := by rw [hout u] at h; exact absurd h (by decide)
  sx u h := by rw [hout u] at h; exact absurd h (by decide)

/-- A step of thread `t` in the condition's code, as the protocol's rest sees it: no change, an
op at the word `W` (the state or the epoch: a read, or an RMW of the newest write), the futex
wait's sleep at the epoch, the return of a futex wait, or a futex wake at the epoch. -/
inductive MStep (W : Word 32 4) (t : ThreadId) (m : Mem) : Mem → Prop
  | same : MStep W t m m
  | op {m' : Mem} : W.Op t { m with current := t } m' →
      W.Ok m' → (W.hist m' = W.hist m ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
        W.hist m' = (W.hist m).push (Word.rmwEnt m' t ord (W.hist m)[(W.hist m).size - 1]! v)) →
      MStep W t m m'
  | sleep {M : Mem} : C.Ep.Op t { m with current := t } M → C.Ep.hist M = C.Ep.hist m →
      C.Ep.Ok M → M.blocks = m.blocks → MStep W t m { M with waiters := M.waiters.push (t, C.Ep.ptr) }
  | woken : MStep W t m { m with current := t, woken := m.woken.erase t }
  | resume : MStep W t m { m with current := t }
  | wake {m' : Mem} (c : Nat) (cs : List Nat) :
      ((Thread.futexWake C.Ep.ptr c cs).run { m with current := t }).run = some (.ok ((), m')) →
      MStep W t m m'

/-- **The condition as a primitive next to its mutex `L`** (`FPrim.ofWords`; a protocol keeps it:
`L.Fits (C.prim L) P U ok`). Its words are the state and the epoch; the role is `sx`; the calm
places are those out of the busy code (`ok` reads no other place: a thread out of the busy code
runs lock code). A step of its code at a word `W` is an `MStep` with the stepping thread's
transition (`CPh.Next`), its lock place and resource (the same, or `out`/`away` around a futex
wait: only a waiter goes `away`), and the epoch's writes (they change only at a signaller's
`epoch += 1`). A thread steps on its own part (a stack block of the condition's code) out of the
lock's code or holding the lock. -/
abbrev prim (L : FLock γ) : FPrim γ :=
  FPrim.ofWords L C.toFPlace .out (fun p => p.busy = false) (fun (_ : Unit) g => C.sx g)
    (fun W => W = C.S ∨ W = C.Ep) (C.Inv L)
    (fun W t g p q h m m' => CPh.Next (C.ph g) p ∧
      ((q = L.ph g ∧ h = L.held g) ∨
        ((L.ph g = .out ∨ L.ph g = .away) ∧ (q = .out ∨ (q = .away ∧ p.waits = true)) ∧
          h = rnil)) ∧
      C.MStep W t m m' ∧ (C.Ep.hist m' = C.Ep.hist m ∨ C.ph g = .inc))
    (fun q => q = .out ∨ q = .holds)

variable {C}

/-! ## A step of the condition's code, as the memory sees it

As for the event (`FEvent.MStep.threads`, …), with the op at the word `W` and the futex wait and
wake at the epoch: only `W`'s bytes change, a new access is at `W` or at the epoch, a lock's word
apart from both keeps its location, a new waiter is the stepping thread at the epoch, and a word
at or apart from each of them stays valid, with a new write only at `W`. -/

namespace MStep

variable {W : Word 32 4} {t : ThreadId} {m m' : Mem}

theorem threads (hs : C.MStep W t m m') : m'.threads = m.threads := by
  cases hs with
  | op hop => exact hop.threads
  | sleep hop => exact hop.threads
  | wake c cs h => rw [Proto.modify_ok h]
  | _ => rfl

theorem clocks (hs : C.MStep W t m m') (u : Nat) :
    VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := by
  cases hs with
  | op hop => exact hop.clocks u
  | sleep hop => exact hop.clocks u
  | wake c cs h => rw [Proto.modify_ok h]; exact VClock.le_refl _
  | _ => exact VClock.le_refl _

theorem cells (hs : C.MStep W t m m') {l : Zig.Loc} (hl : ¬ W.In l) : m'.heap l = m.heap l := by
  cases hs with
  | op hop => exact hop.cells l hl
  | @sleep M _ _ _ hbl => show M.heap l = m.heap l; unfold Mem.heap; rw [hbl]
  | wake c cs h => rw [Proto.modify_ok h]; rfl
  | _ => rfl

theorem fp (hs : C.MStep W t m m') {e : FootprintEntry} (he : e ∈ m'.footprint) :
    e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) ∨ (e.block = C.Ep.b ∧ e.off = C.Ep.o) := by
  cases hs with
  | op hop => exact (hop.of_cur.fpAt e he).imp_right .inl
  | sleep hop => exact (hop.of_cur.fpAt e he).imp_right .inr
  | wake c cs h => rw [Proto.modify_ok h] at he; exact .inl he
  | _ => exact .inl he

theorem block (hs : C.MStep W t m m') {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk) :
    ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  cases hs with
  | op hop => exact hop.of_cur.block hb
  | @sleep M _ _ _ hbl => exact ⟨blk, by show M.blocks[b]? = _; rw [hbl]; exact hb, rfl, rfl, rfl⟩
  | wake c cs h => rw [Proto.modify_ok h]; exact ⟨blk, hb, rfl, rfl, rfl⟩
  | _ => exact ⟨blk, hb, rfl, rfl, rfl⟩

theorem lockLoc (hs : C.MStep W t m m') {L : LockWord} (hW : W.ApartL L) (hE : C.Ep.ApartL L)
    {i : Nat} {l : ALoc} (hl : L.Loc m i l) : L.Loc m' i l := by
  cases hs with
  | op hop => exact hop.of_cur.lockLoc hW hl
  | sleep hop => exact hop.of_cur.lockLoc hE hl
  | wake c cs h => rw [Proto.modify_ok h]; exact hl
  | _ => exact hl

theorem waiters (hs : C.MStep W t m m') {w : ThreadId × Ptr} (hw : w ∈ m'.waiters) :
    w ∈ m.waiters ∨ w = (t, C.Ep.ptr) := by
  cases hs with
  | op hop => exact .inl (hop.of_cur.waiters ▸ hw)
  | sleep hop =>
    rcases Array.mem_push.mp hw with h | h
    · exact .inl (hop.of_cur.waiters ▸ h)
    · exact .inr h
  | wake c cs h => rw [Proto.modify_ok h] at hw; exact .inl (Array.mem_filter.mp hw).1
  | _ => exact .inl hw

theorem word {W' : Word 32 4} (hs : C.MStep W t m m') (hok : W'.Ok m)
    (hW : W' = W ∨ W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o)
    (hE : W' = C.Ep ∨ C.Ep.b ≠ W'.b ∨ C.Ep.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ C.Ep.o) :
    W'.Ok m' ∧ (W'.hist m' = W'.hist m ∨ (W' = W ∧ ∃ x, W'.hist m' = (W'.hist m).push x)) := by
  have hk : ∀ {m₁ : Mem}, m₁.blocks = m.blocks → m₁.atomics = m.atomics →
      m₁.footprint = m.footprint → m₁.threads = m.threads → m₁.clocks = m.clocks →
      W'.Ok m₁ ∧ (W'.hist m₁ = W'.hist m ∨ (W' = W ∧ ∃ x, W'.hist m₁ = (W'.hist m).push x)) :=
    fun hb ha hf ht hc => by
      have := Word.keep_of (W := W') hb ha hf ht fun u => by rw [hc]; exact VClock.le_refl _
      exact ⟨hok.keep this, .inl (Word.hist_keep hok this)⟩
  cases hs with
  | same => exact hk rfl rfl rfl rfl rfl
  | op hop hw hh =>
    rcases hW with rfl | hap
    · exact ⟨hw, hh.imp id fun ⟨_, _, h⟩ => ⟨rfl, _, h⟩⟩
    · exact (hop.of_cur.word hok hap).imp_right .inl
  | @sleep M hop hh hw _ =>
    have hM : W'.Ok M ∧ W'.hist M = W'.hist m := by
      rcases hE with rfl | hap
      · exact ⟨hw, hh⟩
      · exact hop.of_cur.word hok hap
    exact ⟨hM.1.keep (Word.keep_waiters _ _),
      .inl ((Word.hist_keep hM.1 (Word.keep_waiters _ _)).trans hM.2)⟩
  | woken => exact hk rfl rfl rfl rfl rfl
  | resume => exact hk rfl rfl rfl rfl rfl
  | wake c cs h => rw [Proto.modify_ok h]; exact hk rfl rfl rfl rfl rfl

end MStep

/-! ## Facts of the writes -/

theorem add_one_ne (e : BitVec 32) : e + 1 ≠ e := by bv_omega

theorem SV.cases {x : Word.Entry} (h : SV x) {b : BitVec 32} (hb : x.Val b) :
    b = 0 ∨ b = 1 ∨ b = 0x10001 := by
  rcases h with h | h | h
  · exact .inl (FEvent.val_eq hb h)
  · exact .inr (.inl (FEvent.val_eq hb h))
  · exact .inr (.inr (FEvent.val_eq hb h))

/-- The newest write of a word with a write pushed. -/
theorem last_push {h : Array Word.Entry} {x : Word.Entry} : (h.push x)[(h.push x).size - 1]! = x := by
  simp only [Array.size_push, Nat.add_sub_cancel]; exact FEvent.get_push_eq

theorem ne_of_val {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hne : a ≠ b) : ¬ x.Val b :=
  fun hb => hne (FEvent.val_eq ha hb)

variable {L : FLock γ}

/-- A registered waiter: the newest state write is its `(1, 0)` or the signal `(1, 1)`. -/
theorem Era.last {G : ThreadId → γ} {m : Mem} {u i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : C.Era G m u i jr sn e) :
    ((C.S.hist m).size = jr + 1 ∧ (C.lastS m).Val (1 : BitVec 32)) ∨
    ((C.S.hist m).size = jr + 2 ∧ (C.lastS m).Val (0x10001 : BitVec 32)) := by
  rcases h.ssz with hs | hs
  · refine .inl ⟨hs, ?_⟩; unfold FCond.lastS; rw [hs, Nat.add_sub_cancel]; exact h.s0
  · refine .inr ⟨hs, ?_⟩; unfold FCond.lastS; rw [hs, show jr + 2 - 1 = jr + 1 by omega]
    exact h.s1 hs

/-- `Era` after a step that keeps the writes and moves the clocks forward. -/
theorem Era.mono {G G' : ThreadId → γ} {m m' : Mem} {u i jr : Nat} {sn : Bool} {e : BitVec 32}
    (h : C.Era G m u i jr sn e) (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hc : VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hinc : ∀ v, C.ph (G v) = .inc → ∃ w, C.ph (G' w) = .inc) : C.Era G' m' u i jr sn e where
  ssz := by rw [hS]; exact h.ssz
  s0 := by rw [hS]; exact h.s0
  s1 := by rw [hS]; exact h.s1
  esz := by rw [hS, hE]; exact h.esz
  eval := by rw [hE]; exact h.eval
  seen := fun hsn => by
    rw [hE]; obtain ⟨h1, h2⟩ := h.seen hsn; exact ⟨h1, VClock.le_trans h2 hc⟩
  cs := by rw [hS]; exact VClock.le_trans h.cs hc
  ce := by rw [hE]; exact VClock.le_trans h.ce hc
  pend := fun h1 h2 => by
    rw [hS] at h1; rw [hE] at h2
    obtain ⟨v, hv⟩ := h.pend h1 h2; exact hinc v hv

/-! ## The invariant after a step -/

/-- A step that keeps the writes of both words and the futex queue (a read, a return from a
futex wait, a change of `t`'s lock place): the other threads keep their ghost values, and `t`
changes its place as the premises say. -/
theorem Inv.move {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : C.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u)
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hap : C.Ep.ptr ≠ L.ptr) (hwt : ∀ w, w.2 ≠ L.ptr → w ∈ m'.waiters → w ∈ m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwaits : (C.ph (G' t)).waits → (C.ph (G t)).waits)
    (hcr : (C.ph (G' t)).crit → (C.ph (G t)).crit ∧ L.ph (G' t) = .holds)
    (hsig : (C.ph (G' t)).sig ∨ (C.ph (G t)).sig →
      C.ph (G' t) = C.ph (G t) ∧ L.ph (G' t) = L.ph (G t) ∧ (C.sx (G t) → C.sx (G' t)))
    (hen : C.ph (G' t) = .en → ∀ j < (C.Ep.hist m).size,
      VClock.le (C.Ep.hist m)[j]!.clock (m'.clocks[t]!) = true)
    (hld : ∀ i e, C.ph (G' t) = .ld i e → (C.Ep.hist m).size = i + 1 ∧
      (C.Ep.hist m)[i]!.Val e ∧ VClock.le (C.Ep.hist m)[i]!.clock (m'.clocks[t]!) = true)
    (hreg : ∀ i jr sn e, C.ph (G' t) = .reg i jr sn e → ∃ sn', C.ph (G t) = .reg i jr sn' e ∧
      (sn = true → sn' = true ∨ ((C.Ep.hist m).size = i + 2 ∧
        VClock.le (C.Ep.hist m)[i + 1]!.relClock (m'.clocks[t]!) = true)))
    (hreg' : ∀ i jr sn e, C.ph (G t) = .reg i jr sn e → ∃ sn', C.ph (G' t) = .reg i jr sn' e)
    (htq : ∀ w ∈ m.waiters, w.1 = t → ((C.ph (G' t)).waits → w.2 = C.Ep.ptr ∨ w.2 = L.ptr) ∧
      (w.2 = C.Ep.ptr → C.ph (G' t) = C.ph (G t))) :
    C.Inv L G' m' := by
  -- the other threads
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  have hsig' : ∀ u, (C.ph (G u)).sig → C.ph (G' u) = C.ph (G u) := fun u hu => by
    by_cases e : u = t
    · subst e; exact (hsig (.inr hu)).1
    · exact hph u e
  have hinc : ∀ v, C.ph (G v) = .inc → ∃ w, C.ph (G' w) = .inc := fun v hv =>
    ⟨v, by rw [hsig' v (by rw [hv]; rfl), hv]⟩
  have hwk : ∀ v, C.ph (G v) = .wk → C.ph (G' v) = .wk := fun v hv => by
    rw [hsig' v (by rw [hv]; rfl), hv]
  have hregu : ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → ∃ sn', C.ph (G u) = .reg i jr sn' e :=
    fun u i jr sn e hu => by
      by_cases e' : u = t
      · subst e'; obtain ⟨sn', h, -⟩ := hreg i jr sn e hu; exact ⟨sn', h⟩
      · exact ⟨sn, by rw [← hph u e']; exact hu⟩
  have hsigu : ∀ u, (C.ph (G' u)).sig → (C.ph (G u)).sig := fun u hu => by
    by_cases e : u = t
    · subst e; rw [← (hsig (.inl hu)).1]; exact hu
    · rwa [hph u e] at hu
  refine ⟨by rw [hS]; exact hI.sv, fun u v hu hv => ?_, fun hn => ?_, fun u i jr sn e hu => ?_,
    fun u hu j hj => ?_, fun u i e hu => ?_, fun u v hu => ?_, fun u v hu hv => ?_,
    fun u v i jr sn e hu hv => ?_, fun u v i jr sn e hu hv => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · -- one
    have key : ∀ x, (C.ph (G' x)).waits → (C.ph (G x)).waits := fun x hx => by
      by_cases e : x = t
      · subst e; exact hwaits hx
      · rwa [hph x e] at hx
    exact hI.one u v (key u hu) (key v hv)
  · -- idle
    unfold FCond.lastS; rw [hS]; refine hI.idle fun u i jr sn e hu => ?_
    by_cases e' : u = t
    · subst e'; obtain ⟨sn', h⟩ := hreg' i jr sn e hu; exact hn u i jr sn' e h
    · exact hn u i jr sn e (by rw [hph u e']; exact hu)
  · -- era
    by_cases e' : u = t
    · subst e'
      obtain ⟨sn', h, hsn⟩ := hreg i jr sn e hu
      have hera := (hI.era u i jr sn' e h).mono hS hE (hclk u) hinc
      refine { hera with seen := fun hs => ?_ }
      rcases hsn hs with rfl | ⟨h1, h2⟩
      · exact hera.seen rfl
      · rw [hE]; exact ⟨h1, h2⟩
    · exact (hI.era u i jr sn e (by rw [← hph u e']; exact hu)).mono hS hE (hclk u) hinc
  · -- en
    rw [hE] at hj ⊢
    by_cases e' : u = t
    · subst e'; exact hen hu j hj
    · rw [hph u e'] at hu; exact VClock.le_trans (hI.en u hu j hj) (hclk u)
  · -- ld
    rw [hE]
    by_cases e' : u = t
    · subst e'; exact hld i e hu
    · rw [hph u e'] at hu
      obtain ⟨h1, h2, h3⟩ := hI.ld u i e hu
      exact ⟨h1, h2, VClock.le_trans h3 (hclk u)⟩
  · -- nosig
    cases hs : (C.ph (G' v)).sig
    · rfl
    · have hcu : (C.ph (G u)).crit := by
        by_cases e : u = t
        · subst e; exact (hcr hu).1
        · rwa [hph u e] at hu
      have := hI.nosig u v hcu
      rw [hsigu v hs] at this; cases this
  · -- sone
    exact hI.sone u v (hsigu u hu) (hsigu v hv)
  · -- inc
    have hu' : C.ph (G u) = .inc := by rw [← hsig' u (hsigu u (by rw [hu]; rfl))]; exact hu
    obtain ⟨sn', hv'⟩ := hregu v i jr sn e hv
    obtain ⟨h1, h2, h3⟩ := hI.inc u v i jr sn' e hu' hv'
    rw [hS, hE]; exact ⟨h1, h2, VClock.le_trans h3 (hclk u)⟩
  · -- wk
    have hu' : C.ph (G u) = .wk := by rw [← hsig' u (hsigu u (by rw [hu]; rfl))]; exact hu
    obtain ⟨sn', hv'⟩ := hregu v i jr sn e hv
    rw [hE]; exact hI.wk u v i jr sn' e hu' hv'
  · -- q
    have hw := hwt w (by rw [hp]; exact hap) hw
    obtain ⟨i, jr, e, h1, h2⟩ := hI.q w hw hp
    refine ⟨i, jr, e, ?_, ?_⟩
    · by_cases e' : w.1 = t
      · rw [e', (htq w hw e').2 hp, ← e']; exact h1
      · rw [hph _ e']; exact h1
    · rw [hE]
      rcases h2 with h2 | ⟨v, hv⟩
      · exact .inl h2
      · exact .inr ⟨v, hwk v hv⟩
  · -- qw
    by_cases hl : w.2 = L.ptr
    · exact .inr hl
    have hw := hwt w hl hw
    by_cases e' : w.1 = t
    · exact (htq w hw e').1 (by rw [← e']; exact hp)
    · rw [hph _ e'] at hp; exact hI.qw w hw hp
  · -- crit
    by_cases e' : u = t
    · subst e'; exact (hcr hu).2
    · rw [hph u e'] at hu; rw [hG u e']; exact hI.crit u hu
  · -- lp
    by_cases e' : u = t
    · subst e'
      obtain ⟨h1, h2, -⟩ := hsig (.inl hu)
      rw [h2]; exact hI.lp u (by rw [← h1]; exact hu)
    · rw [hph u e'] at hu; rw [hG u e']; exact hI.lp u hu
  · -- sx
    by_cases e' : u = t
    · subst e'
      obtain ⟨h1, -, h3⟩ := hsig (.inl hu)
      exact h3 (hI.sx u (by rw [← h1]; exact hu))
    · rw [hph u e'] at hu; rw [hG u e']; exact hI.sx u hu

/-- A thread enters the wait (`out` → `en`) holding the mutex, when every other thread is out of
the condition's code and every epoch write happened before it (module doc, scope). -/
theorem Inv.enter {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ}
    (hI : C.Inv L (upd G t g) m) (hg : C.ph g = .out) (hgh : L.ph (C.set g .en) = .holds)
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true) :
    C.Inv L (upd G t (C.set g .en)) m := by
  have hen : C.ph (upd G t (C.set g .en) t) = .en := by rw [upd_self, C.ph_set]
  have hout : ∀ u, u ≠ t → C.ph (upd G t (C.set g .en) u) = .out := fun u e => by
    rw [upd_ne _ _ e, hone u e]
  have hph0 : ∀ u, C.ph (upd G t g u) = .out := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hg]
    · rw [upd_ne _ _ e, hone u e]
  -- every thread is at `en` (`t`) or out
  have hcase : ∀ u, (u = t ∧ C.ph (upd G t (C.set g .en) u) = .en) ∨
      (u ≠ t ∧ C.ph (upd G t (C.set g .en) u) = .out) := fun u => by
    by_cases e : u = t
    · subst e; exact .inl ⟨rfl, hen⟩
    · exact .inr ⟨e, hout u e⟩
  refine ⟨hI.sv, fun u v hu hv => ?_, fun _ => ?_, fun u i jr sn e hu => ?_, fun u hu j hj => ?_,
    fun u i e hu => ?_, fun u v _ => ?_, fun u v hu _ => ?_, fun u v i jr sn e hu _ => ?_,
    fun u v i jr sn e hu _ => ?_, fun w hw hp => ?_, fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => ?_, fun u hu => ?_⟩
  · rcases hcase u with ⟨rfl, -⟩ | ⟨-, h⟩
    · rcases hcase v with ⟨rfl, -⟩ | ⟨-, h⟩
      · rfl
      · rw [h] at hv; cases hv
    · rw [h] at hu; cases hu
  · exact hI.idle fun u i jr sn e hu => by rw [hph0] at hu; cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact hhb j hj
    · rw [h] at hu; cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase v with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · obtain ⟨i, jr, e, h1, -⟩ := hI.q w hw hp
    rw [hph0] at h1; cases h1
  · rcases hcase w.1 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (hnq w hw)
    · rw [h] at hp; cases hp
  · rcases hcase u with ⟨rfl, -⟩ | ⟨-, h⟩
    · rw [upd_self]; exact hgh
    · rw [h] at hu; cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu
  · rcases hcase u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hu <;> cases hu

/-- The waiter's `waiters += 1` (`ld i e` → `reg i jr false e`, state write `jr`). -/
theorem Inv.reg {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    {i : Nat} {e : BitVec 32} (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .ld i e) (ht1 : C.ph (G' t) = .reg i (C.S.hist m).size false e)
    (hS : C.S.hist m' = (C.S.hist m).push (Word.rmwEnt m' t ord (C.lastS m) (1 : BitVec 32)))
    (hE : C.Ep.hist m' = C.Ep.hist m) (hwt : m'.waiters = m.waiters)
    (hnq : ∀ w ∈ m.waiters, w.1 ≠ t)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L G' m' := by
  have hsz : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hS]; simp
  have hold : ∀ k, k < (C.S.hist m).size → (C.S.hist m')[k]! = (C.S.hist m)[k]! := fun k hk => by
    rw [hS]; exact FEvent.get_push_lt hk
  have hnew : (C.S.hist m')[(C.S.hist m).size]! = Word.rmwEnt m' t ord (C.lastS m) (1 : BitVec 32) := by
    rw [hS]; exact FEvent.get_push_eq
  have htw : (C.ph (G t)).waits := by rw [ht0]; rfl
  -- every other thread is out of the waiter's places
  have hnw : ∀ u, u ≠ t → (C.ph (G u)).waits = false := fun u hu => by
    cases h : (C.ph (G u)).waits
    · rfl
    · exact absurd (hI.one u t h htw) hu
  have hns : ∀ u, (C.ph (G u)).sig = false := fun u => hI.nosig t u (by rw [ht0]; rfl)
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  -- a place of another thread that is a waiter's or a signaller's is impossible
  have hno : ∀ u, u ≠ t → ∀ p, C.ph (G' u) = p → (p.waits || p.sig) = true → False := by
    intro u hu p hp hw
    rw [hph u hu] at hp
    have h1 := hnw u hu; have h2 := hns u
    rw [hp] at h1 h2; rw [h1, h2] at hw; cases hw
  have hsig' : ∀ u, (C.ph (G' u)).sig = false := fun u => by
    by_cases e : u = t
    · subst e; rw [ht1]; rfl
    · cases h : (C.ph (G' u)).sig
      · rfl
      · exact (hno u e _ rfl (by rw [h, Bool.or_true])).elim
  have hwt' : ∀ u, (C.ph (G' u)).waits → u = t := fun u h => by
    by_cases e : u = t
    · exact e
    · exact (hno u e _ rfl (by rw [h, Bool.true_or])).elim
  have hninc : ∀ u p, C.ph (G' u) = p → p.sig = true → False := fun u p hp h => by
    have := hsig' u; rw [hp, h] at this; cases this
  refine ⟨fun k hk => ?_, fun u v hu hv => (hwt' u hu).trans (hwt' v hv).symm,
    fun hn => absurd ht1 (hn t _ _ _ _), fun u i' jr sn e' hu => ?_,
    fun u hu => absurd (hwt' u (by rw [hu]; rfl)) (fun h => by subst h; rw [ht1] at hu; cases hu),
    fun u i' e' hu => absurd (hwt' u (by rw [hu]; rfl)) (fun h => by subst h; rw [ht1] at hu; cases hu),
    fun u v _ => hsig' v, fun u v hu _ => (hninc u _ rfl hu).elim,
    fun u v i' jr sn e' hu _ => (hninc u _ hu rfl).elim,
    fun u v i' jr sn e' hu _ => (hninc u _ hu rfl).elim,
    fun w hw hp => ?_, fun w hw hp => ?_, fun u hu => ?_,
    fun u hu => (hninc u _ rfl hu).elim, fun u hu => (hninc u _ rfl hu).elim⟩
  · rw [hsz] at hk
    rcases (by omega : k < (C.S.hist m).size ∨ k = (C.S.hist m).size) with hk' | rfl
    · rw [hold k hk']; exact hI.sv k hk'
    · rw [hnew]; exact .inr (.inl FEvent.rmwEnt_val)
  · -- the new registration
    have e1 := hwt' u (by rw [hu]; rfl); subst e1
    rw [ht1] at hu; cases hu
    obtain ⟨hi1, hie, hic⟩ := hI.ld u i e ht0
    exact {
      ssz := .inl hsz
      s0 := by rw [hnew]; exact FEvent.rmwEnt_val
      s1 := fun h => by omega
      esz := .inl (by rw [hE]; exact hi1)
      eval := ⟨by rw [hE]; exact hie, fun h => by rw [hE] at h; omega⟩
      seen := fun h => by cases h
      cs := by rw [hnew]; exact VClock.le_refl _
      ce := by rw [hE]; exact VClock.le_trans hic (hclk u)
      pend := fun h => by omega }
  · rw [hwt] at hw
    obtain ⟨i', jr, e', h1, -⟩ := hI.q w hw hp
    have := hI.one w.1 t (by rw [h1]; rfl) htw
    exact absurd this (hnq w hw)
  · rw [hwt] at hw
    exact absurd (hwt' w.1 hp) (hnq w hw)
  · have e1 := hwt' u (by
      cases h : (C.ph (G' u)) <;> rw [h] at hu <;> first | rfl | cases hu)
    subst e1; rw [ht1] at hu; cases hu

/-- The waiter takes the signal (`reg` → `out`): its `cmpxchg((1, 1) → (0, 0))` succeeded. -/
theorem Inv.consume {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    {i jr : Nat} {sn : Bool} {e : BitVec 32} (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .reg i jr sn e) (ht1 : C.ph (G' t) = .out)
    (hS : C.S.hist m' = (C.S.hist m).push (Word.rmwEnt m' t ord (C.lastS m) (0 : BitVec 32)))
    (hwt : m'.waiters = m.waiters) (hnq : ∀ w ∈ m.waiters, w.1 ≠ t) :
    C.Inv L G' m' := by
  have hsz : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hS]; simp
  have hold : ∀ k, k < (C.S.hist m).size → (C.S.hist m')[k]! = (C.S.hist m)[k]! := fun k hk => by
    rw [hS]; exact FEvent.get_push_lt hk
  have htw : (C.ph (G t)).waits := by rw [ht0]; rfl
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  -- no thread is a waiter after it
  have hnw : ∀ u, (C.ph (G' u)).waits = false := fun u => by
    by_cases e' : u = t
    · subst e'; rw [ht1]; rfl
    · cases h : (C.ph (G' u)).waits
      · rfl
      · rw [hph u e'] at h; exact absurd (hI.one u t h htw) e'
  have hnw' : ∀ u p, C.ph (G' u) = p → p.waits = true → False := fun u p hp h => by
    have := hnw u; rw [hp, h] at this; cases this
  have hsg : ∀ u, (C.ph (G' u)).sig → (C.ph (G u)).sig := fun u hu => by
    by_cases e' : u = t
    · subst e'; rw [ht1] at hu; cases hu
    · rwa [hph u e'] at hu
  refine ⟨fun k hk => ?_, fun u v hu _ => (hnw' u _ rfl hu).elim, fun _ => ?_,
    fun u i' jr' sn' e' hu => (hnw' u _ hu rfl).elim,
    fun u hu => (hnw' u _ hu rfl).elim, fun u i' e' hu => (hnw' u _ hu rfl).elim,
    fun u v hu => (hnw' u _ rfl (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])).elim,
    fun u v hu hv => hI.sone u v (hsg u hu) (hsg v hv),
    fun u v i' jr' sn' e' _ hv => (hnw' v _ hv rfl).elim,
    fun u v i' jr' sn' e' _ hv => (hnw' v _ hv rfl).elim, fun w hw hp => ?_,
    fun w hw hp => (hnw' w.1 _ rfl hp).elim, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hsz] at hk
    rcases (by omega : k < (C.S.hist m).size ∨ k = (C.S.hist m).size) with hk' | rfl
    · rw [hold k hk']; exact hI.sv k hk'
    · rw [hS, FEvent.get_push_eq]; exact .inl FEvent.rmwEnt_val
  · unfold FCond.lastS; rw [hS, last_push]; exact FEvent.rmwEnt_val
  · rw [hwt] at hw
    obtain ⟨i', jr', e', h1, -⟩ := hI.q w hw hp
    exact absurd (hI.one w.1 t (by rw [h1]; rfl) htw) (hnq w hw)
  · exact (hnw' u _ rfl (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])).elim
  · have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    rw [hph u e'] at hu; rw [hG u e']; exact hI.lp u hu
  · have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    rw [hph u e'] at hu; rw [hG u e']; exact hI.sx u hu

/-- A registered waiter, from the newest state write `(1, 0)`. -/
theorem Inv.reg_of {G : ThreadId → γ} {m : Mem} (hI : C.Inv L G m)
    (h1 : (C.lastS m).Val (1 : BitVec 32)) : ∃ u i jr sn e, C.ph (G u) = .reg i jr sn e := by
  refine Classical.byContradiction fun hn => ?_
  exact absurd (FEvent.val_eq (hI.idle fun u i jr sn e hu => hn ⟨u, i, jr, sn, e, hu⟩) h1)
    (by decide)

/-- A signaller's `signals += 1` (`out` → `inc`): its `cmpxchg((1, 0) → (1, 1))` succeeded. -/
theorem Inv.signal {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .out) (ht1 : C.ph (G' t) = .inc) (hlpt : L.ph (G' t) = .out)
    (hsxt : C.sx (G' t)) (hold1 : (C.lastS m).Val (1 : BitVec 32))
    (hS : C.S.hist m' = (C.S.hist m).push (Word.rmwEnt m' t ord (C.lastS m) (0x10001 : BitVec 32)))
    (hE : C.Ep.hist m' = C.Ep.hist m) (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L G' m' := by
  have hsz : (C.S.hist m').size = (C.S.hist m).size + 1 := by rw [hS]; simp
  have hold : ∀ k, k < (C.S.hist m).size → (C.S.hist m')[k]! = (C.S.hist m)[k]! := fun k hk => by
    rw [hS]; exact FEvent.get_push_lt hk
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  -- the registered waiter: its write is the newest, the epoch is still its write `i`
  have hera : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
      (C.S.hist m).size = jr + 1 ∧ (C.Ep.hist m).size = i + 1 ∧ sn = false := by
    intro u i jr sn e hu
    have h := hI.era u i jr sn e hu
    have hs : (C.S.hist m).size = jr + 1 := by
      rcases h.last with ⟨hs, -⟩ | ⟨-, h2⟩
      · exact hs
      · exact absurd (FEvent.val_eq hold1 h2) (by decide)
    have he : (C.Ep.hist m).size = i + 1 := by
      rcases h.esz with he | ⟨-, hs', -⟩
      · exact he
      · omega
    refine ⟨hs, he, ?_⟩
    cases hsn : sn
    · rfl
    · have := (h.seen hsn).1; omega
  obtain ⟨r, ri, rjr, rsn, re, hr⟩ := hI.reg_of hold1
  -- no signaller between its signal and its wake
  have hns : ∀ u, (C.ph (G u)).sig = false := fun u => by
    cases h : C.ph (G u) with
    | inc => have := (hI.inc u r ri rjr rsn re h hr).1; have := (hera r ri rjr rsn re hr).1; omega
    | wk => have := hI.wk u r ri rjr rsn re h hr; have := (hera r ri rjr rsn re hr).2.1; omega
    | _ => rfl
  have hrt : r ≠ t := fun h => by subst h; rw [ht0] at hr; cases hr
  have hsig : ∀ u, (C.ph (G' u)).sig → u = t := fun u hu => by
    by_cases e' : u = t
    · exact e'
    · rw [hph u e', hns u] at hu; cases hu
  have hwts : ∀ u, (C.ph (G' u)).waits → u ≠ t ∧ (C.ph (G u)).waits := fun u hu => by
    have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    exact ⟨e', by rwa [hph u e'] at hu⟩
  -- a waiter is the registered one
  have hwr : ∀ u, (C.ph (G u)).waits → ∃ i jr sn e, C.ph (G u) = .reg i jr sn e := fun u hu => by
    have := hI.one u r hu (by rw [hr]; rfl); subst this; exact ⟨_, _, _, _, hr⟩
  refine ⟨fun k hk => ?_, fun u v hu hv => hI.one u v (hwts u hu).2 (hwts v hv).2,
    fun hn => absurd (hph r hrt ▸ hr) (hn r ri rjr rsn re), fun u i jr sn e hu => ?_,
    fun u hu => ?_, fun u i e hu => ?_, fun u v hu => ?_, fun u v hu hv => (hsig u hu).trans (hsig v hv).symm,
    fun u v i jr sn e hu hv => ?_, fun u v i jr sn e hu hv => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hsz] at hk
    rcases (by omega : k < (C.S.hist m).size ∨ k = (C.S.hist m).size) with hk' | rfl
    · rw [hold k hk']; exact hI.sv k hk'
    · rw [hS, FEvent.get_push_eq]; exact .inr (.inr FEvent.rmwEnt_val)
  · -- the waiter's era: the signal is the state's next write
    have e' : u ≠ t := fun h => by subst h; rw [ht1] at hu; cases hu
    rw [hph u e'] at hu
    have h := hI.era u i jr sn e hu
    obtain ⟨hs, he, rfl⟩ := hera u i jr sn e hu
    exact {
      ssz := .inr (by omega)
      s0 := by rw [hold jr (by omega)]; exact h.s0
      s1 := fun _ => by rw [hS, show jr + 1 = (C.S.hist m).size by omega, FEvent.get_push_eq]
                        exact FEvent.rmwEnt_val
      esz := .inl (by rw [hE]; exact he)
      eval := ⟨by rw [hE]; exact h.eval.1, fun h' => by rw [hE] at h'; omega⟩
      seen := fun h' => by cases h'
      cs := by rw [hold jr (by omega)]; exact VClock.le_trans h.cs (hclk u)
      ce := by rw [hE]; exact VClock.le_trans h.ce (hclk u)
      pend := fun _ _ => ⟨t, ht1⟩ }
  · obtain ⟨e', hw⟩ := hwts u (by rw [hu]; rfl)
    obtain ⟨i, jr, sn, e, h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · obtain ⟨e', hw⟩ := hwts u (by rw [hu]; rfl)
    obtain ⟨i', jr, sn, e'', h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · obtain ⟨e', hw⟩ := hwts u (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])
    obtain ⟨i, jr, sn, e, h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · -- `t` is the signaller at `inc`
    have := hsig u (by rw [hu]; rfl); subst this
    have e' : v ≠ u := fun h => by subst h; rw [ht1] at hv; cases hv
    rw [hph v e'] at hv
    obtain ⟨hs, he, -⟩ := hera v i jr sn e hv
    refine ⟨by omega, by rw [hE]; exact he, ?_⟩
    rw [hS, show jr + 1 = (C.S.hist m).size by omega, FEvent.get_push_eq]; exact VClock.le_refl _
  · have := hsig u (by rw [hu]; rfl); subst this; rw [ht1] at hu; cases hu
  · rw [hwt] at hw
    obtain ⟨i, jr, e, h1, h2⟩ := hI.q w hw hp
    have e' : w.1 ≠ t := fun h => by rw [h, ht0] at h1; cases h1
    refine ⟨i, jr, e, by rw [hph _ e']; exact h1, ?_⟩
    rw [hE]
    rcases h2 with h2 | ⟨v, hv⟩
    · exact .inl h2
    · have := hns v; rw [hv] at this; cases this
  · rw [hwt] at hw
    obtain ⟨e', hw'⟩ := hwts w.1 hp
    rw [← hph _ e'] at hw'
    exact hI.qw w hw (by rw [← hph _ e']; exact hw')
  · obtain ⟨e', hw⟩ := hwts u (by revert hu; cases C.ph (G' u) <;> simp [CPh.crit, CPh.waits])
    obtain ⟨i, jr, sn, e, h⟩ := hwr u hw
    rw [hph u e', h] at hu; cases hu
  · have := hsig u hu; subst this; exact hlpt
  · have := hsig u hu; subst this; exact hsxt

/-- The signaller's `epoch += 1`, a release (`inc` → `wk`). -/
theorem Inv.bump {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} {ord : AtomicOrder}
    {o : BitVec 32} (hI : C.Inv L G m) (hG : ∀ u, u ≠ t → G' u = G u)
    (ht0 : C.ph (G t) = .inc) (ht1 : C.ph (G' t) = .wk) (hlpt : L.ph (G' t) = L.ph (G t))
    (hsxt : C.sx (G t) → C.sx (G' t)) (hrel : ord.isRel = true)
    (hold : (C.lastE m).Val o)
    (hE : C.Ep.hist m' = (C.Ep.hist m).push (Word.rmwEnt m' t ord (C.lastE m) (o + 1)))
    (hS : C.S.hist m' = C.S.hist m) (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L G' m' := by
  have hsz : (C.Ep.hist m').size = (C.Ep.hist m).size + 1 := by rw [hE]; simp
  have hold' : ∀ k, k < (C.Ep.hist m).size → (C.Ep.hist m')[k]! = (C.Ep.hist m)[k]! :=
    fun k hk => by rw [hE]; exact FEvent.get_push_lt hk
  have hnew : (C.Ep.hist m')[(C.Ep.hist m).size]! = Word.rmwEnt m' t ord (C.lastE m) (o + 1) := by
    rw [hE]; exact FEvent.get_push_eq
  have hph : ∀ u, u ≠ t → C.ph (G' u) = C.ph (G u) := fun u hu => by rw [hG u hu]
  have hts : (C.ph (G t)).sig := by rw [ht0]; rfl
  -- no waiter in the critical code, no other signaller
  have hnc : ∀ u, (C.ph (G u)).crit = false := fun u => by
    cases h : (C.ph (G u)).crit
    · rfl
    · have := hI.nosig u t h; rw [hts] at this; cases this
  have hos : ∀ u, (C.ph (G u)).sig → u = t := fun u hu => hI.sone u t hu hts
  have hnc' : ∀ u p, C.ph (G' u) = p → p.crit = true → False := fun u p hp h => by
    by_cases e' : u = t
    · subst e'; rw [ht1] at hp; subst hp; cases h
    · rw [hph u e'] at hp; have := hnc u; rw [hp, h] at this; cases this
  have hsg : ∀ u, (C.ph (G' u)).sig → u = t := fun u hu => by
    by_cases e' : u = t
    · exact e'
    · rw [hph u e'] at hu; exact hos u hu
  have hwts : ∀ u, (C.ph (G' u)).waits → u ≠ t := fun u hu h => by
    subst h; rw [ht1] at hu; cases hu
  -- the registered waiter
  have hreg : ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → u ≠ t ∧ C.ph (G u) = .reg i jr sn e :=
    fun u i jr sn e hu => by
      have e' := hwts u (by rw [hu]; rfl); exact ⟨e', by rw [← hph u e']; exact hu⟩
  have hidle : (∀ u i jr sn e, C.ph (G' u) ≠ .reg i jr sn e) →
      ∀ u i jr sn e, C.ph (G u) ≠ .reg i jr sn e := fun hn u i jr sn e hu => by
    have e' : u ≠ t := fun h => by subst h; rw [ht0] at hu; cases hu
    exact hn u i jr sn e (by rw [hph u e']; exact hu)
  refine ⟨by rw [hS]; exact hI.sv, fun u v hu hv => ?_, fun hn => ?_, fun u i jr sn e hu => ?_,
    fun u hu => (hnc' u _ hu rfl).elim, fun u i e hu => (hnc' u _ hu rfl).elim,
    fun u v hu => (hnc' u _ rfl hu).elim,
    fun u v hu hv => (hsg u hu).trans (hsg v hv).symm,
    fun u v i jr sn e hu hv => ?_, fun u v i jr sn e hu hv => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun u hu => (hnc' u _ rfl hu).elim, fun u hu => ?_, fun u hu => ?_⟩
  · exact hI.one u v (by rwa [← hph u (hwts u hu)]) (by rwa [← hph v (hwts v hv)])
  · unfold FCond.lastS; rw [hS]; exact hI.idle (hidle hn)
  · obtain ⟨e', hu'⟩ := hreg u i jr sn e hu
    have h := hI.era u i jr sn e hu'
    obtain ⟨hs2, he1, hcl⟩ := hI.inc t u i jr sn e ht0 hu'
    have hoe : o = e := by
      have := h.eval.1; unfold FCond.lastE at hold; rw [he1, Nat.add_sub_cancel] at hold
      exact FEvent.val_eq hold this
    subst hoe
    exact {
      ssz := by rw [hS]; exact h.ssz
      s0 := by rw [hS]; exact h.s0
      s1 := by rw [hS]; exact h.s1
      esz := .inr ⟨by omega, by rw [hS]; exact hs2, by
        rw [hS, show i + 1 = (C.Ep.hist m).size by omega, hnew]
        simp only [Word.rmwEnt, hrel, ↓reduceIte]
        exact VClock.le_trans (VClock.le_trans hcl (hclk t)) (VClock.le_merge_right _ _)⟩
      eval := ⟨by rw [hold' i (by omega)]; exact h.eval.1, fun _ => by
        rw [show i + 1 = (C.Ep.hist m).size by omega, hnew]; exact FEvent.rmwEnt_val⟩
      seen := fun hsn => by have := (h.seen hsn).1; omega
      cs := by rw [hS]; exact VClock.le_trans h.cs (hclk u)
      ce := by rw [hold' i (by omega)]; exact VClock.le_trans h.ce (hclk u)
      pend := fun _ h' => by omega }
  · have := hsg u (by rw [hu]; rfl); subst this; rw [ht1] at hu; cases hu
  · have := hsg u (by rw [hu]; rfl); subst this
    obtain ⟨-, hv'⟩ := hreg v i jr sn e hv
    have := (hI.inc u v i jr sn e ht0 hv').2.1; omega
  · rw [hwt] at hw
    obtain ⟨i, jr, e, h1, -⟩ := hI.q w hw hp
    have e' : w.1 ≠ t := fun h => by rw [h, ht0] at h1; cases h1
    exact ⟨i, jr, e, by rw [hph _ e']; exact h1, .inr ⟨t, ht1⟩⟩
  · rw [hwt] at hw
    have e' := hwts w.1 hp
    rw [hph _ e'] at hp; exact hI.qw w hw hp
  · have := hsg u hu; subst this; rw [hlpt]; exact hI.lp u hts
  · have := hsg u hu; subst this; exact hsxt (hI.sx u hts)

/-- The signaller's wake at the epoch (`wk` → `out`), of at least one waiter: the registered
waiter is not in the futex queue any more. -/
theorem Inv.wake {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g : γ} {c : Nat}
    {cs : List Nat} (hI : C.Inv L G m) (ht : C.ph (G t) = .wk) (hg : C.ph g = .out) (hc : 1 ≤ c)
    (h : ((Thread.futexWake C.Ep.ptr c cs).run { m with current := t }).run = some (.ok ((), m'))) :
    C.Inv L (upd G t g) m' := by
  have hm' := Proto.modify_ok h
  subst hm'
  have hts : (C.ph (G t)).sig := by rw [ht]; rfl
  have hos : ∀ u, (C.ph (G u)).sig → u = t := fun u hu => hI.sone u t hu hts
  have hph : ∀ u, u ≠ t → C.ph (upd G t g u) = C.ph (G u) := fun u hu => by rw [upd_ne _ _ hu]
  have hsg : ∀ u, (C.ph (upd G t g u)).sig = false := fun u => by
    by_cases e' : u = t
    · subst e'; rw [upd_self, hg]; rfl
    · cases h : (C.ph (upd G t g u)).sig
      · rfl
      · rw [hph u e'] at h; exact absurd (hos u h) e'
  have hsg' : ∀ u p, C.ph (upd G t g u) = p → p.sig = true → False := fun u p hp h => by
    have := hsg u; rw [hp, h] at this; cases this
  have hwts : ∀ u, (C.ph (upd G t g u)).waits → u ≠ t := fun u hu h => by
    subst h; rw [upd_self, hg] at hu; cases hu
  -- every thread at the epoch's futex was woken
  have hgone : ∀ w ∈ m.waiters, w.2 = C.Ep.ptr →
      (Thread.wakeSet m.waiters C.Ep.ptr c cs).contains w.1 = true := fun w hw hp => by
    have hne : ((m.waiters.filter (·.2 == C.Ep.ptr)).toList.map (·.1)) ≠ [] := by
      intro he
      have : w.1 ∈ ((m.waiters.filter (·.2 == C.Ep.ptr)).toList.map (·.1)) :=
        List.mem_map.mpr ⟨w, by simp [hw, hp], rfl⟩
      rw [he] at this; cases this
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _
      (Thread.wakePick_ne_nil (cs := cs) (by omega : 0 < c) hne)
    have hu' : u ∈ Thread.wakeSet m.waiters C.Ep.ptr c cs := by
      unfold Thread.wakeSet; exact List.mem_toArray.mpr hu
    obtain ⟨w', hw', hp', rfl⟩ := Thread.mem_wakeSet hu'
    obtain ⟨_, _, _, h1, -⟩ := hI.q w' hw' hp'
    obtain ⟨_, _, _, h2, -⟩ := hI.q w hw hp
    have e : w'.1 = w.1 := hI.one _ _ (by rw [h1]; rfl) (by rw [h2]; rfl)
    rw [← e]; exact Array.contains_iff_mem.mpr hu'
  refine ⟨hI.sv, fun u v hu hv => ?_, fun hn => hI.idle fun u i jr sn e hu => ?_,
    fun u i jr sn e hu => ?_, fun u hu => ?_, fun u i e hu => ?_, fun u v hu => hsg v,
    fun u v hu _ => (hsg' u _ rfl hu).elim, fun u v i jr sn e hu _ => (hsg' u _ hu rfl).elim,
    fun u v i jr sn e hu _ => (hsg' u _ hu rfl).elim, fun w hw hp => ?_, fun w hw hp => ?_,
    fun u hu => ?_, fun u hu => (hsg' u _ rfl hu).elim, fun u hu => (hsg' u _ rfl hu).elim⟩
  · exact hI.one u v (by rwa [← hph u (hwts u hu)]) (by rwa [← hph v (hwts v hv)])
  · have e' : u ≠ t := fun h => by subst h; rw [ht] at hu; cases hu
    exact hn u i jr sn e (by rw [hph u e']; exact hu)
  · have e' := hwts u (by rw [hu]; rfl)
    rw [hph u e'] at hu
    have h := hI.era u i jr sn e hu
    have hw := hI.wk t u i jr sn e ht hu
    exact { h with pend := fun _ h' => by change (C.Ep.hist m).size = i + 1 at h'; omega }
  · have e' := hwts u (by rw [hu]; rfl)
    rw [hph u e'] at hu; exact hI.en u hu
  · have e' := hwts u (by rw [hu]; rfl)
    rw [hph u e'] at hu; exact hI.ld u i e hu
  · have hw' : w ∈ m.waiters ∧
        (Thread.wakeSet m.waiters C.Ep.ptr c cs).contains w.1 = false := by
      simpa [Array.mem_filter] using hw
    rw [hgone w hw'.1 hp] at hw'
    cases hw'.2
  · simp only [Array.mem_filter] at hw
    have e' := hwts w.1 hp
    rw [hph _ e'] at hp; exact hI.qw w hw.1 hp
  · have e' : u ≠ t := fun h => by subst h; rw [upd_self, hg] at hu; cases hu
    rw [hph u e'] at hu; rw [upd_ne _ _ e']; exact hI.crit u hu

/-- The waiter's sleep at the epoch, which held its value `e`: the epoch is still its write `i`. -/
theorem Inv.sleep {G : ThreadId → γ} {M : Mem} {t : ThreadId} {i jr : Nat} {e : BitVec 32}
    (hI : C.Inv L G M) (ht : C.ph (G t) = .reg i jr false e) (hv : (C.lastE M).Val e) :
    C.Inv L G { M with waiters := M.waiters.push (t, C.Ep.ptr) } := by
  have h := hI.era t i jr false e ht
  have hsz : (C.Ep.hist M).size = i + 1 := by
    rcases h.esz with h1 | ⟨h1, -⟩
    · exact h1
    · exfalso
      have := (h.eval.2 h1)
      unfold FCond.lastE at hv; rw [h1, show i + 2 - 1 = i + 1 by omega] at hv
      exact add_one_ne e (FEvent.val_eq this hv)
  have hS : C.S.hist ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem) = C.S.hist M := rfl
  have hE : C.Ep.hist ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem) = C.Ep.hist M :=
    rfl
  have hcl : ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem).clocks = M.clocks := rfl
  refine ⟨by rw [hS]; exact hI.sv, hI.one, by unfold FCond.lastS; rw [hS]; exact hI.idle,
    fun u i jr sn e hu => (hI.era u i jr sn e hu).mono hS hE (by rw [hcl]; exact VClock.le_refl _)
      (fun v hv => ⟨v, hv⟩),
    fun u hu j hj => by rw [hE] at hj ⊢; rw [hcl]; exact hI.en u hu j hj,
    fun u i e hu => by rw [hE, hcl]; exact hI.ld u i e hu, hI.nosig, hI.sone,
    fun u v i jr sn e hu hv => by rw [hS, hE, hcl]; exact hI.inc u v i jr sn e hu hv,
    fun u v i jr sn e hu hv => by rw [hE]; exact hI.wk u v i jr sn e hu hv,
    fun w hw hp => ?_, fun w hw hp => ?_, hI.crit, hI.lp, hI.sx⟩
  · rw [hE]
    rcases Array.mem_push.mp hw with hw | rfl
    · exact hI.q w hw hp
    · exact ⟨i, jr, e, ht, .inl hsz⟩
  · rcases Array.mem_push.mp hw with hw | rfl
    · exact hI.qw w hw hp
    · exact .inl rfl

/-- **A step of another component of the protocol** (an event's code) by `t`, which keeps `t`'s
place in the condition and both words' writes: `t` keeps its lock place in the condition's busy
code, and a new waiter in the futex queue is `t` at another word, out of the waiter's places. -/
theorem Inv.other {G G' : ThreadId → γ} {m m' : Mem} {t : ThreadId} (hI : C.Inv L G m)
    (hG : ∀ u, u ≠ t → G' u = G u) (hph : C.ph (G' t) = C.ph (G t))
    (hlph : (C.ph (G t)).busy = true → L.ph (G' t) = L.ph (G t))
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hwt : ∀ w ∈ m'.waiters, w ∈ m.waiters ∨
      (w.1 = t ∧ w.2 ≠ C.Ep.ptr ∧ (C.ph (G t)).waits = false))
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hsxt : C.sx (G t) → C.sx (G' t)) (hap : C.Ep.ptr ≠ L.ptr) :
    C.Inv L G' m' := by
  have I1 : C.Inv L G' { m' with waiters := m.waiters } :=
    hI.move (m' := { m' with waiters := m.waiters }) hG hS hE hap (fun _ _ h => h) hclk
      (by rw [hph]; exact id)
      (fun h => by
        rw [hph] at h
        exact ⟨h, by rw [hlph (by unfold CPh.busy; rw [h]; rfl)]; exact hI.crit t h⟩)
      (fun h => by
        have hs : (C.ph (G t)).sig := by
          rcases h with h | h
          · rwa [hph] at h
          · exact h
        exact ⟨hph, hlph (by unfold CPh.busy; rw [hs, Bool.or_true]), hsxt⟩)
      (fun h j hj => by rw [hph] at h; exact VClock.le_trans (hI.en t h j hj) (hclk t))
      (fun i e h => by
        rw [hph] at h
        obtain ⟨h1, h2, h3⟩ := hI.ld t i e h
        exact ⟨h1, h2, VClock.le_trans h3 (hclk t)⟩)
      (fun i jr sn e h => ⟨sn, by rw [← hph]; exact h, fun hs => .inl hs⟩)
      (fun i jr sn e h => ⟨sn, by rw [hph]; exact h⟩)
      (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h), fun _ => hph⟩)
  refine { I1 with
    era := fun u i jr sn e h => (I1.era u i jr sn e h).mono rfl rfl (VClock.le_refl _)
      fun v hv => ⟨v, hv⟩
    q := fun w hw hp => ?_, qw := fun w hw hp => ?_ }
  · rcases hwt w hw with h | ⟨-, hn, -⟩
    · exact I1.q w h hp
    · exact absurd hp hn
  · rcases hwt w hw with h | ⟨e, -, hn⟩
    · exact I1.qw w h hp
    · rw [e, hph, hn] at hp; cases hp

/-- **A lock step of a thread out of the condition's busy code** keeps the condition's invariant
(for a client's `FLock.Fits.stable`, whose `ok` excludes the busy threads; module doc). -/
theorem Inv.lstep {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {p : LPh} {h : Res}
    (hI : C.Inv L G m) (hwS : C.S.Ok m) (hwE : C.Ep.Ok m) (hapS : C.S.ApartL L.toLockWord)
    (hapE : C.Ep.ApartL L.toLockWord) (hb : (C.ph (G t)).busy = false)
    (hph : ∀ g q h, C.ph (L.set g q h) = C.ph g) (hs : L.Step t m m') :
    C.Inv L (upd G t (L.set (G t) p h)) m' := by
  have hpt : C.ph (upd G t (L.set (G t) p h) t) = C.ph (G t) := by rw [upd_self, hph]
  have hnc : (C.ph (G t)).crit = false := by
    unfold CPh.busy at hb; revert hb; cases (C.ph (G t)).crit <;> simp
  have hns : (C.ph (G t)).sig = false := by
    unfold CPh.busy at hb; revert hb; cases (C.ph (G t)).sig <;> simp
  refine hI.move (fun u hu => upd_ne _ _ hu)
    (Word.hist_keep hwS (Word.keep_lockWordStep hs hapS))
    (Word.hist_keep hwE (Word.keep_lockWordStep hs hapE)) hapE.ptr_ne
    (fun w hl hw => (hs.waiters w hl).mp hw) (fun u => ?_) (by rw [hpt]; exact id)
    (fun h' => by rw [hpt, hnc] at h'; cases h') (fun h' => by
      rw [hpt] at h'; rcases h' with h' | h' <;> rw [hns] at h' <;> cases h')
    (fun h' => by rw [hpt] at h'; rw [h'] at hnc; cases hnc)
    (fun i e h' => by rw [hpt] at h'; rw [h'] at hnc; cases hnc)
    (fun i jr sn e h' => ⟨sn, by rw [← hpt]; exact h', fun hsn => .inl hsn⟩)
    (fun i jr sn e h' => ⟨sn, by rw [hpt]; exact h'⟩)
    (fun w hw e => ⟨fun h' => hI.qw w hw (by rw [e, ← hpt]; exact h'), fun _ => hpt⟩)
  by_cases e : u = t
  · subst e; exact hs.mine
  · rw [hs.others u e]; exact VClock.le_refl _

/-- A waiter's read of state write `j` at `reg i jr sn e`: its `(1, 0)` (only before it loaded
the epoch's next write) or the signal `(1, 1)`. -/
theorem Inv.readS {G : ThreadId → γ} {m : Mem} {t : ThreadId} {i jr : Nat} {sn : Bool}
    {e : BitVec 32} (hI : C.Inv L G m) (ht : C.ph (G t) = .reg i jr sn e) {j : Nat}
    {b : BitVec 32} (hj : j < (C.S.hist m).size) (hv : (C.S.hist m)[j]!.Val b)
    (hfl : Word.Floor (C.S.hist m) (m.clocks[t]!) j) :
    (b = 1 ∧ sn = false) ∨ b = 0x10001 := by
  have h := hI.era t i jr sn e ht
  have hge : jr ≤ j := hfl jr (by rcases h.ssz with h' | h' <;> omega) h.cs
  have hsn : sn = true → jr + 1 ≤ j := fun hs => by
    obtain ⟨h1, h2⟩ := h.seen hs
    rcases h.esz with h3 | ⟨-, h3, h4⟩
    · omega
    · exact hfl (jr + 1) (by omega) (VClock.le_trans h4 h2)
  rcases h.ssz with hs | hs
  · have : j = jr := by omega
    subst this
    refine .inl ⟨FEvent.val_eq hv h.s0, ?_⟩
    cases hs' : sn
    · rfl
    · have := hsn hs'; omega
  · rcases (by omega : j = jr ∨ j = jr + 1) with rfl | rfl
    · refine .inl ⟨FEvent.val_eq hv h.s0, ?_⟩
      cases hs' : sn
      · rfl
      · have := hsn hs'; omega
    · exact .inr (FEvent.val_eq hv (h.s1 hs))

/-- A signaller's read of state write `j`, after every registration (`hseen`): a value of the
state; a value other than `(1, 0)` means a registered waiter was signalled. -/
theorem Inv.readSig {G : ThreadId → γ} {m : Mem} {t : ThreadId} (hI : C.Inv L G m) {j : Nat}
    {b : BitVec 32} (hj : j < (C.S.hist m).size) (hv : (C.S.hist m)[j]!.Val b)
    (hfl : Word.Floor (C.S.hist m) (m.clocks[t]!) j)
    (hseen : ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e →
      VClock.le (C.S.hist m)[jr]!.clock (m.clocks[t]!) = true) :
    (b = 0 ∨ b = 1 ∨ b = 0x10001) ∧
      (b ≠ 1 → ∀ u i jr sn e, C.ph (G u) = .reg i jr sn e → C.Signalled m) := by
  refine ⟨(hI.sv j hj).cases hv, fun hb u i jr sn e hu => ?_⟩
  have h := hI.era u i jr sn e hu
  have hge : jr ≤ j := hfl jr (by rcases h.ssz with h' | h' <;> omega) (hseen u i jr sn e hu)
  rcases h.last with ⟨hs, -⟩ | ⟨-, h2⟩
  · have : j = jr := by omega
    subst this; exact absurd (FEvent.val_eq hv h.s0) hb
  · exact h2

/-- `Inv.move` for a new ghost value `g'` of `t` (`G t = g`). -/
theorem Inv.moveT {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g g' : γ} (hI : C.Inv L G m)
    (hg : G t = g) (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m)
    (hap : C.Ep.ptr ≠ L.ptr) (hwt : ∀ w, w.2 ≠ L.ptr → w ∈ m'.waiters → w ∈ m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hwaits : (C.ph g').waits → (C.ph g).waits)
    (hcr : (C.ph g').crit → (C.ph g).crit ∧ L.ph g' = .holds)
    (hsig : (C.ph g').sig ∨ (C.ph g).sig → C.ph g' = C.ph g ∧ L.ph g' = L.ph g ∧ (C.sx g → C.sx g'))
    (hen : C.ph g' = .en → ∀ j < (C.Ep.hist m).size,
      VClock.le (C.Ep.hist m)[j]!.clock (m'.clocks[t]!) = true)
    (hld : ∀ i e, C.ph g' = .ld i e → (C.Ep.hist m).size = i + 1 ∧
      (C.Ep.hist m)[i]!.Val e ∧ VClock.le (C.Ep.hist m)[i]!.clock (m'.clocks[t]!) = true)
    (hreg : ∀ i jr sn e, C.ph g' = .reg i jr sn e → ∃ sn', C.ph g = .reg i jr sn' e ∧
      (sn = true → sn' = true ∨ ((C.Ep.hist m).size = i + 2 ∧
        VClock.le (C.Ep.hist m)[i + 1]!.relClock (m'.clocks[t]!) = true)))
    (hreg' : ∀ i jr sn e, C.ph g = .reg i jr sn e → ∃ sn', C.ph g' = .reg i jr sn' e)
    (htq : ∀ w ∈ m.waiters, w.1 = t → ((C.ph g').waits → w.2 = C.Ep.ptr ∨ w.2 = L.ptr) ∧
      (w.2 = C.Ep.ptr → C.ph g' = C.ph g)) :
    C.Inv L (upd G t g') m' := by
  subst hg
  exact hI.move (fun u hu => upd_ne _ _ hu) hS hE hap hwt hclk (by rw [upd_self]; exact hwaits)
    (by rw [upd_self]; exact hcr) (by rw [upd_self]; exact hsig) (by rw [upd_self]; exact hen)
    (by rw [upd_self]; exact hld) (by rw [upd_self]; exact hreg) (by rw [upd_self]; exact hreg')
    (by rw [upd_self]; exact htq)

/-- A step of `t` that keeps its places and the writes of both words and the futex queue, with
`t`'s new ghost value `g'` (a step on its own part). -/
theorem Inv.frame {G : ThreadId → γ} {m m' : Mem} {t : ThreadId} {g' : γ} (hI : C.Inv L G m)
    (hph : C.ph g' = C.ph (G t)) (hlph : L.ph g' = L.ph (G t)) (hsx : C.sx (G t) → C.sx g')
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m) (hap : C.Ep.ptr ≠ L.ptr)
    (hwt : m'.waiters = m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) :
    C.Inv L (upd G t g') m' :=
  hI.moveT rfl hS hE hap (fun w _ h => by rwa [hwt] at h) hclk (by rw [hph]; exact id)
    (fun h => by rw [hph] at h; exact ⟨h, by rw [hlph]; exact hI.crit t h⟩)
    (fun _ => ⟨hph, hlph, hsx⟩)
    (fun h j hj => by rw [hph] at h; exact VClock.le_trans (hI.en t h j hj) (hclk t))
    (fun i e h => by
      rw [hph] at h
      obtain ⟨h1, h2, h3⟩ := hI.ld t i e h
      exact ⟨h1, h2, VClock.le_trans h3 (hclk t)⟩)
    (fun i jr sn e h => ⟨sn, by rw [← hph]; exact h, fun hs => .inl hs⟩)
    (fun i jr sn e h => ⟨sn, by rw [hph]; exact h⟩)
    (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e, ← hph]; exact h), fun _ => hph⟩)

/-- A step that keeps the writes of both words and the futex queue, with `t` staying. -/
theorem Inv.stay {G : ThreadId → γ} {m m' : Mem} (t : ThreadId) (hI : C.Inv L G m)
    (hS : C.S.hist m' = C.S.hist m) (hE : C.Ep.hist m' = C.Ep.hist m) (hap : C.Ep.ptr ≠ L.ptr)
    (hwt : ∀ w, w.2 ≠ L.ptr → w ∈ m'.waiters → w ∈ m.waiters)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) : C.Inv L G m' := by
  have := hI.moveT (t := t) (g' := G t) rfl hS hE hap hwt hclk id (fun h => ⟨h, hI.crit t h⟩)
    (fun _ => ⟨rfl, rfl, id⟩)
    (fun h j hj => VClock.le_trans (hI.en t h j hj) (hclk t))
    (fun i e h => let ⟨h1, h2, h3⟩ := hI.ld t i e h; ⟨h1, h2, VClock.le_trans h3 (hclk t)⟩)
    (fun i jr sn e h => ⟨sn, h, fun hs => .inl hs⟩) (fun i jr sn e h => ⟨sn, h⟩)
    (fun w hw e => ⟨fun h => hI.qw w hw (by rw [e]; exact h), fun _ => rfl⟩)
  rwa [upd_same] at this

/-! ## The protocol after a step -/

variable {Tgt : Type} {P : Proto Tgt γ} {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}

/-- An op at the state keeps the epoch's writes. -/
theorem _root_.Zig.Full.FLock.Fits.keepE (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {rX : Res} {m m' : Mem} {t : ThreadId} (hU : U G rX m) (hop : C.S.Op t m m') :
    C.Ep.hist m' = C.Ep.hist m :=
  Word.hist_keep ((hC.wRest (.inr rfl)) _ _ _ hU).1
    (Word.keep_op hop (.inr (.inl (by have := C.ep_o; omega))))

/-- An op at the epoch keeps the state's writes. -/
theorem _root_.Zig.Full.FLock.Fits.keepS (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {rX : Res} {m m' : Mem} {t : ThreadId} (hU : U G rX m) (hop : C.Ep.Op t m m') :
    C.S.hist m' = C.S.hist m :=
  Word.hist_keep ((hC.wRest (.inl rfl)) _ _ _ hU).1
    (Word.keep_op hop (.inr (.inr (by have := C.ep_o; omega))))

/-- After a step of the condition's code by `t` (`g`, new place `p`) that keeps `t`'s lock
place: the protocol's invariant, from the lock's invariant after the step, the rest before it,
and the condition's invariant after it. -/
theorem _root_.Zig.Full.FLock.Fits.backC (hC : L.Fits (C.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {t : ThreadId} {g : γ} {p : CPh} {W : Word 32 4}
    (hW : W = C.S ∨ W = C.Ep) (hg₁ : G₁ t = g) (hn : CPh.Next (C.ph g) p)
    (hU : U G₁ (rsum (W.cellsR m₁) rY) m₁) (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : C.MStep W t m₁ m') (hEp : C.Ep.hist m' = C.Ep.hist m₁ ∨ C.ph g = .inc)
    (hL : L.Inv G₁ (rsum (W.cellsR m') rY) m') (hI : C.Inv L (upd G₁ t (C.set g p)) m') :
    P.inv (upd G₁ t (C.set g p)) m' :=
  hC.back hW hg₁ ⟨hn, .inl ⟨rfl, rfl⟩, hs, hEp⟩ hU hY hL hI

/-- A thread enters the wait (`out` → `en`) holding the mutex (module doc, scope; `hent`: the
client's rest allows it). -/
theorem _root_.Zig.Full.FLock.Fits.enterEn (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {m : Mem} {t : ThreadId} {g : γ} (hgx : C.ph g = .out) (hgh : L.ph g = .holds)
    (hone : ∀ u, u ≠ t → C.ph (G u) = .out)
    (hhb : ∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true)
    (hent : ∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m)
    (hi : P.inv (upd G t g) m) : P.inv (upd G t (C.set g .en)) m := by
  obtain ⟨rX, hL, hU⟩ := (hC.inv _ _).mp hi
  have hnq : ∀ w ∈ m.waiters, w.1 ≠ t := by
    have := hL.w.notQ (t := t) (show L.ph (upd G t g t) ≠ .wait by rw [upd_self, hgh]; decide)
      (show L.ph (upd G t g t) ≠ .away by rw [upd_self, hgh]; decide)
    exact FLock.notQ_mem this
  have hI := (hC.wInv _ _ _ hU).enter hgx (by rw [hC.lph]; exact hgh) hnq hone hhb
  have hL' := hL.relabel (t := t) (g := C.set g .en) (by rw [upd_self, hC.lph])
    (by rw [upd_self, hC.lpart]) (by rw [upd_self, hC.lheld]) (fun r hr => by
      have := hC.lR (upd G t g) t .en r hr; rwa [upd_self] at this)
  rw [upd_upd] at hL'
  exact (hC.inv _ _).mpr ⟨rX, hL', hent rX hU hI⟩

/-- A sleeping waiter of a signalled condition is not in a deadlock: a signaller between its
signal and its wake runs. -/
theorem _root_.Zig.Full.FLock.Fits.liveSig (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ}
    {rX : Res} {m : Mem} {t : ThreadId} (hI : C.Inv L G m) (hL : L.Inv G rX m) (ht : (C.ph (G t)).waits)
    (hs : C.Signalled m) : P.Live t G m := by
  intro hin hall
  obtain ⟨w, hw, he⟩ := Array.any_eq_true'.mp hin
  have e : w.1 = t := by simpa using he
  have hp : w.2 = C.Ep.ptr := by
    rcases hI.qw w hw (by rw [e]; exact ht) with h | h
    · exact h
    · exact absurd (Array.any_eq_true'.mpr ⟨w, hw, by simp [h]⟩) (hC.noWaits hL hall)
  obtain ⟨i, jr, e', h1, h2⟩ := hI.q w hw hp
  have h := hI.era w.1 i jr false e' h1
  have hs2 : (C.S.hist m).size = jr + 2 := by
    rcases h.last with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact absurd (FEvent.val_eq h3 hs) (by decide)
    · exact h3
  -- a signaller runs
  obtain ⟨v, hv⟩ : ∃ v, (C.ph (G v)).sig := by
    rcases h2 with h2 | ⟨v, hv⟩
    · obtain ⟨v, hv⟩ := h.pend hs2 h2; exact ⟨v, by rw [hv]; rfl⟩
    · exact ⟨v, by rw [hv]; rfl⟩
  have hlo := hI.lp v hv
  have hvt := (hL.ht (t := v) (by rw [hlo]; decide)).1
  rcases hall v hvt with h' | h' | h'
  · rw [hC.kfin _ h'] at hv; cases hv
  · have := hL.w.notQ (t := v) (show L.ph (G v) ≠ .wait by rw [hlo]; decide)
      (show L.ph (G v) ≠ .away by rw [hlo]; decide)
    rw [this] at h'; cases h'
  · rw [hC.kjoins _ h'] at hv; cases hv

/-! ## The ops of the condition's code in generated code (`WP`) -/

variable {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat} {g : γ}

/-- An op at a word of the condition: its `MStep`. -/
theorem mstep_op {W : Word 32 4} {m₁ m' : Mem} (hc : m₁.current = t)
    (hop : W.Op t m₁ m') (hw' : W.Ok m')
    (hh : W.hist m' = W.hist m₁ ∨ ∃ (ord : AtomicOrder) (v : BitVec 32),
      W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t ord (W.hist m₁)[(W.hist m₁).size - 1]! v)) :
    C.MStep W t m₁ m' := .op (by rw [FEvent.cur_eq hc]; exact hop) hw' hh

/-- The waiter's acquire load of the epoch at `en` (holding the mutex): it reads the newest write
`i` (every epoch write happened before it), `ld i b`. -/
theorem wp_ldEp (hC : L.Fits (C.prim L) P U ok) (hg : C.ph g = .en)
    (hgh : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b i, m'.current = t →
      P.inv (upd G₁ t (C.set g (.ld i b))) m' → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .acquire 4 C.Ep.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hC (hC.wRest (.inr rfl)) (hC.wAp (.inr rfl)) (by rw [hgh]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv hfl _ hh hw' hop hL => by
      obtain ⟨hI, hnq⟩ := hC.atOp hU (by rw [hg₁, hgh]; decide) (by rw [hg₁, hgh]; decide) hop hL
      have hen := hI.en t (by rw [hg₁]; exact hg)
      have hpos := FEvent.hist_pos ((hC.wRest (.inr rfl)) _ _ _ hU).1
      have hj' : j = (C.Ep.hist m₁).size - 1 := by
        have := hfl ((C.Ep.hist m₁).size - 1) (by omega) (hen _ (by omega)); omega
      subst hj'
      refine h k hk G₁ m' b ((C.Ep.hist m₁).size - 1) hop.current (hC.backC (.inr rfl) hg₁
        (by rw [hg]; exact True.intro) hU hY (mstep_op hc₁ hop hw' (.inl hh)) (.inl hh)
        hL ?_)
      exact hI.moveT hg₁ (hC.keepS hU hop) hh (hC.wAp (.inr rfl)).ptr_ne
        (fun w _ hw => by rw [hop.waiters] at hw; exact hw) hop.clocks
        (fun _ => by rw [hg]; rfl) (fun _ => ⟨by rw [hg]; rfl, by rw [hC.lph]; exact hgh⟩)
        (fun h' => by rw [C.ph_set, hg] at h'; simp [CPh.sig] at h')
        (fun h' => by rw [C.ph_set] at h'; cases h')
        (fun i e h' => by
          rw [C.ph_set] at h'; cases h'
          exact ⟨by omega, hv, VClock.le_trans (hen _ (by omega)) (hop.clocks t)⟩)
        (fun i jr sn e h' => by rw [C.ph_set] at h'; cases h')
        (fun i jr sn e h' => by rw [hg] at h'; cases h')
        (fun w hw e => absurd e (hnq w hw))

/-- The waiter's `waiters += 1` at `ld i e` (after it, `reg i jr false e`): no other waiter, so
it reads `(0, 0)`. -/
theorem _root_.Zig.Full.FLock.Fits.afterReg (hC : L.Fits (C.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {i : Nat} {e : BitVec 32} {ord : AtomicOrder} {old new : BitVec 32}
    (hg₁ : G₁ t = g) (hg : C.ph g = .ld i e) (hgh : L.ph g = .holds) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hop : C.S.Op t m₁ m') (hw' : C.S.Ok m') (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hv : (C.lastS m₁).Val old) (hnew : old = 0 → new = 1)
    (hh : C.S.hist m' = (C.S.hist m₁).push (Word.rmwEnt m' t ord (C.lastS m₁) new)) :
    old = 0 ∧ ∃ jr, P.inv (upd G₁ t (C.set g (.reg i jr false e))) m' := by
  obtain ⟨hI, hnq⟩ := hC.atOp hU (by rw [hg₁, hgh]; decide) (by rw [hg₁, hgh]; decide) hop hL
  have hold : old = 0 := by
    have h0 := hI.idle fun u i' jr sn e' hu => by
      have := hI.one u t (by rw [hu]; rfl) (by rw [hg₁, hg]; rfl)
      subst this; rw [hg₁, hg] at hu; cases hu
    exact FEvent.val_eq hv h0
  have hn := hnew hold
  subst hn
  refine ⟨hold, (C.S.hist m₁).size, hC.backC (.inl rfl) hg₁ (by rw [hg]; exact ⟨rfl, rfl⟩) hU hY
    (mstep_op hc₁ hop hw' (.inr ⟨ord, 1, hh⟩)) (.inl (hC.keepE hU hop)) hL ?_⟩
  exact hI.reg (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hg) (by rw [upd_self, C.ph_set]) hh
    (hC.keepE hU hop) hop.waiters hnq hop.clocks

/-- The waiter's `waiters += 1` on bits (`atomicRmwC`, `Thread.Condition`). -/
theorem wp_reg (hC : L.Fits (C.prim L) P U ok) {i : Nat} {e : BitVec 32}
    (hg : C.ph g = .ld i e) (hgh : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' jr, m'.current = t →
      P.inv (upd G₁ t (C.set g (.reg i jr false e))) m' → Q (0, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .add false .relaxed 4 C.S.ptr (1 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n :=
  FLock.wp_wordRmw hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgh]; decide) hi
    fun k hk G₁ rY m₁ m' old hg₁ hc₁ hU hY hv _ hh _ hw' hop hL => by
      obtain ⟨rfl, jr, hi'⟩ := hC.afterReg hg₁ hg hgh hc₁ hU hY hop hw' hL hv
        (fun h0 => by subst h0; rfl) hh
      exact h k hk G₁ m' jr hop.current hi'

/-- The waiter's `waiters += 1` with a decode (`atomicRmwAsC`, `Io.Condition`). -/
theorem wp_regAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok) {i : Nat}
    {e : BitVec 32} {v : α} (hv1 : Packed.toBits v = (1 : BitVec 32))
    (hdec0 : ∃ r, (Packed.ofBits? (α := α) 0).run = some (.ok r))
    (hg : C.ph g = .ld i e) (hgh : L.ph g = .holds) (hi : P.inv (upd G t g) m)
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' jr r, m'.current = t →
      (Packed.ofBits? (α := α) 0).run = some (.ok r) →
      P.inv (upd G₁ t (C.set g (.reg i jr false e))) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwAsC .add .relaxed 4 C.S.ptr v : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordRmwAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgh]; decide) hi
    (fun G₁ rY m₁ hg₁ hc₁ hU b hb => by
      have hI := hC.wInv _ _ _ hU
      have h0 := hI.idle fun u i' jr sn e' hu => by
        have := hI.one u t (by rw [hu]; rfl) (by rw [hg₁, hg]; rfl)
        subst this; rw [hg₁, hg] at hu; cases hu
      rw [FEvent.val_eq hb h0]; exact hdec0)
    fun k hk G₁ rY m₁ m' old r hg₁ hc₁ hU hY hd hv _ hh _ hw' hop hL => by
      obtain ⟨rfl, jr, hi'⟩ := hC.afterReg hg₁ hg hgh hc₁ hU hY hop hw' hL hv
        (fun h0 => by subst h0; rw [hv1]; rfl) hh
      exact h k hk G₁ m' jr r hop.current hd hi'

/-- **The waiter's futex wait at the epoch** with its value `e` (`futexWaitC`), at
`reg i jr false e` out of the lock's code: it goes on at the same place. A signalled
condition's sleeper is not in a deadlock (`Fits.liveSig`); for one that is not signalled, the
client shows it (`hlive`). -/
theorem wp_waitEp (hC : L.Fits (C.prim L) P U ok) {ε : Type} {w : Nat}
    [Packed ε w] {io : Io} {e' : ε} {i jr : Nat} {e : BitVec 32}
    (he : (Packed.toBits e').setWidth 32 = e) (hg : C.ph g = .reg i jr false e)
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    (hlive : ∀ G₁ m₁, C.ph (G₁ t) = C.ph g → L.ph (G₁ t) = .away → P.inv G₁ m₁ →
      ¬ C.Signalled m₁ → P.Live t G₁ m₁)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t → P.inv (upd G₁ t g) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWaitC io C.Ep.ptr e' : CM Tgt σ Unit).run s) Q G m n := by
  have hheld : L.held g = rnil := by
    obtain ⟨rX, hL, -⟩ := (hC.inv _ _).mp hi
    have := hL.idle t (by rw [upd_self, hgo]; decide); rwa [upd_self] at this
  have hga : C.ph (L.set g .away rnil) = C.ph g := hC.ph_l _ _ _
  have hgo' : L.set g .out rnil = g := by
    have := L.set_self g; rwa [hgo, hheld] at this
  have hnx : CPh.Next (C.ph g) (C.ph g) := CPh.Next.refl _
  have hw : (C.ph g).waits := by rw [hg]; rfl
  -- the condition's invariant with `t`'s new ghost value `g'` (same place in the condition)
  have hmv : ∀ {G₁ : ThreadId → γ} {m₁ m₂ : Mem} {g₁ g₂ : γ}, C.Inv L G₁ m₁ → G₁ t = g₁ →
      C.ph g₂ = C.ph g → C.ph g₁ = C.ph g → C.S.hist m₂ = C.S.hist m₁ →
      C.Ep.hist m₂ = C.Ep.hist m₁ → (∀ w, w.2 ≠ L.ptr → w ∈ m₂.waiters → w ∈ m₁.waiters) →
      (∀ u : ThreadId, VClock.le (m₁.clocks[u]!) (m₂.clocks[u]!) = true) →
      C.Inv L (upd G₁ t g₂) m₂ := fun {G₁ m₁ m₂ g₁ g₂} hI hg₁ h2 h1 hS hE hwt hclk =>
    hI.moveT hg₁ hS hE (hC.wAp (.inr rfl)).ptr_ne hwt hclk (by rw [h1, h2]; exact id)
      (fun h' => by rw [h2, hg] at h'; simp [CPh.crit] at h')
      (fun h' => by rw [h2, h1, hg] at h'; simp [CPh.sig] at h')
      (fun h' => by rw [h2, hg] at h'; cases h')
      (fun _ _ h' => by rw [h2, hg] at h'; cases h')
      (fun i' jr' sn e'' h' => ⟨sn, by rw [h1, ← h2]; exact h', fun hs => .inl hs⟩)
      (fun i' jr' sn e'' h' => ⟨sn, by rw [h2, ← h1]; exact h'⟩)
      (fun w hw' e'' => ⟨fun _ => hI.qw w hw' (by rw [e'', hg₁, h1]; exact hw), fun _ => by
        rw [h1, h2]⟩)
  refine FLock.wp_wordWait hC (hC.wRest (.inr rfl)) (hC.wAp (.inr rfl)) hgo hi (fun rX hU => ?_)
    (fun G₁ m₁ hg₁ hi₁ => ?_) (fun G₁ rY m₁ M hg₁ hU hY hop hh hok₂ hbl hU32 => ?_)
    (fun G₁ rY m₁ M hg₁ hU hY hM => ?_) h
  · -- `t` goes away
    obtain ⟨-, rY, rfl, hY⟩ := (hC.wRest (.inr rfl)) _ _ _ hU
    have hI' : C.Inv L (upd (upd G t g) t (L.set g .away rnil)) m :=
      hmv (hC.wInv _ _ _ hU) (upd_self G t g) hga rfl rfl rfl (fun _ _ h' => h')
        (fun _ => VClock.le_refl _)
    have := hC.wStep (G := upd G t g) (rY := rY) (m := m) (m' := m) (t := t) (p := C.ph g)
      (q := .away) (h := rnil) (.inr rfl) ⟨by rw [upd_self]; exact hnx,
        .inr ⟨.inl (by rw [upd_self]; exact hgo), .inr ⟨rfl, hw⟩, rfl⟩, .same, .inl rfl⟩
      hU hY (by rw [upd_self, C.set_self]; exact hI')
    rwa [upd_self, C.set_self, upd_upd] at this
  · -- no deadlock
    by_cases hs : C.Signalled m₁
    · obtain ⟨rX, hL, hU⟩ := (hC.inv _ _).mp hi₁
      exact hC.liveSig (hC.wInv _ _ _ hU) hL (by rw [hg₁, hga]; exact hw) hs
    · exact hlive G₁ m₁ (by rw [hg₁, hga]) (by rw [hg₁, L.ph_set]) hi₁ hs
  · -- `t` sleeps: the epoch held its value
    have hI := hC.wInv _ _ _ hU
    have hS := hC.keepS hU hop.of_cur
    have hI₁ : C.Inv L G₁ M := by
      have := hmv (g₂ := G₁ t) hI hg₁ (by rw [hg₁, hga]) hga hS hh
        (fun w _ hw' => by rw [hop.waiters] at hw'; exact hw') hop.clocks
      rwa [upd_same] at this
    have hv : (C.lastE M).Val e := by
      unfold FCond.lastE; rw [hh]; rw [he] at hU32; exact ((hC.wRest (.inr rfl)) _ _ _ hU).1.holds_last.mp hU32
    have hst := hC.wStep (G := G₁) (rY := rY) (m := m₁) (t := t) (p := C.ph (G₁ t))
      (q := L.ph (G₁ t)) (h := L.held (G₁ t)) (.inr rfl)
      ⟨CPh.Next.refl _, .inl ⟨rfl, rfl⟩, .sleep hop hh hok₂ hbl, .inl hh⟩ hU hY (by
        rw [C.set_self, L.set_self, upd_same]
        exact hI₁.sleep (by rw [hg₁, hga, hg]) hv)
    rw [C.set_self, L.set_self, upd_same, Word.cellsR_congr (W := C.Ep) (show
      ({ M with waiters := M.waiters.push (t, C.Ep.ptr) } : Mem).blocks = m₁.blocks from hbl)] at hst
    exact hst
  · -- `t` is back, out of the lock's code
    have hI := hC.wInv _ _ _ hU
    have hgq : L.set (C.set (G₁ t) (C.ph (G₁ t))) .out rnil = g := by
      rw [C.set_self, hg₁, L.set_set, hgo']
    have hbl : M.blocks = m₁.blocks := by
      rcases hM with rfl | rfl | ⟨-, -, -, hb⟩
      · rfl
      · rfl
      · exact hb
    have hEh : C.Ep.hist M = C.Ep.hist m₁ := by
      rcases hM with rfl | rfl | ⟨-, hh, -⟩
      · rfl
      · rfl
      · exact hh
    have hSh : C.S.hist M = C.S.hist m₁ := by
      rcases hM with rfl | rfl | ⟨hop, -⟩
      · rfl
      · rfl
      · exact hC.keepS hU hop.of_cur
    have hwt : ∀ w, w.2 ≠ L.ptr → w ∈ M.waiters → w ∈ m₁.waiters := fun w _ hw' => by
      rcases hM with rfl | rfl | ⟨hop, -⟩
      · exact hw'
      · exact hw'
      · rw [hop.waiters] at hw'; exact hw'
    have hclk : ∀ u : ThreadId, VClock.le (m₁.clocks[u]!) (M.clocks[u]!) = true := by
      rcases hM with rfl | rfl | ⟨hop, -⟩
      · exact fun _ => VClock.le_refl _
      · exact fun _ => VClock.le_refl _
      · exact hop.clocks
    have hst := hC.wStep (G := G₁) (rY := rY) (m := m₁) (m' := M) (t := t) (p := C.ph (G₁ t))
      (q := .out) (h := rnil) (.inr rfl) ⟨CPh.Next.refl _,
        .inr ⟨.inr (by rw [hg₁, L.ph_set]), .inl rfl, rfl⟩, ?_, .inl hEh⟩ hU hY (by
        rw [hgq]; exact hmv hI hg₁ rfl hga hSh hEh hwt hclk)
    · rw [hgq, Word.cellsR_congr (W := C.Ep) hbl] at hst
      exact hst
    · rcases hM with rfl | rfl | ⟨hop, hh, hok₂, -⟩
      · exact .woken
      · exact .resume
      · exact .op hop hok₂ (.inl hh)

/-- A read at a word of the condition by `t` (`g`), which stays where it is. -/
theorem _root_.Zig.Full.FLock.Fits.afterReadC (hC : L.Fits (C.prim L) P U ok)
    {G₁ : ThreadId → γ} {rY : Res} {m₁ m' : Mem} {W : Word 32 4} (hW : W = C.S ∨ W = C.Ep) (hg₁ : G₁ t = g)
    (hc₁ : m₁.current = t) (hU : U G₁ (rsum (W.cellsR m₁) rY) m₁)
    (hY : ∀ l, W.In l → rY.heap l = none) (hop : W.Op t m₁ m') (hw' : W.Ok m')
    (hL : L.Inv G₁ (rsum (W.cellsR m') rY) m') (hh : W.hist m' = W.hist m₁) :
    P.inv (upd G₁ t g) m' := by
  have hI := hC.wInv _ _ _ hU
  have hS : C.S.hist m' = C.S.hist m₁ := by
    rcases hW with rfl | rfl
    · exact hh
    · exact hC.keepS hU hop
  have hE : C.Ep.hist m' = C.Ep.hist m₁ := by
    rcases hW with rfl | rfl
    · exact hC.keepE hU hop
    · exact hh
  have := hC.backC hW hg₁ (CPh.Next.refl _) hU hY (mstep_op hc₁ hop hw' (.inl hh)) (.inl hE)
    hL (by
      rw [C.set_self, ← hg₁, upd_same]
      exact hI.stay t hS hE (hC.wAp (.inr rfl)).ptr_ne
        (fun w _ hw => by rw [hop.waiters] at hw; exact hw) hop.clocks)
  rwa [C.set_self] at this

/-- The waiter's acquire load of the epoch at `reg i jr false e`: its write `i` (it stays), or the
signaller's `i + 1` (`reg i jr true e`: the signal happened before it). -/
theorem wp_loadEp (hC : L.Fits (C.prim L) P U ok) {i jr : Nat} {e : BitVec 32}
    (hg : C.ph g = .reg i jr false e) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t →
      (b = e ∧ P.inv (upd G₁ t g) m') ∨
      (b = e + 1 ∧ P.inv (upd G₁ t (C.set g (.reg i jr true e))) m') → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .acquire 4 C.Ep.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hC (hC.wRest (.inr rfl)) (hC.wAp (.inr rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv hfl hacq hh hw' hop hL => by
      obtain ⟨hI, hnq⟩ := hC.atOp hU (by rw [hg₁, hgo]; decide) (by rw [hg₁, hgo]; decide) hop hL
      have hr := hI.era t i jr false e (by rw [hg₁]; exact hg)
      have hge : i ≤ j := hfl i (by rcases hr.esz with h' | ⟨h', -⟩ <;> omega) hr.ce
      refine h k hk G₁ m' b hop.current ?_
      rcases (by rcases hr.esz with h' | ⟨h', -⟩ <;> omega :
          j = i ∨ (j = i + 1 ∧ (C.Ep.hist m₁).size = i + 2)) with rfl | ⟨rfl, hs2⟩
      · exact .inl ⟨FEvent.val_eq hv hr.eval.1,
          hC.afterReadC (.inr rfl) hg₁ hc₁ hU hY hop hw' hL hh⟩
      · refine .inr ⟨FEvent.val_eq hv (hr.eval.2 hs2), hC.backC (.inr rfl) hg₁
          (by rw [hg]; exact ⟨rfl, rfl, rfl⟩) hU hY (mstep_op hc₁ hop hw' (.inl hh)) (.inl hh)
          hL ?_⟩
        exact hI.moveT hg₁ (hC.keepS hU hop) hh (hC.wAp (.inr rfl)).ptr_ne
          (fun w _ hw => by rw [hop.waiters] at hw; exact hw) hop.clocks
          (fun _ => by rw [hg]; rfl) (fun h' => by rw [C.ph_set] at h'; simp [CPh.crit] at h')
          (fun h' => by rw [C.ph_set, hg] at h'; simp [CPh.sig] at h')
          (fun h' => by rw [C.ph_set] at h'; cases h')
          (fun _ _ h' => by rw [C.ph_set] at h'; cases h')
          (fun i' jr' sn e' h' => by
            rw [C.ph_set] at h'; cases h'; exact ⟨false, hg, fun _ => .inr ⟨hs2, hacq rfl⟩⟩)
          (fun i' jr' sn e' h' => by rw [hg] at h'; cases h'; exact ⟨true, by rw [C.ph_set]⟩)
          (fun w hw e' => absurd e' (hnq w hw))

/-- The waiter's relaxed load of the state at `reg i jr sn e` (`atomicLoadC`, `Thread.Condition`):
its `(1, 0)` (only without `sn`) or the signal. -/
theorem wp_loadS (hC : L.Fits (C.prim L) P U ok) {i jr : Nat} {sn : Bool}
    {e : BitVec 32} (hg : C.ph g = .reg i jr sn e) (hgo : L.ph g = .out)
    (hi : P.inv (upd G t g) m) {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t → ((b = 1 ∧ sn = false) ∨ b = 0x10001) →
      P.inv (upd G₁ t g) m' → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .relaxed 4 C.S.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv hfl _ hh hw' hop hL =>
      h k hk G₁ m' b hop.current ((hC.wInv _ _ _ hU).readS (by rw [hg₁]; exact hg) hj hv hfl)
        (hC.afterReadC (.inl rfl) hg₁ hc₁ hU hY hop hw' hL hh)

/-- The decode of every value of the state. -/
theorem dec_of {α : Type} [Packed α 32]
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {G₁ : ThreadId → γ} {m₁ : Mem} (hI : C.Inv L G₁ m₁) :
    ∀ j < (C.S.hist m₁).size, ∀ b, (C.S.hist m₁)[j]!.Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r) :=
  fun j hj b hv => hdec b ((hI.sv j hj).cases hv)

/-- The waiter's relaxed load of the state with a decode (`atomicLoadAsC`, `Io.Condition`). -/
theorem wp_loadSAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok)
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {i jr : Nat} {sn : Bool} {e : BitVec 32} (hg : C.ph g = .reg i jr sn e) (hgo : L.ph g = .out)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b r, m'.current = t →
      (Packed.ofBits? (α := α) b).run = some (.ok r) → ((b = 1 ∧ sn = false) ∨ b = 0x10001) →
      P.inv (upd G₁ t g) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α .relaxed 4 C.S.ptr : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordLoadAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    (fun _ _ _ _ _ hU => dec_of hdec (hC.wInv _ _ _ hU))
    fun k hk G₁ rY m₁ m' b r j hg₁ hc₁ hU hY hd hj hv hfl _ hh hw' hop hL =>
      h k hk G₁ m' b r hop.current hd ((hC.wInv _ _ _ hU).readS (by rw [hg₁]; exact hg) hj hv hfl)
        (hC.afterReadC (.inl rfl) hg₁ hc₁ hU hY hop hw' hL hh)

/-- The waiter takes the signal: its successful `cmpxchg((1, 1) → (0, 0))` (`out`). -/
theorem _root_.Zig.Full.FLock.Fits.afterConsume (hC : L.Fits (C.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {i jr : Nat} {sn : Bool} {e : BitVec 32} {ord : AtomicOrder}
    (hg₁ : G₁ t = g) (hg : C.ph g = .reg i jr sn e) (hgo : L.ph g = .out) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hop : C.S.Op t m₁ m') (hw' : C.S.Ok m') (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hh : C.S.hist m' = (C.S.hist m₁).push (Word.rmwEnt m' t ord (C.lastS m₁) (0 : BitVec 32))) :
    P.inv (upd G₁ t (C.set g .out)) m' := by
  obtain ⟨hI, hnq⟩ := hC.atOp hU (by rw [hg₁, hgo]; decide) (by rw [hg₁, hgo]; decide) hop hL
  exact hC.backC (.inl rfl) hg₁ (by rw [hg]; exact True.intro) hU hY
    (mstep_op hc₁ hop hw' (.inr ⟨ord, 0, hh⟩)) (.inl (hC.keepE hU hop)) hL
    (hI.consume (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hg) (by rw [upd_self, C.ph_set]) hh
      hop.waiters hnq)

/-- The waiter's weak `cmpxchg((1, 1) → (0, 0))` (acquire) at `reg i jr sn e`, on bits
(`Thread.Condition`): on success it is out; on failure it read its `(1, 0)` or the signal. -/
theorem wp_consume (hC : L.Fits (C.prim L) P U ok) {succ fail : AtomicOrder}
    {exp new : BitVec 32} (hnew : new = 0) {i jr : Nat} {sn : Bool}
    {e : BitVec 32} (hg : C.ph g = .reg i jr sn e) (hgo : L.ph g = .out)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (C.set g .out)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b, ((b = 1 ∧ sn = false) ∨ b = 0x10001) → P.inv (upd G₁ t g) m' →
        Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakC (n := 32) succ fail 4 C.S.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  subst hnew
  exact FLock.wp_wordWeakCas hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hop hL => ⟨fun _ _ hh _ =>
      (h k hk G₁ m' hop.current).1 (hC.afterConsume hg₁ hg hgo hc₁ hU hY hop hw' hL hh),
      fun j b hj hv hfl _ hh => (h k hk G₁ m' hop.current).2 b
        ((hC.wInv _ _ _ hU).readS (by rw [hg₁]; exact hg) hj hv hfl)
        (hC.afterReadC (.inl rfl) hg₁ hc₁ hU hY hop hw' hL hh)⟩

/-- The waiter's weak `cmpxchg` with a decode (`cmpxchgWeakAsC`, `Io.Condition`). -/
theorem wp_consumeAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok)
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {succ fail : AtomicOrder} {exp new : α}
    (hnew : Packed.toBits new = (0 : BitVec 32)) {i jr : Nat} {sn : Bool} {e : BitVec 32}
    (hg : C.ph g = .reg i jr sn e) (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (C.set g .out)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b r, (Packed.ofBits? (α := α) b).run = some (.ok r) →
        ((b = 1 ∧ sn = false) ∨ b = 0x10001) → P.inv (upd G₁ t g) m' → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakAsC succ fail 4 C.S.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n :=
  FLock.wp_wordWeakCasAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    (fun _ _ _ _ _ hU => dec_of hdec (hC.wInv _ _ _ hU))
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hop hL => ⟨fun _ _ hh _ =>
      (h k hk G₁ m' hop.current).1 (hC.afterConsume hg₁ hg hgo hc₁ hU hY hop hw' hL
        (by rw [hh, hnew])),
      fun j b r hd hj hv hfl _ hh => (h k hk G₁ m' hop.current).2 b r hd
        ((hC.wInv _ _ _ hU).readS (by rw [hg₁]; exact hg) hj hv hfl)
        (hC.afterReadC (.inl rfl) hg₁ hc₁ hU hY hop hw' hL hh)⟩

/-- A signaller's read of the state at `out` after every registration (`hseen`). -/
theorem _root_.Zig.Full.FLock.Fits.afterReadSig (hC : L.Fits (C.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} (hg₁ : G₁ t = g) (hc₁ : m₁.current = t)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hop : C.S.Op t m₁ m') (hw' : C.S.Ok m') (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hh : C.S.hist m' = C.S.hist m₁) {j : Nat} {b : BitVec 32} (hj : j < (C.S.hist m₁).size)
    (hv : (C.S.hist m₁)[j]!.Val b) (hfl : Word.Floor (C.S.hist m₁) (m₁.clocks[t]!) j) :
    (b = 0 ∨ b = 1 ∨ b = 0x10001) ∧
      (b ≠ 1 → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e → C.Signalled m') ∧
      P.inv (upd G₁ t g) m' := by
  obtain ⟨h1, h2⟩ := (hC.wInv _ _ _ hU).readSig hj hv hfl (hseen G₁ _ m₁ hg₁ hU)
  refine ⟨h1, fun hb u i jr sn e hu => ?_, hC.afterReadC (.inl rfl) hg₁ hc₁ hU hY hop hw' hL hh⟩
  unfold FCond.Signalled FCond.lastS; rw [hh]; exact h2 hb u i jr sn e hu

/-- A signaller's relaxed load of the state at `out`, on bits (`Thread.Condition`). -/
theorem wp_sload (hC : L.Fits (C.prim L) P U ok) (hgo : L.ph g = .out)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b, m'.current = t → (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      (b ≠ 1 → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e → C.Signalled m') →
      P.inv (upd G₁ t g) m' → Q (b, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadC (n := 32) .relaxed 4 C.S.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n :=
  FLock.wp_wordLoad hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' b j hg₁ hc₁ hU hY hj hv hfl _ hh hw' hop hL =>
      let ⟨h1, h2, h3⟩ := hC.afterReadSig hg₁ hc₁ hseen hU hY hop hw' hL hh hj hv hfl
      h k hk G₁ m' b hop.current h1 h2 h3

/-- A signaller's relaxed load of the state with a decode (`atomicLoadAsC`, `Io.Condition`). -/
theorem wp_sloadAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok)
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    (hgo : L.ph g = .out)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' b r, m'.current = t →
      (Packed.ofBits? (α := α) b).run = some (.ok r) → (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      (b ≠ 1 → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e → C.Signalled m') →
      P.inv (upd G₁ t g) m' → Q (r, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicLoadAsC α .relaxed 4 C.S.ptr : CM Tgt σ α).run s) Q G m n :=
  FLock.wp_wordLoadAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    (fun _ _ _ _ _ hU => dec_of hdec (hC.wInv _ _ _ hU))
    fun k hk G₁ rY m₁ m' b r j hg₁ hc₁ hU hY hd hj hv hfl _ hh hw' hop hL =>
      let ⟨h1, h2, h3⟩ := hC.afterReadSig hg₁ hc₁ hseen hU hY hop hw' hL hh hj hv hfl
      h k hk G₁ m' b r hop.current hd h1 h2 h3

/-- A signaller's successful `cmpxchg((1, 0) → (1, 1))`: it is at `inc`. -/
theorem _root_.Zig.Full.FLock.Fits.afterSignal (hC : L.Fits (C.prim L) P U ok) {G₁ : ThreadId → γ}
    {rY : Res} {m₁ m' : Mem} {ord : AtomicOrder} (hg₁ : G₁ t = g) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out) (hsx : C.sx g) (hc₁ : m₁.current = t)
    (hU : U G₁ (rsum (C.S.cellsR m₁) rY) m₁) (hY : ∀ l, C.S.In l → rY.heap l = none)
    (hop : C.S.Op t m₁ m') (hw' : C.S.Ok m') (hL : L.Inv G₁ (rsum (C.S.cellsR m') rY) m')
    (hv : (C.lastS m₁).Val (1 : BitVec 32))
    (hh : C.S.hist m' = (C.S.hist m₁).push
      (Word.rmwEnt m' t ord (C.lastS m₁) (0x10001 : BitVec 32))) :
    P.inv (upd G₁ t (C.set g .inc)) m' := by
  have hI := hC.wInv _ _ _ hU
  exact hC.backC (.inl rfl) hg₁ (by rw [hgx]; exact True.intro) hU hY
    (mstep_op hc₁ hop hw' (.inr ⟨ord, _, hh⟩)) (.inl (hC.keepE hU hop)) hL
    (hI.signal (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hgx) (by rw [upd_self, C.ph_set])
      (by rw [upd_self, hC.lph]; exact hgo) (by rw [upd_self, C.sx_set]; exact hsx) hv hh
      (hC.keepE hU hop) hop.waiters hop.clocks)

/-- A signaller's weak `cmpxchg((1, 0) → (1, 1))` (release) at `out`, on bits
(`Thread.Condition`): on success it is at `inc`; on failure it read a value of the state, as
`wp_sload`. -/
theorem wp_signal (hC : L.Fits (C.prim L) P U ok) {succ fail : AtomicOrder}
    {exp new : BitVec 32} (hexp : exp = 1) (hnew : new = 0x10001) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out) (hsx : C.sx g)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) {Q : Option (BitVec 32) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (C.set g .inc)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
        (b ≠ 1 → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e → C.Signalled m') →
        P.inv (upd G₁ t g) m' → Q (some b, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakC (n := 32) succ fail 4 C.S.ptr exp new : CM Tgt σ _).run s) Q G m n := by
  subst hexp hnew
  exact FLock.wp_wordWeakCas hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hop hL => ⟨fun hv _ hh _ =>
      (h k hk G₁ m' hop.current).1 (hC.afterSignal hg₁ hgx hgo hsx hc₁ hU hY hop hw' hL hv hh),
      fun j b hj hv hfl _ hh =>
        let ⟨h1, h2, h3⟩ := hC.afterReadSig hg₁ hc₁ hseen hU hY hop hw' hL hh hj hv hfl
        (h k hk G₁ m' hop.current).2 b h1 h2 h3⟩

/-- A signaller's weak `cmpxchg` with a decode (`cmpxchgWeakAsC`, `Io.Condition`). -/
theorem wp_signalAs {α : Type} [Packed α 32] (hC : L.Fits (C.prim L) P U ok)
    (hdec : ∀ b : BitVec 32, (b = 0 ∨ b = 1 ∨ b = 0x10001) →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {succ fail : AtomicOrder} {exp new : α} (hexp : Packed.toBits exp = (1 : BitVec 32))
    (hnew : Packed.toBits new = (0x10001 : BitVec 32)) (hgx : C.ph g = .out)
    (hgo : L.ph g = .out) (hsx : C.sx g)
    (hseen : ∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true)
    (hi : P.inv (upd G t g) m) {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (P.inv (upd G₁ t (C.set g .inc)) m' → Q (none, s) G₁ m' k) ∧
      (∀ b r, (Packed.ofBits? (α := α) b).run = some (.ok r) → (b = 0 ∨ b = 1 ∨ b = 0x10001) →
        (b ≠ 1 → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e → C.Signalled m') →
        P.inv (upd G₁ t g) m' → Q (some r, s) G₁ m' k))
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((cmpxchgWeakAsC succ fail 4 C.S.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n :=
  FLock.wp_wordWeakCasAs hC (hC.wRest (.inl rfl)) (hC.wAp (.inl rfl)) (by rw [hgo]; decide) hi
    (fun _ _ _ _ _ hU => dec_of hdec (hC.wInv _ _ _ hU))
    fun k hk G₁ rY m₁ m' hg₁ hc₁ hU hY hw' hop hL => ⟨fun hv _ hh _ =>
      (h k hk G₁ m' hop.current).1 (hC.afterSignal hg₁ hgx hgo hsx hc₁ hU hY hop hw' hL
        (by rw [← hexp]; exact hv) (by rw [hh, hnew])),
      fun j b r hd hj hv hfl _ hh =>
        let ⟨h1, h2, h3⟩ := hC.afterReadSig hg₁ hc₁ hseen hU hY hop hw' hL hh hj hv hfl
        (h k hk G₁ m' hop.current).2 b r hd h1 h2 h3⟩

/-- The signaller's `epoch += 1` (release) at `inc`: it is at `wk`. -/
theorem wp_bump (hC : L.Fits (C.prim L) P U ok) (hg : C.ph g = .inc)
    (hgo : L.ph g = .out) (hi : P.inv (upd G t g) m)
    {Q : BitVec 32 × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m' o, m'.current = t → P.inv (upd G₁ t (C.set g .wk)) m' →
      Q (o, s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((atomicRmwC .add false .release 4 C.Ep.ptr (1 : BitVec 32) : CM Tgt σ (BitVec 32)).run s)
      Q G m n :=
  FLock.wp_wordRmw hC (hC.wRest (.inr rfl)) (hC.wAp (.inr rfl)) (by rw [hgo]; decide) hi
    fun k hk G₁ rY m₁ m' old hg₁ hc₁ hU hY hv _ hh _ hw' hop hL => by
      have hI := hC.wInv _ _ _ hU
      exact h k hk G₁ m' old hop.current (hC.backC (.inr rfl) hg₁ (by rw [hg]; exact True.intro)
        hU hY (mstep_op hc₁ hop hw' (.inr ⟨_, _, hh⟩)) (.inr hg) hL
        (hI.bump (fun u hu => upd_ne _ _ hu) (by rw [hg₁]; exact hg) (by rw [upd_self, C.ph_set])
          (by rw [upd_self, hC.lph, hg₁]) (fun h' => by rw [upd_self, C.sx_set, ← hg₁]; exact h')
          rfl hv hh (hC.keepS hU hop) hop.waiters hop.clocks))

/-- The signaller's wake at the epoch (`futexWakeC`, at least one waiter) at `wk`: it is out, and
a registered waiter was signalled. -/
theorem wp_wakeEp (hC : L.Fits (C.prim L) P U ok) {io : Io} {c : BitVec 32}
    (hc : 1 ≤ c.toNat) (hg : C.ph g = .wk) (hi : P.inv (upd G t g) m)
    {Q : Unit × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = t →
      (∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e → C.Signalled m') →
      P.inv (upd G₁ t (C.set g .out)) m' → Q ((), s) G₁ m' k)
    (hcost : P.cost = none := by first | rfl | assumption) :
    P.WP t ((futexWakeC io C.Ep.ptr c : CM Tgt σ Unit).run s) Q G m n :=
  FLock.wp_wordWake hC (hC.wAp (.inr rfl)) hi fun k hk G₁ rX m₁ cs m' hg₁ hU hw hL => by
    have hm' := Proto.modify_ok hw
    obtain ⟨-, rY, rfl, hY⟩ := (hC.wRest (.inr rfl)) _ _ _ hU
    have hI := hC.wInv _ _ _ hU
    have hcl : C.Ep.cellsR m' = C.Ep.cellsR m₁ := Word.cellsR_congr (by rw [hm'])
    have hEh : C.Ep.hist m' = C.Ep.hist m₁ := by rw [hm']; rfl
    have hSh : C.S.hist m' = C.S.hist m₁ := by rw [hm']; rfl
    refine h k hk G₁ m' (by rw [hm']) (fun u i jr sn e hu => ?_)
      (hC.backC (.inr rfl) hg₁ (by rw [hg]; exact True.intro) hU hY (.wake c.toNat cs hw)
        (.inl hEh) (by rw [hcl]; exact hL)
        (hI.wake (by rw [hg₁]; exact hg) (C.ph_set _ _) hc hw))
    have hr := hI.era u i jr sn e hu
    have hw2 := hI.wk t u i jr sn e (by rw [hg₁]; exact hg) hu
    rcases hr.esz with h1 | ⟨-, hs2, -⟩
    · omega
    · unfold FCond.Signalled FCond.lastS
      rw [hSh, hs2, show jr + 2 - 1 = jr + 1 by omega]; exact hr.s1 hs2

/-- `g` at the place it has. -/
theorem set_of {g : γ} {p : CPh} (h : C.ph g = p) : C.set g p = g := h ▸ C.set_self g

/-- The epoch's pointer is the condition's plus 4. -/
theorem ptr_ep : C.S.ptr.add 4 = C.Ep.ptr := by
  simp only [Word.ptr, Ptr.add, C.ep_b, C.ep_o]; congr 1

/-- The epoch's pointer is formed from the condition's (`&cond.epoch`, MM-3). -/
theorem _root_.Zig.Full.FLock.Fits.projE (hC : L.Fits (C.prim L) P U ok) {G : ThreadId → γ} {m : Mem}
    (hi : P.inv G m) : (ptrProject C.S.ptr (·.add 4)).run m = pure (C.S.ptr.add 4, m) := by
  obtain ⟨rX, -, hU⟩ := (hC.inv _ _).mp hi
  obtain ⟨blk, hblk, -, hsz, -⟩ := ((hC.wRest (.inr rfl)) _ _ _ hU).1.blk
  rw [C.ep_b] at hblk
  have := C.ep_o
  exact ptrProject_add_run (inBounds_of (b := C.S.b) rfl hblk (by simp [Word.ptr])
    (by simp [Word.ptr]; omega)) (inBounds_of (b := C.S.b) rfl hblk
    (by simp [Word.ptr, Ptr.add]; omega) (by simp [Word.ptr, Ptr.add]; omega))

/-- A byte of the epoch is not the state's. -/
theorem ep_notS {l : Zig.Loc} (hl : C.Ep.In l) : ¬ C.S.In l := by
  obtain ⟨-, h2, -⟩ := hl
  rintro ⟨-, -, h3⟩
  have := C.ep_o
  omega

/-- **A step of a thread on its own part** in the condition's code (`g`, out of the lock's code
or holding the lock; a stack block: `allocStack`, its stores and loads, `free`), with a thread
triple: its part becomes the triple's post (`FLock.setPart`; `Fits.wOwn`), and both words keep
their writes. -/
theorem wp_liftPart (hC : L.Fits (C.prim L) P U ok) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      C.S.hist m' = C.S.hist m → C.Ep.hist m' = C.Ep.hist m →
      P.inv (upd G t (L.setPart g r')) m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  FLock.wp_liftPartW hC (hC.wRest (.inl rfl)) hgo hi hc htt hp
    (fun a m' r' rY hr hq hc' hU hL hY hs hk hL' => by
      have hhS := Word.hist_keepK ((hC.wRest (.inl rfl)) _ _ _ hU).1 hk
      -- the epoch's cells are in `rY`; they stay
      obtain ⟨hwE, rY', hrX, hY'⟩ := (hC.wRest (.inr rfl)) _ _ _ hU
      have hcE : ∀ l, C.Ep.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
        intro l hl
        have hS0 : ∀ m₀ : Mem, (C.S.cellsR m₀).heap l = none := fun _ => cellsAt_none (ep_notS hl)
        cases e : m.heap l with
        | none => exact absurd e (hwE.cellIn hl)
        | some c =>
          have hYl : rY.heap l = some ⟨c, none⟩ := by
            have := congrArg (fun r : Res => r.heap l) hrX
            simpa [FHeap.union_apply, hS0, Word.cellsR, cellsAt_of hl, e, hY' l hl] using this
          rw [hL'.restCell (fc := ⟨c, none⟩) (by simp [FHeap.union_apply, hS0, hYl])]; rfl
      have hwF : ∀ l, C.Ep.In l →
          (rsum (L.wordR m) (rsum (C.S.cellsR m) rY)).heap.erase l ≠ none := fun l hl => by
        have := cellsAt_some hl (hwE.cellIn hl) (m := m)
        rw [hrX]
        simp only [rsum, FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
          Option.or_eq_none_iff, not_and]
        intro _ h; exact absurd h this
      have hhE := Word.hist_keepK hwE
        (Word.keepK_fstep hs hwF (fun i l hl => (hwE.loc i l hl).1) hcE)
      have hI' : C.Inv L (upd G t (L.setPart g r')) m' := by
        have := (hC.wInv _ _ _ hU).frame (t := t) (g' := L.setPart g r')
          (by rw [upd_self, hC.ph_part]) (by rw [upd_self, L.ph_setPart])
          (fun h => by rw [upd_self] at h; exact (hC.role_part () _ _).mpr h) hhS hhE
          (hC.wAp (.inr rfl)).ptr_ne hs.waiters hs.clock
        rwa [upd_upd] at this
      have hU' := hC.wOwn (G := upd G t g) (t := t) (r := r') (.inl rfl)
        (by rw [upd_self]; exact hgo) hU hL hY hc hs hk (by rw [upd_self, upd_upd]; exact hL')
        (by rw [upd_self, upd_upd]; exact hI')
      rw [upd_self, upd_upd] at hU'
      exact h a m' r' hr hq hc' hhS hhE ((hC.inv _ _).mpr ⟨_, hL', hU'⟩)) hret

/-- `wp_liftPart` for a step of generated code (`liftM`). -/
theorem wp_liftPartM (hC : L.Fits (C.prim L) P U ok) {α : Type} {x : MemM α}
    {Pa : FAssn} {Qa : α → FAssn} {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (hgo : L.ph g = .out ∨ L.ph g = .holds) (hi : P.inv (upd G t g) m) (hc : m.current = t)
    (htt : FTTriple Pa x Qa) (hp : Pa (L.part g))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → Qa a r' → m'.current = t →
      C.S.hist m' = C.S.hist m → C.Ep.hist m' = C.Ep.hist m →
      P.inv (upd G t (L.setPart g r')) m' → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((liftM x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (wp_liftPart hC hgo hi hc htt hp (fun a m' r' hr hq hc' hS hE hi' =>
    WP.pure' (h a m' r' hr hq hc' hS hE hi')) hret)

end FCond

/-- **A condition implementation** in generated code: `wait(cond, io, mutex)` and
`signal(cond, io)` with the rules that a client uses, for every protocol that has the condition
next to its mutex (`L.Fits (C.prim L) P U ok`; the mutex's contended value `c`) and counts no
turns.

- `wait_wp`: the mutex's holder, out of the condition's code, that waits returns holding the
  mutex again (after it took a signal). It enters only when every other thread is out of the
  condition's code and after every epoch write (`hone`, `hhb`: the scope of the module doc), the
  client's rest allows its entry (`hent`), and the client shows that its sleep at a condition
  that is not signalled is not a deadlock (`hlive`). The waiter is the running thread
  (`m.current = t`), the same premise and reason as `MutexImpl.unlock_wp`: the waiter holds the
  mutex, which only the running thread can (Zig's `Thread.mutexOwnerCheck`), and every client has
  the fact from its previous step (the lock's post). `Thread.Condition.wait` (0.15.2) needs it:
  it allocates its deadline block, a memory step with no stop before it, first. So the premise is
  the contract of every Zig condition, not a restriction of this one.
- `signal_wp`: a thread out of the condition's and the lock's code that may signal, whose stops
  come after every registration (`hseen`), returns out of the condition's code; a registered
  waiter is then signalled. -/
structure CondImpl (Tgt : Type) where
  wait : Ptr → Io → Ptr → ConcM Tgt Unit
  signal : Ptr → Io → ConcM Tgt Unit
  /-- The contended value of the mutex that `wait` unlocks and locks. -/
  c : Nat
  wait_wp : ∀ {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits (C.prim L) P U ok →
    P.cost = none → ∀ {p q : Ptr}, p = C.S.ptr → q = L.ptr → L.c = c →
    ∀ (t : ThreadId) (g : γ), C.ph g = .out → L.ph g = .holds → ok g →
    ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    (∀ u, u ≠ t → C.ph (G u) = .out) →
    (∀ j < (C.Ep.hist m).size, VClock.le (C.Ep.hist m)[j]!.clock (m.clocks[t]!) = true) →
    (∀ rX, U (upd G t g) rX m → C.Inv L (upd G t (C.set g .en)) m →
      U (upd G t (C.set g .en)) rX m) →
    (∀ G₁ m₁, (∃ i jr e, C.ph (G₁ t) = .reg i jr false e) → L.ph (G₁ t) = .away →
      P.inv G₁ m₁ → ¬ C.Signalled m₁ → P.Live t G₁ m₁) →
    P.inv (upd G t g) m → m.current = t →
    P.WP t (wait p io q) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
      ∃ rL, P.inv (upd G' t (L.set g .holds rL)) m') G m d
  signal_wp : ∀ {γ : Type} {L : FLock γ} {C : FCond γ} {P : Proto Tgt γ}
    {U : (ThreadId → γ) → Res → Mem → Prop} {ok : γ → Prop}, L.Fits (C.prim L) P U ok →
    P.cost = none → ∀ {p : Ptr}, p = C.S.ptr → ∀ (t : ThreadId) (g : γ), C.ph g = .out →
    L.ph g = .out → C.sx g → ∀ (io : Io) (G : ThreadId → γ) (m : Mem) (d : Nat),
    (∀ G₁ rX m₁, G₁ t = g → U G₁ rX m₁ → ∀ u i jr sn e, C.ph (G₁ u) = .reg i jr sn e →
      VClock.le (C.S.hist m₁)[jr]!.clock (m₁.clocks[t]!) = true) →
    P.inv (upd G t g) m →
    P.WP t (signal p io) (fun _ G' m' d' => d' < d ∧ m'.current = t ∧ P.inv (upd G' t g) m' ∧
      ∀ u i jr sn e, C.ph (G' u) = .reg i jr sn e → C.Signalled m') G m d

end Full
end Zig
