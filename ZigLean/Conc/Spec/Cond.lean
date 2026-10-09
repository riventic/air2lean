import ZigLean.Conc.Spec.Count
import ZigLean.Conc.Spec.IoMutex

/-!
# The condition-variable contract (`CondSpec`), and std's `Io.Condition` with `Io.Mutex`
satisfies it over every futex that satisfies `FutexSpec`

`std.Io.Condition` (Zig 0.16.0 `lib/std/Io.zig:1653`; `Io.Threaded.condWait`/`condSignal`/
`condBroadcast` at `Io/Threaded.zig:18652` are the same code without the vtable), with Mesa
semantics: a `wait` may return without a signal, and a later waiter may take a signal, so a
client re-checks its predicate.

**The most general client** (`cmgc I X N`): threads `0 … N-1`, for every `N`. Each thread is
idle, holds the mutex, or runs an op of the implementation `I`, which is the mutex and the
condition together (a `wait` releases and re-takes the mutex):

* an idle thread calls `lock` or `tryLock`; a holder calls `unlock` or `wait`, or writes the
  resource (as in `MutexSpec`);
* any thread calls `signal` or `broadcast`, holding the mutex or not (`Io.Threaded` signals after
  `mutexUnlock`; the op records which, `signal h`);
* a thread in an op takes the implementation's steps and returns (`lock`, a successful
  `tryLock` and `wait` return holding the mutex).

**Obligations** (ghost). The mutex's acquisitions are numbered (`gen`); `seen t` is the number
of thread `t`'s last acquisition, and `wgen u` the number current when `u` called `wait`. A
`wait` of `u` with `wgen u < seen t` was called before `t`'s last acquisition, so it happens
before every later op of `t`: it is **eligible** for `t`'s signals (`elig`). A `signal` call
raises the count of owed returns `O` by one if fewer are owed than there are eligible waiters,
a `broadcast` raises it to their number, and a return from `wait` pays one. A waiter that called
`wait` after the signaler's last acquisition races with the signal and is owed nothing; a later
waiter may still take a signal (std's `signals` counter allows it), which pays the debt as well.

**The contract** (`CondSpec I M B`):

| clause | statement |
|---|---|
| `excl` | at most one thread holds the mutex |
| `view` | a holder's view is the real value (ownership transfer, also through `wait`) |
| `live` | for at most `M` threads: no deadlock while a thread runs an op other than `wait` |
| `wake` | for at most `M` threads and fewer than `B` `signal`/`broadcast` calls: no lost wakeup — if a return is owed and no thread holds the mutex, some thread in an op can step |

`ioCond_spec (hF : FutexSpec condView Fx) : CondSpec (ioCond Fx) 65535 (2 ^ 32)`. The two bounds
are std's: `wait` asserts `waiters < maxInt(u16)`, and a waiter that loaded the epoch misses a
signal if exactly a multiple of `2^32` epoch increments happen before it sleeps on the loaded
value (the comment in `condSignal`: "extraordinarily unlikely"). The proof keeps the epoch as an
unbounded number whose low 32 bits are the futex word, so the futex compares modulo `2^32`.

The mutex part of the proof is `IoMutex.lean`'s invariant: the state of the mutex, seen as a
most general client of `Io.Mutex` (`CState.proj`), makes only `Io.Mutex` steps, over the futex
restricted to the mutex word (`Futex.atMtx`, which satisfies the safety part of the contract).
The condition part (`CEp`) counts: the signals pending (`signals`) are at most the waiters that
are awake and will see a new epoch, plus the signalers that have not bumped the epoch, plus the
waiters a pending wake can reach (`min W Q`). The cond words' own acquire/release edges are not
modelled: the resource moves only through the mutex, so the model's views are a lower bound of
the real ones.
-/

namespace Zig
namespace Spec

/-! ## The contract -/

/-- The ops of a mutex with a condition variable. `h`: the caller holds the mutex. -/
inductive COp where
  | lock
  | tryLock
  | unlock
  | wait
  | signal (h : Bool)
  | broadcast (h : Bool)
  deriving DecidableEq, Repr

/-- A thread of the condition's most general client. -/
inductive CCtl (L : Type) where
  | idle
  | holds
  | run (op : COp) (l : L)
  deriving DecidableEq

/-- What a thread is after op `op` returned `b`. -/
def COp.after {L : Type} : COp → Bool → CCtl L
  | .lock, _ => .holds
  | .tryLock, b => if b then .holds else .idle
  | .unlock, _ => .idle
  | .wait, _ => .holds
  | .signal h, _ | .broadcast h, _ => if h then .holds else .idle

/-- The return of op `op` with `b` acquires the mutex. -/
def COp.acq : COp → Bool → Bool
  | .lock, _ | .wait, _ => true
  | .tryLock, b => b
  | _, _ => false

/-- The returns owed after a `signal`/`broadcast` call, with `E` eligible waiters (module doc). -/
def COp.owe (op : COp) (O E : Nat) : Nat :=
  match op with
  | .signal _ => if O < E then O + 1 else O
  | .broadcast _ => max O E
  | _ => O

/-- The thread waits (it runs `wait`). -/
def CCtl.waiting {L : Type} : CCtl L → Bool
  | .run .wait _ => true
  | _ => false

/-- A state of the condition's most general client. -/
structure CState (I : Impl COp) (X : Type) where
  sh : I.Sh X
  ctl : Tid → CCtl I.Loc
  cur : Tid → X
  val : X
  /-- The number of the mutex's acquisitions (ghost). -/
  gen : Nat
  /-- The number of each thread's last acquisition (ghost). -/
  seen : Tid → Nat
  /-- The number current at each thread's last `wait` call (ghost). -/
  wgen : Tid → Nat
  /-- The returns from `wait` owed (ghost). -/
  O : Nat
  /-- The `signal`/`broadcast` calls (ghost). -/
  calls : Nat

/-- The waiters eligible for thread `t`'s signals (module doc). -/
def CState.elig {I : Impl COp} {X : Type} (N : Nat) (s : CState I X) (t : Tid) : Nat :=
  tsum N fun u => if (s.ctl u).waiting && decide (s.wgen u < s.seen t) then 1 else 0

/-- A step of thread `t` of the condition's most general client (module doc). -/
inductive CStep (I : Impl COp) {X : Type} (N : Nat) (t : Tid) : CState I X → CState I X → Prop
  | call {s : CState I X} (op : COp) (hop : op = .lock ∨ op = .tryLock) (h : s.ctl t = .idle) :
      CStep I N t s { s with ctl := tset s.ctl t (.run op (I.start op)) }
  | unlock {s : CState I X} (h : s.ctl t = .holds) :
      CStep I N t s { s with ctl := tset s.ctl t (.run .unlock (I.start .unlock)) }
  | wait {s : CState I X} (h : s.ctl t = .holds) :
      CStep I N t s { s with ctl := tset s.ctl t (.run .wait (I.start .wait)), wgen := tset s.wgen t s.gen }
  | notify {s : CState I X} (op : COp) {h : Bool} (hop : op = .signal h ∨ op = .broadcast h)
      (hc : s.ctl t = if h then .holds else .idle) :
      CStep I N t s { s with
        ctl := tset s.ctl t (.run op (I.start op))
        O := op.owe s.O (s.elig N t)
        calls := s.calls + 1 }
  | write {s : CState I X} (x : X) (h : s.ctl t = .holds) :
      CStep I N t s { s with cur := tset s.cur t x, val := x }
  | exec {s : CState I X} {op : COp} {l l' : I.Loc} {sh' : I.Sh X} {v' : X}
      (h : s.ctl t = .run op l) (hs : I.step t l s.sh (s.cur t) l' sh' v') :
      CStep I N t s { s with sh := sh', ctl := tset s.ctl t (.run op l'), cur := tset s.cur t v' }
  | ret {s : CState I X} {op : COp} {l : I.Loc} {b : Bool}
      (h : s.ctl t = .run op l) (hd : I.done l = some b) :
      CStep I N t s { s with
        ctl := tset s.ctl t (op.after b)
        gen := if op.acq b then s.gen + 1 else s.gen
        seen := if op.acq b then tset s.seen t (s.gen + 1) else s.seen
        O := if op = .wait then s.O - 1 else s.O }

/-- The condition's most general client with `N` threads. -/
abbrev cmgc (I : Impl COp) (X : Type) (N : Nat) : Sys where
  St := CState I X
  init s := ∃ x₀, I.init x₀ s.sh ∧ (∀ t, s.ctl t = .idle) ∧ (∀ t, s.cur t = x₀) ∧ s.val = x₀ ∧
    s.gen = 0 ∧ (∀ t, s.seen t = 0) ∧ (∀ t, s.wgen t = 0) ∧ s.O = 0 ∧ s.calls = 0
  step t s s' := t < N ∧ CStep I N t s s'

/-- A deadlock with an op other than `wait` pending: no thread holds the mutex, a thread runs a
`lock`, `tryLock`, `unlock`, `signal` or `broadcast`, and no thread in an op can step. -/
def CStuck (I : Impl COp) {X : Type} (N : Nat) (s : CState I X) : Prop :=
  (∀ t, s.ctl t ≠ .holds) ∧ (∃ t op l, s.ctl t = .run op l ∧ op ≠ .wait) ∧
    ∀ t op l, s.ctl t = .run op l → ¬ (cmgc I X N).Enabled t s

/-- A lost wakeup: a return from `wait` is owed, no thread holds the mutex, and no thread in an
op can step. -/
def CLost (I : Impl COp) {X : Type} (N : Nat) (s : CState I X) : Prop :=
  (∀ t, s.ctl t ≠ .holds) ∧ 0 < s.O ∧ ∀ t op l, s.ctl t = .run op l → ¬ (cmgc I X N).Enabled t s

/-- The condition-variable contract (module doc). -/
structure CondSpec (I : Impl COp) (M B : Nat) : Prop where
  excl : ∀ X N, (cmgc I X N).Invariant fun s => ∀ t u, s.ctl t = .holds → s.ctl u = .holds → t = u
  view : ∀ X N, (cmgc I X N).Invariant fun s => ∀ t, s.ctl t = .holds → s.cur t = s.val
  live : ∀ X N, N ≤ M → (cmgc I X N).Invariant fun s => ¬ CStuck I N s
  wake : ∀ X N, N ≤ M → (cmgc I X N).Invariant fun s => s.calls < B → ¬ CLost I N s

/-! ## The futex of the mutex and the epoch -/

/-- The two futex words: the mutex's state and the condition's epoch. -/
inductive CA where
  | mtx
  | ep
  deriving DecidableEq, Repr

/-- The futex's view of the memory `(mutex word, epoch)`: the epoch's `u32` is its low 32 bits. -/
def condView (m : Nat × Nat) : CA → Option (BitVec 32)
  | .mtx => some (BitVec.ofNat 32 m.1)
  | .ep => some (BitVec.ofNat 32 m.2)

/-- The waiters at the mutex word, as a queue of `Futex.atMtx`. -/
def mtxQ (q : Queue CA) : Queue Unit := (q.filter (·.2 == .mtx)).map fun x => (x.1, ())

theorem mem_mtxQ {q : Queue CA} {u : Tid} : (u, ()) ∈ mtxQ q ↔ (u, CA.mtx) ∈ q := by
  unfold mtxQ
  simp only [List.mem_map, List.mem_filter, beq_iff_eq, Prod.mk.injEq, and_true]
  constructor
  · rintro ⟨⟨x, a⟩, ⟨hx, ha⟩, rfl⟩; simp only at ha; subst ha; exact hx
  · intro h; exact ⟨(u, .mtx), ⟨h, rfl⟩, rfl⟩

theorem mtxQ_perm {q q' : Queue CA} (h : q'.Perm q) : (mtxQ q').Perm (mtxQ q) :=
  (h.filter _).map _

theorem mtxQ_append (q : Queue CA) (t : Tid) : mtxQ (q ++ [(t, .mtx)]) = mtxQ q ++ [(t, ())] := by
  simp [mtxQ, List.filter_append]

theorem mtxQ_append_ep (q : Queue CA) (t : Tid) : mtxQ (q ++ [(t, .ep)]) = mtxQ q := by
  simp [mtxQ, List.filter_append]

theorem mtxQ_drop (q : Queue CA) (ws : List Tid) : mtxQ (q.drop ws) = (mtxQ q).drop ws := by
  unfold mtxQ Queue.drop
  rw [List.filter_map, List.filter_filter, List.filter_filter]
  congr 2
  funext x
  simp [Function.comp, Bool.and_comm]

theorem waitersAt_mtxQ (q : Queue CA) : (mtxQ q).waitersAt () = q.waitersAt .mtx := by
  unfold Queue.waitersAt mtxQ
  rw [List.filter_map, List.map_map]
  simp [Function.comp]

theorem mtxQ_wf {q : Queue CA} (h : q.WF) : (mtxQ q).WF := by
  unfold Queue.WF mtxQ at *
  rw [List.map_map]
  exact (List.filter_sublist.map _).nodup h

/-- The futex restricted to the mutex word (`Io.Mutex`'s futex inside the condition). -/
abbrev Futex.atMtx (Fx : Futex (Nat × Nat) CA) : Futex Nat Unit where
  F := Fx.F
  init := Fx.init
  queue f := mtxQ (Fx.queue f)
  wait t _ e tm n f r f' := ∃ ep, Fx.wait t .mtx e tm (n, ep) f r f'
  resume := Fx.resume
  wake t _ n f f' := (Fx.queue f).WF ∧ Fx.wake t .mtx n f f'

/-- **The restriction to the mutex word keeps the safety part of the futex contract.** -/
theorem FutexSafe.atMtx {Fx : Futex (Nat × Nat) CA} (h : FutexSafe condView Fx) :
    FutexSafe wordView Fx.atMtx where
  init f hf := by show mtxQ _ = []; rw [h.init f hf]; rfl
  wait_word t _ e tm n f r f' := by
    rintro ⟨ep, hw⟩
    obtain ⟨v, hv, he⟩ := h.wait_word _ _ _ _ _ _ _ _ hw
    exact ⟨v, hv, he⟩
  wait_local t _ e tm n n' f r f' hW := by
    rintro ⟨ep, hw⟩
    exact ⟨ep, h.wait_local t .mtx e tm (n, ep) (n', ep) f r f' hW hw⟩
  wait_sleep t _ e tm n f f' := by
    rintro ⟨ep, hw⟩
    have := mtxQ_perm (h.wait_sleep _ _ _ _ _ _ _ hw)
    rwa [mtxQ_append] at this
  wait_ret t _ e tm n f r f' := by
    rintro ⟨ep, hw⟩
    obtain ⟨hp, ht⟩ := h.wait_ret _ _ _ _ _ _ _ _ hw
    exact ⟨mtxQ_perm hp, ht⟩
  resume t tm f r f' hr := by
    obtain ⟨hp, ht⟩ := h.resume _ _ _ _ _ hr
    refine ⟨?_, ht⟩
    have := mtxQ_perm hp
    rwa [mtxQ_drop] at this
  wake t _ n f f' _ := by
    rintro ⟨hwf, hk⟩
    obtain ⟨ws, hnd, hws, hlen, hp⟩ := h.wake _ _ _ _ _ hwf hk
    refine ⟨ws, hnd, fun u hu => mem_mtxQ.mpr (hws u hu), ?_, ?_⟩
    · show min n ((mtxQ _).waitersAt ()).length ≤ _
      rw [waitersAt_mtxQ]; exact hlen
    · have := mtxQ_perm hp
      rwa [mtxQ_drop] at this

/-! ## `Io.Condition` with `Io.Mutex` -/

/-- The shared state: the mutex word (with the view of its newest message), the condition's
`state` (`waiters`, `signals`), its `epoch` (an unbounded number; the futex word is its low 32
bits) and the futex. -/
structure CSh (Fx : Futex (Nat × Nat) CA) (X : Type) where
  m : AWord X
  w : Nat
  sg : Nat
  ep : Nat
  f : Fx.F

/-- The places in the code. `e`: the epoch that the waiter loaded; `bc`: a `broadcast`. -/
inductive CL where
  /-- `lock`, `tryLock`, `unlock`: `Io.Mutex`'s code. -/
  | m (l : IL)
  /-- `wait`'s `epoch.load(.acquire)` at its start. -/
  | le0
  /-- `wait`'s `state.fetchAdd(.{ .waiters = 1 }, .monotonic)`. -/
  | add (e : Nat)
  /-- `wait`'s `mutex.unlock()`. -/
  | wu (e : Nat) (l : IL)
  /-- `wait`'s `futexWaitUncancelable(&epoch, e)`, before the futex op. -/
  | fw (e : Nat)
  /-- In that futex wait: the thread went to sleep. -/
  | sleep (e : Nat)
  /-- `wait`'s `epoch.load(.acquire)` after the futex wait. -/
  | le
  /-- `wait`'s `state.load(.monotonic)`. -/
  | ls (e : Nat)
  /-- `wait`'s `cmpxchgWeak` that takes a signal, expecting `(w, s)`. -/
  | cx (e w s : Nat)
  /-- `wait`'s `mutex.lockUncancelable()` (the `defer`). -/
  | wl (l : IL)
  /-- `signal`/`broadcast`'s `state.load(.monotonic)`. -/
  | sld (bc : Bool)
  /-- Its `cmpxchgWeak`, expecting `(w, s)`. -/
  | scx (bc : Bool) (w s : Nat)
  /-- Its `epoch.fetchAdd(1, .release)`, before waking `n`. -/
  | bump (n : Nat)
  /-- Its `futexWake(&epoch, n)`. -/
  | swake (n : Nat)
  /-- A `signal`/`broadcast` returned. -/
  | fin
  deriving DecidableEq

/-- The atomic steps of the code over the futex `Fx`, by thread `t` with view `v`. The mutex's
code is `IoStep` over the restricted futex; `wait`'s assertion `waiters < maxInt(u16)` has no
step when it fails. -/
inductive CondStep (Fx : Futex (Nat × Nat) CA) {X : Type} (t : Tid) :
    CL → CSh Fx X → X → CL → CSh Fx X → X → Prop
  | mtx {l l' : IL} {sh : CSh Fx X} {v : X} {w' : AWord X} {f' : Fx.F} {v' : X} :
      IoStep Fx.atMtx t l sh.m sh.f v l' (w', f') v' →
      CondStep Fx t (.m l) sh v (.m l') { sh with m := w', f := f' } v'
  | wum {e : Nat} {l l' : IL} {sh : CSh Fx X} {v : X} {w' : AWord X} {f' : Fx.F} {v' : X} :
      IoStep Fx.atMtx t l sh.m sh.f v l' (w', f') v' →
      CondStep Fx t (.wu e l) sh v (.wu e l') { sh with m := w', f := f' } v'
  | wlm {l l' : IL} {sh : CSh Fx X} {v : X} {w' : AWord X} {f' : Fx.F} {v' : X} :
      IoStep Fx.atMtx t l sh.m sh.f v l' (w', f') v' →
      CondStep Fx t (.wl l) sh v (.wl l') { sh with m := w', f := f' } v'
  | le0 {sh : CSh Fx X} {v : X} : CondStep Fx t .le0 sh v (.add sh.ep) sh v
  | add {e : Nat} {sh : CSh Fx X} {v : X} : sh.w < 65535 →
      CondStep Fx t (.add e) sh v (.wu e .rel) { sh with w := sh.w + 1 } v
  | wuDone {e : Nat} {sh : CSh Fx X} {v : X} : CondStep Fx t (.wu e (.fin false)) sh v (.fw e) sh v
  | fwSleep {e : Nat} {sh : CSh Fx X} {v : X} {f' : Fx.F} :
      Fx.wait t .ep (BitVec.ofNat 32 e) false (sh.m.val, sh.ep) sh.f none f' →
      CondStep Fx t (.fw e) sh v (.sleep e) { sh with f := f' } v
  | fwRet {e : Nat} {sh : CSh Fx X} {v : X} {f' : Fx.F} {r : WaitRet} :
      Fx.wait t .ep (BitVec.ofNat 32 e) false (sh.m.val, sh.ep) sh.f (some r) f' →
      CondStep Fx t (.fw e) sh v .le { sh with f := f' } v
  | resume {e : Nat} {sh : CSh Fx X} {v : X} {f' : Fx.F} {r : WaitRet} :
      Fx.resume t false sh.f r f' → CondStep Fx t (.sleep e) sh v .le { sh with f := f' } v
  | le {sh : CSh Fx X} {v : X} : CondStep Fx t .le sh v (.ls sh.ep) sh v
  | lsPos {e : Nat} {sh : CSh Fx X} {v : X} : 0 < sh.sg →
      CondStep Fx t (.ls e) sh v (.cx e sh.w sh.sg) sh v
  | lsZero {e : Nat} {sh : CSh Fx X} {v : X} : sh.sg = 0 → CondStep Fx t (.ls e) sh v (.fw e) sh v
  | cxOk {e w s : Nat} {sh : CSh Fx X} {v : X} : sh.w = w → sh.sg = s →
      CondStep Fx t (.cx e w s) sh v (.wl .cas) { sh with w := w - 1, sg := s - 1 } v
  | cxSpur {e w s : Nat} {sh : CSh Fx X} {v : X} : sh.w = w → sh.sg = s →
      CondStep Fx t (.cx e w s) sh v (.cx e w s) sh v
  | cxFailPos {e w s : Nat} {sh : CSh Fx X} {v : X} : (sh.w ≠ w ∨ sh.sg ≠ s) → 0 < sh.sg →
      CondStep Fx t (.cx e w s) sh v (.cx e sh.w sh.sg) sh v
  | cxFailZero {e w s : Nat} {sh : CSh Fx X} {v : X} : (sh.w ≠ w ∨ sh.sg ≠ s) → sh.sg = 0 →
      CondStep Fx t (.cx e w s) sh v (.fw e) sh v
  | sldGo {bc : Bool} {sh : CSh Fx X} {v : X} : sh.sg < sh.w →
      CondStep Fx t (.sld bc) sh v (.scx bc sh.w sh.sg) sh v
  | sldDone {bc : Bool} {sh : CSh Fx X} {v : X} : sh.w ≤ sh.sg →
      CondStep Fx t (.sld bc) sh v .fin sh v
  | scxOk {bc : Bool} {w s : Nat} {sh : CSh Fx X} {v : X} : sh.w = w → sh.sg = s →
      CondStep Fx t (.scx bc w s) sh v (.bump (if bc then w - s else 1))
        { sh with sg := if bc then w else s + 1 } v
  | scxSpur {bc : Bool} {w s : Nat} {sh : CSh Fx X} {v : X} : sh.w = w → sh.sg = s →
      CondStep Fx t (.scx bc w s) sh v (.scx bc w s) sh v
  | scxFailGo {bc : Bool} {w s : Nat} {sh : CSh Fx X} {v : X} : (sh.w ≠ w ∨ sh.sg ≠ s) →
      sh.sg < sh.w → CondStep Fx t (.scx bc w s) sh v (.scx bc sh.w sh.sg) sh v
  | scxFailDone {bc : Bool} {w s : Nat} {sh : CSh Fx X} {v : X} : (sh.w ≠ w ∨ sh.sg ≠ s) →
      sh.w ≤ sh.sg → CondStep Fx t (.scx bc w s) sh v .fin sh v
  | bump {n : Nat} {sh : CSh Fx X} {v : X} :
      CondStep Fx t (.bump n) sh v (.swake n) { sh with ep := sh.ep + 1 } v
  | swake {n : Nat} {sh : CSh Fx X} {v : X} {f' : Fx.F} : Fx.wake t .ep n sh.f f' →
      CondStep Fx t (.swake n) sh v .fin { sh with f := f' } v

/-- `Io.Condition` with `Io.Mutex` over the futex `Fx` (module doc). -/
abbrev ioCond (Fx : Futex (Nat × Nat) CA) : Impl COp where
  Sh X := CSh Fx X
  init x₀ sh := sh.m = ⟨0, x₀⟩ ∧ sh.w = 0 ∧ sh.sg = 0 ∧ sh.ep = 0 ∧ Fx.init sh.f
  Loc := CL
  start
    | .lock => .m .cas
    | .tryLock => .m .attempt
    | .unlock => .m .rel
    | .wait => .le0
    | .signal _ => .sld false
    | .broadcast _ => .sld true
  step t l sh v l' sh' v' := CondStep Fx t l sh v l' sh' v'
  done
    | .m (.fin b) => some b
    | .wl (.fin true) => some true
    | .fin => some false
    | _ => none

/-! ## The mutex, seen as a client of `Io.Mutex` -/

/-- What a thread is for the mutex. -/
def projCtl : CCtl CL → Ctl IL
  | .idle => .idle
  | .holds => .holds
  | .run .lock (.m l) => .run .lock l
  | .run .tryLock (.m l) => .run .tryLock l
  | .run .unlock (.m l) => .run .unlock l
  | .run .wait .le0 | .run .wait (.add _) => .holds
  | .run .wait (.wu _ l) => .run .unlock l
  | .run .wait (.wl l) => .run .lock l
  | .run (.signal h) _ | .run (.broadcast h) _ => if h then .holds else .idle
  | _ => .idle

variable {Fx : Futex (Nat × Nat) CA}

/-- The state of the mutex as a state of `Io.Mutex`'s most general client. -/
def CState.proj {X : Type} (s : CState (ioCond Fx) X) : MState (ioMutex Fx.atMtx) X :=
  ⟨(s.sh.m, s.sh.f), fun u => projCtl (s.ctl u), s.cur, s.val⟩

/-! ## The invariant -/

namespace CPlace

/-- `lock`'s places in `Io.Mutex`'s code. -/
def lockL : IL → Bool
  | .cas | .xchg | .wait | .asleep | .fin true => true
  | _ => false

/-- `tryLock`'s places. -/
def tryL : IL → Bool
  | .attempt | .fin _ => true
  | _ => false

/-- `unlock`'s places. -/
def unlL : IL → Bool
  | .rel | .wake | .fin false => true
  | _ => false

/-- The places that a thread can be at. -/
def ok : CCtl CL → Bool
  | .idle | .holds => true
  | .run .lock (.m l) => lockL l
  | .run .tryLock (.m l) => tryL l
  | .run .unlock (.m l) => unlL l
  | .run .wait .le0 | .run .wait (.add _) | .run .wait (.fw _) | .run .wait (.sleep _)
  | .run .wait .le | .run .wait (.ls _) | .run .wait (.cx _ _ _) => true
  | .run .wait (.wu _ l) => unlL l
  | .run .wait (.wl l) => lockL l
  | .run (.signal _) (.scx false w s) | .run (.broadcast _) (.scx true w s) => decide (s < w)
  | .run (.signal _) (.sld false) | .run (.broadcast _) (.sld true)
  | .run (.signal _) (.bump _) | .run (.broadcast _) (.bump _)
  | .run (.signal _) (.swake _) | .run (.broadcast _) (.swake _)
  | .run (.signal _) .fin | .run (.broadcast _) .fin => true
  | _ => false

/-- A waiter counted in `waiters` (registered, no signal taken yet). -/
def reg : CCtl CL → Nat
  | .run .wait (.wu _ _) | .run .wait (.fw _) | .run .wait (.sleep _) | .run .wait .le
  | .run .wait (.ls _) | .run .wait (.cx _ _ _) => 1
  | _ => 0

/-- A waiter that took a signal and re-takes the mutex. -/
def cwl : CCtl CL → Nat
  | .run .wait (.wl _) => 1
  | _ => 0

/-- A `signal` before its `cmpxchg`. -/
def spend : CCtl CL → Nat
  | .run (.signal _) (.sld _) | .run (.signal _) (.scx _ _ _) => 1
  | _ => 0

/-- A `broadcast` before its `cmpxchg`. -/
def bpend : CCtl CL → Bool
  | .run (.broadcast _) (.sld _) | .run (.broadcast _) (.scx _ _ _) => true
  | _ => false

/-- A `signal`/`broadcast` that has not bumped the epoch yet. -/
def nb : CCtl CL → Nat
  | .run (.signal _) (.sld _) | .run (.signal _) (.scx _ _ _) | .run (.signal _) (.bump _)
  | .run (.broadcast _) (.sld _) | .run (.broadcast _) (.scx _ _ _) | .run (.broadcast _) (.bump _) => 1
  | _ => 0

/-- A waiter that still owns the mutex: before its `mutex.unlock()`'s `xchg`. -/
def preRel : CCtl CL → Bool
  | .run .wait .le0 | .run .wait (.add _) | .run .wait (.wu _ .rel) => true
  | _ => false

/-- The waiters that a signaler will wake, before its epoch bump. -/
def bW : CCtl CL → Nat
  | .run _ (.bump n) => n
  | _ => 0

/-- The same, after its epoch bump. -/
def wW : CCtl CL → Nat
  | .run _ (.swake n) => n
  | _ => 0

/-- The epoch that a waiter loaded. -/
def eOf : CCtl CL → Nat
  | .run _ (.add e) | .run _ (.wu e _) | .run _ (.fw e) | .run _ (.sleep e) | .run _ (.ls e)
  | .run _ (.cx e _ _) => e
  | _ => 0

/-- A registered waiter that will see a new epoch or the state before it sleeps again (it is
not about to sleep on the current epoch `ep`); asleep waiters count here too, and the queue is
subtracted (`CInv.epoch`). -/
def aw (ep : Nat) : CCtl CL → Nat
  | .run .wait (.wu e _) | .run .wait (.fw e) => if e = ep then 0 else 1
  | .run .wait (.sleep _) | .run .wait .le | .run .wait (.ls _) | .run .wait (.cx _ _ _) => 1
  | _ => 0

end CPlace

open CPlace

/-- Thread `u` sleeps at the epoch. -/
def CState.qi {X : Type} (s : CState (ioCond Fx) X) (u : Tid) : Nat :=
  if (u, CA.ep) ∈ Fx.queue s.sh.f then 1 else 0

/-- The invariant of `Io.Condition` with `Io.Mutex` (module doc). -/
structure CInv {X : Type} (N : Nat) (s : CState (ioCond Fx) X) : Prop where
  mtx : IoInv s.proj
  ok : ∀ t, CPlace.ok (s.ctl t) = true
  idle : ∀ t, N ≤ t → s.ctl t = .idle
  qwf : (Fx.queue s.sh.f).WF
  qep : ∀ u, (u, CA.ep) ∈ Fx.queue s.sh.f → ∃ e, s.ctl u = .run .wait (.sleep e)
  eload : ∀ u, eOf (s.ctl u) ≤ s.sh.ep
  /-- Every epoch bump, done or to come, belongs to a `signal`/`broadcast` call. -/
  epc : s.sh.ep + tsum N (fun u => nb (s.ctl u)) ≤ s.calls
  wcnt : s.sh.w = tsum N (fun u => reg (s.ctl u))
  sgw : s.sh.sg ≤ s.sh.w
  seen : ∀ t, s.seen t ≤ s.gen
  /-- A waiter that has not released the mutex called `wait` at the current acquisition. -/
  wgen : ∀ u, preRel (s.ctl u) = true → s.wgen u = s.gen
  /-- No more returns are owed than there are waiters. -/
  oblW : s.O ≤ s.sh.w + tsum N (fun u => cwl (s.ctl u))
  /-- With no `broadcast` pending, the owed returns are covered by the signals, the pending
  `signal`s and the waiters that took one. -/
  oblS : (∀ u, bpend (s.ctl u) = false) →
    s.O ≤ s.sh.sg + tsum N (fun u => spend (s.ctl u)) + tsum N (fun u => cwl (s.ctl u))
  /-- **The epoch argument**: the signals pending are covered by the waiters awake that will see
  them, the signalers that have not bumped the epoch, and those that will wake sleepers. -/
  epoch : s.sh.ep < 2 ^ 32 →
    s.sh.sg + tsum N s.qi ≤ tsum N (fun u => aw s.sh.ep (s.ctl u)) + tsum N (fun u => bW (s.ctl u)) +
      min (tsum N (fun u => wW (s.ctl u))) (tsum N s.qi)

/-! ### The mutex part follows `Io.Mutex` -/

theorem proj_tset (f : Tid → CCtl CL) (t : Tid) (c : CCtl CL) :
    (fun u => projCtl (tset f t c u)) = tset (fun u => projCtl (f u)) t (projCtl c) := by
  funext u; by_cases hu : u = t
  · rw [hu, tset_self, tset_self]
  · rw [tset_ne _ _ hu, tset_ne _ _ hu]

theorem mstate_eq {I : MutexImpl} {X : Type} {p q : MState I X} (h1 : p.sh = q.sh) (h2 : p.ctl = q.ctl)
    (h3 : p.cur = q.cur) (h4 : p.val = q.val) : p = q := by
  cases p; cases q; simp_all

section
variable {X : Type} {s s' : CState (ioCond Fx) X}

/-- A step of the mutex's client. -/
theorem proj_sim (hFs : FutexSafe condView Fx) (hi : IoInv s.proj) {t : Tid}
    {p' : MState (ioMutex Fx.atMtx) X} (hs : MStep (ioMutex Fx.atMtx) t s.proj p') (he : p' = s'.proj) :
    IoInv s'.proj :=
  he ▸ ioMutex_step hFs.atMtx hi hs

/-- A step that the mutex does not see, but for the futex's other address. -/
theorem proj_frame (hi : IoInv s.proj) (hctl : ∀ u, projCtl (s'.ctl u) = projCtl (s.ctl u))
    (hm : s'.sh.m = s.sh.m) (hcur : s'.cur = s.cur) (hval : s'.val = s.val)
    (hq : (mtxQ (Fx.queue s'.sh.f)).Perm (mtxQ (Fx.queue s.sh.f))) : IoInv s'.proj := by
  have hc : (fun u => projCtl (s'.ctl u)) = fun u => projCtl (s.ctl u) := funext hctl
  have hmem : ∀ x, x ∈ mtxQ (Fx.queue s'.sh.f) ↔ x ∈ mtxQ (Fx.queue s.sh.f) := fun x => hq.mem_iff
  obtain ⟨hok, hexcl, hb, hword, hview, hmsg, hqwf, hqloc, hwit⟩ := hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [CState.proj, hc, hm, hcur, hval] at * <;>
    try assumption
  · exact hqwf.perm hq
  · intro u a ha; exact hqloc u a ((hmem _).mp ha)
  · intro hne
    have hne' : mtxQ (Fx.queue s.sh.f) ≠ [] := fun he => hne (List.eq_nil_iff_forall_not_mem.mpr
      fun x hx => by have := (hmem x).mp hx; rw [he] at this; cases this)
    obtain ⟨v, hv, hw⟩ := hwit hne'
    exact ⟨v, Queue.has_eq_false.mpr fun a ha => Queue.has_eq_false.mp hv a ((hmem _).mp ha), hw⟩

/-- `mtxQ` of a queue that changed only at the epoch. -/
theorem mtxQ_drop_ep {q : Queue CA} {ws : List Tid} (hq : q.WF) (hws : ∀ u ∈ ws, (u, CA.ep) ∈ q) :
    (mtxQ q).drop ws = mtxQ q := by
  unfold Queue.drop
  refine List.filter_eq_self.mpr fun x hx => ?_
  have hx' : (x.1, CA.mtx) ∈ q := mem_mtxQ.mp (by cases x; exact hx)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_any_beq, List.any_eq_false,
    beq_iff_eq]
  intro u hu he
  subst he
  cases hq.unique hx' (hws _ hu)

end

/-! ### The invariant is inductive: helpers -/

namespace CInv

variable {X : Type} {N : Nat} {s s' : CState (ioCond Fx) X}

theorem lt_of_ne_idle (hi : CInv N s) {t : Tid} (h : s.ctl t ≠ .idle) : t < N :=
  Nat.lt_of_not_le fun hn => h (hi.idle t hn)

theorem lt_of_run (hi : CInv N s) {t : Tid} {op : COp} {l : CL} (h : s.ctl t = .run op l) : t < N :=
  hi.lt_of_ne_idle (by rw [h]; intro he; cases he)

/-- A thread that is not asleep at the epoch is not in the queue there. -/
theorem not_ep (hi : CInv N s) {t : Tid} (h : ∀ e, s.ctl t ≠ .run .wait (.sleep e)) :
    (t, CA.ep) ∉ Fx.queue s.sh.f := fun hm => by
  obtain ⟨e, he⟩ := hi.qep t hm; exact h e he

/-- A thread whose place is not the mutex's `asleep` is not in its queue. -/
theorem not_mtx (hi : CInv N s) {t : Tid} (h : projCtl (s.ctl t) ≠ .run .lock .asleep) :
    (t, CA.mtx) ∉ Fx.queue s.sh.f := fun hm => h (hi.mtx.qloc t () (mem_mtxQ.mpr hm))

/-- A thread that is asleep neither at the mutex nor at the epoch is not in the queue. -/
theorem not_has (hi : CInv N s) {t : Tid} (h1 : projCtl (s.ctl t) ≠ .run .lock .asleep)
    (h2 : ∀ e, s.ctl t ≠ .run .wait (.sleep e)) : (Fx.queue s.sh.f).has t = false :=
  Queue.has_eq_false.mpr fun a ha => by
    cases a
    · exact hi.not_mtx h1 ha
    · exact hi.not_ep h2 ha

/-- The threads asleep at the epoch are among the waiters counted by `aw`. -/
theorem qi_le_aw (hq : ∀ u, (u, CA.ep) ∈ Fx.queue s.sh.f → ∃ e, s.ctl u = .run .wait (.sleep e))
    (ep : Nat) : tsum N s.qi ≤ tsum N (fun u => aw ep (s.ctl u)) :=
  tsum_le fun u _ => by
    unfold CState.qi
    split
    · rename_i hm; obtain ⟨e, he⟩ := hq u hm; rw [he]; exact Nat.le_refl _
    · exact Nat.zero_le _

/-- Sums over the threads do not see a move between places where the summand is equal. -/
theorem tsum_same (g : CCtl CL → Nat) {t : Tid} {c : CCtl CL} (h : g c = g (s.ctl t)) :
    tsum N (fun u => g (tset s.ctl t c u)) = tsum N (fun u => g (s.ctl u)) := by
  rw [tset_same g s.ctl t c h]

/-- The sum of `qi` when the queue at the epoch has the same members. -/
theorem qi_same (hqe : ∀ u, (u, CA.ep) ∈ Fx.queue s'.sh.f ↔ (u, CA.ep) ∈ Fx.queue s.sh.f) :
    tsum N s'.qi = tsum N s.qi := by
  unfold CState.qi; simp only [hqe]

/-- **The invariant from its clauses**, with the thread clauses checked at `t` only. -/
theorem next (hi : CInv N s) {t : Tid} (ht : t < N) {c : CCtl CL}
    (hctl : s'.ctl = tset s.ctl t c) (hmtx : IoInv s'.proj) (hok : CPlace.ok c = true)
    (hqwf : (Fx.queue s'.sh.f).WF)
    (hqep : ∀ u, (u, CA.ep) ∈ Fx.queue s'.sh.f → ∃ e, s'.ctl u = .run .wait (.sleep e))
    (hep : s.sh.ep ≤ s'.sh.ep) (heo : eOf c ≤ s'.sh.ep)
    (hepc : s'.sh.ep + tsum N (fun u => nb (s'.ctl u)) ≤ s'.calls)
    (hw : s'.sh.w = tsum N (fun u => reg (s'.ctl u))) (hsgw : s'.sh.sg ≤ s'.sh.w)
    (hseen : ∀ u, s'.seen u ≤ s'.gen) (hwgen : ∀ u, preRel (s'.ctl u) = true → s'.wgen u = s'.gen)
    (hoblW : s'.O ≤ s'.sh.w + tsum N (fun u => cwl (s'.ctl u)))
    (hoblS : (∀ u, bpend (s'.ctl u) = false) →
      s'.O ≤ s'.sh.sg + tsum N (fun u => spend (s'.ctl u)) + tsum N (fun u => cwl (s'.ctl u)))
    (hepoch : s'.sh.ep < 2 ^ 32 →
      s'.sh.sg + tsum N s'.qi ≤ tsum N (fun u => aw s'.sh.ep (s'.ctl u)) +
        tsum N (fun u => bW (s'.ctl u)) + min (tsum N (fun u => wW (s'.ctl u))) (tsum N s'.qi)) :
    CInv N s' where
  mtx := hmtx
  ok := by rw [hctl]; exact tset_all (Q := fun c => CPlace.ok c = true) hok fun u _ => hi.ok u
  idle u hu := by rw [hctl, tset_ne _ _ (fun e => by subst e; tomega)]; exact hi.idle u hu
  qwf := hqwf
  qep := hqep
  eload u := by
    rw [hctl]; by_cases hu : u = t
    · rw [hu, tset_self]; exact heo
    · rw [tset_ne _ _ hu]; exact Nat.le_trans (hi.eload u) hep
  epc := hepc
  wcnt := hw
  sgw := hsgw
  seen := hseen
  wgen := hwgen
  oblW := hoblW
  oblS := hoblS
  epoch := hepoch

/-- **A step that changes no count**: thread `t` moves between places where every summand is
the same, and the condition's words, the owed returns and the calls stay. -/
theorem same (hi : CInv N s) {t : Tid} (ht : t < N) {c : CCtl CL}
    (hctl : s'.ctl = tset s.ctl t c) (hmtx : IoInv s'.proj) (hok : CPlace.ok c = true)
    (hqwf : (Fx.queue s'.sh.f).WF)
    (hqe : ∀ u, (u, CA.ep) ∈ Fx.queue s'.sh.f ↔ (u, CA.ep) ∈ Fx.queue s.sh.f)
    (htq : (t, CA.ep) ∈ Fx.queue s.sh.f → ∃ e, c = .run .wait (.sleep e))
    (hw : s'.sh.w = s.sh.w) (hsg : s'.sh.sg = s.sh.sg) (hep : s'.sh.ep = s.sh.ep)
    (hO : s'.O = s.O) (hcalls : s'.calls = s.calls)
    (hseen : ∀ u, s'.seen u ≤ s'.gen) (hwgen : ∀ u, preRel (s'.ctl u) = true → s'.wgen u = s'.gen)
    (hr : reg c = reg (s.ctl t)) (hcw : cwl c = cwl (s.ctl t)) (hsp : spend c = spend (s.ctl t))
    (hbp : bpend c = bpend (s.ctl t)) (hnb : nb c = nb (s.ctl t)) (hbw : bW c = bW (s.ctl t))
    (hww : wW c = wW (s.ctl t)) (haw : aw s.sh.ep c = aw s.sh.ep (s.ctl t)) (heo : eOf c ≤ s.sh.ep) :
    CInv N s' := by
  have er := tsum_same (N := N) reg hr
  have ecw := tsum_same (N := N) cwl hcw
  have esp := tsum_same (N := N) spend hsp
  have enb := tsum_same (N := N) nb hnb
  have ebw := tsum_same (N := N) bW hbw
  have eww := tsum_same (N := N) wW hww
  have eaw := tsum_same (N := N) (aw s.sh.ep) haw
  have eq := qi_same (N := N) hqe
  refine hi.next ht hctl hmtx hok hqwf ?_ (by rw [hep]; exact Nat.le_refl _) (by rw [hep]; exact heo)
    ?_ ?_ ?_ hseen hwgen ?_ ?_ ?_ <;> (try rw [hctl]) <;> (try rw [hctl] at *)
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self]; rw [hut] at hu; exact htq ((hqe t).mp hu)
    · rw [tset_ne _ _ hut]; exact hi.qep u ((hqe u).mp hu)
  · rw [enb, hep, hcalls]; exact hi.epc
  · rw [er, hw]; exact hi.wcnt
  · rw [hsg, hw]; exact hi.sgw
  · rw [ecw, hO, hw]; exact hi.oblW
  · intro hb
    have hb' : ∀ u, bpend (s.ctl u) = false := by
      intro u; by_cases hut : u = t
      · rw [hut, ← hbp]; have := hb t; rwa [tset_self] at this
      · have := hb u; rwa [tset_ne _ _ hut] at this
    rw [ecw, esp, hO, hsg]; exact hi.oblS hb'
  · intro hlt
    rw [hep] at hlt ⊢
    rw [eaw, ebw, eww, eq, hsg]; exact hi.epoch hlt

/-- The seen/wgen clauses when no acquisition happens and `t` keeps its relation to them. -/
theorem keep_gen (hi : CInv N s) {t : Tid} {c : CCtl CL} (hctl : s'.ctl = tset s.ctl t c)
    (hgen : s'.gen = s.gen) (hseen : s'.seen = s.seen) (hwg : s'.wgen = s.wgen)
    (hpre : preRel c = true → s.wgen t = s.gen) :
    (∀ u, s'.seen u ≤ s'.gen) ∧ (∀ u, preRel (s'.ctl u) = true → s'.wgen u = s'.gen) := by
  refine ⟨fun u => by rw [hseen, hgen]; exact hi.seen u, fun u hu => ?_⟩
  rw [hwg, hgen]; rw [hctl] at hu
  by_cases hut : u = t
  · rw [hut, tset_self] at hu; rw [hut]; exact hpre hu
  · rw [tset_ne _ _ hut] at hu; exact hi.wgen u hu

end CInv

/-- An `Io.Mutex` step in the condition's code changes the queue only at the mutex word. -/
theorem iostep_q (hF : FutexSafe condView Fx) {X : Type} {t : Tid} {l l' : IL} {w : AWord X}
    {f : Fx.atMtx.F} {v v' : X} {sh' : AWord X × Fx.atMtx.F} (hs : IoStep Fx.atMtx t l w f v l' sh' v')
    (hwf : (Fx.queue f).WF) (hte : (t, CA.ep) ∉ Fx.queue f)
    (htn : l ≠ .asleep → (Fx.queue f).has t = false) :
    (Fx.queue sh'.2).WF ∧ ∀ u, (u, CA.ep) ∈ Fx.queue sh'.2 ↔ (u, CA.ep) ∈ Fx.queue f := by
  cases hs with
  | casOk | casWait | casSpin | tryOk | tryFail | xchgOk | xchgWait | relWake | relDone =>
    exact ⟨hwf, fun _ => Iff.rfl⟩
  | sleep hw =>
    obtain ⟨ep, hw⟩ := hw
    refine ⟨hF.wf_wait hwf (htn (by intro he; cases he)) hw, fun u => ?_⟩
    rw [hF.mem_wait hw]; simp
  | back hw =>
    obtain ⟨ep, hw⟩ := hw
    refine ⟨hF.wf_wait hwf (htn (by intro he; cases he)) hw, fun u => ?_⟩
    rw [hF.mem_wait hw]; simp
  | resume hr =>
    refine ⟨hF.wf_resume hwf hr, fun u => ?_⟩
    rw [hF.mem_resume hr]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, fun e => ?_⟩; simp only at e; subst e; exact hte h
  | wake hk =>
    obtain ⟨-, hk⟩ := hk
    refine ⟨hF.wf_wake hwf hk, fun u => ⟨fun h => hF.mem_wake hwf hk h, fun h => ?_⟩⟩
    exact hF.wake_keeps hwf hk h (by intro he; cases he)

/-! ### Facts about places -/

namespace CPlace

theorem lockL_eq (l : IL) : lockL l = IoPlace.ok (.run .lock l) := by
  cases l <;> try rfl
  all_goals (rename_i b; cases b <;> rfl)

theorem tryL_eq (l : IL) : tryL l = IoPlace.ok (.run .tryLock l) := by
  cases l <;> try rfl
  all_goals (rename_i b; cases b <;> rfl)

theorem unlL_eq (l : IL) : unlL l = IoPlace.ok (.run .unlock l) := by
  cases l <;> try rfl
  all_goals (rename_i b; cases b <;> rfl)

theorem aw_le_reg (ep : Nat) (c : CCtl CL) : aw ep c ≤ reg c := by
  match c with
  | .run .wait (.wu e _) | .run .wait (.fw e) => simp only [aw, reg]; split <;> omega
  | .run .wait (.sleep _) | .run .wait .le | .run .wait (.ls _) | .run .wait (.cx _ _ _) =>
    exact Nat.le_refl _
  | .idle | .holds => exact Nat.le_refl _
  | .run .wait .le0 | .run .wait (.add _) | .run .wait (.m _) | .run .wait (.wl _)
  | .run .wait (.sld _) | .run .wait (.scx _ _ _) | .run .wait (.bump _) | .run .wait (.swake _)
  | .run .wait .fin => exact Nat.le_refl _
  | .run .lock _ | .run .tryLock _ | .run .unlock _ | .run (.signal _) _ | .run (.broadcast _) _ =>
    simp only [aw, reg]; exact Nat.le_refl _

/-- After an epoch bump, no waiter is about to sleep on the new epoch. -/
theorem aw_succ {ep : Nat} {c : CCtl CL} (h : eOf c ≤ ep) : aw (ep + 1) c = reg c := by
  match c with
  | .run .wait (.wu e _) | .run .wait (.fw e) =>
    simp only [eOf] at h; simp only [aw, reg]; split <;> omega
  | .run .wait (.sleep _) | .run .wait .le | .run .wait (.ls _) | .run .wait (.cx _ _ _) => rfl
  | .idle | .holds => rfl
  | .run .wait .le0 | .run .wait (.add _) | .run .wait (.m _) | .run .wait (.wl _)
  | .run .wait (.sld _) | .run .wait (.scx _ _ _) | .run .wait (.bump _) | .run .wait (.swake _)
  | .run .wait .fin => rfl
  | .run .lock _ | .run .tryLock _ | .run .unlock _ | .run (.signal _) _ | .run (.broadcast _) _ =>
    simp only [aw, reg]

theorem preRel_own {c : CCtl CL} (h : preRel c = true) : IoPlace.own (projCtl c) = true := by
  match c, h with
  | .run .wait .le0, _ | .run .wait (.add _), _ | .run .wait (.wu _ .rel), _ => rfl

/-- A waiter that is not before its release is counted in `waiters` or re-takes the mutex. -/
theorem waiting_cnt {c : CCtl CL} (hok : ok c = true) (hw : c.waiting = true) (hp : preRel c = false) :
    1 ≤ reg c + cwl c := by
  match c, hok, hw, hp with
  | .run .wait (.wu _ l), hok, _, hp => simp only [reg, cwl]; omega
  | .run .wait (.fw _), _, _, _ | .run .wait (.sleep _), _, _, _ | .run .wait .le, _, _, _
  | .run .wait (.ls _), _, _, _ | .run .wait (.cx _ _ _), _, _, _ | .run .wait (.wl _), _, _, _ =>
    simp only [reg, cwl]; omega

end CPlace

/-- An `Io.Mutex` step never returns to `unlock`'s `xchg`. -/
theorem iostep_not_rel {F : Futex Nat Unit} {X : Type} {t : Tid} {l l' : IL} {w : AWord X} {f : F.F}
    {v v' : X} {sh' : AWord X × F.F} (hs : IoStep F t l w f v l' sh' v') : l' ≠ .rel := by
  cases hs <;> intro he <;> cases he

namespace CInv

variable {X : Type} {N : Nat} {s s' : CState (ioCond Fx) X}

/-- The eligible waiters are counted in `waiters` or re-take the mutex. -/
theorem elig_le (hi : CInv N s) (t : Tid) :
    s.elig N t ≤ s.sh.w + tsum N (fun u => cwl (s.ctl u)) := by
  rw [hi.wcnt, ← tsum_add]
  refine tsum_le fun u _ => ?_
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hw, hlt⟩ := hc
    have hp : preRel (s.ctl u) = false := by
      cases hp : preRel (s.ctl u)
      · rfl
      · have := hi.wgen u hp; have := hi.seen t; omega
    exact waiting_cnt (hi.ok u) hw hp
  · exact Nat.zero_le _

/-- While a thread owns the mutex, no other waiter is before its release. -/
theorem no_preRel (hi : CInv N s) {t : Tid} (ho : IoPlace.own (projCtl (s.ctl t)) = true) {u : Tid}
    (hu : u ≠ t) : preRel (s.ctl u) = false := by
  cases hp : preRel (s.ctl u)
  · rfl
  · exact absurd (hi.mtx.excl u t (preRel_own hp) ho) hu

end CInv

/-! ### The invariant is inductive: the client's steps -/

/-- The mutex's view of a move of thread `t`. -/
theorem proj_ctl_eq {X : Type} {s s' : CState (ioCond Fx) X} {t : Tid} {c' : Ctl IL}
    (h1 : ∀ u, u ≠ t → s'.ctl u = s.ctl u) (h2 : projCtl (s'.ctl t) = c') :
    tset s.proj.ctl t c' = s'.proj.ctl := by
  funext u
  show tset (fun u => projCtl (s.ctl u)) t c' u = projCtl (s'.ctl u)
  by_cases hu : u = t
  · rw [hu, tset_self, h2]
  · rw [tset_ne _ _ hu, h1 u hu]

/-- The place where a `signal`/`broadcast` starts. -/
theorem notify_place {op : COp} {h : Bool} (hop : op = .signal h ∨ op = .broadcast h) (ep : Nat) :
    projCtl (.run op ((ioCond Fx).start op)) = (if h then .holds else .idle) ∧
    CPlace.ok (.run op ((ioCond Fx).start op)) = true ∧ reg (.run op ((ioCond Fx).start op)) = 0 ∧
    cwl (.run op ((ioCond Fx).start op)) = 0 ∧ nb (.run op ((ioCond Fx).start op)) = 1 ∧
    bW (.run op ((ioCond Fx).start op)) = 0 ∧ wW (.run op ((ioCond Fx).start op)) = 0 ∧
    aw ep (.run op ((ioCond Fx).start op)) = 0 ∧ preRel (.run op ((ioCond Fx).start op)) = false ∧
    eOf (.run op ((ioCond Fx).start op)) = 0 ∧
    ((spend (.run op ((ioCond Fx).start op)) = 1 ∧ bpend (.run op ((ioCond Fx).start op)) = false ∧
        op = .signal h) ∨
      (spend (.run op ((ioCond Fx).start op)) = 0 ∧ bpend (.run op ((ioCond Fx).start op)) = true ∧
        op = .broadcast h)) := by
  rcases hop with rfl | rfl <;> cases h <;> simp [projCtl, CPlace.ok, reg, cwl, nb, bW, wW, aw, preRel,
    eOf, spend, bpend]

namespace CInv

variable {X : Type} {N : Nat} {s : CState (ioCond Fx) X}

theorem call (hFs : FutexSafe condView Fx) (hi : CInv N s) {t : Tid} (ht : t < N) {op : COp}
    (hop : op = .lock ∨ op = .tryLock) (h : s.ctl t = .idle) :
    CInv N { s with ctl := tset s.ctl t (.run op ((ioCond Fx).start op)) } := by
  have hp : projCtl (s.ctl t) = .idle := by rw [h]; rfl
  have hne : ∀ e, s.ctl t ≠ .run .wait (.sleep e) := by rw [h]; intro e he; cases he
  have hmop : ∃ mop : MOp, mop ≠ .unlock ∧
      projCtl (.run op ((ioCond Fx).start op)) = .run mop ((ioMutex Fx.atMtx).start mop) := by
    rcases hop with rfl | rfl
    · exact ⟨.lock, by decide, rfl⟩
    · exact ⟨.tryLock, by decide, rfl⟩
  obtain ⟨mop, hmu, hpm⟩ := hmop
  have hmtx := proj_sim (s' := { s with ctl := tset s.ctl t (.run op ((ioCond Fx).start op)) })
    hFs hi.mtx (MStep.call (I := ioMutex Fx.atMtx) mop hmu hp)
    (mstate_eq rfl (proj_ctl_eq (fun u hu => tset_ne _ _ hu) (by dsimp only; rw [tset_self, hpm])) rfl rfl)
  obtain ⟨hs1, hs2⟩ := hi.keep_gen (s' := { s with ctl := tset s.ctl t (.run op ((ioCond Fx).start op)) })
    rfl rfl rfl rfl (fun hp => by rcases hop with rfl | rfl <;> cases hp)
  have hz : CPlace.ok (.run op ((ioCond Fx).start op)) = true ∧
      reg (.run op ((ioCond Fx).start op)) = reg (s.ctl t) ∧ cwl (.run op ((ioCond Fx).start op)) = cwl (s.ctl t) ∧
      spend (.run op ((ioCond Fx).start op)) = spend (s.ctl t) ∧
      bpend (.run op ((ioCond Fx).start op)) = bpend (s.ctl t) ∧
      nb (.run op ((ioCond Fx).start op)) = nb (s.ctl t) ∧ bW (.run op ((ioCond Fx).start op)) = bW (s.ctl t) ∧
      wW (.run op ((ioCond Fx).start op)) = wW (s.ctl t) ∧
      aw s.sh.ep (.run op ((ioCond Fx).start op)) = aw s.sh.ep (s.ctl t) := by
    rw [h]; rcases hop with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8⟩ := hz
  exact hi.same ht rfl hmtx z0 hi.qwf (fun _ => Iff.rfl) (fun hm => absurd hm (hi.not_ep hne))
    rfl rfl rfl rfl rfl hs1 hs2 z1 z2 z3 z4 z5 z6 z7 z8
    (by rcases hop with rfl | rfl <;> exact Nat.zero_le _)

theorem unlock (hFs : FutexSafe condView Fx) (hi : CInv N s) {t : Tid} (ht : t < N)
    (h : s.ctl t = .holds) :
    CInv N { s with ctl := tset s.ctl t (.run .unlock ((ioCond Fx).start .unlock)) } := by
  have hp : projCtl (s.ctl t) = .holds := by rw [h]; rfl
  have hne : ∀ e, s.ctl t ≠ .run .wait (.sleep e) := by rw [h]; intro e he; cases he
  have hmtx := proj_sim (s' := { s with ctl := tset s.ctl t (.run .unlock ((ioCond Fx).start .unlock)) })
    hFs hi.mtx (MStep.unlock (I := ioMutex Fx.atMtx) hp)
    (mstate_eq rfl (proj_ctl_eq (fun u hu => tset_ne _ _ hu) (by dsimp only; rw [tset_self]; rfl)) rfl rfl)
  obtain ⟨hs1, hs2⟩ := hi.keep_gen (s' := { s with ctl := tset s.ctl t (.run .unlock ((ioCond Fx).start .unlock)) })
    rfl rfl rfl rfl (fun hp => by cases hp)
  exact hi.same ht rfl hmtx rfl hi.qwf (fun _ => Iff.rfl) (fun hm => absurd hm (hi.not_ep hne))
    rfl rfl rfl rfl rfl hs1 hs2 (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl)
    (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (Nat.zero_le _)

theorem wait (hi : CInv N s) {t : Tid} (ht : t < N) (h : s.ctl t = .holds) :
    CInv N { s with
      ctl := tset s.ctl t (.run .wait ((ioCond Fx).start .wait))
      wgen := tset s.wgen t s.gen } := by
  have hne : ∀ e, s.ctl t ≠ .run .wait (.sleep e) := by rw [h]; intro e he; cases he
  have hmtx : IoInv (CState.proj { s with
      ctl := tset s.ctl t (.run .wait ((ioCond Fx).start .wait))
      wgen := tset s.wgen t s.gen }) :=
    proj_frame hi.mtx (fun u => by
      by_cases hu : u = t
      · show projCtl (tset s.ctl t _ u) = _; rw [hu, tset_self, h]; rfl
      · show projCtl (tset s.ctl t _ u) = _; rw [tset_ne _ _ hu]) rfl rfl rfl (List.Perm.refl _)
  refine hi.same ht rfl hmtx rfl hi.qwf (fun _ => Iff.rfl) (fun hm => absurd hm (hi.not_ep hne))
    rfl rfl rfl rfl rfl hi.seen (fun u hu => ?_) (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl)
    (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (by rw [h]; rfl) (Nat.zero_le _)
  show tset s.wgen t s.gen u = s.gen
  by_cases hut : u = t
  · rw [hut, tset_self]
  · rw [tset_ne _ _ hut]
    have hu' : preRel (tset s.ctl t (.run .wait ((ioCond Fx).start .wait)) u) = true := hu
    rw [tset_ne _ _ hut] at hu'
    exact hi.wgen u hu'

theorem write (hFs : FutexSafe condView Fx) (hi : CInv N s) {t : Tid} (ht : t < N) (x : X)
    (h : s.ctl t = .holds) : CInv N { s with cur := tset s.cur t x, val := x } := by
  have hp : projCtl (s.ctl t) = .holds := by rw [h]; rfl
  have hne : ∀ e, s.ctl t ≠ .run .wait (.sleep e) := by rw [h]; intro e he; cases he
  have hmtx := proj_sim (s' := { s with cur := tset s.cur t x, val := x })
    hFs hi.mtx (MStep.write (I := ioMutex Fx.atMtx) x hp) (mstate_eq rfl rfl rfl rfl)
  have hctl : ({ s with cur := tset s.cur t x, val := x } : CState (ioCond Fx) X).ctl = tset s.ctl t .holds := by
    show s.ctl = _; rw [← h, tset_id]
  obtain ⟨hs1, hs2⟩ := hi.keep_gen (s' := { s with cur := tset s.cur t x, val := x }) hctl rfl rfl rfl
    (fun hp => by cases hp)
  exact hi.same ht hctl hmtx rfl hi.qwf (fun _ => Iff.rfl) (fun hm => absurd hm (hi.not_ep hne))
    rfl rfl rfl rfl rfl hs1 hs2 (by rw [h]) (by rw [h]) (by rw [h]) (by rw [h]) (by rw [h]) (by rw [h])
    (by rw [h]) (by rw [h]) (Nat.zero_le _)

theorem notify (hi : CInv N s) {t : Tid} (ht : t < N) {op : COp} {h : Bool}
    (hop : op = .signal h ∨ op = .broadcast h) (hc : s.ctl t = if h then .holds else .idle) :
    CInv N { s with
      ctl := tset s.ctl t (.run op ((ioCond Fx).start op))
      O := op.owe s.O (s.elig N t)
      calls := s.calls + 1 } := by
  have hne : ∀ e, s.ctl t ≠ .run .wait (.sleep e) := by
    rw [hc]; intro e he; cases h <;> simp at he
  have hc0 : reg (s.ctl t) = 0 ∧ cwl (s.ctl t) = 0 ∧ spend (s.ctl t) = 0 ∧ bpend (s.ctl t) = false ∧
      nb (s.ctl t) = 0 ∧ bW (s.ctl t) = 0 ∧ wW (s.ctl t) = 0 ∧ aw s.sh.ep (s.ctl t) = 0 ∧
      projCtl (s.ctl t) = (if h then .holds else .idle) := by
    rw [hc]; cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := hc0
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := notify_place (Fx := Fx) hop s.sh.ep
  have hE := hi.elig_le t
  generalize CCtl.run op ((ioCond Fx).start op) = c at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 ⊢
  have hmtx : IoInv (CState.proj { s with
      ctl := tset s.ctl t c
      O := op.owe s.O (s.elig N t)
      calls := s.calls + 1 }) :=
    proj_frame hi.mtx (fun u => by
      by_cases hu : u = t
      · show projCtl (tset s.ctl t c u) = _; rw [hu, tset_self, p1, z9]
      · show projCtl (tset s.ctl t c u) = _; rw [tset_ne _ _ hu]) rfl rfl rfl (List.Perm.refl _)
  have e1 := tsum_tset nb s.ctl ht c
  have e2 := tsum_tset reg s.ctl ht c
  have e3 := tsum_tset cwl s.ctl ht c
  have e4 := tsum_tset spend s.ctl ht c
  have e5 := tsum_tset (aw s.sh.ep) s.ctl ht c
  have e6 := tsum_tset bW s.ctl ht c
  have e7 := tsum_tset wW s.ctl ht c
  have hepc := hi.epc
  have hw := hi.wcnt
  have hoW := hi.oblW
  refine hi.next ht rfl hmtx p2 hi.qwf (fun u hu => ?_) (Nat.le_refl _) (by rw [p10]; exact Nat.zero_le _)
    ?_ ?_ hi.sgw hi.seen (fun u hu => ?_) ?_ (fun hb => ?_) (fun hlt => ?_)
  · have := hi.qep u hu
    by_cases hut : u = t
    · rw [hut] at this; obtain ⟨e, he⟩ := this; exact absurd he (hne e)
    · show ∃ e, tset s.ctl t c u = _; rw [tset_ne _ _ hut]; exact this
  · show s.sh.ep + tsum N (fun u => nb (tset s.ctl t c u)) ≤ s.calls + 1; omega
  · show s.sh.w = tsum N (fun u => reg (tset s.ctl t c u)); omega
  · have hu' : preRel (tset s.ctl t c u) = true := hu
    by_cases hut : u = t
    · rw [hut, tset_self, p9] at hu'; cases hu'
    · rw [tset_ne _ _ hut] at hu'; exact hi.wgen u hu'
  · show op.owe s.O (s.elig N t) ≤ s.sh.w + tsum N (fun u => cwl (tset s.ctl t c u))
    rcases p11 with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp only [COp.owe] <;> (try split) <;> omega
  · rcases p11 with ⟨q1, q2, rfl⟩ | ⟨q1, q2, rfl⟩
    · have hb' : ∀ u, bpend (s.ctl u) = false := fun u => by
        by_cases hut : u = t
        · rw [hut, z4]
        · have := hb u; simp only at this; rwa [tset_ne _ _ hut] at this
      have := hi.oblS hb'
      show COp.owe (.signal h) s.O (s.elig N t) ≤ s.sh.sg + tsum N (fun u => spend (tset s.ctl t c u)) +
        tsum N (fun u => cwl (tset s.ctl t c u))
      simp only [COp.owe]; split <;> omega
    · have := hb t; simp only at this; rw [tset_self, q2] at this; cases this
  · have := hi.epoch hlt
    show s.sh.sg + tsum N s.qi ≤ tsum N (fun u => aw s.sh.ep (tset s.ctl t c u)) +
      tsum N (fun u => bW (tset s.ctl t c u)) + min (tsum N (fun u => wW (tset s.ctl t c u))) (tsum N s.qi)
    omega

end CInv

end Spec
end Zig
