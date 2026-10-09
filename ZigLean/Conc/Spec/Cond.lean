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

end Spec
end Zig
