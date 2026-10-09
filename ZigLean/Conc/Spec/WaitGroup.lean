import ZigLean.Conc.Spec.Count
import ZigLean.Conc.Spec.IoMutex

/-!
# The wait-group contract (`WaitGroupSpec`), and std's `Io.Threaded.WaitGroup` satisfies it over
every futex that satisfies `FutexSpec`

`Io.Threaded`'s private `WaitGroup` (Zig 0.16.0 `lib/std/Io/Threaded.zig:18592`) counts the
worker threads: `start` before a worker is spawned, `finish` when it ends (`defer`), and one
`wait` in `join` (`deinit`). `value` is a `monotonic` load used as a pool-size hint; it gives no
guarantee and is not part of the contract.

**Views that merge.** Several finishers publish their writes to one waiter, so a view is an
element of a join semilattice (`Lat`, `ZigLean/Conc/Spec/Count.lean`) and an acquire **joins**
the message's view into the reader's (`MutexSpec` only needs adoption). A release RMW puts the
writer's view joined with the message's old view (the release sequence goes on through an RMW).
An implementation (`JImpl`) gets the join as a parameter and nothing else, so it cannot invent a
view.

**The most general client** (`wmgc I X L N`): threads `0 … N-1`, for every `N`. Each thread is
idle, runs an op, or has **got** the wait (it returned from `wait`).

* any idle thread calls `start` while no `wait` has been called; a `start` that returns makes a
  **token**;
* any idle thread calls `finish` while there is a token, and takes it;
* one idle thread calls `wait` once, when no `start` runs (std's contract: every `start` happens
  before `wait`; `Threaded.join` spawns no worker after it, and the assertion
  `prev_state & is_waiting == 0` allows one `wait`);
* an idle thread, or one that got the wait, learns anything (`learn x`: its view grows: its own
  writes);
* a thread in an op takes the implementation's steps; a `finish` that returns adds the
  finisher's view to the ghost `fin`.

**The contract** (`WaitGroupSpec I`), for every view lattice and every `N`:

| clause | statement |
|---|---|
| `view` | the thread that got the wait sees `fin`: everything every finisher saw when its `finish` returned, so every write before each `finish` |
| `done` | when a thread got the wait, every token has been taken by a `finish` |
| `live` | no deadlock: if no token is left and a thread runs an op, some thread in an op can step |

`threadedWG_spec (hF : FutexSpec wordView Fx)`: the std algorithm (a counter `state` with
`is_waiting = 1`, `one_pending = 2`, and an `Io.Event` over `eventWait`/`eventSet`), one atomic
step per atomic op of the source, satisfies the contract over every futex `Fx` that satisfies the
futex contract. The finisher's `acq_rel` `fetchSub` collects the earlier finishers' views in the
counter's message, the last one's `release` `xchg` of the event carries them on, and the
waiter's `acquire` (`fetchAdd`, `cmpxchg` or load) joins them.
-/

namespace Zig
namespace Spec

/-! ## The contract -/

/-- The ops of a wait group. -/
inductive WOp where
  | start
  | finish
  | wait
  deriving DecidableEq, Repr

/-- An implementation whose views merge (module doc): `Impl` whose steps get the join. -/
structure JImpl (Op : Type) where
  Sh : Type → Type
  /-- The shared state at the start, when every view is `x₀`. -/
  init : {X : Type} → X → Sh X → Prop
  Loc : Type
  start : Op → Loc
  /-- An atomic step of thread `t` at `l` with view `v`, given the join of views. -/
  step : {X : Type} → (X → X → X) → Tid → Loc → Sh X → X → Loc → Sh X → X → Prop
  /-- The op at `l` has returned. -/
  done : Loc → Bool

/-- A thread of the wait group's most general client. -/
inductive WCtl (L : Type) where
  | idle
  /-- It returned from `wait`. -/
  | got
  | run (op : WOp) (l : L)
  deriving DecidableEq

/-- A state of the wait group's most general client. -/
structure WState (I : JImpl WOp) (X : Type) where
  sh : I.Sh X
  ctl : Tid → WCtl I.Loc
  cur : Tid → X
  /-- The tokens: `start`s that returned and that no `finish` took yet (ghost). -/
  tok : Nat
  /-- The join of the finishers' views when their `finish` returned (ghost). -/
  fin : X
  /-- `wait` was called (ghost). -/
  waited : Bool

/-- A step of thread `t` of the wait group's most general client (module doc). -/
inductive WStep (I : JImpl WOp) {X : Type} (L : Lat X) (t : Tid) : WState I X → WState I X → Prop
  | learn {s : WState I X} (x : X) (h : s.ctl t = .idle ∨ s.ctl t = .got) :
      WStep I L t s { s with cur := tset s.cur t (L.join (s.cur t) x) }
  | start {s : WState I X} (h : s.ctl t = .idle) (hw : s.waited = false) :
      WStep I L t s { s with ctl := tset s.ctl t (.run .start (I.start .start)) }
  | finish {s : WState I X} (h : s.ctl t = .idle) (hk : 0 < s.tok) :
      WStep I L t s { s with ctl := tset s.ctl t (.run .finish (I.start .finish)), tok := s.tok - 1 }
  | wait {s : WState I X} (h : s.ctl t = .idle) (hw : s.waited = false)
      (hs : ∀ u l, s.ctl u ≠ .run .start l) :
      WStep I L t s { s with ctl := tset s.ctl t (.run .wait (I.start .wait)), waited := true }
  | exec {s : WState I X} {op : WOp} {l l' : I.Loc} {sh' : I.Sh X} {v' : X}
      (h : s.ctl t = .run op l) (hs : I.step L.join t l s.sh (s.cur t) l' sh' v') :
      WStep I L t s { s with sh := sh', ctl := tset s.ctl t (.run op l'), cur := tset s.cur t v' }
  | retStart {s : WState I X} {l : I.Loc} (h : s.ctl t = .run .start l) (hd : I.done l = true) :
      WStep I L t s { s with ctl := tset s.ctl t .idle, tok := s.tok + 1 }
  | retFinish {s : WState I X} {l : I.Loc} (h : s.ctl t = .run .finish l) (hd : I.done l = true) :
      WStep I L t s { s with ctl := tset s.ctl t .idle, fin := L.join s.fin (s.cur t) }
  | retWait {s : WState I X} {l : I.Loc} (h : s.ctl t = .run .wait l) (hd : I.done l = true) :
      WStep I L t s { s with ctl := tset s.ctl t .got }

/-- The wait group's most general client with `N` threads and the view lattice `L`. -/
abbrev wmgc (I : JImpl WOp) (X : Type) (L : Lat X) (N : Nat) : Sys where
  St := WState I X
  init s := ∃ x₀, I.init x₀ s.sh ∧ (∀ t, s.ctl t = .idle) ∧ (∀ t, s.cur t = x₀) ∧ s.tok = 0 ∧
    s.fin = x₀ ∧ s.waited = false
  step t s s' := t < N ∧ WStep I L t s s'

/-- A deadlock: no token is left, a thread runs an op, and no thread in an op can step. -/
def WStuck (I : JImpl WOp) {X : Type} (L : Lat X) (N : Nat) (s : WState I X) : Prop :=
  s.tok = 0 ∧ (∃ t op l, s.ctl t = .run op l) ∧
    ∀ t op l, s.ctl t = .run op l → ¬ (wmgc I X L N).Enabled t s

/-- The wait-group contract (module doc). -/
structure WaitGroupSpec (I : JImpl WOp) : Prop where
  view : ∀ X (L : Lat X) N, (wmgc I X L N).Invariant fun s =>
    ∀ t, s.ctl t = .got → L.le s.fin (s.cur t)
  done : ∀ X (L : Lat X) N, (wmgc I X L N).Invariant fun s => ∀ t, s.ctl t = .got → s.tok = 0
  live : ∀ X (L : Lat X) N, (wmgc I X L N).Invariant fun s => ¬ WStuck I L N s

/-! ## `Io.Threaded.WaitGroup` -/

/-- The shared state: the counter `state` (`is_waiting = 1`, `one_pending = 2`), the event word
(`unset = 0`, `waiting = 1`, `is_set = 2`) and the futex. -/
structure WSh (Fx : Futex Nat Unit) (X : Type) where
  st : AWord X
  ev : AWord X
  f : Fx.F

/-- The places in `Threaded.WaitGroup`'s code (with `eventWait`/`eventSet` inlined). -/
inductive WL where
  /-- `start`'s `fetchAdd(one_pending, .monotonic)`. -/
  | add
  /-- `finish`'s `fetchSub(one_pending, .acq_rel)`. -/
  | sub
  /-- `eventSet`'s `xchg(.is_set, .release)`. -/
  | set
  /-- `eventSet`'s `futexWake(event, maxInt(u32))`. -/
  | wake
  /-- `wait`'s `fetchAdd(is_waiting, .acquire)`. -/
  | wadd
  /-- `eventWait`'s `cmpxchgStrong(.unset, .waiting, .acquire, .acquire)`. -/
  | cas
  /-- `eventWait`'s `futexWaitUncancelable(event, .waiting)`, before the futex op. -/
  | fwait
  /-- In that futex wait: the thread went to sleep. -/
  | asleep
  /-- `eventWait`'s `@atomicLoad(.acquire)` after the futex wait. -/
  | load
  /-- The op returned. -/
  | fin
  deriving DecidableEq

/-- The atomic steps of `Threaded.WaitGroup` over the futex `Fx` (whose memory is the event
word), by thread `t` with view `v`; `j` is the join. Std's assertions (`finish` with no pending
`start`, a second `wait`) and `unreachable`s (an event read as `unset` after the wait) have no
step. -/
inductive WgStep (Fx : Futex Nat Unit) {X : Type} (j : X → X → X) (t : Tid) :
    WL → WSh Fx X → X → WL → WSh Fx X → X → Prop
  | add {sh : WSh Fx X} {v : X} :
      WgStep Fx j t .add sh v .fin { sh with st := ⟨sh.st.val + 2, sh.st.msg⟩ } v
  | subSet {sh : WSh Fx X} {v : X} : sh.st.val = 3 →
      WgStep Fx j t .sub sh v .set { sh with st := ⟨1, j v sh.st.msg⟩ } (j v sh.st.msg)
  | subDone {sh : WSh Fx X} {v : X} : 2 ≤ sh.st.val → sh.st.val ≠ 3 →
      WgStep Fx j t .sub sh v .fin { sh with st := ⟨sh.st.val - 2, j v sh.st.msg⟩ } (j v sh.st.msg)
  | setWake {sh : WSh Fx X} {v : X} : sh.ev.val = 1 →
      WgStep Fx j t .set sh v .wake { sh with ev := ⟨2, j sh.ev.msg v⟩ } v
  | setDone {sh : WSh Fx X} {v : X} : sh.ev.val ≠ 1 →
      WgStep Fx j t .set sh v .fin { sh with ev := ⟨2, j sh.ev.msg v⟩ } v
  | wake {sh : WSh Fx X} {v : X} {f' : Fx.F} : Fx.wake t () (2 ^ 32 - 1) sh.f f' →
      WgStep Fx j t .wake sh v .fin { sh with f := f' } v
  | waddWait {sh : WSh Fx X} {v : X} : sh.st.val % 2 = 0 → 2 ≤ sh.st.val →
      WgStep Fx j t .wadd sh v .cas { sh with st := ⟨sh.st.val + 1, sh.st.msg⟩ } (j v sh.st.msg)
  | waddDone {sh : WSh Fx X} {v : X} : sh.st.val = 0 →
      WgStep Fx j t .wadd sh v .fin { sh with st := ⟨1, sh.st.msg⟩ } (j v sh.st.msg)
  | casSet {sh : WSh Fx X} {v : X} : sh.ev.val = 0 →
      WgStep Fx j t .cas sh v .fwait { sh with ev := ⟨1, sh.ev.msg⟩ } (j v sh.ev.msg)
  | casWaiting {sh : WSh Fx X} {v : X} : sh.ev.val = 1 →
      WgStep Fx j t .cas sh v .fwait sh (j v sh.ev.msg)
  | casIsSet {sh : WSh Fx X} {v : X} : sh.ev.val = 2 →
      WgStep Fx j t .cas sh v .fin sh (j v sh.ev.msg)
  | sleep {sh : WSh Fx X} {v : X} {f' : Fx.F} : Fx.wait t () 1 false sh.ev.val sh.f none f' →
      WgStep Fx j t .fwait sh v .asleep { sh with f := f' } v
  | back {sh : WSh Fx X} {v : X} {f' : Fx.F} {r : WaitRet} :
      Fx.wait t () 1 false sh.ev.val sh.f (some r) f' →
      WgStep Fx j t .fwait sh v .load { sh with f := f' } v
  | resume {sh : WSh Fx X} {v : X} {f' : Fx.F} {r : WaitRet} : Fx.resume t false sh.f r f' →
      WgStep Fx j t .asleep sh v .load { sh with f := f' } v
  | loadSet {sh : WSh Fx X} {v : X} : sh.ev.val = 2 →
      WgStep Fx j t .load sh v .fin sh (j v sh.ev.msg)
  | loadWaiting {sh : WSh Fx X} {v : X} : sh.ev.val = 1 →
      WgStep Fx j t .load sh v .fwait sh (j v sh.ev.msg)

/-- `Io.Threaded.WaitGroup` over the futex `Fx` (module doc). -/
abbrev threadedWG (Fx : Futex Nat Unit) : JImpl WOp where
  Sh X := WSh Fx X
  init x₀ sh := sh.st = ⟨0, x₀⟩ ∧ sh.ev = ⟨0, x₀⟩ ∧ Fx.init sh.f
  Loc := WL
  start
    | .start => .add
    | .finish => .sub
    | .wait => .wadd
  step j t l sh v l' sh' v' := WgStep Fx j t l sh v l' sh' v'
  done l := l == .fin

namespace WgPlace

/-- The places that a thread can be at. -/
def ok : WCtl WL → Bool
  | .idle | .got | .run .start .add | .run .start .fin | .run .finish .sub | .run .finish .set
  | .run .finish .wake | .run .finish .fin | .run .wait .wadd | .run .wait .cas
  | .run .wait .fwait | .run .wait .asleep | .run .wait .load | .run .wait .fin => true
  | _ => false

/-- A `start` whose `fetchAdd` ran. -/
def pS : WCtl WL → Nat
  | .run .start .fin => 1
  | _ => 0

/-- A `finish` whose `fetchSub` has not run. -/
def pF : WCtl WL → Nat
  | .run .finish .sub => 1
  | _ => 0

/-- The waiter after its `fetchAdd(is_waiting)`. -/
def pW : WCtl WL → Nat
  | .run .wait .cas | .run .wait .fwait | .run .wait .asleep | .run .wait .load
  | .run .wait .fin | .got => 1
  | _ => 0

/-- The waiter. -/
def isW : WCtl WL → Bool
  | .run .wait _ | .got => true
  | _ => false

/-- A finisher after its `fetchSub`. -/
def post : WCtl WL → Bool
  | .run .finish .set | .run .finish .wake | .run .finish .fin => true
  | _ => false

/-- The waiter returned, or is about to. -/
def wdone : WCtl WL → Bool
  | .run .wait .fin | .got => true
  | _ => false

/-- The waiter waits for the event. -/
def wev : WCtl WL → Bool
  | .run .wait .cas | .run .wait .fwait | .run .wait .asleep | .run .wait .load => true
  | _ => false

/-- The waiter is in the futex wait or at the load after it. -/
def wfut : WCtl WL → Bool
  | .run .wait .fwait | .run .wait .asleep | .run .wait .load => true
  | _ => false

end WgPlace

open WgPlace

variable {Fx : Futex Nat Unit}

/-- The pending count: the tokens, the `start`s whose `fetchAdd` ran, and the `finish`es whose
`fetchSub` has not run. -/
def WState.P {X : Type} (N : Nat) (s : WState (threadedWG Fx) X) : Nat :=
  s.tok + tsum N (fun u => pS (s.ctl u)) + tsum N (fun u => pF (s.ctl u))

/-- The invariant of `Threaded.WaitGroup` (module doc). -/
structure WgInv {X : Type} (L : Lat X) (N : Nat) (s : WState (threadedWG Fx) X) : Prop where
  ok : ∀ t, WgPlace.ok (s.ctl t) = true
  idle : ∀ t, N ≤ t → s.ctl t = .idle
  /-- The counter is the pending count, and its bit `is_waiting`. -/
  cnt : s.sh.st.val = 2 * s.P N + tsum N (fun u => pW (s.ctl u))
  one : ∀ t u, isW (s.ctl t) = true → isW (s.ctl u) = true → t = u
  waited : ∀ t, isW (s.ctl t) = true → s.waited = true
  nostart : s.waited = true → ∀ t l, s.ctl t ≠ .run .start l
  evb : s.sh.ev.val ≤ 2
  evw : ∀ t, wfut (s.ctl t) = true → s.sh.ev.val ≠ 0
  /-- Once the event is set, nothing is pending and its message has the counter's. -/
  evset : s.sh.ev.val = 2 → s.P N = 0 ∧ s.waited = true ∧ L.le s.sh.st.msg s.sh.ev.msg
  setter : ∀ t, s.ctl t = .run .finish .set →
    s.P N = 0 ∧ s.waited = true ∧ L.le s.sh.st.msg (s.cur t)
  fin : L.le s.fin s.sh.st.msg
  post : ∀ t, post (s.ctl t) = true → L.le (s.cur t) s.sh.st.msg
  wdone : ∀ t, wdone (s.ctl t) = true → s.P N = 0 ∧ L.le s.sh.st.msg (s.cur t)
  /-- A waiter that waits for the event is not the last one: something is pending, or the
  event is about to be set. -/
  wwait : ∀ t, wev (s.ctl t) = true → s.sh.ev.val ≠ 2 →
    0 < s.P N ∨ ∃ u, s.ctl u = .run .finish .set
  qwf : (Fx.queue s.sh.f).WF
  qloc : ∀ u a, (u, a) ∈ Fx.queue s.sh.f → s.ctl u = .run .wait .asleep
  /-- A sleeping waiter: the event is `waiting`, or a wake is coming. -/
  wit : Fx.queue s.sh.f ≠ [] → s.sh.ev.val = 1 ∨ ∃ u, s.ctl u = .run .finish .wake

/-! ## Helpers -/

theorem tset_apply {β : Type} (f : Tid → β) (t : Tid) (x : β) (u : Tid) :
    tset f t x u = if u = t then x else f u := rfl

/-- How a sum over the threads changes when thread `t` moves (additive form, for `omega`). -/
theorem tsum_move {β : Type} {N : Nat} (g : β → Nat) (f : Tid → β) {t : Tid} (ht : t < N) (c : β) :
    tsum N (fun u => g (tset f t c u)) + g (f t) = tsum N (fun u => g (f u)) + g c :=
  tsum_tset g f ht c

/-- The event word of a sleeping wait is `1`. -/
theorem bv_one {n : Nat} (hn : n ≤ 2) (h : wordView n () = some 1) : n = 1 := by
  have h' := congrArg BitVec.toNat (Option.some.inj h)
  simp only [BitVec.toNat_ofNat] at h'
  have : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  omega

namespace WgInv

variable {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}

theorem op_ok (hi : WgInv L N s) {t : Tid} {op : WOp} {l : WL} (h : s.ctl t = .run op l) :
    WgPlace.ok (.run op l) = true := by
  rw [← h]; exact hi.ok t

theorem pW_le (c : WCtl WL) : pW c ≤ 1 := by
  cases c with
  | run op l => cases op <;> cases l <;> simp [pW]
  | _ => simp [pW]

theorem isW_of_pW {c : WCtl WL} (h : 0 < pW c) : isW c = true := by
  cases c with
  | run op l => cases op <;> cases l <;> simp_all [pW, isW]
  | _ => simp_all [pW, isW]

/-- At most one waiter, so `is_waiting` is one bit. -/
theorem wbit (hi : WgInv L N s) : tsum N (fun u => pW (s.ctl u)) ≤ 1 :=
  tsum_le_one (fun _ => pW_le _) fun u v hu hv => hi.one u v (isW_of_pW hu) (isW_of_pW hv)

/-- A thread `t < N` that has `pW` makes the bit `1`. -/
theorem wbit_eq (hi : WgInv L N s) {t : Tid} (ht : t < N) (h : pW (s.ctl t) = 1) :
    tsum N (fun u => pW (s.ctl u)) = 1 := by
  have := le_tsum (fun u => pW (s.ctl u)) ht
  have := hi.wbit
  omega

/-- A thread at `p` is below `N`. -/
theorem lt_of_ne_idle (hi : WgInv L N s) {t : Tid} (h : s.ctl t ≠ .idle) : t < N :=
  Nat.lt_of_not_le fun hn => h (hi.idle t hn)

theorem not_has (hi : WgInv L N s) {t : Tid} (h : s.ctl t ≠ .run .wait .asleep) :
    (Fx.queue s.sh.f).has t = false :=
  Queue.has_eq_false.mpr fun a ha => h (hi.qloc t a ha)

/-- A thread at `p` makes `tsum N (g ∘ ctl)` positive. -/
theorem pos_of (hi : WgInv L N s) {g : WCtl WL → Nat} {t : Tid} (h : 0 < g (s.ctl t))
    (hidle : g .idle = 0) : 0 < tsum N (fun u => g (s.ctl u)) := by
  have ht : t < N := hi.lt_of_ne_idle fun he => by rw [he, hidle] at h; omega
  have := le_tsum (fun u => g (s.ctl u)) ht
  omega

/-- No `start` runs once `wait` was called, so `pS` sums to `0`. -/
theorem pS_zero (hi : WgInv L N s) (hw : s.waited = true) : tsum N (fun u => pS (s.ctl u)) = 0 :=
  tsum_eq_zero fun u _ => by
    cases hc : s.ctl u with
    | run op l => cases op with
      | start => exact absurd hc (hi.nostart hw u l)
      | _ => rfl
    | _ => rfl

end WgInv

theorem tset_all {β : Type} {Q : β → Prop} {f : Tid → β} {t : Tid} {c : β}
    (hc : Q c) (h : ∀ u, u ≠ t → Q (f u)) : ∀ u, Q (tset f t c u) := by
  intro u; by_cases hu : u = t
  · rw [hu, tset_self]; exact hc
  · rw [tset_ne _ _ hu]; exact h u hu

theorem tset_all2 {β γ : Type} {Q : β → γ → Prop} {f : Tid → β} {g : Tid → γ} {t : Tid} {c : β}
    {v : γ} (hc : Q c v) (h : ∀ u, u ≠ t → Q (f u) (g u)) : ∀ u, Q (tset f t c u) (tset g t v u) := by
  intro u; by_cases hu : u = t
  · rw [hu, tset_self, tset_self]; exact hc
  · rw [tset_ne _ _ hu, tset_ne _ _ hu]; exact h u hu

/-- A hypothesis about the new place of a thread other than `t`. -/
theorem tset_of_ne {β : Type} {f : Tid → β} {t u : Tid} {c : β} (h : u ≠ t) :
    tset f t c u = f u := tset_ne _ _ h


/-! ## The invariant is inductive -/

namespace WgInv

variable {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}

/-- The sums after thread `t` moves from `c` to `c'`. -/
theorem sums (s : WState (threadedWG Fx) X) {t : Tid} (ht : t < N) {c c' : WCtl WL}
    (h : s.ctl t = c) :
    tsum N (fun u => pS (tset s.ctl t c' u)) + pS c = tsum N (fun u => pS (s.ctl u)) + pS c' ∧
    tsum N (fun u => pF (tset s.ctl t c' u)) + pF c = tsum N (fun u => pF (s.ctl u)) + pF c' ∧
    tsum N (fun u => pW (tset s.ctl t c' u)) + pW c = tsum N (fun u => pW (s.ctl u)) + pW c' := by
  subst h
  exact ⟨tsum_move pS s.ctl ht c', tsum_move pF s.ctl ht c', tsum_move pW s.ctl ht c'⟩

/-- The waiter's existence when the bit is set. -/
theorem waited_of_bit (hi : WgInv L N s) (h : 0 < tsum N (fun u => pW (s.ctl u))) :
    s.waited = true := by
  obtain ⟨u, -, hu⟩ := exists_of_tsum_pos h
  exact hi.waited u (isW_of_pW hu)

/-- A thread that is not the waiter has `pW = 0`. -/
theorem pW_of_not_isW {c : WCtl WL} (h : isW c = false) : pW c = 0 := by
  cases c with
  | run op l => cases op <;> cases l <;> simp_all [pW, isW]
  | _ => simp_all [pW, isW]

/-- The bit is clear while the waiter is at its `fetchAdd`. -/
theorem bit_zero (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .wait .wadd) :
    tsum N (fun u => pW (s.ctl u)) = 0 :=
  tsum_eq_zero fun u _ => by
    by_cases hut : u = t
    · rw [hut, h]; rfl
    · cases hw : isW (s.ctl u)
      · exact pW_of_not_isW hw
      · exact absurd (hi.one u t hw (by rw [h]; rfl)) hut

/-- The queue holds at most the one waiter. -/
theorem queue_len (hi : WgInv L N s) : ((Fx.queue s.sh.f).waitersAt ()).length ≤ 1 := by
  have hnd := Queue.waitersAt_nodup hi.qwf ()
  have hall : ∀ a ∈ (Fx.queue s.sh.f).waitersAt (), ∀ b ∈ (Fx.queue s.sh.f).waitersAt (), a = b := by
    intro a ha b hb
    have ha' := hi.qloc a () (Queue.mem_waitersAt.mp ha)
    have hb' := hi.qloc b () (Queue.mem_waitersAt.mp hb)
    exact hi.one a b (by rw [ha']; rfl) (by rw [hb']; rfl)
  revert hnd hall
  generalize (Fx.queue s.sh.f).waitersAt () = l
  intro hnd hall
  match l, hnd, hall with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hnd, hall =>
    have := hall a List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self)
    subst this
    simp at hnd

end WgInv

/-! ### The client's own steps -/

namespace WgInv

variable {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}

theorem learn (hi : WgInv L N s) {t : Tid} (x : X) (h : s.ctl t = .idle ∨ s.ctl t = .got) :
    WgInv L N { s with cur := tset s.cur t (L.join (s.cur t) x) } := by
  have hnr : ∀ op l, s.ctl t ≠ .run op l := by
    intro op l he; rcases h with h | h <;> rw [h] at he <;> cases he
  constructor <;> dsimp only
  · exact hi.ok
  · exact hi.idle
  · exact hi.cnt
  · exact hi.one
  · exact hi.waited
  · exact hi.nostart
  · exact hi.evb
  · exact hi.evw
  · exact hi.evset
  · intro u hu
    have hut : u ≠ t := fun e => hnr _ _ (e ▸ hu)
    rw [tset_ne _ _ hut]; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · subst hut; rcases h with h | h <;> rw [h] at hu <;> cases hu
    · rw [tset_ne _ _ hut]; exact hi.post u hu
  · intro u hu
    obtain ⟨hP, hle⟩ := hi.wdone u hu
    refine ⟨hP, ?_⟩
    by_cases hut : u = t
    · subst hut; rw [tset_self]; exact Lat.le_join_of_le_left _ hle
    · rw [tset_ne _ _ hut]; exact hle
  · exact hi.wwait
  · exact hi.qwf
  · exact hi.qloc
  · exact hi.wit

/-- A thread that moves between places where it is neither the waiter nor a finisher past its
`fetchSub` (a call, the return of `start`), changing only the ghosts. -/
theorem inert (hi : WgInv L N s) {t : Tid} (ht : t < N) {c0 : WCtl WL} (h : s.ctl t = c0)
    (h0W : isW c0 = false) (h0set : c0 ≠ .run .finish .set) (h0wake : c0 ≠ .run .finish .wake)
    (h0asl : c0 ≠ .run .wait .asleep) {c : WCtl WL}
    (hok : WgPlace.ok c = true) (hpW : pW c = 0) (hpost : WgPlace.post c = false)
    (hwd : WgPlace.wdone c = false) (hwev : wev c = false) (hwf : wfut c = false)
    (hset : c ≠ .run .finish .set) {tok : Nat} (htok : tok + pS c + pF c = s.tok + pS c0 + pF c0)
    {w : Bool} (hwt : s.waited = true → w = true) (hisW : isW c = true → w = true ∧ ∀ u, isW (s.ctl u) = false)
    (hns : w = true → (∀ l, c ≠ .run .start l) ∧ ∀ u l, s.ctl u ≠ .run .start l) :
    WgInv L N { s with ctl := tset s.ctl t c, tok := tok, waited := w } := by
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := c) h
  have z3 : pW c0 = 0 := pW_of_not_isW h0W
  have hP : WState.P N { s with ctl := tset s.ctl t c, tok := tok, waited := w } = s.P N := by
    unfold WState.P; dsimp only; omega
  have hidle : ∀ u, u ≠ t → isW (s.ctl u) = true → w = true := fun u _ hu => hwt (hi.waited u hu)
  constructor <;> dsimp only
  · exact tset_all (Q := fun c => WgPlace.ok c = true) hok fun u _ => hi.ok u
  · intro u hu; rw [tset_ne _ _ (fun e => by subst e; tomega)]; exact hi.idle u hu
  · rw [hP]; have := hi.cnt; unfold WState.P at this ⊢; omega
  · intro a b ha hb
    by_cases hat : a = t <;> by_cases hbt : b = t
    · rw [hat, hbt]
    · rw [hat, tset_self] at ha; rw [tset_ne _ _ hbt] at hb
      rw [(hisW ha).2 b] at hb; cases hb
    · rw [hbt, tset_self] at hb; rw [tset_ne _ _ hat] at ha
      rw [(hisW hb).2 a] at ha; cases ha
    · rw [tset_ne _ _ hat] at ha; rw [tset_ne _ _ hbt] at hb; exact hi.one a b ha hb
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; exact (hisW hu).1
    · rw [tset_ne _ _ hut] at hu; exact hidle u hut hu
  · intro hw u l
    obtain ⟨hc, ho⟩ := hns hw
    by_cases hut : u = t
    · rw [hut, tset_self]; exact hc l
    · rw [tset_ne _ _ hut]; exact ho u l
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (fun h => by rw [hwf] at h; cases h)
      fun u _ => hi.evw u
  · intro he; obtain ⟨h1, h2, h3⟩ := hi.evset he; exact ⟨hP ▸ h1, hwt h2, h3⟩
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; exact absurd hu hset
    · rw [tset_ne _ _ hut] at hu
      obtain ⟨h1, h2, h3⟩ := hi.setter u hu; exact ⟨hP ▸ h1, hwt h2, h3⟩
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [hpost] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [hwd] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP]; exact hi.wdone u hu
  · intro u hu hne
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [hwev] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu
      rcases hi.wwait u hu hne with h1 | ⟨v, hv⟩
      · exact .inl (hP ▸ h1)
      · have hvt : v ≠ t := fun e => h0set (by rw [← h, ← e]; exact hv)
        exact .inr ⟨v, by rw [tset_ne _ _ hvt]; exact hv⟩
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    have hut : u ≠ t := fun e => h0asl (by rw [← h, ← e]; exact hu)
    rw [tset_ne _ _ hut]; exact hu
  · intro hne
    rcases hi.wit hne with h1 | ⟨v, hv⟩
    · exact .inl h1
    · have hvt : v ≠ t := fun e => h0wake (by rw [← h, ← e]; exact hv)
      exact .inr ⟨v, by rw [tset_ne _ _ hvt]; exact hv⟩


/-- The clauses about the threads' places, for a move of `t` from `c0` to `c` that keeps it the
waiter or not and starts no `start`. -/
theorem places (hi : WgInv L N s) {t : Tid} (ht : t < N) {c0 c : WCtl WL} (h : s.ctl t = c0)
    (hok : WgPlace.ok c = true) (hW : isW c = isW c0)
    (hS : ∀ l, c = .run .start l → ∃ l0, c0 = .run .start l0) :
    (∀ u, WgPlace.ok (tset s.ctl t c u) = true) ∧ (∀ u, N ≤ u → tset s.ctl t c u = .idle) ∧
    (∀ a b, isW (tset s.ctl t c a) = true → isW (tset s.ctl t c b) = true → a = b) ∧
    (∀ u, isW (tset s.ctl t c u) = true → s.waited = true) ∧
    (s.waited = true → ∀ u l, tset s.ctl t c u ≠ .run .start l) := by
  have hown : ∀ u, isW (tset s.ctl t c u) = isW (s.ctl u) := by
    intro u; by_cases hu : u = t
    · rw [hu, tset_self, hW, h]
    · rw [tset_ne _ _ hu]
  refine ⟨tset_all (Q := fun c => WgPlace.ok c = true) hok fun u _ => hi.ok u, fun u hu => ?_,
    fun a b ha hb => hi.one a b (hown a ▸ ha) (hown b ▸ hb), fun u hu => hi.waited u (hown u ▸ hu),
    fun hw u l => ?_⟩
  · rw [tset_ne _ _ (fun e => by subst e; tomega)]; exact hi.idle u hu
  · by_cases hu : u = t
    · rw [hu, tset_self]; intro he
      obtain ⟨l0, hl0⟩ := hS l he
      exact hi.nostart hw t l0 (h.trans hl0)
    · rw [tset_ne _ _ hu]; exact hi.nostart hw u l

/-- The waiter's places are not a `start`'s or a `finish`'s. -/
theorem pS_pF_of_pW {c : WCtl WL} (h : pW c = 1) : pS c = 0 ∧ pF c = 0 := by
  cases c with
  | run op l => cases op <;> cases l <;> simp_all [pW, pS, pF]
  | _ => simp_all [pW, pS, pF]

/-- A step of the waiter between places after its `fetchAdd`, outside the futex, that changes
only its view. -/
theorem wmove (hi : WgInv L N s) {t : Tid} (ht : t < N) {c0 c : WCtl WL} (h : s.ctl t = c0)
    (hW0 : pW c0 = 1) (hW : pW c = 1) (hok : WgPlace.ok c = true) (hiW : isW c = isW c0)
    (h0asl : c0 ≠ .run .wait .asleep) {v' : X}
    (hevw : wfut c = true → s.sh.ev.val ≠ 0)
    (hwd : WgPlace.wdone c = true → s.P N = 0 ∧ L.le s.sh.st.msg v')
    (hwev : wev c = true → s.sh.ev.val ≠ 2 → 0 < s.P N ∨ ∃ u, s.ctl u = .run .finish .set) :
    WgInv L N { s with ctl := tset s.ctl t c, cur := tset s.cur t v' } := by
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := c) h
  obtain ⟨z1, z2⟩ := pS_pF_of_pW hW0
  obtain ⟨z1', z2'⟩ := pS_pF_of_pW hW
  have hP : WState.P N { s with ctl := tset s.ctl t c, cur := tset s.cur t v' } = s.P N := by
    unfold WState.P; dsimp only; omega
  have hpost0 : ∀ {c : WCtl WL}, pW c = 1 → WgPlace.post c = false := by
    intro c hc; cases c with
    | run op l => cases op <;> cases l <;> simp_all [pW, WgPlace.post]
    | _ => simp_all [pW, WgPlace.post]
  have hne : ∀ {c : WCtl WL} {op l}, pW c = 1 → op ≠ WOp.wait → c ≠ .run op l := by
    intro c op l hc hop he; subst he; cases op <;> cases l <;> simp_all [pW]
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h hok hiW fun l he => absurd he (hne hW (by decide))
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · rw [hP]; have := hi.cnt; unfold WState.P at this ⊢; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) hevw fun u _ => hi.evw u
  · intro he; rw [hP]; exact hi.evset he
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; exact absurd hu (hne hW (by decide))
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut, hP]; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [hpost0 hW] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [hut, tset_self, hP]; exact hwd hu
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut, hP]; exact hi.wdone u hu
  · intro u hu hev
    have hset : ∀ v, s.ctl v = .run .finish .set → tset s.ctl t c v = .run .finish .set := by
      intro v hv
      have hvt : v ≠ t := fun e => hne hW0 (op := .finish) (by decide) (by rw [← h, ← e]; exact hv)
      rw [tset_ne _ _ hvt]; exact hv
    rw [hP]
    by_cases hut : u = t
    · rw [hut, tset_self] at hu
      rcases hwev hu hev with h1 | ⟨v, hv⟩
      · exact .inl h1
      · exact .inr ⟨v, hset v hv⟩
    · rw [tset_ne _ _ hut] at hu
      rcases hi.wwait u hu hev with h1 | ⟨v, hv⟩
      · exact .inl h1
      · exact .inr ⟨v, hset v hv⟩
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    have hut : u ≠ t := fun e => h0asl (by rw [← h, ← e]; exact hu)
    rw [tset_ne _ _ hut]; exact hu
  · intro hq
    rcases hi.wit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · have hvt : v ≠ t := fun e => hne hW0 (op := .finish) (by decide) (by rw [← h, ← e]; exact hv)
      exact .inr ⟨v, by rw [tset_ne _ _ hvt]; exact hv⟩

end WgInv


/-! ### Steps of the implementation -/

namespace WgInv

variable {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}

theorem isW_of_wdone {c : WCtl WL} (h : WgPlace.wdone c = true) : isW c = true := by
  cases c with
  | run op l => cases op <;> cases l <;> simp_all [WgPlace.wdone, isW]
  | _ => simp_all [WgPlace.wdone, isW]

theorem isW_of_wev {c : WCtl WL} (h : wev c = true) : isW c = true := by
  cases c with
  | run op l => cases op <;> cases l <;> simp_all [wev, isW]
  | _ => simp_all [wev]

theorem pW_of_wev {c : WCtl WL} (h : wev c = true) : pW c = 1 := by
  cases c with
  | run op l => cases op <;> cases l <;> simp_all [wev, pW]
  | _ => simp_all [wev]

theorem ne_of_ctl {t u : Tid} {a b : WCtl WL} (hu : s.ctl u = a) (ht : s.ctl t = b) (hab : a ≠ b) :
    u ≠ t := fun e => hab (by rw [← hu, ← ht, e])

/-- `start`'s `fetchAdd`. -/
theorem add (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .start .add) :
    WgInv L N { s with
      sh := { s.sh with st := ⟨s.sh.st.val + 2, s.sh.st.msg⟩ }
      ctl := tset s.ctl t (.run .start .fin)
      cur := tset s.cur t (s.cur t) } := by
  rw [tset_id]
  have ht : t < N := hi.lt_of_ne_idle (by rw [h]; intro he; cases he)
  have hw : s.waited = false := by
    cases hw : s.waited
    · rfl
    · exact absurd h (hi.nostart hw t _)
  have nw : ∀ u, isW (s.ctl u) = false := fun u => by
    cases hu : isW (s.ctl u)
    · rfl
    · rw [hi.waited u hu] at hw; cases hw
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := .run .start .fin) h
  have z : pS (.run .start .add : WCtl WL) = 0 ∧ pS (.run .start .fin : WCtl WL) = 1 ∧
    pF (.run .start .add : WCtl WL) = 0 ∧ pF (.run .start .fin : WCtl WL) = 0 ∧
    pW (.run .start .add : WCtl WL) = 0 ∧ pW (.run .start .fin : WCtl WL) = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h (c := .run .start .fin) rfl rfl fun _ _ => ⟨_, rfl⟩
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · have := hi.cnt; unfold WState.P at this ⊢; dsimp only; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact hi.evw u hu
  · intro he; rw [(hi.evset he).2.1] at hw; cases hw
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [(hi.setter u hu).2.1] at hw; cases hw
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact absurd (isW_of_wdone hu) (by rw [nw u]; simp)
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact absurd (isW_of_wev hu) (by rw [nw u]; simp)
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    rw [tset_ne _ _ (ne_of_ctl hu h (by intro he; cases he))]; exact hu
  · intro hq
    rcases hi.wit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, by rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv⟩


theorem lt_of_run (hi : WgInv L N s) {t : Tid} {op : WOp} {l : WL} (h : s.ctl t = .run op l) : t < N :=
  hi.lt_of_ne_idle (by rw [h]; intro he; cases he)

/-- `finish`'s `fetchSub` that reads `3` (the last pending, with the waiter): the event's `set`
comes next. -/
theorem subSet (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .finish .sub) (h3 : s.sh.st.val = 3) :
    WgInv L N { s with
      sh := { s.sh with st := ⟨1, L.join (s.cur t) s.sh.st.msg⟩ }
      ctl := tset s.ctl t (.run .finish .set)
      cur := tset s.cur t (L.join (s.cur t) s.sh.st.msg) } := by
  have ht := hi.lt_of_run h
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := .run .finish .set) h
  have z : pS (.run .finish .sub : WCtl WL) = 0 ∧ pS (.run .finish .set : WCtl WL) = 0 ∧
    pF (.run .finish .sub : WCtl WL) = 1 ∧ pF (.run .finish .set : WCtl WL) = 0 ∧
    pW (.run .finish .sub : WCtl WL) = 0 ∧ pW (.run .finish .set : WCtl WL) = 0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := hi.cnt
  have hb := hi.wbit
  unfold WState.P at hc
  have hP1 : s.P N = 1 := by unfold WState.P; omega
  have hw : s.waited = true := hi.waited_of_bit (by omega)
  have hP' : WState.P N { s with
      sh := { s.sh with st := ⟨1, L.join (s.cur t) s.sh.st.msg⟩ }
      ctl := tset s.ctl t (.run .finish .set)
      cur := tset s.cur t (L.join (s.cur t) s.sh.st.msg) } = 0 := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h (c := .run .finish .set) rfl rfl
    fun _ he => by cases he
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · rw [hP']; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (by simp [wfut])
      fun u _ => hi.evw u
  · intro he; have := (hi.evset he).1; omega
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self]; exact ⟨hP', hw, Lat.le_refl _⟩
    · rw [tset_ne _ _ hut] at hu; have := (hi.setter u hu).1; omega
  · exact Lat.le_join_of_le_right _ hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self]; exact Lat.le_refl _
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]
      exact Lat.le_join_of_le_right _ (hi.post u hu)
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; simp [WgPlace.wdone] at hu
    · rw [tset_ne _ _ hut] at hu; have := (hi.wdone u hu).1; omega
  · intro _ _ _; exact .inr ⟨t, tset_self _ _ _⟩
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    rw [tset_ne _ _ (ne_of_ctl hu h (by intro he; cases he))]; exact hu
  · intro hq
    rcases hi.wit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, by rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv⟩

/-- `finish`'s `fetchSub` that leaves something pending. -/
theorem subDone (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .finish .sub)
    (h2 : 2 ≤ s.sh.st.val) (h3 : s.sh.st.val ≠ 3) :
    WgInv L N { s with
      sh := { s.sh with st := ⟨s.sh.st.val - 2, L.join (s.cur t) s.sh.st.msg⟩ }
      ctl := tset s.ctl t (.run .finish .fin)
      cur := tset s.cur t (L.join (s.cur t) s.sh.st.msg) } := by
  have ht := hi.lt_of_run h
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := .run .finish .fin) h
  have z : pS (.run .finish .sub : WCtl WL) = 0 ∧ pS (.run .finish .fin : WCtl WL) = 0 ∧
    pF (.run .finish .sub : WCtl WL) = 1 ∧ pF (.run .finish .fin : WCtl WL) = 0 ∧
    pW (.run .finish .sub : WCtl WL) = 0 ∧ pW (.run .finish .fin : WCtl WL) = 0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := hi.cnt
  have hb := hi.wbit
  unfold WState.P at hc
  have hPdef : s.P N = s.tok + tsum N (fun u => pS (s.ctl u)) + tsum N (fun u => pF (s.ctl u)) := rfl
  have hP1 : 1 ≤ s.P N := by omega
  have hP' : WState.P N { s with
      sh := { s.sh with st := ⟨s.sh.st.val - 2, L.join (s.cur t) s.sh.st.msg⟩ }
      ctl := tset s.ctl t (.run .finish .fin)
      cur := tset s.cur t (L.join (s.cur t) s.sh.st.msg) } + 1 = s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h (c := .run .finish .fin) rfl rfl
    fun _ he => by cases he
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · unfold WState.P; dsimp only; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (by simp [wfut])
      fun u _ => hi.evw u
  · intro he; have := (hi.evset he).1; omega
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; have := (hi.setter u hu).1; omega
  · exact Lat.le_join_of_le_right _ hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self]; exact Lat.le_refl _
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]
      exact Lat.le_join_of_le_right _ (hi.post u hu)
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; simp [WgPlace.wdone] at hu
    · rw [tset_ne _ _ hut] at hu; have := (hi.wdone u hu).1; omega
  · intro u hu _
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; simp [wev] at hu
    · rw [tset_ne _ _ hut] at hu
      have hW := hi.wbit_eq (hi.lt_of_ne_idle (fun he => by rw [he] at hu; simp [wev] at hu))
        (pW_of_wev hu)
      left; unfold WState.P; dsimp only; omega
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    rw [tset_ne _ _ (ne_of_ctl hu h (by intro he; cases he))]; exact hu
  · intro hq
    rcases hi.wit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, by rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv⟩

/-- `eventSet`'s `xchg(.is_set, .release)`: the wake comes next if the waiter waits. -/
theorem setE (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .finish .set) {c : WCtl WL}
    (hc : c = .run .finish .wake ∨ c = .run .finish .fin) (h1 : s.sh.ev.val = 1 → c = .run .finish .wake) :
    WgInv L N { s with
      sh := { s.sh with ev := ⟨2, L.join s.sh.ev.msg (s.cur t)⟩ }
      ctl := tset s.ctl t c
      cur := tset s.cur t (s.cur t) } := by
  rw [tset_id]
  have ht := hi.lt_of_run h
  obtain ⟨hP, hw, hle⟩ := hi.setter t h
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := c) h
  have hz : pS c = 0 ∧ pF c = 0 ∧ pW c = 0 ∧ WgPlace.post c = true ∧ WgPlace.ok c = true ∧
      isW c = false ∧ WgPlace.wdone c = false ∧ wev c = false ∧ wfut c = false ∧
      c ≠ .run .finish .set ∧ c ≠ .run .wait .asleep := by
    rcases hc with rfl | rfl <;> refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;>
      intro he <;> cases he
  obtain ⟨zS, zF, zW, zpost, zok, zisW, zwd, zwev, zwf, zset, zasl⟩ := hz
  have z : pS (.run .finish .set : WCtl WL) = 0 ∧ pF (.run .finish .set : WCtl WL) = 0 ∧
    pW (.run .finish .set : WCtl WL) = 0 := ⟨rfl, rfl, rfl⟩
  have hP' : WState.P N { s with
      sh := { s.sh with ev := ⟨2, L.join s.sh.ev.msg (s.cur t)⟩ }
      ctl := tset s.ctl t c } = s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h zok (by rw [zisW]; rfl)
    fun l he => by rcases hc with rfl | rfl <;> cases he
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · rw [hP']; have := hi.cnt; omega
  · exact c3
  · exact c4
  · exact c5
  · exact Nat.le_refl _
  · intro _ _ he; cases he
  · intro _; exact ⟨hP' ▸ hP, hw, Lat.le_join_of_le_right _ hle⟩
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; exact absurd hu zset
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut]; exact hi.post t (by rw [h]; rfl)
    · rw [tset_ne _ _ hut] at hu; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [zwd] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.wdone u hu
  · intro _ _ he; exact absurd rfl he
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    have hut : u ≠ t := ne_of_ctl hu h (by intro he; cases he)
    rw [tset_ne _ _ hut]; exact hu
  · intro hq
    rcases hi.wit hq with h1' | ⟨v, hv⟩
    · exact .inr ⟨t, by rw [tset_self]; exact h1 h1'⟩
    · exact .inr ⟨v, by rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv⟩

/-- `wait`'s `fetchAdd(is_waiting, .acquire)`, with the new place `c` (`cas` if something is
pending, else the return). -/
theorem wadd (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .wait .wadd)
    {c : WCtl WL} (hc : c = .run .wait .cas ∨ c = .run .wait .fin)
    (hcas : c = .run .wait .cas → 2 ≤ s.sh.st.val) (hfin : c = .run .wait .fin → s.sh.st.val = 0) :
    WgInv L N { s with
      sh := { s.sh with st := ⟨s.sh.st.val + 1, s.sh.st.msg⟩ }
      ctl := tset s.ctl t c
      cur := tset s.cur t (L.join (s.cur t) s.sh.st.msg) } := by
  have ht := hi.lt_of_run h
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := c) h
  have h0 := hi.bit_zero h
  have hz : pS c = 0 ∧ pF c = 0 ∧ pW c = 1 ∧ WgPlace.ok c = true ∧ isW c = true ∧
      WgPlace.post c = false ∧ wfut c = false ∧ (∀ op l, op ≠ .wait → c ≠ .run op l) := by
    rcases hc with rfl | rfl <;> refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩ <;>
      intro op l hop he <;> cases he <;> exact hop rfl
  obtain ⟨zS, zF, zW, zok, zisW, zpost, zwf, zop⟩ := hz
  have z : pS (.run .wait .wadd : WCtl WL) = 0 ∧ pF (.run .wait .wadd : WCtl WL) = 0 ∧
    pW (.run .wait .wadd : WCtl WL) = 0 := ⟨rfl, rfl, rfl⟩
  have hc' := hi.cnt
  have hPdef : s.P N = s.tok + tsum N (fun u => pS (s.ctl u)) + tsum N (fun u => pF (s.ctl u)) := rfl
  have hP' : WState.P N { s with
      sh := { s.sh with st := ⟨s.sh.st.val + 1, s.sh.st.msg⟩ }
      ctl := tset s.ctl t c
      cur := tset s.cur t (L.join (s.cur t) s.sh.st.msg) } = s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h zok (by rw [zisW]; rfl)
    fun l he => (zop .start l (by intro e; cases e) he).elim
  have hset : ∀ v, s.ctl v = .run .finish .set → tset s.ctl t c v = .run .finish .set := fun v hv => by
    rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · unfold WState.P; dsimp only; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (by rw [zwf]; intro he; cases he)
      fun u _ => hi.evw u
  · intro he'; rw [hP']; exact hi.evset he'
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; exact absurd hu (zop .finish .set (by intro e; cases e))
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut, hP']; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [zpost] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]; exact hi.post u hu
  · intro u hu
    rw [hP']
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [hut, tset_self]
      rcases hc with rfl | rfl
      · simp [WgPlace.wdone] at hu
      · exact ⟨by have := hfin rfl; omega, Lat.le_join_right _ _⟩
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]; exact hi.wdone u hu
  · intro u hu hev
    rw [hP']
    by_cases hut : u = t
    · rw [hut, tset_self] at hu
      rcases hc with rfl | rfl
      · exact .inl (by have := hcas rfl; omega)
      · simp [wev] at hu
    · rw [tset_ne _ _ hut] at hu
      rcases hi.wwait u hu hev with h1 | ⟨v, hv⟩
      · exact .inl h1
      · exact .inr ⟨v, hset v hv⟩
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    rw [tset_ne _ _ (ne_of_ctl hu h (by intro he; cases he))]; exact hu
  · intro hq
    rcases hi.wit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, by rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv⟩

/-- `eventWait`'s `cmpxchg` that sets the event to `waiting`. -/
theorem casSet (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .wait .cas) (h0 : s.sh.ev.val = 0) :
    WgInv L N { s with
      sh := { s.sh with ev := ⟨1, s.sh.ev.msg⟩ }
      ctl := tset s.ctl t (.run .wait .fwait)
      cur := tset s.cur t (L.join (s.cur t) s.sh.ev.msg) } := by
  have ht := hi.lt_of_run h
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := .run .wait .fwait) h
  have z : pS (.run .wait .cas : WCtl WL) = 0 ∧ pF (.run .wait .cas : WCtl WL) = 0 ∧
    pW (.run .wait .cas : WCtl WL) = 1 ∧ pS (.run .wait .fwait : WCtl WL) = 0 ∧
    pF (.run .wait .fwait : WCtl WL) = 0 ∧ pW (.run .wait .fwait : WCtl WL) = 1 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc' := hi.cnt
  have hPdef : s.P N = s.tok + tsum N (fun u => pS (s.ctl u)) + tsum N (fun u => pF (s.ctl u)) := rfl
  have hP' : WState.P N { s with
      sh := { s.sh with ev := ⟨1, s.sh.ev.msg⟩ }
      ctl := tset s.ctl t (.run .wait .fwait)
      cur := tset s.cur t (L.join (s.cur t) s.sh.ev.msg) } = s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h (c := .run .wait .fwait) rfl rfl
    fun _ he => by cases he
  have hset : ∀ v, s.ctl v = .run .finish .set → tset s.ctl t (.run .wait .fwait) v = .run .finish .set :=
    fun v hv => by rw [tset_ne _ _ (ne_of_ctl hv h (by intro he; cases he))]; exact hv
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · unfold WState.P; dsimp only; omega
  · exact c3
  · exact c4
  · exact c5
  · decide
  · intro _ _ he; cases he
  · intro he; cases he
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut, hP']; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut]; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [tset_ne _ _ hut, hP']; exact hi.wdone u hu
  · intro u hu _
    rw [hP']
    have hu' : wev (s.ctl u) = true := by
      by_cases hut : u = t
      · rw [hut, h]; rfl
      · rw [tset_ne _ _ hut] at hu; exact hu
    rcases hi.wwait u hu' (by rw [h0]; decide) with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, hset v hv⟩
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    rw [tset_ne _ _ (ne_of_ctl hu h (by intro he; cases he))]; exact hu
  · intro _; exact .inl rfl

/-- The waiter's places in its futex wait. -/
theorem wfut_facts {c : WCtl WL} (hc : wfut c = true) :
    pS c = 0 ∧ pF c = 0 ∧ pW c = 1 ∧ WgPlace.ok c = true ∧ isW c = true ∧ WgPlace.post c = false ∧
    WgPlace.wdone c = false ∧ wev c = true ∧ (∀ op l, op ≠ .wait → c ≠ .run op l) := by
  match c, hc with
  | .run .wait .fwait, _ | .run .wait .asleep, _ | .run .wait .load, _ =>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun op l hop he => by cases he; exact hop rfl⟩

/-- A step of the waiter in its futex wait that changes only the futex. -/
theorem wq (hi : WgInv L N s) {t : Tid} {c0 c : WCtl WL} (h : s.ctl t = c0) (hc0 : wfut c0 = true)
    (hc : wfut c = true) {f' : Fx.F} (hqwf : (Fx.queue f').WF)
    (hqloc : ∀ u a, (u, a) ∈ Fx.queue f' → tset s.ctl t c u = .run .wait .asleep)
    (hwit : Fx.queue f' ≠ [] → s.sh.ev.val = 1 ∨ ∃ u, s.ctl u = .run .finish .wake) :
    WgInv L N { s with
      sh := { s.sh with f := f' }
      ctl := tset s.ctl t c
      cur := tset s.cur t (s.cur t) } := by
  rw [tset_id]
  have hfw := @wfut_facts
  obtain ⟨zS0, zF0, zW0, -, zisW0, -, -, zwev0, zop0⟩ := hfw hc0
  obtain ⟨zS, zF, zW, zok, zisW, zpost, zwd, zwev, zop⟩ := hfw hc
  have ht : t < N := hi.lt_of_ne_idle (by rw [h]; intro he; rw [he] at hc0; cases hc0)
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := c) h
  have hP' : WState.P N { s with sh := { s.sh with f := f' }, ctl := tset s.ctl t c } = s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h zok (by rw [zisW, zisW0])
    fun l he => (zop .start l (by intro e; cases e) he).elim
  have hset : ∀ v, s.ctl v = .run .finish .set → tset s.ctl t c v = .run .finish .set := fun v hv => by
    rw [tset_ne _ _ (fun e => zop0 .finish .set (by intro e; cases e) (by rw [← h, ← e]; exact hv))]
    exact hv
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · rw [hP']; have := hi.cnt; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (fun _ => hi.evw t (by rw [h]; exact hc0))
      fun u _ => hi.evw u
  · intro he; rw [hP']; exact hi.evset he
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; exact absurd hu (zop .finish .set (by intro e; cases e))
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [zpost] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; rw [zwd] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.wdone u hu
  · intro u hu hev
    rw [hP']
    have hu' : wev (s.ctl u) = true := by
      by_cases hut : u = t
      · rw [hut, h]; exact zwev0
      · rw [tset_ne _ _ hut] at hu; exact hu
    rcases hi.wwait u hu' hev with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, hset v hv⟩
  · exact hqwf
  · exact hqloc
  · intro hq
    rcases hwit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · refine .inr ⟨v, ?_⟩
      rw [tset_ne _ _ (fun e => zop0 .finish .wake (by intro e; cases e) (by rw [← h, ← e]; exact hv))]
      exact hv

/-- The return of `finish`: its view joins `fin`. -/
theorem retFinish (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .finish .fin) :
    WgInv L N { s with ctl := tset s.ctl t .idle, fin := L.join s.fin (s.cur t) } := by
  have ht := hi.lt_of_run h
  obtain ⟨e1, e2, e3⟩ := sums s ht (c' := .idle) h
  have z : pS (.run .finish .fin : WCtl WL) = 0 ∧ pF (.run .finish .fin : WCtl WL) = 0 ∧
    pW (.run .finish .fin : WCtl WL) = 0 ∧ pS (.idle : WCtl WL) = 0 ∧ pF (.idle : WCtl WL) = 0 ∧
    pW (.idle : WCtl WL) = 0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP' : WState.P N { s with ctl := tset s.ctl t .idle, fin := L.join s.fin (s.cur t) } = s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := places hi ht h (c := .idle) rfl rfl fun _ he => by cases he
  have ne : ∀ {u : Tid} {c : WCtl WL}, s.ctl u = c → c ≠ .run .finish .fin → u ≠ t :=
    fun hu hc => ne_of_ctl hu h hc
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · rw [hP']; have := hi.cnt; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (by intro he; cases he)
      fun u _ => hi.evw u
  · intro he; rw [hP']; exact hi.evset he
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.setter u hu
  · exact Lat.join_le hi.fin (hi.post t (by rw [h]; rfl))
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.wdone u hu
  · intro u hu hev
    rw [hP']
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu
      rcases hi.wwait u hu hev with h1 | ⟨v, hv⟩
      · exact .inl h1
      · exact .inr ⟨v, by rw [tset_ne _ _ (ne hv (by intro he; cases he))]; exact hv⟩
  · exact hi.qwf
  · intro u a ha
    have hu := hi.qloc u a ha
    rw [tset_ne _ _ (ne hu (by intro he; cases he))]; exact hu
  · intro hq
    rcases hi.wit hq with h1 | ⟨v, hv⟩
    · exact .inl h1
    · exact .inr ⟨v, by rw [tset_ne _ _ (ne hv (by intro he; cases he))]; exact hv⟩

end WgInv


section
variable (hF : FutexSpec wordView Fx)
include hF

theorem threadedWG_init {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}
    (h : (wmgc (threadedWG Fx) X L N).init s) : WgInv L N s := by
  obtain ⟨x₀, ⟨hst, hev, hf⟩, hctl, hcur, htok, hfin, hw⟩ := h
  have hq := hF.init _ hf
  have hz : ∀ (g : WCtl WL → Nat), g .idle = 0 → tsum N (fun u => g (s.ctl u)) = 0 :=
    fun g hg => tsum_eq_zero fun u _ => by rw [hctl]; exact hg
  have hP : s.P N = 0 := by
    unfold WState.P; rw [htok, hz pS rfl, hz pF rfl]
  constructor
  · intro t; rw [hctl]; rfl
  · intro t _; exact hctl t
  · rw [hP, hz pW rfl, hst]
  · intro t u ht; rw [hctl] at ht; cases ht
  · intro t ht; rw [hctl] at ht; cases ht
  · intro h; rw [hw] at h; cases h
  · rw [hev]; exact Nat.zero_le _
  · intro t ht; rw [hctl] at ht; cases ht
  · intro h; rw [hev] at h; cases h
  · intro t ht; rw [hctl] at ht; cases ht
  · rw [hfin, hst]; exact Lat.le_refl _
  · intro t ht; rw [hctl] at ht; cases ht
  · intro t ht; rw [hctl] at ht; cases ht
  · intro t ht; rw [hctl] at ht; cases ht
  · rw [hq]; exact Queue.WF.nil
  · intro u a ha; rw [hq] at ha; cases ha
  · intro hne; exact absurd hq hne

/-- `eventSet`'s `futexWake(maxInt(u32))`: it wakes the waiter. -/
theorem threadedWG_wake {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}
    (hi : WgInv L N s) {t : Tid} (h : s.ctl t = .run .finish .wake) {f' : Fx.F}
    (hk : Fx.wake t () (2 ^ 32 - 1) s.sh.f f') :
    WgInv L N { s with
      sh := { s.sh with f := f' }
      ctl := tset s.ctl t (.run .finish .fin)
      cur := tset s.cur t (s.cur t) } := by
  rw [tset_id]
  have ht := hi.lt_of_run h
  obtain ⟨e1, e2, e3⟩ := WgInv.sums s ht (c' := .run .finish .fin) h
  have z : pS (.run .finish .wake : WCtl WL) = 0 ∧ pF (.run .finish .wake : WCtl WL) = 0 ∧
    pW (.run .finish .wake : WCtl WL) = 0 ∧ pS (.run .finish .fin : WCtl WL) = 0 ∧
    pF (.run .finish .fin : WCtl WL) = 0 ∧ pW (.run .finish .fin : WCtl WL) = 0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP' : WState.P N { s with sh := { s.sh with f := f' }, ctl := tset s.ctl t (.run .finish .fin) } =
      s.P N := by
    unfold WState.P; dsimp only; omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := WgInv.places hi ht h (c := .run .finish .fin) rfl rfl
    fun _ he => by cases he
  have hempty : Fx.queue f' = [] := by
    have hall := hF.wake_all hi.qwf hk (by have := hi.queue_len; omega)
    exact List.eq_nil_iff_forall_not_mem.mpr fun ⟨u, ()⟩ hm => hall u hm
  have ne : ∀ {u : Tid} {c : WCtl WL}, s.ctl u = c → c ≠ .run .finish .wake → u ≠ t :=
    fun hu hc => WgInv.ne_of_ctl hu h hc
  constructor <;> dsimp only
  · exact c1
  · exact c2
  · rw [hP']; have := hi.cnt; omega
  · exact c3
  · exact c4
  · exact c5
  · exact hi.evb
  · exact tset_all (Q := fun c => wfut c = true → s.sh.ev.val ≠ 0) (by intro he; cases he)
      fun u _ => hi.evw u
  · intro he; rw [hP']; exact hi.evset he
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.setter u hu
  · exact hi.fin
  · intro u hu
    by_cases hut : u = t
    · rw [hut]; exact hi.post t (by rw [h]; rfl)
    · rw [tset_ne _ _ hut] at hu; exact hi.post u hu
  · intro u hu
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu; rw [hP']; exact hi.wdone u hu
  · intro u hu hev
    rw [hP']
    by_cases hut : u = t
    · rw [hut, tset_self] at hu; cases hu
    · rw [tset_ne _ _ hut] at hu
      rcases hi.wwait u hu hev with h1 | ⟨v, hv⟩
      · exact .inl h1
      · exact .inr ⟨v, by rw [tset_ne _ _ (ne hv (by intro he; cases he))]; exact hv⟩
  · rw [hempty]; exact Queue.WF.nil
  · intro u a ha; rw [hempty] at ha; cases ha
  · intro hq; exact absurd hempty hq

/-- A step of thread `t < N` keeps the invariant. -/
theorem threadedWG_step {X : Type} {L : Lat X} {N : Nat} {t : Tid} {s s' : WState (threadedWG Fx) X}
    (hi : WgInv L N s) (ht : t < N) (hs : WStep (threadedWG Fx) L t s s') : WgInv L N s' := by
  cases hs with
  | learn x h => exact hi.learn x h
  | start h hw =>
    exact hi.inert ht h (c := .run .start .add) (tok := s.tok) (w := s.waited) (h0W := rfl)
      (h0set := by intro he; cases he) (h0wake := by intro he; cases he)
      (h0asl := by intro he; cases he) (hok := rfl) (hpW := rfl) (hpost := rfl) (hwd := rfl)
      (hwev := rfl) (hwf := rfl) (hset := by intro he; cases he) (htok := rfl) (hwt := id)
      (hisW := fun he => by cases he) (hns := fun hw' => by rw [hw] at hw'; cases hw')
  | finish h hk =>
    exact hi.inert ht h (c := .run .finish .sub) (tok := s.tok - 1) (w := s.waited) (h0W := rfl)
      (h0set := by intro he; cases he) (h0wake := by intro he; cases he)
      (h0asl := by intro he; cases he) (hok := rfl) (hpW := rfl) (hpost := rfl) (hwd := rfl)
      (hwev := rfl) (hwf := rfl) (hset := by intro he; cases he)
      (htok := by show s.tok - 1 + 0 + 1 = s.tok + 0 + 0; omega) (hwt := id)
      (hisW := fun he => by cases he) (hns := fun hw => ⟨fun l he => (by cases he), hi.nostart hw⟩)
  | wait h hw hs =>
    exact hi.inert ht h (c := .run .wait .wadd) (tok := s.tok) (w := true) (h0W := rfl)
      (h0set := by intro he; cases he) (h0wake := by intro he; cases he)
      (h0asl := by intro he; cases he) (hok := rfl) (hpW := rfl) (hpost := rfl) (hwd := rfl)
      (hwev := rfl) (hwf := rfl) (hset := by intro he; cases he) (htok := rfl) (hwt := fun _ => rfl)
      (hisW := fun _ => ⟨rfl, fun u => by
        cases hu : isW (s.ctl u)
        · rfl
        · rw [hi.waited u hu] at hw; cases hw⟩)
      (hns := fun _ => ⟨fun l he => (by cases he), hs⟩)
  | retStart h hd =>
    rename_i l
    cases l <;> simp at hd
    exact hi.inert ht h (c := .idle) (tok := s.tok + 1) (w := s.waited) (h0W := rfl)
      (h0set := by intro he; cases he) (h0wake := by intro he; cases he)
      (h0asl := by intro he; cases he) (hok := rfl) (hpW := rfl) (hpost := rfl) (hwd := rfl)
      (hwev := rfl) (hwf := rfl) (hset := by intro he; cases he) (htok := rfl) (hwt := id)
      (hisW := fun he => by cases he) (hns := fun hw => ⟨fun l he => (by cases he), hi.nostart hw⟩)
  | retFinish h hd =>
    rename_i l
    cases l <;> simp at hd
    exact hi.retFinish h
  | retWait h hd =>
    rename_i l
    cases l <;> simp at hd
    have := hi.wmove ht h (c := .got) (v' := s.cur t) rfl rfl rfl rfl (by intro he; cases he)
      (by intro he; cases he) (fun _ => (hi.wdone t (by rw [h]; rfl)))
      (by intro he; cases he)
    rw [tset_id] at this
    exact this
  | exec h hstep =>
    rename_i op l l' sh' v'
    have hok := hi.op_ok h
    cases hstep with
    | add =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.add h
    | subSet h3 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.subSet h h3
    | subDone h2 h3 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.subDone h h2 h3
    | setWake h1 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.setE h (.inl rfl) fun _ => rfl
    | setDone h1 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.setE h (.inr rfl) fun h1' => absurd h1' h1
    | wake hk =>
      cases op <;> try exact absurd hok (by decide)
      exact threadedWG_wake hF hi h hk
    | waddWait he h2 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.wadd h (.inl rfl) (fun _ => h2) fun he' => by cases he'
    | waddDone h0 =>
      cases op <;> try exact absurd hok (by decide)
      have := hi.wadd h (.inr rfl) (fun he' => by cases he') fun _ => h0
      rw [h0] at this; exact this
    | casSet h0 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.casSet h h0
    | casWaiting h1 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.wmove ht h (c := .run .wait .fwait) rfl rfl rfl rfl (by intro he; cases he)
        (fun _ => by rw [h1]; decide) (fun he => by cases he)
        fun _ hne => hi.wwait t (by rw [h]; rfl) hne
    | casIsSet h2 =>
      cases op <;> try exact absurd hok (by decide)
      obtain ⟨hP, -, hle⟩ := hi.evset h2
      exact hi.wmove ht h (c := .run .wait .fin) rfl rfl rfl rfl (by intro he; cases he)
        (fun he => by cases he)
        (fun _ => ⟨hP, Lat.le_join_of_le_right _ hle⟩) (fun he => by cases he)
    | loadSet h2 =>
      cases op <;> try exact absurd hok (by decide)
      obtain ⟨hP, -, hle⟩ := hi.evset h2
      exact hi.wmove ht h (c := .run .wait .fin) rfl rfl rfl rfl (by intro he; cases he)
        (fun he => by cases he)
        (fun _ => ⟨hP, Lat.le_join_of_le_right _ hle⟩) (fun he => by cases he)
    | loadWaiting h1 =>
      cases op <;> try exact absurd hok (by decide)
      exact hi.wmove ht h (c := .run .wait .fwait) rfl rfl rfl rfl (by intro he; cases he)
        (fun _ => by rw [h1]; decide) (fun he => by cases he)
        fun _ hne => hi.wwait t (by rw [h]; rfl) hne
    | sleep hfw =>
      cases op <;> try exact absurd hok (by decide)
      have hnt := hi.not_has (t := t) (by rw [h]; intro he; cases he)
      have h1 : s.sh.ev.val = 1 := bv_one hi.evb (hF.sleep_word hfw)
      have hmem := hF.mem_wait hfw
      refine hi.wq h rfl rfl (hF.wf_wait hi.qwf hnt hfw) (fun u a ha => ?_) fun _ => .inl h1
      rcases (hmem (u, a)).mp ha with ha | ⟨-, he⟩
      · have hu := hi.qloc u a ha
        rw [tset_ne _ _ (WgInv.ne_of_ctl hu h (by intro he; cases he))]; exact hu
      · cases he; rw [tset_self]
    | back hfw =>
      cases op <;> try exact absurd hok (by decide)
      have hnt := hi.not_has (t := t) (by rw [h]; intro he; cases he)
      have hmem := hF.mem_wait hfw
      refine hi.wq h rfl rfl (hF.wf_wait hi.qwf hnt hfw) (fun u a ha => ?_) fun hq => ?_
      · rcases (hmem (u, a)).mp ha with ha | ⟨he, -⟩
        · have hu := hi.qloc u a ha
          rw [tset_ne _ _ (WgInv.ne_of_ctl hu h (by intro he; cases he))]; exact hu
        · cases he
      · refine hi.wit fun he => hq ?_
        exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
          rcases (hmem x).mp hx with hx | ⟨he', -⟩
          · rw [he] at hx; cases hx
          · cases he'
    | resume hfr =>
      cases op <;> try exact absurd hok (by decide)
      have hmem := hF.mem_resume hfr
      refine hi.wq h rfl rfl (hF.wf_resume hi.qwf hfr) (fun u a ha => ?_) fun hq => ?_
      · obtain ⟨ha, hut⟩ := (hmem (u, a)).mp ha
        rw [tset_ne _ _ hut]; exact hi.qloc u a ha
      · refine hi.wit fun he => hq ?_
        exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
          have := ((hmem x).mp hx).1; rw [he] at this; cases this

/-- The invariant of `Threaded.WaitGroup` is inductive over every futex that satisfies the
contract. -/
theorem threadedWG_inductive (X : Type) (L : Lat X) (N : Nat) :
    (wmgc (threadedWG Fx) X L N).Inductive (WgInv L N) :=
  ⟨fun _ h => threadedWG_init hF h, fun _ _ _ hi hs => threadedWG_step hF hi hs.1 hs.2⟩

/-- No deadlock: a thread in `Threaded.WaitGroup`'s code that is not asleep in the futex queue
can step. -/
theorem threadedWG_enabled {X : Type} {L : Lat X} {N : Nat} {s : WState (threadedWG Fx) X}
    (hi : WgInv L N s) {t : Tid} {op : WOp} {l : WL} (h : s.ctl t = .run op l)
    (hq : (Fx.queue s.sh.f).has t = false) : (wmgc (threadedWG Fx) X L N).Enabled t s := by
  have ht := hi.lt_of_run h
  have hok := hi.op_ok h
  have ex : ∀ {l' : WL} {sh' : WSh Fx X} {v' : X},
      WgStep Fx L.join t l s.sh (s.cur t) l' sh' v' → (wmgc (threadedWG Fx) X L N).Enabled t s :=
    fun hs => ⟨_, ht, WStep.exec h hs⟩
  have hc := hi.cnt
  have hb := hi.wbit
  have hPdef : s.P N = s.tok + tsum N (fun u => pS (s.ctl u)) + tsum N (fun u => pF (s.ctl u)) := rfl
  cases l with
  | fin =>
    cases op with
    | start => exact ⟨_, ht, WStep.retStart h rfl⟩
    | finish => exact ⟨_, ht, WStep.retFinish h rfl⟩
    | wait => exact ⟨_, ht, WStep.retWait h rfl⟩
  | add => exact ex WgStep.add
  | sub =>
    cases op <;> try exact absurd hok (by decide)
    have := hi.pos_of (g := pF) (t := t) (by rw [h]; exact Nat.zero_lt_one) rfl
    by_cases h3 : s.sh.st.val = 3
    · exact ex (WgStep.subSet h3)
    · exact ex (WgStep.subDone (by omega) h3)
  | set =>
    by_cases h1 : s.sh.ev.val = 1
    · exact ex (WgStep.setWake h1)
    · exact ex (WgStep.setDone h1)
  | wake =>
    obtain ⟨f', hk⟩ := hF.wake_total t () (2 ^ 32 - 1) s.sh.f hi.qwf
    exact ex (WgStep.wake hk)
  | wadd =>
    cases op <;> try exact absurd hok (by decide)
    have h0 := hi.bit_zero h
    by_cases hz : s.sh.st.val = 0
    · exact ex (WgStep.waddDone hz)
    · exact ex (WgStep.waddWait (by omega) (by omega))
  | cas =>
    have := hi.evb
    by_cases h0 : s.sh.ev.val = 0
    · exact ex (WgStep.casSet h0)
    · by_cases h1 : s.sh.ev.val = 1
      · exact ex (WgStep.casWaiting h1)
      · exact ex (WgStep.casIsSet (by omega))
  | fwait =>
    obtain ⟨r, f', hw⟩ := hF.wait_total t () 1 false s.sh.ev.val s.sh.f _ rfl hq
    cases r with
    | none => exact ex (WgStep.sleep hw)
    | some r => exact ex (WgStep.back hw)
  | asleep =>
    obtain ⟨r, f', hr⟩ := hF.resume_total t false s.sh.f hq
    exact ex (WgStep.resume hr)
  | load =>
    cases op <;> try exact absurd hok (by decide)
    have h0 := hi.evw t (by rw [h]; rfl)
    have := hi.evb
    by_cases h1 : s.sh.ev.val = 1
    · exact ex (WgStep.loadWaiting h1)
    · exact ex (WgStep.loadSet (by omega))

/-- **`Io.Threaded.WaitGroup` satisfies the wait-group contract over every futex that satisfies
the futex contract.** -/
theorem threadedWG_spec : WaitGroupSpec (threadedWG Fx) where
  view X L N := (threadedWG_inductive hF X L N).invariant fun s hi t ht => by
    obtain ⟨-, hle⟩ := hi.wdone t (by rw [ht]; rfl)
    exact Lat.le_trans hi.fin hle
  done X L N := (threadedWG_inductive hF X L N).invariant fun s hi t ht => by
    have hP := (hi.wdone t (by rw [ht]; rfl)).1
    unfold WState.P at hP; omega
  live X L N := (threadedWG_inductive hF X L N).invariant fun s hi ⟨htok, ⟨t, op, l, h⟩, hn⟩ => by
    -- every thread in the code is disabled, so each one is asleep in the queue: the waiter
    have hall : ∀ u op l, s.ctl u = .run op l → (Fx.queue s.sh.f).has u = true := by
      intro u op l hu
      cases hq : (Fx.queue s.sh.f).has u
      · exact absurd (threadedWG_enabled hF hi hu hq) (hn u op l hu)
      · rfl
    obtain ⟨a, ha⟩ := Queue.has_eq_true.mp (hall t op l h)
    have hne : Fx.queue s.sh.f ≠ [] := List.ne_nil_of_mem ha
    have hw := hi.qloc t a ha
    have notq : ∀ {u : Tid} {op : WOp} {l : WL}, s.ctl u = .run op l → l ≠ .asleep → False :=
      fun hu hl => by
        have := hall _ _ _ hu
        obtain ⟨b, hb⟩ := Queue.has_eq_true.mp this
        exact hl (by have := hi.qloc _ b hb; rw [hu] at this; cases this; rfl)
    by_cases h2 : s.sh.ev.val = 2
    · rcases hi.wit hne with h1 | ⟨v, hv⟩
      · omega
      · exact notq hv (by intro he; cases he)
    · rcases hi.wwait t (by rw [hw]; rfl) h2 with hP | ⟨v, hv⟩
      · have hS := hi.pS_zero (hi.waited t (by rw [hw]; rfl))
        have : 0 < tsum N (fun u => pF (s.ctl u)) := by unfold WState.P at hP; omega
        obtain ⟨v, -, hv⟩ := exists_of_tsum_pos this
        cases hc : s.ctl v with
        | run op l =>
          rw [hc] at hv
          cases op <;> cases l <;> simp [pF] at hv
          exact notq hc (by intro he; cases he)
        | _ => rw [hc] at hv; simp [pF] at hv
      · exact notq hv (by intro he; cases he)

end

end Spec
end Zig
