import ZigLean.Conc.Basic
import ZigLean.Mem.Thread

/-!
# The scheduler

`Zig.Sched.run env dispatch fuel o main m0` runs the concurrent function `main` and every thread it
spawns, from the memory `m0`, and gives the result of `main`. Threads take turns at sync ops
(`ZigLean/Conc/Basic.lean`): at each turn the oracle `o` picks one of the threads that can go
on, the scheduler does that thread's op, and the thread runs to its next stop.

- **Environment** (`Env`, explicit in every statement). `env.spawn`: a `spawn` may fail with a
  declared error (`fallible`, within the caller's budget `Mem.spawnLimit`) or not (`available`).
  `env.io`: how `Io.Group.async` executes (`asyncChoice`, `asyncOptions`): `Io.Threaded` on `cpus`
  CPUs, or any `Io` implementation.
- **Oracle.** The `i`-th choice of a run is `o i` modulo the number of options, so every `o` is
  a valid schedule. A spec over all schedules is a statement for every `o` (and every `fuel`).
- **Threads.** Thread 0 is `main`. `spawn t` adds a thread that starts with `dispatch t` at its
  first turn; a valid `join tid` waits until thread `tid` has ended, while an invalid handle
  goes on immediately to report `.illegal`. The clock and join rules are
  those of `ZigLean/Mem/Thread.lean` (`Thread.fork`, `Thread.join`, `checkJoinedByChild`).
- **Deferred tasks.** `spawnGated t` adds a thread as `spawn t` does, but the thread waits at
  `gate` while its record is gated (`Mem.isGated`): an `Io.Group.async` task that runs only once its group's
  `await` or `cancel` releases it (`Thread.groupTake`). Its clock is its spawner's at the
  spawn; the model gives it no edge from the awaiter, which only adds outcomes.
- **Futex.** `wait p e`: if the `u32` at `p` is `e`, the thread waits until a `wake` at `p`;
  else it goes on. A `wake` wakes up to `n` of the waiters at `p`, which the oracle picks
  (`chooseWake`, `Thread.wakeSet`): no queue order is promised. A wake gives no happens-before
  edge (the std code reads the value again with an acquire). A wait that would sleep may
  instead return spuriously: an oracle choice of two options (`spuriousWake`); the thread goes
  on with the memory before the wait. A sleeping thread leaves the waiters only through a wake,
  a cancelation request (`Thread.requestCancel`) or an OS interrupt (`Os.interrupt`, OSG-01).
  The queue is in `Mem` (`Thread.futexWait`, `Thread.futexWake`).
- **Ends.** An error in any thread is the result of the run. `main` ends the run; it must have
  consumed every handle it owns (`checkJoinedByChild 0`: joined or detached). A joined thread has
  ended; a detached one may still run, and `main`'s end ends it, as the process exit does. If no
  thread can go on and one has not ended, the run is `.deadlock`.
- **Catch scope.** `ConcM.tryCatch` handles errors produced by the thread before or after a
  sync op. Errors raised by the scheduler's execution of spawn/join/wait/wake or its end check
  terminate the entire run; sync responses carry only successful results, so such errors do
  not enter the thread's catch handler.
- **Fuel.** `fuel` bounds the number of turns and the depth of each thread's run. Out of fuel is
  `none`, as a loop that does not end.

`runTrace` also gives the number of options of each choice, for a search over schedules (the
diff test, `tests/diff/Diff.lean`).
-/

namespace Zig
namespace Sched

variable {Tgt α : Type}

/-- A thread that waits at a sync op. -/
structure Paused (Tgt β : Type) where
  depth : Nat
  op : SyncOp Tgt
  k : op.Resp → Mem → CoN Tgt (β × Mem) depth

/-- A thread: waits at an op, or has ended. -/
inductive TS (Tgt β : Type) where
  | paused (p : Paused Tgt β)
  | done

/-- The state between two turns. `kids[i]` is thread `i + 1`. -/
structure State (Tgt α : Type) where
  main : TS Tgt α
  kids : Array (TS Tgt Unit)
  mem : Mem
  /-- The number of choices so far: the next one is `o step`. -/
  step : Nat
  /-- The number of options of each choice so far. -/
  trace : Array Nat

/-- Thread `t` has ended. -/
def State.isDone (s : State Tgt α) (t : ThreadId) : Bool :=
  if t = 0 then (match s.main with | .done => true | _ => false)
  else match s.kids[t - 1]? with
    | some .done => true
    | _ => false

/-- Thread `t`, which waits at the op, can go on now. Invalid join handles run their error
check immediately; only a valid handle can wait for its target. -/
def canGo (s : State Tgt α) (t : ThreadId) : SyncOp Tgt → Bool
  | .join tid => !Thread.joinValid s.mem t tid || s.isDone tid
  | .wait .. => !(s.mem.waiters.any (·.1 == t))
  | .gate => !s.mem.isGated t
  | _ => true

/-- The threads that can go on, in thread order. -/
def State.ready (s : State Tgt α) : Array ThreadId :=
  let main := match s.main with | .paused p => if canGo s 0 p.op then #[0] else #[] | .done => #[]
  main ++ (s.kids.zipIdx.filterMap fun (ts, i) => match ts with
    | .paused p => if canGo s (i + 1) p.op then some (i + 1) else none
    | .done => none)

/-- A thread has not ended. -/
def State.anyRunning (s : State Tgt α) : Bool :=
  (match s.main with | .paused _ => true | .done => false) ||
    s.kids.any fun ts => match ts with | .paused _ => true | .done => false

/-- The next choice of the oracle among `n` options (`n = 0`: `0`, no choice). -/
def State.choose (s : State Tgt α) (o : Nat → Nat) (n : Nat) : Nat × State Tgt α :=
  (if n = 0 then 0 else o s.step % n, { s with step := s.step + 1, trace := s.trace.push n })

/-- A `MemM` step on the memory of the run. -/
def State.onMem {β : Type} (s : State Tgt α) (x : MemM β) : Except (Option Error) (β × State Tgt α) :=
  match (x.run s.mem).run with
  | some (.ok (b, m)) => .ok (b, { s with mem := m })
  | some (.error e) => .error (some e)
  | none => .error none

/-- The result of a run: `none` for no result. -/
abbrev Out (α : Type) := Option (Except Error (α × Mem))

def outOf {β : Type} : Option Error → Out β
  | some e => some (.error e)
  | none => none

/-- Thread `t`'s run reached `tree`: it stops at a sync op or ends. `none`: `main` ended with
this value. -/
def settle {β : Type} (t : ThreadId) (s : State Tgt α) {n : Nat} (tree : CoN Tgt (β × Mem) n) :
    Except (Option Error) (TS Tgt β × Option β × State Tgt α) :=
  match tree with
  | .leaf none => .error none
  | .leaf (some (.error e)) => .error (some e)
  | .leaf (some (.ok (v, m))) =>
    match (Thread.checkJoinedByChild t |>.run m).run with
    | some (.ok (_, m)) => .ok (.done, some v, { s with mem := m })
    | some (.error e) => .error (some e)
    | none => .error none
  | .sync op m k => .ok (.paused ⟨_, op, k⟩, none, { s with mem := m })

/-- The option of the oracle at a futex wait that would sleep with which the wait returns
spuriously instead (option 0 sleeps). `std.Io.futexWait`, `futexWaitUncancelable` and
`std.Thread.Futex.wait` permit a spurious return (`docs/std-models.md` §Spurious wakeups). -/
def spuriousWake : Nat := 1

/-- The outcome of a thread assignment in the environment: 0 assigns a child; `c > 0` is the
declared error `spawnErrorAt (c - 1)`. Under `available` there is no choice; under `fallible`
the oracle picks among every outcome that the caller's budget admits. -/
def State.spawnOutcome (env : Env) (s : State Tgt α) (o : Nat → Nat) : Nat × State Tgt α :=
  match env.spawn with
  | .available => (0, s)
  | .fallible =>
    let (c, s') := s.choose o (assignmentCount (spawnErrors.size + 1) s.mem)
    (assignmentOutcome s.mem.spawnAdmits c, s')

/-- Choices of the oracle with the option counts `counts`, in order. -/
def State.chooseMany (s : State Tgt α) (o : Nat → Nat) : List Nat → List Nat × State Tgt α
  | [] => ([], s)
  | c :: cs =>
    let (x, s) := s.choose o c
    let (xs, s) := s.chooseMany o cs
    (x :: xs, s)

/-- The waiters that a wake of up to `n` waiters at `p` wakes: one choice for each, among the
waiters at `p` not picked yet (`Thread.wakeSet`). -/
def State.chooseWake (s : State Tgt α) (o : Nat → Nat) (p : Ptr) (n : Nat) : List Nat × State Tgt α :=
  let k := Thread.waitersAt s.mem.waiters p
  s.chooseMany o ((List.range (Nat.min n k)).map (k - ·))

/-- The execution of an `Io.Group.async` task that the oracle picks among the environment's
`asyncOptions`. -/
def State.asyncChoice (env : Env) (s : State Tgt α) (o : Nat → Nat) : Nat × State Tgt α :=
  let opts := asyncOptions env.io s.mem
  let (i, s') := s.choose o opts.size
  (opts[i]?.getD 0, s')

/-- Thread `t` does its op and runs to its next stop, retaining choices even when it fails or
has no result. -/
def turnTrace {β : Type} (env : Env) (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat) (t : ThreadId)
    (s : State Tgt α) (p : Paused Tgt β) :
    Except (Option Error) (TS Tgt β × Option β × State Tgt α) × Array Nat :=
  let s := { s with mem := { s.mem with current := t } }
  match p with
  | ⟨_, .yield, k⟩ => (settle t s (k () s.mem), s.trace)
  | ⟨_, .choose n, k⟩ =>
    let (c, s) := s.choose o n
    (settle t s (k c s.mem), s.trace)
  | ⟨_, .pick count, k⟩ =>
    let (c, s) := s.choose o (count s.mem)
    (settle t s (k c s.mem), s.trace)
  | ⟨_, .spawn tgt, k⟩ =>
    let (c, s) := s.spawnOutcome env o
    if c = 0 then
      (do
        let (child, s) ← s.onMem Thread.fork
        -- The new thread starts with `dispatch tgt` at its first turn, as thread `child`.
        let s := { s with kids := s.kids.push (.paused ⟨fuel, .yield, fun _ m => dispatch tgt fuel m⟩) }
        settle t s (k (.ok child) s.mem), s.trace)
    else (settle t s (k (.error (spawnErrorAt (c - 1))) s.mem), s.trace)
  | ⟨_, .asyncChoice, k⟩ =>
    let (c, s) := s.asyncChoice env o
    (settle t s (k c s.mem), s.trace)
  | ⟨_, .spawnGated tgt, k⟩ =>
    (do
      let (child, s) ← s.onMem Thread.forkGated
      -- The deferred task waits at `gate` until its group releases it, then runs `dispatch tgt`.
      let s := { s with kids := s.kids.push (.paused ⟨fuel, .gate, fun _ m => dispatch tgt fuel m⟩) }
      settle t s (k child s.mem), s.trace)
  | ⟨_, .gate, k⟩ => (settle t s (k () s.mem), s.trace)
  | ⟨_, .join tid, k⟩ =>
    (do
      let ((), s) ← s.onMem (Thread.join tid)
      settle t s (k () s.mem), s.trace)
  | ⟨d, .wait ptr e, k⟩ =>
    match s.onMem (Thread.futexWait ptr e) with
    | .error err => (.error err, s.trace)
    | .ok (false, s₁) => (settle t s₁ (k () s₁.mem), s.trace)
    | .ok (true, s₁) =>
      -- The kernel may return spuriously instead of sleeping (`spuriousWake`): option 1
      -- goes on with the memory before the wait (the thread is not in the queue).
      let (c, s₂) := s.choose o 2
      if c = spuriousWake then (settle t s₂ (k () s₂.mem), s₂.trace)
      else (.ok (.paused ⟨d, .wait ptr e, k⟩, none, { s₁ with step := s₂.step, trace := s₂.trace }),
        s₂.trace)
  | ⟨_, .wake ptr n, k⟩ =>
    let (cs, s) := s.chooseWake o ptr n
    (do
      let ((), s) ← s.onMem (Thread.futexWake ptr n cs)
      settle t s (k () s.mem), s.trace)

/-- The semantic result of one turn; `turnTrace` also retains its oracle choices. -/
def turn {β : Type} (env : Env) (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat)
    (t : ThreadId) (s : State Tgt α) (p : Paused Tgt β) :
    Except (Option Error) (TS Tgt β × Option β × State Tgt α) :=
  (turnTrace env dispatch fuel o t s p).1

/-- Up to `fuel` turns. -/
def go (env : Env) (dispatch : Tgt → ConcM Tgt Unit) (o : Nat → Nat) :
    Nat → State Tgt α → Out α × Array Nat
  | 0, s => (none, s.trace)
  | fuel + 1, s =>
    let ready := s.ready
    if ready.isEmpty then
      (if s.anyRunning then some (.error .deadlock) else none, s.trace)
    else
    let (i, s) := s.choose o ready.size
    let t := ready[i]!
    if t = 0 then
      match s.main with
      | .done => (none, s.trace)
      | .paused p =>
        let result := turnTrace env dispatch fuel o 0 s p
        match result.1 with
        | .error e => (outOf e, result.2)
        | .ok (_, some v, s) => (some (.ok (v, s.mem)), s.trace)
        | .ok (ts, none, s) => go env dispatch o fuel { s with main := ts }
    else
      match s.kids[t - 1]? with
      | some (.paused p) =>
        let result := turnTrace env dispatch fuel o t s p
        match result.1 with
        | .error e => (outOf e, result.2)
        | .ok (ts, _, s) => go env dispatch o fuel { s with kids := s.kids.set! (t - 1) ts }
      | _ => (none, s.trace)

/-- `run`, and the number of options of each choice. -/
def runTrace (env : Env) (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat)
    (main : ConcM Tgt α)
    (m0 : Mem) : Out α × Array Nat :=
  let s0 : State Tgt α := { main := .done, kids := #[], mem := { m0 with current := 0 },
                            step := 0, trace := #[] }
  match settle 0 s0 (main fuel s0.mem) with
  | .error e => (outOf e, #[])
  | .ok (_, some v, s) => (some (.ok (v, s.mem)), #[])
  | .ok (ts, none, s) => go env dispatch o fuel { s with main := ts }

/-- The result of `main` under the schedule `o`, with at most `fuel` turns. -/
def run (env : Env) (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat)
    (main : ConcM Tgt α) (m0 : Mem) : Result (α × Mem) :=
  ExceptT.mk (runTrace env dispatch fuel o main m0).1

end Sched
end Zig
