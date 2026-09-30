import ZigLean.Conc.Basic
import ZigLean.Mem.Thread

/-!
# The scheduler

`Zig.Sched.run dispatch fuel o main m0` runs the concurrent function `main` and every thread it
spawns, from the memory `m0`, and gives the result of `main`. Threads take turns at sync ops
(`ZigLean/Conc/Basic.lean`): at each turn the oracle `o` picks one of the threads that can go
on, the scheduler does that thread's op, and the thread runs to its next stop.

- **Oracle.** The `i`-th choice of a run is `o i` modulo the number of options, so every `o` is
  a valid schedule. A spec over all schedules is a statement for every `o` (and every `fuel`).
- **Threads.** Thread 0 is `main`. `spawn t` adds a thread that starts with `dispatch t` at its
  first turn; `join tid` can go on only when thread `tid` has ended. The clock and join rules are
  those of `ZigLean/Mem/Thread.lean` (`Thread.fork`, `Thread.join`, `checkJoinedByChild`).
- **Futex.** `wait p e`: if the `u32` at `p` is `e`, the thread waits until a `wake` at `p` (the
  waiters wake in the order they began to wait); else it goes on. A wake gives no happens-before
  edge (the std code reads the value again with an acquire). The model has no spurious wakeup.
  The queue is in `Mem` (`Thread.futexWait`, `Thread.futexWake`).
- **Ends.** An error in any thread is the result of the run. `main` ends the run; it must have
  joined every thread it spawned (`checkJoinedByChild 0`), so every thread has ended then. If no
  thread can go on and one has not ended, the run is `.deadlock`.
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

/-- Thread `t`, which waits at the op, can go on now. -/
def canGo (s : State Tgt α) (t : ThreadId) : SyncOp Tgt → Bool
  | .join tid => s.isDone tid
  | .wait .. => !(s.mem.waiters.any (·.1 == t))
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

/-- Thread `t` does its op `p.op` and runs to its next stop. -/
def turn {β : Type} (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat) (t : ThreadId)
    (s : State Tgt α) (p : Paused Tgt β) :
    Except (Option Error) (TS Tgt β × Option β × State Tgt α) := do
  let s := { s with mem := { s.mem with current := t } }
  match p with
  | ⟨_, .yield, k⟩ => settle t s (k () s.mem)
  | ⟨_, .choose n, k⟩ =>
    let (c, s) := s.choose o n
    settle t s (k c s.mem)
  | ⟨_, .pick count, k⟩ =>
    let (c, s) := s.choose o (count s.mem)
    settle t s (k c s.mem)
  | ⟨_, .spawn tgt, k⟩ =>
    let (child, s) ← s.onMem Thread.fork
    -- The new thread starts with `dispatch tgt` at its first turn, as thread `child`.
    let s := { s with kids := s.kids.push (.paused ⟨fuel, .yield, fun _ m => dispatch tgt fuel m⟩) }
    settle t s (k child s.mem)
  | ⟨_, .join tid, k⟩ =>
    let ((), s) ← s.onMem (Thread.join tid)
    settle t s (k () s.mem)
  | ⟨d, .wait ptr e, k⟩ =>
    let (sleep, s) ← s.onMem (Thread.futexWait ptr e)
    if sleep then .ok (.paused ⟨d, .wait ptr e, k⟩, none, s) else settle t s (k () s.mem)
  | ⟨_, .wake ptr n, k⟩ =>
    let ((), s) ← s.onMem (Thread.futexWake ptr n)
    settle t s (k () s.mem)

/-- Up to `fuel` turns. -/
def go (dispatch : Tgt → ConcM Tgt Unit) (o : Nat → Nat) : Nat → State Tgt α → Out α × Array Nat
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
        match turn dispatch fuel o 0 s p with
        | .error e => (outOf e, s.trace)
        | .ok (_, some v, s) => (some (.ok (v, s.mem)), s.trace)
        | .ok (ts, none, s) => go dispatch o fuel { s with main := ts }
    else
      match s.kids[t - 1]? with
      | some (.paused p) =>
        match turn dispatch fuel o t s p with
        | .error e => (outOf e, s.trace)
        | .ok (ts, _, s) => go dispatch o fuel { s with kids := s.kids.set! (t - 1) ts }
      | _ => (none, s.trace)

/-- `run`, and the number of options of each choice. -/
def runTrace (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat) (main : ConcM Tgt α)
    (m0 : Mem) : Out α × Array Nat :=
  let s0 : State Tgt α := { main := .done, kids := #[], mem := { m0 with current := 0 },
                            step := 0, trace := #[] }
  match settle 0 s0 (main fuel s0.mem) with
  | .error e => (outOf e, #[])
  | .ok (_, some v, s) => (some (.ok (v, s.mem)), #[])
  | .ok (ts, none, s) => go dispatch o fuel { s with main := ts }

/-- The result of `main` under the schedule `o`, with at most `fuel` turns. -/
def run (dispatch : Tgt → ConcM Tgt Unit) (fuel : Nat) (o : Nat → Nat) (main : ConcM Tgt α)
    (m0 : Mem) : Result (α × Mem) :=
  ExceptT.mk (runTrace dispatch fuel o main m0).1

end Sched
end Zig
