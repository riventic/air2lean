import ZigLean.Conc.Sched
import ZigLean.Conc.Call
import ZigLean.Conc.Progress

/-!
# A canceled `Io.Group` task (C05): the client

The shape of this client is that of generated code for

```zig
fn worker(io: Io, status: *u32, done: *u32) Io.Cancelable!void {
    for (0..3) |i| {
        // A cancelation point that does not block: the word holds 0, not 7.
        io.futexWait(u32, status, 7) catch |err| {
            status.* = 2; // canceled
            return err;
        };
        done.* = @intCast(i + 1);
    }
    status.* = 1; // completed
}

pub fn cancelClient(io: Io, gpa: Allocator) !struct { u32, u32 } {
    const status = try gpa.create(u32); status.* = 0;
    const done = try gpa.create(u32); done.* = 0;
    var g: Io.Group = .init;
    g.async(io, worker, .{ io, status, done });
    std.atomic.spinLoopHint(); // the task may run before the cancelation
    g.cancel(io);
    const r = .{ status.*, done.* };
    gpa.destroy(status); gpa.destroy(done);
    return r;
}
```

`main` hands the two words to the task (C01 `Transfer.owned`), cancels the group and takes them
back at the join that `Group.cancel` does. The task completes (`status = 1`, all three steps
done) or observes `error.Canceled` at one of its three cancelation points (`status = 2`, fewer
than three steps done). `Proofs/Cancel/Group.lean` proves over all schedules that these are the
only results, that the task's words come back to `main` and that every block is freed.
`cancelClient_completed` and `cancelClient_canceled*` below are kernel computations of single
schedules that reach each of the four results; each frees every block.
-/

open Zig

namespace Cancel

/-- The one spawn target: `worker(io, status, done)`. -/
inductive Tgt where
  | worker (status done : Ptr)

/-- The worker's cancelation point `i` and the steps after it; `k` steps are left. -/
def steps (status done : Ptr) : Nat → Nat → CM Tgt Unit Unit
  | _, 0 => callMC (store 4 status (1 : BitVec 32))
  | i, k + 1 => do
    match ← futexWaitCancelableC ⟨⟩ status (7 : BitVec 32) with
    | .error _ => callMC (store 4 status (2 : BitVec 32))
    | .ok () => do
      callMC (store 4 done (BitVec.ofNat 32 (i + 1)))
      steps status done (i + 1) k

def worker (status done : Ptr) : ConcM Tgt Unit := (steps status done 0 3).run' ()

def dispatch : Tgt → ConcM Tgt Unit
  | .worker status done => worker status done

/-- `main`: the result is `(status, done)`. -/
def cancelClient : ConcM Tgt (BitVec 32 × BitVec 32) :=
  (do
    let status ← callMC (alloc .heap 4 4)
    callMC (store 4 status (0 : BitVec 32))
    let done ← callMC (alloc .heap 4 4)
    callMC (store 4 done (0 : BitVec 32))
    let g ← callMC (alloc .stack 16 8)
    groupAsyncC g ⟨⟩ (Tgt.worker status done)
    spinLoopHintC
    groupCancelC g ⟨⟩
    let s ← callMC (load (BitVec 32) 4 status)
    let d ← callMC (load (BitVec 32) 4 done)
    callMC (free status)
    callMC (free done)
    callMC (free g)
    pure (s, d) : CM Tgt Unit (BitVec 32 × BitVec 32)).run' ()

/-- The declared result contract: completed with all work done, or canceled with work left. -/
def Outcome (r : BitVec 32 × BitVec 32) : Prop :=
  (r.1 = 1 ∧ r.2 = 3) ∨ (r.1 = 2 ∧ r.2.toNat < 3)

instance (r : BitVec 32 × BitVec 32) : Decidable (Outcome r) := by
  unfold Outcome; infer_instance

/-- The value of a run and whether every block is freed, if it gave one. -/
def resultOf (r : Result ((BitVec 32 × BitVec 32) × Mem)) : Option ((BitVec 32 × BitVec 32) × Bool) :=
  match r.run with
  | some (.ok (v, m)) => some (v, m.blocks.all (!·.live))
  | _ => none

/-- The oracle that follows `xs`, then takes option 0. -/
def follow (xs : List Nat) : Nat → Nat := fun i => xs.getD i 0

/-- The task runs all three steps before `main` cancels: completed. -/
theorem cancelClient_completed :
    resultOf (Sched.run dispatch 60 (follow [1, 1, 1, 1, 1, 1]) cancelClient {}) =
      some ((1, 3), true) := by
  decide +kernel

/-- `main` cancels before the task's first cancelation point: canceled with no step done. -/
theorem cancelClient_canceled :
    resultOf (Sched.run dispatch 60 (follow []) cancelClient {}) = some ((2, 0), true) := by
  decide +kernel

/-- The request arrives while the task is at its second cancelation point: canceled with one
step done. -/
theorem cancelClient_canceled_one :
    resultOf (Sched.run dispatch 60 (follow [1, 1, 1]) cancelClient {}) = some ((2, 1), true) := by
  decide +kernel

/-- Canceled with two steps done. -/
theorem cancelClient_canceled_two :
    resultOf (Sched.run dispatch 60 (follow [1, 1, 1, 1]) cancelClient {}) =
      some ((2, 2), true) := by
  decide +kernel

end Cancel
