import ZigLean.Conc.Detach

/-!
# Detached threads and handle ownership: run-level witnesses (C07)

The all-schedules results are kernel theorems: `Proofs/Detach/Worker.lean` (a detached worker
that owns and frees its heap buffer) and `Proofs/Detach/Transfer.lean` (a transferred handle
joined by its one owner), over the model rules of `ZigLean/Conc/Detach.lean`. This file pins,
by kernel evaluation of `Sched.run` under concrete schedules, that the model rejects the misuses:

1. **Stack data.** `launch` keeps a 4-byte stack local, spawns a reader with its address,
   detaches the reader, yields once and exits its frame (frees the block). `main` goes on
   after `launch` returns. A schedule where the reader runs before the frame exit reads `5`;
   one where it runs after reads a dead block: `.illegal`. A schedule where `main` ends first
   ends the run (the process exit) before the reader reads.
2. **Consumed handles.** A join or a second detach of a detached handle throws `.illegal`.
   Ending with an unjoined, undetached kid throws `.illegal`; detaching it instead is accepted.
3. **One owner.** After `main` hands `A`'s handle to `B`, `B`'s join of `A` is accepted, a join
   of `A` by `main` (the old owner) throws `.illegal`, and `B` ending without consuming the
   handle throws `.illegal`. Without the transfer, `B`'s join of `A` throws `.illegal`.

No `native_decide` is used.
-/

open Zig

namespace Detach.Runtime

inductive Tgt where
  /-- Reads the `u32` at `p`. -/
  | reader (p : Ptr)
  /-- Does nothing. -/
  | idle
  /-- Joins the handle `h`. -/
  | joiner (h : ThreadId)
  /-- Ends without consuming any handle. -/
  | holder

def dispatch : Tgt → ConcM Tgt Unit
  | .reader p => do let _ ← ConcM.liftMem (load (BitVec 32) 4 p); pure ()
  | .idle => pure ()
  | .joiner h => do let _ ← ConcM.sync (Tgt := Tgt) (.join h); pure ()
  | .holder => pure ()

def spawn (t : Tgt) : ConcM Tgt ThreadId := do
  match ← ConcM.sync (.spawn t) with
  | .ok c => pure c
  | .error _ => throw .unspecified
def join (h : ThreadId) : ConcM Tgt Unit := do let _ ← ConcM.sync (Tgt := Tgt) (.join h); pure ()
def yield : ConcM Tgt Unit := ConcM.sync (Tgt := Tgt) .yield
def mem {α : Type} (x : MemM α) : ConcM Tgt α := ConcM.liftMem x

/-- The outcome of a run: `ok`, `.illegal`, another error or no result. -/
inductive Out where
  | ok | illegal | other | none
  deriving DecidableEq

def classify {α : Type} : Option (Except Error (α × Mem)) → Out
  | some (.ok _) => .ok
  | some (.error .illegal) => .illegal
  | some (.error _) => .other
  | none => .none

def run {α : Type} (o : Nat → Nat) (main : ConcM Tgt α) : Out :=
  classify (Sched.run ⟨.any, .available⟩ dispatch 64 o main {}).run

/-- The oracle that picks option `cs[i]` at choice `i` (modulo the number of options) and the
first option afterwards. Choice 0 is `main`'s first turn, the only option. -/
def pick (cs : List Nat) : Nat → Nat := fun i => cs.getD i 0

/-! ## 1. Stack data dies with the frame -/

/-- A frame with a stack local whose address a detached reader captured. -/
def launch : ConcM Tgt Unit := do
  let x ← mem (allocStack 4 4)
  mem (store 4 x (5 : BitVec 32))
  let w ← spawn (.reader x)
  mem (Thread.detach w)
  yield
  mem (free x)

def stackMain : ConcM Tgt Nat := do
  launch
  yield
  yield
  pure 0

/-- The reader runs before the frame exit: it reads the live local, but the detach gives no
happens-before edge (`ThreadRec.released`), so the frame exit (a write of the block, audit #3)
races with that read. -/
theorem stack_read_before_exit : run (pick [0, 1]) stackMain = .illegal := by decide +kernel

/-- The reader runs after the frame exit: a use after free. -/
theorem stack_read_after_exit : run (pick [0, 0, 1]) stackMain = .illegal := by decide +kernel

/-- `main` ends before the reader runs: the run (the process) ends. -/
theorem stack_main_ends_first : run (pick [0, 0, 0]) stackMain = .ok := by decide +kernel

/-! ## 2. Detach consumes the handle -/

def joinAfterDetach : ConcM Tgt Nat := do
  let w ← spawn .idle
  mem (Thread.detach w)
  join w
  pure 0

def detachTwice : ConcM Tgt Nat := do
  let w ← spawn .idle
  mem (Thread.detach w)
  mem (Thread.detach w)
  pure 0

def leaveUnjoined (detach : Bool) : ConcM Tgt Nat := do
  let w ← spawn .idle
  if detach then mem (Thread.detach w)
  pure 0

theorem join_after_detach_illegal :
    run (pick []) joinAfterDetach = .illegal ∧ run (pick [1, 1]) joinAfterDetach = .illegal := by
  decide +kernel

theorem detach_twice_illegal : run (pick []) detachTwice = .illegal := by decide +kernel

theorem unjoined_illegal : run (pick []) (leaveUnjoined false) = .illegal := by decide +kernel

theorem detached_ok : run (pick []) (leaveUnjoined true) = .ok := by decide +kernel

/-! ## 3. One authorized join owner -/

/-- `main` spawns `A`, then `B` with `A`'s handle; `transfer`: it hands the handle to `B`. Then
`main` joins `B` (`mainJoinsA`: also `A`). -/
def handOff (transfer mainJoinsA : Bool) : ConcM Tgt Nat := do
  let a ← spawn .idle
  let b ← spawn (.joiner a)
  if transfer then mem (Thread.transferHandle a b)
  if mainJoinsA then join a
  join b
  pure 0

/-- The transferred handle is joined by its owner `B`. -/
theorem transfer_join_ok : run (pick []) (handOff true false) = .ok ∧
    run (pick [1, 1, 1]) (handOff true false) = .ok := by decide +kernel

/-- `main` and `B` both join `A`: `main` no longer owns the handle. -/
theorem transfer_double_join_illegal : run (pick []) (handOff true true) = .illegal := by
  decide +kernel

/-- Without the transfer, `B` does not own `A`'s handle: its join is `.illegal` (on a schedule
where `B` reaches its join before `main` ends). -/
theorem join_without_transfer_illegal : run (pick [0, 2]) (handOff false true) = .illegal := by
  decide +kernel

/-- `B` receives the handle and ends without consuming it. -/
def transferToHolder : ConcM Tgt Nat := do
  let a ← spawn .idle
  let b ← spawn .holder
  mem (Thread.transferHandle a b)
  join b
  pure 0

theorem transfer_obligation_illegal : run (pick []) transferToHolder = .illegal := by
  decide +kernel

end Detach.Runtime
