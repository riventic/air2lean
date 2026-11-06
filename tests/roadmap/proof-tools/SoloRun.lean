import ZigLean.Conc.RunResult
import ZigLean.Sep.Full.Conc

open Zig

/-! A concrete run of a `partial_fixpoint` group (as a recursive call group of generated code),
by the kernel: the group's defining equations (`unfold`) take the run past every recursive call
it makes, then `decide +kernel` computes it (`docs/proof-tools.md`, concrete runs of programs
with loops). Each round unfolds `evenC` and then `oddC`, so round `r` reaches `evenC (6 - 2 * r)`:
4 rounds reach `evenC 0`, whose result needs no further call. -/

mutual
def evenC (n : Nat) : ConcM Unit (Except ErrName (BitVec 32)) :=
  if n = 0 then pure (.ok 1) else oddC (n - 1)
partial_fixpoint
def oddC (n : Nat) : ConcM Unit (Except ErrName (BitVec 32)) :=
  if n = 0 then pure (.ok 0) else evenC (n - 1)
partial_fixpoint
end

-- The scheduler's run of the group as the main thread.
theorem even_six : Witness.okVal (Sched.run ⟨.any, .available⟩ (fun _ => pure ()) 100 (fun _ => 0)
    (evenC 6) {}) = some 1 := by
  iterate 4 unfold evenC oddC
  decide +kernel

/-- info: 'even_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms even_six

-- The in-thread reading (`Sched.soloRun`) that `CTriple` speaks about.
theorem even_six_solo : Witness.okVal ((Sched.soloRun 100 (evenC 6)).run {}) = some 1 := by
  iterate 4 unfold evenC oddC
  decide +kernel

/-- info: 'even_six_solo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms even_six_solo

-- Rejected: after 3 rounds the run reaches `evenC 0` still folded, a `partial_fixpoint` the kernel
-- does not compute, so `decide` fails (it gets stuck rather than proving anything).
example : Witness.okVal ((Sched.soloRun 100 (evenC 6)).run {}) = some 1 := by
  fail_if_success ((iterate 3 unfold evenC oddC); decide +kernel)
  exact even_six_solo

-- Rejected: a wrong value, which the kernel's run refutes.
example : Witness.okVal ((Sched.soloRun 100 (evenC 6)).run {}) ≠ some 0 := by
  rw [even_six_solo]; decide
