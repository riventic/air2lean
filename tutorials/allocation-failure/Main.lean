import Proofs.Lists.Alloc

/-!
Allocation failure: `push` allocates a list node with `try a.create(Node)`. When the allocator
fails, `push` returns `error.OutOfMemory` and the caller owns exactly what it owned before: no
leak, no partial node, no panic. The allocator `a` is any allocator that meets the
`std.mem.Allocator` contract (`CAllocSpec`, `Proofs/Lists/Alloc.lean`); the contract allows
every allocation to fail.

From the repository root:
  lake build Proofs.Lists.Alloc
  lake env lean tutorials/allocation-failure/Main.lean

See tutorials/allocation-failure/README.md for the source, the exercise and the negative control.
-/

namespace AllocationFailure

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)
  (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I)

include hfit h

/-- A failed `push` returns `error.OutOfMemory`, and after it the caller holds exactly the
allocator's state and the vtable, with the frame `rF` (whatever else the program owns)
untouched. -/
theorem push_failure_keeps_state (q : Option Ptr) (v : BitVec 32) (n : Nat) (m m' : Mem)
    (r rF : Res) (hh : Holds m r rF) (hr : (I.own ⋆ vtR vtp fns.toList) r) (hs : m.FSeq)
    (err : ErrName)
    (run : ((Sched.soloRun n (push ⟨ctx, vtp⟩ q v)).run m).run = some (.ok (.error err, m'))) :
    err = "OutOfMemory" ∧ ∃ r', Holds m' r' rF ∧ (I.own ⋆ vtR vtp fns.toList) r' := by
  have t := push_spec ctx vtp fns I e q v hfit h n m r rF hh hr hs
  rw [run] at t
  obtain ⟨r', hh', hq, -⟩ := t
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hq
  obtain ⟨oom, h2⟩ := Full.sep_lift.mp h2
  exact ⟨oom, _, hh', r₁, r₂, hd, rfl, h1, h2⟩

end AllocationFailure
