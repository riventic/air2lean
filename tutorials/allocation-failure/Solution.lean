import Proofs.Lists.Alloc

/-! Exercise solution: a successful `push` adds exactly one node, a grant of the allocator
(which holds the fee it paid), next to what the caller owned before; the frame is untouched. -/

namespace AllocationFailure

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)
  (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I)

include hfit h

theorem push_success_adds_node (q : Option Ptr) (v : BitVec 32) (n : Nat) (m m' : Mem)
    (r rF : Res) (hh : Holds m r rF) (hr : (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) r)
    (hs : m.FSeq) (p : Ptr)
    (run : ((Sched.soloRun n (push ⟨ctx, vtp⟩ q v)).run m).run = some (.ok (.ok p, m'))) :
    ∃ r', Holds m' r' rF ∧ (I.own ⋆ (node I φ p v q ⋆ vtR vtp fns.toList)) r' := by
  have t := (push_spec ctx vtp fns I e φ q v hfit h).toSolo n m r rF hh hr hs
  rw [run] at t
  obtain ⟨r', hh', hq, -⟩ := t
  exact ⟨r', hh', hq⟩

end AllocationFailure
