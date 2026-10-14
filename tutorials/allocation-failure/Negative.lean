import Proofs.Lists.Alloc

/-! Negative control: Lean must reject this file. `push` can fail, so no proof shows that
every run returns a node; the failure branch of `push_spec` has no pointer to offer, only the
fact that the error is `OutOfMemory` (and the fee back). -/
-- expect-error: Type mismatch

namespace AllocationFailure

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)
  (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I)

include hfit h

theorem push_never_fails (q : Option Ptr) (v : BitVec 32) (n : Nat) (m m' : Mem)
    (r rF : Res) (hh : Holds m r rF) (hr : (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) r)
    (hs : m.FSeq) (err : ErrName)
    (run : ((Sched.soloRun n (push ⟨ctx, vtp⟩ q v)).run m).run = some (.ok (.error err, m'))) :
    False := by
  have t := (push_spec ctx vtp fns I e φ q v hfit h).toSolo n m r rF hh hr hs
  rw [run] at t
  obtain ⟨r', hh', hq, -⟩ := t
  simp only [pushed] at hq
  obtain ⟨oom, -⟩ := Full.sep_lift.mp (ac_cast hq (by ac_rfl) :
    (⟪err = "OutOfMemory"⟫ ⋆ (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain)) r')
  exact oom

end AllocationFailure
