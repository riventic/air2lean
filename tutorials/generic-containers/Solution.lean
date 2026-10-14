import Proofs.Lists.Append

/-! Exercise solution: a failed `append` reports `error.OutOfMemory` and keeps the old list. -/

namespace GenericContainers

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc Lists.Append

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

theorem append_failure (p : Ptr) (xs : List (BitVec 32)) (v : BitVec 32)
    (room : I.fits (4 * growTo (xs.length + 1)) 2)
    (contract : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ (alist I φ p xs ⋆ vtR vtp fns.toList)))
      (array_list_Aligned_u32_null_append p ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (I.fee φ ⋆ ((FAssn.ex fun ys =>
        ⟪∀ err, r = .error err → err = "OutOfMemory" ∧ ys = xs⟫ ⋆ alist I φ p ys) ⋆
        vtR vtp fns.toList))) :=
  (append_spec ctx vtp fns I e φ p xs v room contract).post fun r _ h =>
    sep_mono_right (fun _ h => sep_mono_right (fun _ h => sep_mono_left (fun _ h => by
      cases r with
      | ok => exact ⟨xs ++ [v], sep_lift.mpr ⟨nofun, h⟩⟩
      | error =>
        obtain ⟨oom, h⟩ := sep_lift.mp h
        exact ⟨xs, sep_lift.mpr ⟨(fun _ h' => by cases h'; exact ⟨oom, rfl⟩), h⟩⟩) h) h) h

end GenericContainers
