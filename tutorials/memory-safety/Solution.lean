import Proofs.Lists.Alloc

/-! Exercise solution: reversing a list and then freeing it leaks nothing, for every allocator
that meets the `std.mem.Allocator` contract. From the list and the allocator's state, the run
ends with the allocator's state and the fee of every node only: every node of the list is given
back, and the frame (everything else the program owns) is untouched. -/

namespace MemorySafety.Exercise

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

variable [Ext]

/-- Reverse the list at `hd` with the generated `reverse`, then free it with the generated
`freeAll`. -/
def reverseThenFree (a : mem_Allocator) (hd : Option Ptr) : ConcM Tgt Unit :=
  ConcM.liftMem (reverse hd) >>= fun r => freeAll a r

theorem reverseThenFree_spec (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)
    (φ : Frac) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) (hd : Option Ptr)
    (xs : List (BitVec 32)) :
    CTriple (I.own ⋆ (list I φ hd xs ⋆ vtR vtp fns.toList)) (reverseThenFree ⟨ctx, vtp⟩ hd)
      (fun _ => I.own ⋆ (fees I φ xs.length ⋆ vtR vtp fns.toList)) :=
  CTriple.bind (CTriple.liftMem (((Lists.Linked.reverse_thread (X := nodeRest I φ) hd xs).toPartial.frame
      (R := I.own ⋆ vtR vtp fns.toList)).pre fun _ hr => ac_cast hr (by ac_rfl)))
    fun r => ((freeAll_spec ctx vtp fns I e φ r xs.reverse h).pre fun _ hr => ac_cast hr (by ac_rfl)).post
      fun _ _ hr => by rwa [List.length_reverse] at hr

end MemorySafety.Exercise
