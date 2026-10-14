import Proofs.Lists.Alloc

/-! Negative control: Lean must reject this file. A client that pushes a node and never frees
it leaks: on success, `push_spec`'s post-condition owns the new node (which holds the fee it
paid) besides the allocator's state, so the run cannot end owning only the allocator's state and
the fee. The proof attempt treats the leaked node as freed. -/
-- expect-error: Type mismatch

namespace MemorySafety.NegativeControl

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

variable [Ext]

/-- `_ = try push(a, null, v);` and return without a free. -/
def forgetFree (a : mem_Allocator) (v : BitVec 32) : ConcM Tgt Unit :=
  push a none v >>= fun _ => pure ()

theorem forgetFree_no_leak (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)
    (φ : Frac) (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I)
    (v : BitVec 32) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) (forgetFree ⟨ctx, vtp⟩ v)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) :=
  CTriple.bind (push_spec ctx vtp fns I e φ none v hfit h)
    (fun _ => CTriple.ret (Q := fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ())

end MemorySafety.NegativeControl
