import Proofs.Lists.Sep

/-! Negative control: Lean must reject this file. A client that pushes a node and never frees
it leaks: on success, `push_total`'s post-condition owns the new node, so the run cannot end
owning no bytes (`emp`). The proof attempt treats the leaked node as freed. -/
-- expect-error: Type mismatch

namespace MemorySafety.NegativeControl

open Zig Assn Lists

/-- `_ = try push(a, null, v);` and return without a free. -/
def forgetFree (a : Allocator) (v : BitVec 32) : MemM Unit :=
  push a none v >>= fun _ => pure ()

theorem forgetFree_no_leak (a : Allocator) (v : BitVec 32) :
    TotalTriple emp (forgetFree a v) (fun _ => emp) :=
  TotalTriple.bind (push_total a none v) (fun _ => TotalTriple.ret (Q := fun _ => emp) ())

end MemorySafety.NegativeControl
