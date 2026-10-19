import AllocTranslated.PageLinux
import Proofs.Lists.Open
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Init

/-! A concrete admissible page-allocator environment for the translated list
client. Its callback runs the real translated PageAllocator; the start memory
is that allocator's generated global memory and real vtable. -/

namespace AllocTranslated.KernelBytes
open Zig Zig.Full

instance pageEnv : Lists.Open.Ext where
  call0 f c n a ra :=
    if f = (⟨some 2, 0⟩ : Ptr) then
      ConcM.liftMem (Sched.soloRun 16 (PageLinux.heap_PageAllocator_alloc c n ⟨a.bits⟩ ra))
    else throw .illegal
  call1 f c s a n ra :=
    if f = (⟨some 4, 0⟩ : Ptr) then
      ConcM.liftMem (PageLinux.heap_PageAllocator_remap c s ⟨a.bits⟩ n ra)
    else throw .illegal
  call2 f c s a ra :=
    if f = (⟨some 5, 0⟩ : Ptr) then
      ConcM.liftMem (PageLinux.heap_PageAllocator_free c s ⟨a.bits⟩ ra)
    else throw .illegal

def allocator : Lists.Open.mem_Allocator := ⟨Ptr.null, ⟨some 1, 0⟩⟩

theorem start_admissible : (PageLinux.mem0 .fresh).FSeq := by
  apply Mem.init_fseq
  decide +kernel

theorem push_succeeds :
    (match ((Sched.soloRun 100 (Lists.Open.push allocator none 7)).run
        (PageLinux.mem0 .fresh)).run with
      | some (.ok (.ok _, _)) => true
      | _ => false) = true := by
  decide +kernel

end AllocTranslated.KernelBytes
