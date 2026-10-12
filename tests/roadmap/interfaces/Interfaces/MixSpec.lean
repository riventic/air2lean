import Interfaces.Mix
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Pinned
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region

namespace Interfaces.MixSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Mix

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

variable [Ext]

/-- The program's allocator functions (the FixedBufferAllocator's entries at the addresses of
`mem0`) and the environment (`Ext.call0` for `alloc`; the program calls no other entry through
an open pointer). -/
def tables : AllocTables Tgt where
  alloc := [(⟨some 0, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  resize := [(⟨some 1, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  remap := [(⟨some 2, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  free := [(⟨some 3, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  env := { AllocEnv.closed with alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2 }

set_option maxHeartbeats 2000000 in
/-- **`allocBytesAligned` for every allocator**: the code that the vtable `fns` reaches (the
FixedBufferAllocator or the environment) meets `CAllocSpec`. -/
theorem allocBytes_spec (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (n ra : BitVec 64)
    (hn : 0 < n.toNat) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.dispatch tables fns) ctx I) :
    CTriple (I.own ⋆ vtR vtp fns.toList)
      (mem_Allocator_allocBytesAligned__anon_c9141768de1a ⟨ctx, vtp⟩ n ra)
      (fun r => I.own ⋆ (I.allocResult 2 n.toNat r ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.alloc h]

end Interfaces.MixSpec
