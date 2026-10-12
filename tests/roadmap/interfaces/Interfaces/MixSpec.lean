import Interfaces.Mix
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region

namespace Interfaces.MixSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Mix

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

variable [Ext]

/-- The program's allocator functions (the FixedBufferAllocator's entries at the addresses of
`mem0`) and the environment: `Ext.call0` for `alloc`, and `e`'s other entries, which the program
never calls through an open pointer (a fixed `.illegal` there would make `CAllocSpec` of an
environment allocator unsatisfiable, `docs/interfaces.md`). -/
def tables (e : AllocEnv Tgt) : AllocTables Tgt where
  alloc := [(⟨some 0, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  resize := [(⟨some 1, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  remap := [(⟨some 2, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  free := [(⟨some 3, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  env := { e with alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2 }

set_option maxHeartbeats 2000000 in
/-- **`allocBytesAligned` for every allocator**: the code that the vtable `fns` reaches (the
FixedBufferAllocator or the environment) meets `CAllocSpec`. -/
theorem allocBytes_spec (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (n ra : BitVec 64)
    (φ : Frac) (e : AllocEnv Tgt) (hn : 0 < n.toNat) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.dispatch (tables e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList))
      (mem_Allocator_allocBytesAligned__anon_c9141768de1a ⟨ctx, vtp⟩ n ra)
      (fun r => I.own ⋆ (I.allocResult 2 n.toNat φ r ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.alloc h]

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

set_option maxHeartbeats 2000000 in
theorem create_spec (hfit : I.fits (4 : BitVec 64).toNat 2)
    (h : CAllocSpec (CVTable.dispatch (tables e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList))
      (mem_Allocator_create__anon_8f6a81b88324 ⟨ctx, vtp⟩)
      (fun r => I.own ⋆ (I.allocResult 2 4 φ r ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.alloc h]

/-- The `u32` that `make` returns for the fee `φ`: its 4 bytes hold `v`; with
`error.OutOfMemory`, the fee back. -/
def makeResult (v : BitVec 32) : Except ErrName Ptr → FAssn
  | .ok p => I.granted p 2 φ (writeBytes (Array.replicate 4 .undef) 0 (Enc.encode v))
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

-- the store of `v` at the start of the grant (not a default rule, `Full/Region.lean`)
attribute [local fsym] FTotalTriple.regionStore0

set_option maxHeartbeats 2000000 in
/-- **`make` for every allocator**: the FixedBufferAllocator of `withFba` or any environment
allocator that meets `CAllocSpec`. -/
theorem make_spec (v : BitVec 32) (hfit : I.fits (4 : BitVec 64).toNat 2)
    (h : CAllocSpec (CVTable.dispatch (tables e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) (make ⟨ctx, vtp⟩ v)
      (fun r => I.own ⋆ (makeResult I φ v r ⋆ vtR vtp fns.toList)) := by
  -- `cases x`: fsym does not split a `match` on a symbolic `Except` (fsym-engine ledger)
  fsym [create_spec ctx vtp fns I e φ hfit h]
  cases x <;> fsym

end Interfaces.MixSpec
