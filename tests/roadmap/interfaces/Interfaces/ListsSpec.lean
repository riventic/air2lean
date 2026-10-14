import Interfaces.Lists
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region

/-!
# `examples/lists/lists.zig` for every allocator (`docs/interfaces.md`)

`lists.zig` has no allocator of its own: every call through its `std.mem.Allocator` parameter
reaches the environment (`Ext`, premise EXT-05). Its theorems assume `CAllocSpec` of the
environment's allocator at the vtable `fns` (`CVTable.env`) and nothing else. The environment's
entries are the generated `Ext.call<i>` for the three entries' types that the program calls, and
any implementation `e` of the one it does not (`resize`), so the assumption holds for every
allocator that meets the contract.
-/

namespace Interfaces.ListsSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Lists

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

variable [Ext]

/-- The environment's allocator entries: `Ext.call0` (`alloc`), `Ext.call1` (`remap`) and
`Ext.call2` (`free`); `e`'s `resize`, which the program never calls. -/
def env (e : AllocEnv Tgt) : AllocEnv Tgt :=
  { e with
    alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2
    remap := fun f a => Ext.call1 f a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2
    free := fun f a => Ext.call2 f a.1 a.2.1 (al a.2.2.1) a.2.2.2 }

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

set_option maxHeartbeats 2000000 in
theorem create_spec (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) (mem_Allocator_create__anon_48603a336c43 ⟨ctx, vtp⟩)
      (fun r => I.own ⋆ (I.allocResult 3 16 φ r ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.alloc h]

/-- The node that `push` makes for the fee `φ`: its 16 bytes (`next` at 0, `val` at 8, padding
undefined); with `error.OutOfMemory`, the fee back. -/
def pushResult (next : Option Ptr) (v : BitVec 32) : Except ErrName Ptr → FAssn
  | .ok p => I.granted p 3 φ (writeBytes (writeBytes (Array.replicate 16 .undef) 8 (Enc.encode v)) 0 (Enc.encode next))
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

-- the store of `next` at the start of the node's region (not a default rule, `Full/Region.lean`)
attribute [local fsym] FTotalTriple.regionStore0

set_option maxHeartbeats 2000000 in
theorem push_spec (next : Option Ptr) (v : BitVec 32) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushResult I φ next v r ⋆ vtR vtp fns.toList)) := by
  fsym [create_spec ctx vtp fns I e φ hfit h]

omit [Ext] in
theorem fromByteUnits_8 : mem_Alignment_fromByteUnits 8 = pure mem_Alignment.«8» := by
  have h : (8 : BitVec 64).ctz = 3 := Zig.ctz_twoPow (k := 3) (by decide)
  unfold mem_Alignment_fromByteUnits math_isPowerOfTwo__anon_38853e1fe316 debug_assert
  simp only [Zig.ctz, h]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem destroy_spec (p : Ptr) (bs : Array Byte) (hbs : bs.size = 16)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted p 3 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  -- fsym does not evaluate the pure helper on its literal (fsym-engine ledger)
  unfold mem_Allocator_destroy__anon_a9add1f02861
  simp only [fromByteUnits_8]
  fsym [CAllocSpec.free h]

end Interfaces.ListsSpec
