import Interfaces.Lists
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Pinned
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region

namespace Interfaces.ListsSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Lists

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv)

set_option maxHeartbeats 2000000 in
theorem create_spec (hfit : I.fits (16 : BitVec 64).toNat 3)
    (hA : ∀ len ra, 0 < len.toNat → I.fits len.toNat 3 →
      CTriple I.own (Zig.extCall (Ext.call0 fns.alloc ctx len mem_Alignment.«8» ra))
        (I.allocPost len.toNat 3)) :
    CTriple (I.own ⋆ vtR vtp fns.toList) (mem_Allocator_create__anon_48603a336c43 ⟨ctx, vtp⟩)
      (fun r => I.own ⋆ (I.allocResult 3 16 r ⋆ vtR vtp fns.toList)) := by
  fsym [hA]

end Interfaces.ListsSpec

namespace Interfaces.ListsSpec
open Zig Zig.Full Zig.Full.FAssn Interfaces.Lists
variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv)

/-- The node that `push` makes: its 16 bytes (`next` at 0, `val` at 8, padding undefined). -/
def pushResult (next : Option Ptr) (v : BitVec 32) : Except ErrName Ptr → FAssn
  | .ok p => I.granted p 3 (writeBytes (writeBytes (Array.replicate 16 .undef) 8 (Enc.encode v)) 0 (Enc.encode next))
  | .error e => ⟪e = "OutOfMemory"⟫

set_option maxHeartbeats 2000000 in
theorem push_spec (next : Option Ptr) (v : BitVec 32) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (hA : ∀ len ra, 0 < len.toNat → I.fits len.toNat 3 →
      CTriple I.own (Zig.extCall (Ext.call0 fns.alloc ctx len mem_Alignment.«8» ra))
        (I.allocPost len.toNat 3)) :
    CTriple (I.own ⋆ vtR vtp fns.toList) (push ⟨ctx, vtp⟩ next v)
      (fun r => I.own ⋆ (pushResult I next v r ⋆ vtR vtp fns.toList)) := by
  fsym [create_spec ctx vtp fns I hfit hA]
  cases x <;> fsym

end Interfaces.ListsSpec

namespace Interfaces.ListsSpec
open Zig Zig.Full Zig.Full.FAssn Interfaces.Lists
variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv)

omit [Ext] in
theorem fromByteUnits_8 : mem_Alignment_fromByteUnits 8 = pure mem_Alignment.«8» := by
  have h : (8 : BitVec 64).ctz = 3 := Zig.ctz_twoPow (k := 3) (by decide)
  unfold mem_Alignment_fromByteUnits math_isPowerOfTwo__anon_38853e1fe316 debug_assert
  simp only [Zig.ctz, h]
  rfl

omit [Ext] in
theorem fromByteUnits_8_step {P : FAssn} :
    FTotalTriple P (StateT.lift (mem_Alignment_fromByteUnits 8) : MemM mem_Alignment)
      (fun r => ⟪r = mem_Alignment.«8»⟫ ⋆ P) := by
  rw [fromByteUnits_8]
  exact (FTotalTriple.ret (Q := fun r => ⟪r = mem_Alignment.«8»⟫ ⋆ P) _).pre fun _ h => sep_lift.mpr ⟨rfl, h⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem destroy_spec (p : Ptr) (bs : Array Byte) (hbs : bs.size = 16)
    (hF : ∀ (s : Slice) ra (bs : Array Byte), s.len.toNat = bs.size → 0 < bs.size →
      CTriple (I.own ⋆ I.granted s.ptr 3 bs) (Zig.extCall (Ext.call2 fns.free ctx s mem_Alignment.«8» ra))
        (fun _ => I.own)) :
    CTriple (I.own ⋆ (I.granted p 3 bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_a9add1f02861 ⟨ctx, vtp⟩ p) (fun _ => I.own ⋆ vtR vtp fns.toList) := by
  unfold mem_Allocator_destroy__anon_a9add1f02861
  simp only [fromByteUnits_8]
  fsym [hF]

end Interfaces.ListsSpec
