import AllocFba.Full
import ZigLean.Sep.Full.Auto
namespace AllocFba.FBA
open Zig Zig.Full Zig.Full.FAssn Gen

theorem t_owns {ctx : Ptr} {B : FBuf} {e : Nat} {q : Frac} {b cb : BlockId} {R : FAssn} {s : Slice} (hb : B.ptr.block = some b) (hc : ctx.block = some cb)
    (hc0 : 0 ≤ ctx.off) (hsb : s.ptr.block = B.ptr.block) (h0 : 0 ≤ B.ptr.off)
    (hlo : B.ptr.off ≤ s.ptr.off) (hhi : s.ptr.off + s.len.toNat ≤ B.ptr.off + B.cap)
    (hA : B.A + B.ptr.off.toNat + B.cap < 2 ^ 64) :
    FTotalTriple (fst ctx B e q b cb ⋆ R) (heap_FixedBufferAllocator_ownsSlice ctx s)
      (fun r => ⟪r = true⟫ ⋆ (fst ctx B e q b cb ⋆ R)) := by
  fsym

#print axioms AllocFba.FBA.t_owns
