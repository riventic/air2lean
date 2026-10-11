import AllocFba.Bridge
import ZigLean.Sep.Full.Auto
namespace AllocFba.FBA2
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Gen

structure FBuf where
  ptr : Ptr
  cap : Nat
  A : Nat
  S : Nat
  K : BlockKind
  cA : Nat

def bnd (B : FBuf) : Nat := B.ptr.off.toNat + B.cap

def FOk (ctx : Ptr) (B : FBuf) (e : Nat) (tail : Array Byte) : Prop :=
  e ≤ B.cap ∧ tail.size = B.cap - e ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧ 0 ≤ B.ptr.off ∧
    (B.cA + ctx.off.toNat) % 8 = 0 ∧ 0 ≤ ctx.off

def fown (ctx : Ptr) (B : FBuf) : FAssn :=
  FAssn.ex fun e => FAssn.ex fun tail => FAssn.ex fun q => FAssn.ex fun b => FAssn.ex fun cb =>
    ⟪FOk ctx B e tail ∧ B.ptr.block = some b ∧ ctx.block = some cb⟫ ⋆
    up (pts ctx 8 (BitVec.ofNat 64 e)) ⋆ up (pts (ctx.add 8) 8 (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice)) ⋆
    known cb B.cA ⋆ known b B.A ⋆ bshare b q (bnd B) ⋆ Junk ⋆
    up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail)

def ftok (B : FBuf) (p : Ptr) (n _k A S : Nat) (K : BlockKind) (_q : Frac) : FAssn :=
  ⟪p.block = B.ptr.block ∧ A = B.A ∧ S = B.S ∧ K = B.K ∧ B.ptr.off ≤ p.off ∧
    p.off + n ≤ B.ptr.off + B.cap⟫

def finv (ctx : Ptr) (B : FBuf) : FAllocInv where
  own := fown ctx B
  tok := ftok B
  fits n k := B.cap + 2 ^ k + n ≤ 2 ^ 64


