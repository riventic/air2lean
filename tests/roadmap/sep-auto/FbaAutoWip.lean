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
    known cb B.cA ⋆ known b B.A ⋆ bshare b q (bnd B) ⋆ junk ⋆
    up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail)

def ftok (B : FBuf) (p : Ptr) (n _k A S : Nat) (K : BlockKind) (_q : Frac) : FAssn :=
  ⟪p.block = B.ptr.block ∧ A = B.A ∧ S = B.S ∧ K = B.K ∧ B.ptr.off ≤ p.off ∧
    p.off + n ≤ B.ptr.off + B.cap⟫

def finv (ctx : Ptr) (B : FBuf) : FAllocInv where
  own := fown ctx B
  tok := ftok B
  fits n k := B.cap + 2 ^ k + n ≤ 2 ^ 64


theorem ffree (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.free ctx s k ra)
      (fun _ => (finv ctx B).own) := by
  fsym


set_option maxHeartbeats 2000000 in
theorem fresize (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hn : 0 < n.toNat) (hfit : (finv ctx B).fits n.toNat k) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.resize ctx s k n ra)
      ((finv ctx B).resizePost s.ptr k bs n.toNat) := by
  set_option trace.fsym true in fsym

theorem falloc (ctx : Ptr) (B : FBuf) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (hn : 0 < n.toNat) (hk : k < 64) (hfit : (finv ctx B).fits n.toNat k) :
    FTotalTriple (fown ctx B) (impl.alloc ctx n k ra) ((finv ctx B).allocPost n.toNat k) := by
  fsym
