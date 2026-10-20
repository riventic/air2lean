import Proofs.Basic.Cases
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Slice
import ZigLean.Sep.Full.Witness

/-!
# The saturating-add contract for every enrolled Basic case

Each generated `clampAdd` satisfies the same total full-state contract for all
16-bit inputs and every frame. `fsym` walks each case's own code using the existing
width-generic unsigned saturating-add arithmetic rule. No overflow premise is
needed. The returning-input companions use the existing Full witness library.
-/

open Zig Zig.Full Zig.Full.FAssn

namespace Basic.CaseContracts.V0_17_0.H_6c696e7578

theorem clampAdd_total (P : FAssn) (a b : BitVec 16) :
    FTotalTriple P
      (StateT.lift (Basic.Gen.V0_17_0.H_6c696e7578.clampAdd a b) : MemM (BitVec 16))
      (fun r => ⟪r = BitVec.ofNat 16 (min (a.toNat + b.toNat) 65535)⟫ ⋆ P) := by
  fsym

theorem clampAdd_live (a b : BitVec 16) :
    Witness.FLive emp
      (StateT.lift (Basic.Gen.V0_17_0.H_6c696e7578.clampAdd a b) : MemM (BitVec 16)) :=
  Witness.FLive.of_total (clampAdd_total emp a b) Witness.FAdmit.of_emp

end Basic.CaseContracts.V0_17_0.H_6c696e7578

namespace Basic.CaseContracts.V0_16_0.H_6c696e7578

theorem clampAdd_total (P : FAssn) (a b : BitVec 16) :
    FTotalTriple P
      (StateT.lift (Basic.Gen.V0_16_0.H_6c696e7578.clampAdd a b) : MemM (BitVec 16))
      (fun r => ⟪r = BitVec.ofNat 16 (min (a.toNat + b.toNat) 65535)⟫ ⋆ P) := by
  fsym

theorem clampAdd_live (a b : BitVec 16) :
    Witness.FLive emp
      (StateT.lift (Basic.Gen.V0_16_0.H_6c696e7578.clampAdd a b) : MemM (BitVec 16)) :=
  Witness.FLive.of_total (clampAdd_total emp a b) Witness.FAdmit.of_emp

end Basic.CaseContracts.V0_16_0.H_6c696e7578

namespace Basic.CaseContracts.V0_15_2.H_6c696e7578

theorem clampAdd_total (P : FAssn) (a b : BitVec 16) :
    FTotalTriple P
      (StateT.lift (Basic.Gen.V0_15_2.H_6c696e7578.clampAdd a b) : MemM (BitVec 16))
      (fun r => ⟪r = BitVec.ofNat 16 (min (a.toNat + b.toNat) 65535)⟫ ⋆ P) := by
  fsym

theorem clampAdd_live (a b : BitVec 16) :
    Witness.FLive emp
      (StateT.lift (Basic.Gen.V0_15_2.H_6c696e7578.clampAdd a b) : MemM (BitVec 16)) :=
  Witness.FLive.of_total (clampAdd_total emp a b) Witness.FAdmit.of_emp

end Basic.CaseContracts.V0_15_2.H_6c696e7578

namespace Basic.CaseContracts.V0_14_1.H_6c696e7578

theorem clampAdd_total (P : FAssn) (a b : BitVec 16) :
    FTotalTriple P
      (StateT.lift (Basic.Gen.V0_14_1.H_6c696e7578.clampAdd a b) : MemM (BitVec 16))
      (fun r => ⟪r = BitVec.ofNat 16 (min (a.toNat + b.toNat) 65535)⟫ ⋆ P) := by
  fsym

theorem clampAdd_live (a b : BitVec 16) :
    Witness.FLive emp
      (StateT.lift (Basic.Gen.V0_14_1.H_6c696e7578.clampAdd a b) : MemM (BitVec 16)) :=
  Witness.FLive.of_total (clampAdd_total emp a b) Witness.FAdmit.of_emp

end Basic.CaseContracts.V0_14_1.H_6c696e7578
