import Proofs.Sync.CondCases
import ZigLean.Sep.Full.IoSem

/-!
# The semaphore contract for every enrolled Sync profile

Each instance supplies only its generated locals, exits and code equations to the `IoSemCode`
interface (`ZigLean/Sep/Full/IoSem.lean`), with its profile's own mutex and condition
(`Proofs/Sync/MutexCases.lean`, `Proofs/Sync/CondCases.lean`). Its general walks prove `SemImpl`
once; clients use the resulting `SemImpl` rules. `Io.Semaphore`'s `waitUncancelable` and `post`
are the same generated code in every profile; the instances differ only in the profile's names.
The public `Sync.ioSem` (`Proofs/Sync/IoSemaphore.lean`) is the instance for the public
translation.
-/

open Zig Zig.Conc Zig.Full

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578

open Sync.Gen.V0_17_1.H_6c696e7578

/-- `Io.Semaphore`'s code in the actual Zig 0.17.1 Linux translation. -/
def semCode : IoSemCode Tgt where
  M := mutex
  C := cond
  c_eq := rfl
  cwait_unm_pre _ _ hu := hu
  cwait_unm_keep _ _ _ _ h := h
  σ := Io_Semaphore_waitUncancelableLocals
  E := Io_Semaphore_waitUncancelableExit
  ret := .ret
  stop := .br4
  rep := .rep5
  again := Io_Semaphore_waitUncancelable.again5
  body := Io_Semaphore_waitUncancelable.loop5
  body_eq _ _ := by
    simp only [Io_Semaphore_waitUncancelable.loop5, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  wait := Io_Semaphore_waitUncancelable
  wait_eq := ⟨_, _, fun _ _ => by
    simp only [Io_Semaphore_waitUncancelable, IoSemCode.waitOf, IoSemCode.lockLoopOf, bind_assoc,
      pure_bind]; rfl,
    fun _ _ => by simp only [IoSemCode.takeOf, bind_assoc, pure_bind, Norm.ite_bind]; rfl,
    by rfl⟩
  σp := Io_Semaphore_postLocals
  Ep := Io_Semaphore_postExit
  pret := .ret
  post := Io_Semaphore_post
  post_eq := ⟨_, fun _ _ => by
    simp only [Io_Semaphore_post, IoSemCode.postOf, pure_bind]; rfl, by rfl⟩

/-- This profile's translated semaphore satisfies the general semaphore contract. -/
def sem : SemImpl Tgt := semCode.impl

end Sync.CaseContracts.V0_17_1.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_6c696e7578

open Sync.Gen.V0_16_0.H_6c696e7578

/-- `Io.Semaphore`'s code in the actual Zig 0.16.0 Linux translation. -/
def semCode : IoSemCode Tgt where
  M := mutex
  C := cond
  c_eq := rfl
  cwait_unm_pre _ _ hu := hu
  cwait_unm_keep _ _ _ _ h := h
  σ := Io_Semaphore_waitUncancelableLocals
  E := Io_Semaphore_waitUncancelableExit
  ret := .ret
  stop := .br4
  rep := .rep5
  again := Io_Semaphore_waitUncancelable.again5
  body := Io_Semaphore_waitUncancelable.loop5
  body_eq _ _ := by
    simp only [Io_Semaphore_waitUncancelable.loop5, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  wait := Io_Semaphore_waitUncancelable
  wait_eq := ⟨_, _, fun _ _ => by
    simp only [Io_Semaphore_waitUncancelable, IoSemCode.waitOf, IoSemCode.lockLoopOf, bind_assoc,
      pure_bind]; rfl,
    fun _ _ => by simp only [IoSemCode.takeOf, bind_assoc, pure_bind, Norm.ite_bind]; rfl,
    by rfl⟩
  σp := Io_Semaphore_postLocals
  Ep := Io_Semaphore_postExit
  pret := .ret
  post := Io_Semaphore_post
  post_eq := ⟨_, fun _ _ => by
    simp only [Io_Semaphore_post, IoSemCode.postOf, pure_bind]; rfl, by rfl⟩

/-- This profile's translated semaphore satisfies the general semaphore contract. -/
def sem : SemImpl Tgt := semCode.impl

end Sync.CaseContracts.V0_16_0.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_64617277696e

open Sync.Gen.V0_16_0.H_64617277696e

/-- `Io.Semaphore`'s code in the actual Zig 0.16.0 Darwin translation. -/
def semCode : IoSemCode Tgt where
  M := mutex
  C := cond
  c_eq := rfl
  cwait_unm_pre _ _ hu := hu
  cwait_unm_keep _ _ _ _ h := h
  σ := Io_Semaphore_waitUncancelableLocals
  E := Io_Semaphore_waitUncancelableExit
  ret := .ret
  stop := .br4
  rep := .rep5
  again := Io_Semaphore_waitUncancelable.again5
  body := Io_Semaphore_waitUncancelable.loop5
  body_eq _ _ := by
    simp only [Io_Semaphore_waitUncancelable.loop5, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  wait := Io_Semaphore_waitUncancelable
  wait_eq := ⟨_, _, fun _ _ => by
    simp only [Io_Semaphore_waitUncancelable, IoSemCode.waitOf, IoSemCode.lockLoopOf, bind_assoc,
      pure_bind]; rfl,
    fun _ _ => by simp only [IoSemCode.takeOf, bind_assoc, pure_bind, Norm.ite_bind]; rfl,
    by rfl⟩
  σp := Io_Semaphore_postLocals
  Ep := Io_Semaphore_postExit
  pret := .ret
  post := Io_Semaphore_post
  post_eq := ⟨_, fun _ _ => by
    simp only [Io_Semaphore_post, IoSemCode.postOf, pure_bind]; rfl, by rfl⟩

/-- This profile's translated semaphore satisfies the general semaphore contract. -/
def sem : SemImpl Tgt := semCode.impl

end Sync.CaseContracts.V0_16_0.H_64617277696e
