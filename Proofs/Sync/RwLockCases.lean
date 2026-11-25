import Proofs.Sync.SemCases
import ZigLean.Sep.Full.IoRwLock

/-!
# The reader/writer lock contract for every enrolled Sync profile

Each instance supplies only its generated locals, exits and code equations to the `IoRwLockCode`
interface (`ZigLean/Sep/Full/IoRwLock.lean`), with its profile's own mutex and semaphore
(`Proofs/Sync/MutexCases.lean`, `Proofs/Sync/SemCases.lean`). Its general walks prove
`RwLockImpl` once; clients use the resulting `RwLockImpl` rules. `Io.RwLock`'s code is the same
generated code in every profile; the instances differ only in the profile's names. The public
`Sync.ioRwLock` (`Proofs/Sync/IoRwLock.lean`) is the instance for the public translation. The
continuations' equations at their exits are `by rfl` blocks, as there.
-/

open Zig Zig.Conc Zig.Full

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578

open Sync.Gen.V0_17_1.H_6c696e7578

/-- `Io.RwLock`'s code in the actual Zig 0.17.1 Linux translation. -/
def rwLockCode : IoRwLockCode Tgt where
  M := mutex
  S := sem
  c_eq := rfl
  wait_unm_pre _ _ hu := hu
  wait_unm_keep _ _ _ _ := ⟨fun h => h, fun h => h⟩
  σL := Io_RwLock_lockUncancelableLocals
  EL := Io_RwLock_lockUncancelableExit
  lret := .ret
  lmid := .br8
  lock := Io_RwLock_lockUncancelable
  lock_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockUncancelable, IoRwLockCode.lockOf, pure_bind]
    rfl, by rfl, by rfl⟩
  σU := Io_RwLock_unlockLocals
  EU := Io_RwLock_unlockExit
  uret := .ret
  unlock := Io_RwLock_unlock
  unlock_eq := ⟨_, fun _ _ => by
    simp only [Io_RwLock_unlock, IoRwLockCode.unlockOf, pure_bind]
    rfl, by rfl⟩
  σR := Io_RwLock_lockSharedUncancelableLocals
  ER := Io_RwLock_lockSharedUncancelableExit
  getSt s := s.state
  setSt s v := { s with state := v }
  get_set _ _ := rfl
  rret := .ret
  rslow := .br7
  rfail := .br15
  rnext := .br9
  rrep := .rep8
  again := Io_RwLock_lockSharedUncancelable.again8
  again_rep := rfl
  again_ret := rfl
  again_slow := rfl
  body := Io_RwLock_lockSharedUncancelable.loop8
  body_eq := ⟨_, _, fun _ => by
    simp only [Io_RwLock_lockSharedUncancelable.loop8, IoRwLockCode.bodyOf, bind_assoc, pure_bind]
    rfl, fun _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
  lockShared := Io_RwLock_lockSharedUncancelable
  lockShared_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockSharedUncancelable, IoRwLockCode.lockSharedOf, pure_bind]
    rfl, fun _ _ => by rfl, fun _ _ => by rfl, by rfl⟩
  σS := Io_RwLock_unlockSharedLocals
  ES := Io_RwLock_unlockSharedExit
  sret := .ret
  smid := .br4
  s8 := .br8
  unlockShared := Io_RwLock_unlockShared
  unlockShared_eq := ⟨_, _, _, fun _ _ => by
    simp only [Io_RwLock_unlockShared, IoRwLockCode.unlockSharedOf, bind_assoc, pure_bind]
    rfl, fun _ _ => by rfl, fun _ _ => by rfl, by rfl, by rfl⟩

/-- This profile's translated reader/writer lock satisfies the general reader/writer contract. -/
def rwLock : RwLockImpl Tgt := rwLockCode.impl

end Sync.CaseContracts.V0_17_1.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_6c696e7578

open Sync.Gen.V0_16_0.H_6c696e7578

/-- `Io.RwLock`'s code in the actual Zig 0.16.0 Linux translation. -/
def rwLockCode : IoRwLockCode Tgt where
  M := mutex
  S := sem
  c_eq := rfl
  wait_unm_pre _ _ hu := hu
  wait_unm_keep _ _ _ _ := ⟨fun h => h, fun h => h⟩
  σL := Io_RwLock_lockUncancelableLocals
  EL := Io_RwLock_lockUncancelableExit
  lret := .ret
  lmid := .br8
  lock := Io_RwLock_lockUncancelable
  lock_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockUncancelable, IoRwLockCode.lockOf, pure_bind]
    rfl, by rfl, by rfl⟩
  σU := Io_RwLock_unlockLocals
  EU := Io_RwLock_unlockExit
  uret := .ret
  unlock := Io_RwLock_unlock
  unlock_eq := ⟨_, fun _ _ => by
    simp only [Io_RwLock_unlock, IoRwLockCode.unlockOf, pure_bind]
    rfl, by rfl⟩
  σR := Io_RwLock_lockSharedUncancelableLocals
  ER := Io_RwLock_lockSharedUncancelableExit
  getSt s := s.state
  setSt s v := { s with state := v }
  get_set _ _ := rfl
  rret := .ret
  rslow := .br7
  rfail := .br15
  rnext := .br9
  rrep := .rep8
  again := Io_RwLock_lockSharedUncancelable.again8
  again_rep := rfl
  again_ret := rfl
  again_slow := rfl
  body := Io_RwLock_lockSharedUncancelable.loop8
  body_eq := ⟨_, _, fun _ => by
    simp only [Io_RwLock_lockSharedUncancelable.loop8, IoRwLockCode.bodyOf, bind_assoc, pure_bind]
    rfl, fun _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
  lockShared := Io_RwLock_lockSharedUncancelable
  lockShared_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockSharedUncancelable, IoRwLockCode.lockSharedOf, pure_bind]
    rfl, fun _ _ => by rfl, fun _ _ => by rfl, by rfl⟩
  σS := Io_RwLock_unlockSharedLocals
  ES := Io_RwLock_unlockSharedExit
  sret := .ret
  smid := .br4
  s8 := .br8
  unlockShared := Io_RwLock_unlockShared
  unlockShared_eq := ⟨_, _, _, fun _ _ => by
    simp only [Io_RwLock_unlockShared, IoRwLockCode.unlockSharedOf, bind_assoc, pure_bind]
    rfl, fun _ _ => by rfl, fun _ _ => by rfl, by rfl, by rfl⟩

/-- This profile's translated reader/writer lock satisfies the general reader/writer contract. -/
def rwLock : RwLockImpl Tgt := rwLockCode.impl

end Sync.CaseContracts.V0_16_0.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_64617277696e

open Sync.Gen.V0_16_0.H_64617277696e

/-- `Io.RwLock`'s code in the actual Zig 0.16.0 Darwin translation. -/
def rwLockCode : IoRwLockCode Tgt where
  M := mutex
  S := sem
  c_eq := rfl
  wait_unm_pre _ _ hu := hu
  wait_unm_keep _ _ _ _ := ⟨fun h => h, fun h => h⟩
  σL := Io_RwLock_lockUncancelableLocals
  EL := Io_RwLock_lockUncancelableExit
  lret := .ret
  lmid := .br8
  lock := Io_RwLock_lockUncancelable
  lock_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockUncancelable, IoRwLockCode.lockOf, pure_bind]
    rfl, by rfl, by rfl⟩
  σU := Io_RwLock_unlockLocals
  EU := Io_RwLock_unlockExit
  uret := .ret
  unlock := Io_RwLock_unlock
  unlock_eq := ⟨_, fun _ _ => by
    simp only [Io_RwLock_unlock, IoRwLockCode.unlockOf, pure_bind]
    rfl, by rfl⟩
  σR := Io_RwLock_lockSharedUncancelableLocals
  ER := Io_RwLock_lockSharedUncancelableExit
  getSt s := s.state
  setSt s v := { s with state := v }
  get_set _ _ := rfl
  rret := .ret
  rslow := .br7
  rfail := .br15
  rnext := .br9
  rrep := .rep8
  again := Io_RwLock_lockSharedUncancelable.again8
  again_rep := rfl
  again_ret := rfl
  again_slow := rfl
  body := Io_RwLock_lockSharedUncancelable.loop8
  body_eq := ⟨_, _, fun _ => by
    simp only [Io_RwLock_lockSharedUncancelable.loop8, IoRwLockCode.bodyOf, bind_assoc, pure_bind]
    rfl, fun _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
  lockShared := Io_RwLock_lockSharedUncancelable
  lockShared_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockSharedUncancelable, IoRwLockCode.lockSharedOf, pure_bind]
    rfl, fun _ _ => by rfl, fun _ _ => by rfl, by rfl⟩
  σS := Io_RwLock_unlockSharedLocals
  ES := Io_RwLock_unlockSharedExit
  sret := .ret
  smid := .br4
  s8 := .br8
  unlockShared := Io_RwLock_unlockShared
  unlockShared_eq := ⟨_, _, _, fun _ _ => by
    simp only [Io_RwLock_unlockShared, IoRwLockCode.unlockSharedOf, bind_assoc, pure_bind]
    rfl, fun _ _ => by rfl, fun _ _ => by rfl, by rfl, by rfl⟩

/-- This profile's translated reader/writer lock satisfies the general reader/writer contract. -/
def rwLock : RwLockImpl Tgt := rwLockCode.impl

end Sync.CaseContracts.V0_16_0.H_64617277696e
