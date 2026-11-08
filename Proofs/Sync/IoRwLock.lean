import Proofs.Sync.IoSemaphore
import ZigLean.Sep.Full.IoRwLock

/-!
# `Io.RwLock` of `examples/sync` as a reader/writer lock (`RwLockImpl`)

The per-item obligation of `Io.RwLock` (Zig 0.16.0's std code) in this program's generated code:
its `lockUncancelable`, `unlock`, `lockSharedUncancelable` and `unlockShared` are `Io.RwLock`'s
code (`IoRwLockCode`, `ZigLean/Sep/Full/IoRwLock.lean`) over the program's `Io.Mutex` (`ioMutex`)
and `Io.Semaphore` (`ioSem`, whose wait admits a positive unmetered fragment and keeps that part:
`payUnmetered`, `keepPart`), so they satisfy the reader/writer contract (`RwLockImpl`) for every
protocol that has the lock. This file gives the program's names and the unfolding equations.
-/

open Zig Zig.Conc Zig.Full

namespace Sync

/-- `Io.RwLock`'s code in this program. -/
def ioRwLockCode : IoRwLockCode Tgt where
  M := ioMutex
  S := ioSem
  c_eq := rfl
  wait_unm_pre _ _ hu := hu
  wait_unm_keep _ _ _ _ := ⟨fun h => h, fun h => h⟩
  σL := Io_RwLock_lockUncancelableLocals
  EL := Io_RwLock_lockUncancelableExit
  lret := .ret
  lmid := .br8
  lock := Io_RwLock_lockUncancelable
  lock_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockUncancelable, IoRwLockCode.lockOf, bind_assoc, pure_bind]
    rfl, rfl, rfl⟩
  σU := Io_RwLock_unlockLocals
  EU := Io_RwLock_unlockExit
  uret := .ret
  unlock := Io_RwLock_unlock
  unlock_eq := ⟨_, fun _ _ => by
    simp only [Io_RwLock_unlock, IoRwLockCode.unlockOf, bind_assoc, pure_bind]
    rfl, rfl⟩
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
    rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩
  lockShared := Io_RwLock_lockSharedUncancelable
  lockShared_eq := ⟨_, _, fun _ _ => by
    simp only [Io_RwLock_lockSharedUncancelable, IoRwLockCode.lockSharedOf, bind_assoc, pure_bind]
    rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  σS := Io_RwLock_unlockSharedLocals
  ES := Io_RwLock_unlockSharedExit
  sret := .ret
  smid := .br4
  s8 := .br8
  unlockShared := Io_RwLock_unlockShared
  unlockShared_eq := ⟨_, _, _, fun _ _ => by
    simp only [Io_RwLock_unlockShared, IoRwLockCode.unlockSharedOf, bind_assoc, pure_bind]
    rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- **`Io.RwLock` of this program is a reader/writer lock** (`RwLockImpl`). -/
def ioRwLock : RwLockImpl Tgt := ioRwLockCode.impl

end Sync
