import Proofs.Sync.Gen
import ZigLean.Sep.Full.IoMutex

/-!
# `Io.Mutex` of `examples/sync` as a mutex (`MutexImpl`)

The per-item obligation of `Io.Mutex` (Zig 0.16.0's std code) in this program's generated code:
its `lockUncancelable` and `unlock` are `Io.Mutex`'s code (`IoMutexCode`,
`ZigLean/Sep/Full/IoMutex.lean`), so they satisfy the mutex contract (`MutexImpl`) for every
protocol that has the lock. This file gives the program's names and the unfolding equations.
-/

open Zig Zig.Conc Zig.Full

namespace Sync

/-- The states of `Io.Mutex`. -/
def ioMutexS : LockWord.States Io_Mutex_State where
  unl := .unlocked
  one := .locked_once
  two := .contended
  c := 2
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

/-- `Io.Mutex`'s code in this program. -/
def ioMutexCode : IoMutexCode Tgt where
  S := Io_Mutex_State
  st := ioMutexS
  σ := Io_Mutex_lockUncancelableLocals
  E := Io_Mutex_lockUncancelableExit
  ret := .ret
  stop := .br22
  rep := .rep23
  again := Io_Mutex_lockUncancelable.again23
  again_rep := rfl
  again_stop := rfl
  body := Io_Mutex_lockUncancelable.loop23
  body_eq _ _ := by
    simp only [Io_Mutex_lockUncancelable.loop23, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  lock := Io_Mutex_lockUncancelable
  lock_eq := ⟨_, _, fun _ _ => by
    simp only [Io_Mutex_lockUncancelable, IoMutexCode.lockOf, bind_assoc, pure_bind, Norm.ite_bind]
    rfl, rfl, rfl⟩
  μ := Io_Mutex_unlockLocals
  ν := Io_Mutex_unlockExit
  umid := .br7
  uret := .ret
  unlock := Io_Mutex_unlock
  unlock_eq := ⟨_, _, _, fun _ _ => by
    simp only [Io_Mutex_unlock, IoMutexCode.unlockOf, bind_assoc, pure_bind]; rfl,
    fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- **`Io.Mutex` of this program is a mutex** (`MutexImpl`). -/
def ioMutex : MutexImpl Tgt := ioMutexCode.impl

end Sync
