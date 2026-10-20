import Proofs.Sync.Cases
import ZigLean.Sep.Full.IoMutex

/-!
# The mutex contract for every enrolled Sync profile

Each instance supplies only its generated states and code equations to the existing
`IoMutexCode` contract. Its general `body_wp`, `lock_wp` and `unlock_wp` proofs are shared;
clients use the resulting `MutexImpl` rules with `fsym`. The profile-local types, encoders
and functions remain distinct. The public `Sync.ioMutex` instance is unchanged.
-/

open Zig Zig.Conc Zig.Full

namespace Sync.CaseContracts.V0_17_0.H_6c696e7578

open Sync.Gen.V0_17_0.H_6c696e7578

/-- The lock-word representation in the actual Zig 0.17.0 Linux translation. -/
def states : LockWord.States Io_Mutex_State where
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

/-- Code correspondence for this profile, with its own generated types and functions. -/
def code : IoMutexCode Tgt where
  S := Io_Mutex_State
  st := states
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

/-- This profile's translated mutex satisfies the existing general mutex contract. -/
def mutex : MutexImpl Tgt := code.impl

end Sync.CaseContracts.V0_17_0.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_6c696e7578

open Sync.Gen.V0_16_0.H_6c696e7578

/-- The lock-word representation in the actual Zig 0.16.0 Linux translation. -/
def states : LockWord.States Io_Mutex_State where
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

/-- Code correspondence for this profile, with its own generated types and functions. -/
def code : IoMutexCode Tgt where
  S := Io_Mutex_State
  st := states
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

/-- This profile's translated mutex satisfies the existing general mutex contract. -/
def mutex : MutexImpl Tgt := code.impl

end Sync.CaseContracts.V0_16_0.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_64617277696e

open Sync.Gen.V0_16_0.H_64617277696e

/-- The lock-word representation in the actual Zig 0.16.0 Darwin translation. -/
def states : LockWord.States Io_Mutex_State where
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

/-- Code correspondence for this profile, with its own generated types and functions. -/
def code : IoMutexCode Tgt where
  S := Io_Mutex_State
  st := states
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

/-- This profile's translated mutex satisfies the existing general mutex contract. -/
def mutex : MutexImpl Tgt := code.impl

end Sync.CaseContracts.V0_16_0.H_64617277696e
