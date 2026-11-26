import Proofs.Sync.Cond
import ZigLean.Sep.Full.IoSem

/-!
# `Io.Semaphore` of `examples/sync` as a semaphore (`SemImpl`)

The per-item obligation of `Io.Semaphore` (Zig 0.16.0's std code) in this program's generated
code: its `waitUncancelable` and `post` are `Io.Semaphore`'s code (`IoSemCode`,
`ZigLean/Sep/Full/IoSem.lean`), with the program's `Io.Mutex` (`ioMutex`) and `Io.Condition`
(`ioCond`), so they satisfy the semaphore contract (`SemImpl`) for every protocol that has the
semaphore, with any number of waiters and posters. This file gives the program's names and the
unfolding equations. Every golden case of `sync` has its own instance in
`Proofs/Sync/SemCases.lean`.
-/

open Zig Zig.Conc Zig.Full

namespace Sync

/-- `Io.Semaphore`'s code in this program. -/
def ioSemCode : IoSemCode Tgt where
  M := ioMutex
  C := ioCond
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

/-- **`Io.Semaphore` of this program is a semaphore** (`SemImpl`), with the program's
`Io.Mutex` and `Io.Condition`: both ops keep the caller's part and pay from its unmetered
fragment. -/
def ioSem : SemImpl Tgt := ioSemCode.impl

end Sync
