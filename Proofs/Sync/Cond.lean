import Proofs.Sync.IoMutex
import ZigLean.Sep.Full.IoCond

/-!
# `Io.Condition` of `examples/sync` as a condition (`CondImpl`)

The per-item obligation of `Io.Condition` (Zig 0.16.0's std code) in this program's generated
code: its `signal`, `broadcast`, `waitInner(…, true)` and `waitUncancelable` are `Io.Condition`'s code
(`IoCondCode`, `ZigLean/Sep/Full/IoCond.lean`), with the program's `Io.Mutex` (`ioMutex`), so
they satisfy the condition contract (`CondImpl`) for every protocol that has the condition next
to its mutex. This file gives the program's names and the unfolding equations. Every golden case
of `sync` (Zig 0.16.0 and 0.17.1, whose `waitUncancelable` inlines `waitInner`'s loops) has its
own instance in `Proofs/Sync/CondCases.lean`.
-/

open Zig Zig.Conc Zig.Full

namespace Sync

/-- `Io.Condition`'s code in this program. -/
def ioCondCode : IoCondCode Tgt where
  M := ioMutex
  S := Io_Condition_State
  wa := Io_Condition_State.waiters
  si := Io_Condition_State.signals
  pack := Io_Condition_State.mk
  dassert := debug_assert
  σs := Io_Condition_signalLocals
  Es := Io_Condition_signalExit
  sprev := Io_Condition_signalLocals.prev_state
  ssetPrev s v := { s with prev_state := v }
  sret := .ret
  sstop := .br10
  srep := .rep11
  sagain := Io_Condition_signal.again11
  sbody := Io_Condition_signal.loop11
  sbody_eq _ _ := by
    simp only [Io_Condition_signal.loop11, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  signal := Io_Condition_signal
  signal_eq := ⟨_, _, fun _ _ => by
    simp only [Io_Condition_signal, IoCondCode.signalOf, bind_assoc, pure_bind]; rfl,
    by rfl, by rfl, by rfl⟩
  σb := Io_Condition_broadcastLocals
  Eb := Io_Condition_broadcastExit
  bprev := Io_Condition_broadcastLocals.prev_state
  bsetPrev s v := { s with prev_state := v }
  bret := .ret
  bstop := .br10
  brep := .rep11
  bagain := Io_Condition_broadcast.again11
  bbody := Io_Condition_broadcast.loop11
  bbody_eq _ _ := by
    simp only [Io_Condition_broadcast.loop11, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  broadcast := Io_Condition_broadcast
  broadcast_eq := ⟨_, _, fun _ _ => by
    simp only [Io_Condition_broadcast, IoCondCode.signalOf, bind_assoc, pure_bind]; rfl,
    by rfl, by rfl, by rfl⟩
  σ := Io_Condition_waitInnerLocals
  E := Io_Condition_waitInnerExit
  ep := Io_Condition_waitInnerLocals.epoch
  setEp s v := { s with epoch := v }
  prev := Io_Condition_waitInnerLocals.prev_state
  setPrev s v := { s with prev_state := v }
  done := .ret (.ok ())
  istop := .br55
  irep := .rep56
  orep := .rep23
  iagain := Io_Condition_waitInner.again56
  oagain := Io_Condition_waitInner.again23
  inner := Io_Condition_waitInner.loop56
  inner_eq _ _ _ := by
    simp only [Io_Condition_waitInner.loop56, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  outer p io q := Io_Condition_waitInner.loop23 p io q true
  outer_eq := ⟨_, fun _ _ _ => by
    simp only [Io_Condition_waitInner.loop23, IoCondCode.outerOf, bind_assoc, pure_bind,
      Norm.ite_bind, ↓reduceIte, isNonErr, isErr, Bool.not_false]; rfl,
    by simp only [pure_bind], by simp only [pure_bind]⟩
  R := Except ErrName Unit
  rv := .ok ()
  core p io q := Io_Condition_waitInner p io q true
  core_eq := ⟨_, fun _ _ _ => by
    simp only [Io_Condition_waitInner, IoCondCode.coreOf, bind_assoc, pure_bind]; rfl, by rfl⟩
  wait := Io_Condition_waitUncancelable
  wait_eq := .call (σ := Io_Condition_waitUncancelableLocals) _
    Io_Condition_waitUncancelableExit.ret _ (fun _ _ _ => by
      simp only [Io_Condition_waitUncancelable, pure_bind]; rfl)
      (by simp only [isNonErr, isErr, Bool.not_false, ↓reduceIte, pure_bind]) (by rfl)

/-- `Io.Condition` of this program as a condition, with the program's `Io.Mutex`. -/
def ioCond : CondImpl Tgt := ioCondCode.impl

end Sync
