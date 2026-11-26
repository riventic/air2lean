import Proofs.Sync.MutexCases
import ZigLean.Sep.Full.IoCond

/-!
# The condition contract for every enrolled Sync profile

Each instance supplies only its generated states, locals, exits and code equations to the
`IoCondCode` interface (`ZigLean/Sep/Full/IoCond.lean`), with its profile's own mutex
(`Proofs/Sync/MutexCases.lean`). Its general walks prove `CondImpl` once for both shapes of the
wait: Zig 0.16.0's `waitUncancelable` calls `waitInner(…, true)` (`WaitShape.call`), Zig 0.17.1's
holds the inlined loops itself (`WaitShape.direct`). Clients use the resulting `CondImpl` rules.
The public `Sync.ioCond` (`Proofs/Sync/Cond.lean`) is the instance for the public translation.
-/

open Zig Zig.Conc Zig.Full

namespace Sync.CaseContracts.V0_17_1.H_6c696e7578

open Sync.Gen.V0_17_1.H_6c696e7578

/-- `Io.Condition`'s code in the actual Zig 0.17.1 Linux translation: the wait is its core. -/
def condCode : IoCondCode Tgt where
  M := mutex
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
  σ := Io_Condition_waitUncancelableLocals
  E := Io_Condition_waitUncancelableExit
  ep := Io_Condition_waitUncancelableLocals.epoch
  setEp s v := { s with epoch := v }
  prev := Io_Condition_waitUncancelableLocals.prev_state
  setPrev s v := { s with prev_state := v }
  done := .ret
  istop := .br44
  irep := .rep45
  orep := .rep22
  iagain := Io_Condition_waitUncancelable.again45
  oagain := Io_Condition_waitUncancelable.again22
  inner := Io_Condition_waitUncancelable.loop45
  inner_eq _ _ _ := by
    simp only [Io_Condition_waitUncancelable.loop45, bind_assoc, pure_bind, Norm.ite_bind]; rfl
  outer := Io_Condition_waitUncancelable.loop22
  outer_eq := ⟨_, fun _ _ _ => by
    simp only [Io_Condition_waitUncancelable.loop22, IoCondCode.outerOf, bind_assoc, pure_bind]
    rfl, by rfl, by rfl⟩
  R := Unit
  rv := ()
  core := Io_Condition_waitUncancelable
  core_eq := ⟨_, fun _ _ _ => by
    simp only [Io_Condition_waitUncancelable, IoCondCode.coreOf, bind_assoc, pure_bind]; rfl,
    by rfl⟩
  wait := Io_Condition_waitUncancelable
  wait_eq := .direct fun _ _ _ => by simp only [bind_pure_unit]

/-- This profile's translated condition satisfies the general condition contract. -/
def cond : CondImpl Tgt := condCode.impl

end Sync.CaseContracts.V0_17_1.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_6c696e7578

open Sync.Gen.V0_16_0.H_6c696e7578

/-- `Io.Condition`'s code in the actual Zig 0.16.0 Linux translation: the wait calls
`waitInner(…, true)`. -/
def condCode : IoCondCode Tgt where
  M := mutex
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

/-- This profile's translated condition satisfies the general condition contract. -/
def cond : CondImpl Tgt := condCode.impl

end Sync.CaseContracts.V0_16_0.H_6c696e7578

namespace Sync.CaseContracts.V0_16_0.H_64617277696e

open Sync.Gen.V0_16_0.H_64617277696e

/-- `Io.Condition`'s code in the actual Zig 0.16.0 Darwin translation: the wait calls
`waitInner(…, true)`. -/
def condCode : IoCondCode Tgt where
  M := mutex
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

/-- This profile's translated condition satisfies the general condition contract. -/
def cond : CondImpl Tgt := condCode.impl

end Sync.CaseContracts.V0_16_0.H_64617277696e
