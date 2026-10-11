import Proofs.Threadsync.Lock
import ZigLean.Witness

/-!
# `Thread.Futex.Deadline` with no timeout

`Condition.wait` and `ResetEvent.waitUntilSet` (0.15.2) store a `Deadline` in a 48-byte block on
the waiter's stack. With `timeout = null` the block holds `dl0`: `Deadline.wait` reads `none` and
does one futex wait. `DLb` and `DL` are the facts on the block that a waiter keeps in its own part
(`Proofs/Threadsync/WaitGroup.lean`, `Proofs/Threadsync/Handoff.lean`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Assn

namespace Threadsync

/-- The deadline with no timeout, as `Deadline.init(null)` returns it: the bytes of
`timeout = null`, and `started` undefined (`Zig.Bytes`). -/
def dl0 : Bytes Thread_Futex_Deadline :=
  writeBytes (Array.replicate 48 Byte.undef) 0 (Enc.encode (none : Option (BitVec 64)))

/-- The deadline block after the store of `dl0`. -/
def bsD : Array Byte := writeBytes (Array.replicate 48 Byte.undef) 0 dl0

theorem dl0_size : dl0.size = 48 := by decide +kernel

theorem bsD_size : bsD.size = 48 := by
  unfold bsD; rw [writeBytes_size _ _ _ (by rw [dl0_size]; decide)]; simp

def isNone (r : Option (Except Error (Option (BitVec 64)))) : Bool :=
  match r with
  | some (.ok none) => true
  | _ => false

/-- A decode of `none` from its `isNone` check. -/
theorem none_of_isNone {r : Result (Option (BitVec 64))} (h : isNone r.run = true) : r = pure none := by
  revert h
  generalize r = r'
  intro h
  show r'.run = some (.ok none)
  unfold isNone at h
  split at h
  · assumption
  · cases h

theorem dl_none : (Enc.decode (bsD.extract 0 (0 + 16)) : Result (Option (BitVec 64))) = pure none :=
  none_of_isNone (by decide +kernel)

/-- `Deadline.init(null)`'s bytes after its store of `timeout`. -/
theorem dinit_bytes : Bytes.set (Bytes.setUndef Thread_Futex_Deadline (Bytes.undef Thread_Futex_Deadline) 0) 0
    (none : Option (BitVec 64)) = dl0 := by
  decide +kernel

/-- Its read of `timeout` decodes only the bytes of `timeout`. -/
theorem dinit_timeout : (Bytes.get (Option (BitVec 64)) dl0 0 : Result (Option (BitVec 64))) = pure none :=
  none_of_isNone (by decide +kernel)

/-- `started` stays undefined: a read of it throws `.unspecified`. -/
theorem dinit_started : (Bytes.get time_Timer dl0 16 : Result time_Timer).run = some (.error .unspecified) := by
  have h : (match (Bytes.get time_Timer dl0 16 : Result time_Timer).run with
    | some (.error .unspecified) => true
    | _ => false) = true := by decide +kernel
  revert h
  generalize (Bytes.get time_Timer dl0 16 : Result time_Timer).run = r
  intro h
  split at h
  · rfl
  · cases h

theorem dinit_eq : Thread_Futex_Deadline_init none = (pure dl0 : ConcM Tgt _) := by
  unfold Thread_Futex_Deadline_init
  simp only [StateT.run'_eq, StateT.run_bind, pure_bind, StateT.run_modify, StateT.run_get,
    map_pure, bind_pure_comp, dinit_bytes, dinit_timeout, liftM, monadLift, MonadLift.monadLift]
  rfl

/-- A heap of bytes in another block than block 0. -/
theorem hb0_of {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap} {b : Nat}
    (hb : bytesAt p A S K bs h) (hpb : p.block = some b) (hb0 : b ≠ 0) : ∀ y, h (0, y) = none :=
  fun y => by
    cases e : h (0, y)
    · rfl
    · exfalso; have := bytesAt_block hb hpb (l := (0, y)) (by rw [e]; simp); exact hb0 this.symm

/-- A deadline block `p` (part `hD`, bytes `bs`), not block 0. -/
structure DLb (p : Ptr) (bs : Array Byte) (hD : Heap) : Prop where
  off : p.off = 0
  blk : ∃ b, p.block = some b ∧ b ≠ 0
  bytes : ∃ A, A % 8 = 0 ∧ bytesAt p A 48 .stack bs hD

theorem DLb.b0 {p : Ptr} {bs : Array Byte} {hD : Heap} (h : DLb p bs hD) :
    ∀ y, hD (0, y) = none := by
  obtain ⟨b, hpb, hb0⟩ := h.blk
  obtain ⟨A, -, hb⟩ := h.bytes
  exact hb0_of hb hpb hb0

/-- The deadline block with no timeout. -/
abbrev DL (p : Ptr) (hD : Heap) : Prop := DLb p bsD hD

nonvacuity_witness none_of_isNone := ⟨pure none, rfl, trivial⟩

end Threadsync
