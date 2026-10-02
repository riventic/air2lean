import Proofs.Threadsync.Lock

/-!
# `Thread.Futex.Deadline` with no timeout

`Condition.wait` and `ResetEvent.waitUntilSet` (0.15.2) store a `Deadline` in a 48-byte block on
the waiter's stack. With `timeout = null` the block holds `dl0`: `Deadline.wait` reads `none` and
does one futex wait. `DLb` and `DL` are the facts on the block that a waiter keeps in its own part
(`Proofs/Threadsync/WaitGroup.lean`, `Proofs/Threadsync/Handoff.lean`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Assn

namespace Threadsync

/-- The deadline with no timeout. -/
def dl0 : Thread_Futex_Deadline := { (default : Thread_Futex_Deadline) with timeout := none }

/-- The deadline block after the store of `dl0`. -/
def bsD : Array Byte := writeBytes (Array.replicate 48 Byte.undef) 0 (Enc.encode dl0)

theorem dl0_size : (Enc.encode dl0).size = 48 := by decide +kernel

theorem bsD_size : bsD.size = 48 := by
  unfold bsD; rw [writeBytes_size _ _ _ (by rw [dl0_size]; decide)]; simp

def isNone (r : Option (Except Error (Option (BitVec 64)))) : Bool :=
  match r with
  | some (.ok none) => true
  | _ => false

theorem dl_none_b : isNone ((Enc.decode (bsD.extract 0 (0 + 16)) : Result (Option (BitVec 64))).run) =
    true := by
  decide +kernel

theorem dl_none : (Enc.decode (bsD.extract 0 (0 + 16)) : Result (Option (BitVec 64))) = pure none := by
  have h := dl_none_b
  revert h
  generalize (Enc.decode (bsD.extract 0 (0 + 16)) : Result (Option (BitVec 64))) = r
  intro h
  show r.run = some (.ok none)
  unfold isNone at h
  split at h
  · assumption
  · cases h

theorem dinit_eq : Thread_Futex_Deadline_init none = (pure dl0 : ConcM Tgt _) := by
  unfold Thread_Futex_Deadline_init
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, StateT.run_modify,
    StateT.run_get, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, map_pure, bind_pure_comp]
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

end Threadsync
