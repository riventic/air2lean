import Proofs.Threadsync.Gen
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Tick
import ZigLean.Witness

/-!
# `Thread.Futex.Deadline` with no timeout

`Condition.wait` and `ResetEvent.waitUntilSet` (0.15.2) store a `Deadline` in a 48-byte block on
the waiter's stack. With `timeout = null` the block holds `dl0`: `Deadline.wait` reads `none` and
does one futex wait. `DLb` and `DL` are the facts on the block that a waiter keeps in its own part
(`Proofs/Threadsync/WaitGroup.lean`, `Proofs/Threadsync/Cond.lean`, `Proofs/Threadsync/Event.lean`).
-/

open Zig Zig.Conc Zig.Conc.Proto Assn

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
    · exfalso
      have hl : h (0, y) ≠ none := by rw [e]; simp
      obtain ⟨b', hb', -, hown⟩ := hb
      rw [hpb] at hb'; cases hb'
      rw [hown] at hl
      split at hl
      · rename_i hc; exact hb0 hc.1.symm
      · exact absurd rfl hl

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

/-! ## The deadline block in a thread's part (full-state)

The waiter's part while it runs `Condition.wait` or `ResetEvent.waitUntilSet`: the part `r₀` it
had before, and the deadline block `q` with the bytes `bs` (`DPart`). Its `alloc`, the store of
`dl0`, the read of `timeout` and the `free` are thread triples (`FTTriple`), for the event's and
the condition's `wp_liftPart`. -/

open Zig.Full Zig.Full.FAssn in
/-- The part `r₀` and the deadline block `q` with the bytes `bs`. -/
def DPart (r₀ : Res) (q : Ptr) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
    ⟪q.block = some b ∧ q.off = 0 ∧ A % 8 = 0⟫ ⋆
      ((up (bytesAt q A 48 .stack bs) ⋆ bext b 48 .stack) ⋆ (· = r₀))

section DPart
open Zig.Full Zig.Full.FAssn

theorem dpart_of {r₀ r : Res} {q : Ptr} {bs : Array Byte} {A : Nat} {b : BlockId}
    (hq : q.block = some b) (h0 : q.off = 0) (hA : A % 8 = 0)
    (h : ((up (bytesAt q A 48 .stack bs) ⋆ bext b 48 .stack) ⋆ (· = r₀)) r) : DPart r₀ q bs r :=
  ⟨A, b, sep_lift.mpr ⟨⟨hq, h0, hA⟩, h⟩⟩

theorem DPart.get {r₀ r : Res} {q : Ptr} {bs : Array Byte} (h : DPart r₀ q bs r) :
    ∃ A b, q.block = some b ∧ q.off = 0 ∧ A % 8 = 0 ∧
      ((up (bytesAt q A 48 .stack bs) ⋆ bext b 48 .stack) ⋆ (· = r₀)) r := by
  obtain ⟨A, b, h⟩ := h
  obtain ⟨⟨h1, h2, h3⟩, h⟩ := sep_lift.mp h
  exact ⟨A, b, h1, h2, h3, h⟩

/-- `allocStack 48 8`: the deadline block, next to the part. A stack block needs the plain mode
(`FTriple.allocStackDrop`), which the part holds (`Res.Plain`) and splits off
(`EUpd.plain_split`). -/
theorem dalloc (r₀ : Res) (hpl : r₀.Plain) :
    FTTriple (· = r₀) (allocStack 48 8) (fun q => DPart r₀ q (Array.replicate 48 .undef)) :=
  FTTriple.eupd (EUpd.plain_split fun _ h => h ▸ hpl)
    (((by fsym [FTriple.allocStackDrop] : FTTriple plain _ _).frame (R := (· = r₀))).conseq
      (fun _ h => sep_comm h)
      fun q r h => by
        obtain ⟨A, h⟩ := sep_ex.mp h
        obtain ⟨b, h⟩ := sep_ex.mp h
        obtain ⟨⟨h1, h2, h3⟩, h⟩ := sep_lift.mp (sep_assoc h)
        exact dpart_of h1 h2 h3 h)

/-- The store of `dl0` (`Deadline.init(null)`) in the deadline block. -/
theorem dstore {r₀ : Res} {q : Ptr} {bs : Array Byte} (hbs : bs.size = 48) :
    FTTriple (DPart r₀ q bs) (storeBytes q 8 dl0) (fun _ => DPart r₀ q bsD) := by
  intro m r rF hh hp hc ho
  obtain ⟨A, b, hq, h0, hA, hp⟩ := hp.get
  have hw : writeBytes bs 0 dl0 = bsD := by
    unfold bsD
    rw [writeBytes_all (by rw [dl0_size, hbs]), writeBytes_all (by rw [dl0_size]; simp)]
  have ht := ((FTTriple.storeBytesAt (p := q) (q := q) (k := 0) (a := 8) (A := A) (S := 48)
    (K := .stack) (bs := bs) (b := b) dl0 hq (by cases q; simp [Ptr.add]) (by rw [dl0_size]; decide)
    (by simp [hbs, dl0_size]) (by rw [h0]; simpa using hA) (by decide)).frame
    (R := (· = r₀))).post (Q' := fun _ => DPart r₀ q bsD) fun _ r h =>
      dpart_of hq h0 hA (by rw [hw] at h; exact h)
  exact ht m r rF hh hp hc ho

/-- The read of `timeout` (`none`) in the deadline block. -/
theorem dload {r₀ : Res} {q : Ptr} :
    FTTriple (DPart r₀ q bsD) (Zig.load (Option (BitVec 64)) 8 q)
      (fun x => ⟪x = none⟫ ⋆ DPart r₀ q bsD) := by
  intro m r rF hh hp hc ho
  obtain ⟨A, b, hq, h0, hA, hp⟩ := hp.get
  have hl : FTTriple (up (bytesAt q A 48 .stack bsD) ⋆ bext b 48 .stack)
      (Zig.load (Option (BitVec 64)) 8 q)
      (fun x => ⟪x = none⟫ ⋆ (up (bytesAt q A 48 .stack bsD) ⋆ bext b 48 .stack)) := by
    have hs := bsD_size
    fsym [FTotalTriple.loadBlock (T := Option (BitVec 64)) (A := A) (S := 48) (K := .stack)
      (al := 8) hq (by decide) (by rw [bsD_size]; decide) dl_none (by simp [h0, hA])]
  have ht := (hl.frame (R := (· = r₀))).post
    (Q' := fun x => ⟪x = none⟫ ⋆ DPart r₀ q bsD) fun _ r h => by
      obtain ⟨h1, h⟩ := sep_lift.mp (sep_assoc h)
      exact sep_lift.mpr ⟨h1, dpart_of hq h0 hA h⟩
  exact ht m r rF hh hp hc ho

/-- The `free` of the deadline block: the part is `r₀` again. -/
theorem dfree {r₀ : Res} {q : Ptr} {bs : Array Byte} (hbs : bs.size = 48) :
    FTTriple (DPart r₀ q bs) (free q) (fun _ => (· = r₀)) := by
  intro m r rF hh hp hc ho
  obtain ⟨A, b, hq, h0, hA, hp⟩ := hp.get
  have hf : FTTriple (up (bytesAt q A 48 .stack bs) ⋆ bext b 48 .stack) (free q) (fun _ => emp) := by
    fsym
  have ht := (hf.frame (R := (· = r₀))).post (Q' := fun _ => (· = r₀)) fun _ r h =>
      (sep_emp (P := (· = r₀)) (r := r)).mp (sep_comm h)
  exact ht m r rF hh hp hc ho

end DPart

end Threadsync
