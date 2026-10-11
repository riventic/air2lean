import ZigLean.Mem.Enc
import ZigLean.Sep.Triple
import ZigLean.Sep.Try

open Zig
open scoped Zig
deriving instance DecidableEq for Except
namespace GlobalPayloads

-- An independent model address consists only of existing global provenance and a sum.
-- It neither allocates a block nor consults optional/error initialization state.
def resolved (root : Ptr) (parent payload leaf : Nat) : Ptr :=
  root.add ((parent + payload + leaf : Nat) : Int)

theorem provenance (root : Ptr) (parent payload leaf : Nat) :
    (resolved root parent payload leaf).block = root.block := rfl

theorem optional_alias (root : Ptr) (parent leaf : Nat) :
    resolved root parent 0 leaf = (root.add parent).add leaf := by
  simp [resolved, Ptr.add, Int.natCast_add, Int.add_assoc]

theorem small_alias (root : Ptr) (parent : Nat) :
    resolved root parent 2 0 = errPayloadPtr (BitVec 8) (root.add parent) := by
  change root.add ((parent + 2 + 0 : Nat) : Int) = (root.add parent).add (2 : Int)
  simp [Ptr.add, Int.natCast_add, Int.add_assoc]

theorem wide_alias (root : Ptr) (parent : Nat) :
    resolved root parent 0 0 = errPayloadPtr (BitVec 64) (root.add parent) := by
  change root.add ((parent + 0 + 0 : Nat) : Int) = (root.add parent).add (0 : Int)
  simp [Ptr.add]

theorem equal_alias (root : Ptr) (parent : Nat) :
    resolved root parent 0 0 = errPayloadPtr (BitVec 16) (root.add parent) := by
  change root.add ((parent + 0 + 0 : Nat) : Int) = (root.add parent).add (0 : Int)
  simp [Ptr.add]

theorem read_frame {T : Type} [Enc T] (root : Ptr) (parent payload leaf a : Nat)
    (v : T) (R : Assn) (hn : 0 < Enc.size T) :
    Triple (pts (resolved root parent payload leaf) a v ∗ R)
      (load T a (resolved root parent payload leaf))
      (fun r => (⌜r = v⌝ ∗ pts (resolved root parent payload leaf) a v) ∗ R) :=
  (Triple.load hn).frame

theorem write_frame {T : Type} [Enc T] [LawfulEnc T]
    (root : Ptr) (parent payload leaf a : Nat) (v w : T) (R : Assn) (hn : 0 < Enc.size T) :
    Triple (pts (resolved root parent payload leaf) a v ∗ R)
      (store a (resolved root parent payload leaf) w)
      (fun _ => pts (resolved root parent payload leaf) a w ∗ R) :=
  (Triple.store hn w).frame

private def root : Ptr := { block := some 0, off := 0 }
private def value (m : Mem) (x : MemM α) : Option (Except Error α) :=
  (x.run m).run.map (·.map Prod.fst)

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

-- Each tested object has neighboring bytes in the same existing global block.
private def smallBytes : Array Byte :=
  #[.int 77, .int 88] ++ Enc.encode (Except.ok (19#8) : Except ErrName (BitVec 8)) ++ #[.int 99]
private def smallMem (kind : BlockKind := .global) : Mem :=
  Mem.ofGlobals .fresh [(smallBytes, 2, kind)]
private def writeSmall : MemM (BitVec 8 × BitVec 8 × BitVec 8) := do
  let q := resolved root 2 2 0
  store 1 q (31#8)
  pure (← load (BitVec 8) 1 q, ← load (BitVec 8) 1 root, ← load (BitVec 8) 1 (root.add 6))

private def wideBytes : Array Byte :=
  Array.replicate 8 (.int 77) ++
    Enc.encode (Except.ok (41#64) : Except ErrName (BitVec 64)) ++ #[.int 99]
private def writeWide : MemM (BitVec 64 × BitVec 8 × BitVec 8) := do
  let q := resolved root 8 0 0
  store 8 q (123#64)
  pure (← load (BitVec 64) 8 q, ← load (BitVec 8) 1 root, ← load (BitVec 8) 1 (root.add 24))

-- Obtaining an absent payload address preserves provenance; decoding its undef bytes fails.
private def absentOptional : Mem :=
  Mem.ofGlobals .fresh [(Enc.encode (none : Option (BitVec 8)), 1, .global)]
private def absentError : Mem :=
  Mem.ofGlobals .fresh [(Enc.encode (Except.error "Bad" : Except ErrName (BitVec 8)), 2, .global)]

def main : IO Unit := do
  check "small runtime projection alias" (resolved root 2 2 0) (errPayloadPtr (BitVec 8) (root.add 2))
  check "wide runtime projection alias" (resolved root 8 0 0) (errPayloadPtr (BitVec 64) (root.add 8))
  check "equal-alignment runtime projection alias" (resolved root 2 0 0) (errPayloadPtr (BitVec 16) (root.add 2))
  check "optional nested alias" (resolved root 7 0 3) ((root.add 7).add 3)
  check "small write frame" (value smallMem writeSmall) (some (.ok (31#8, 77#8, 99#8)))
  check "wide write frame" (value (Mem.ofGlobals .fresh [(wideBytes, 8, .global)]) writeWide)
    (some (.ok (123#64, 77#8, 99#8)))
  check "const write rejected" (value (smallMem .constGlobal) writeSmall) (some (.error .illegal))
  check "absent optional stays undefined"
    (value absentOptional (load (BitVec 8) 1 (resolved root 0 0 0))) (some (.error .unspecified))
  check "absent error stays undefined"
    (value absentError (load (BitVec 8) 1 (resolved root 0 2 0))) (some (.error .unspecified))
  check "unbacked pointer stays invalid"
    (value {} (load (BitVec 8) 1 (resolved root 0 2 0))) (some (.error .illegal))
  IO.println "global payload alias, frame, const and absent-payload model checks passed"

end GlobalPayloads

def main : IO Unit := GlobalPayloads.main
