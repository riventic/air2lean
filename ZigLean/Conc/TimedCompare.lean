import ZigLean.Conc.TimedBody
import ZigLean.Conc.Lemmas

/-! Source-side event contract for the selected timed compare. This module does not
assert correspondence to an OS futex backend. The caller must supply a successful
selected read, and an explicit current-message premise for newest-byte agreement. -/
namespace Zig.TimedBody

/-- One compare read, with its read choice and RC11 location/view updates retained.
There is no additional newest-byte read and no acquire edge. -/
def readAtomicCompareStep (choice : Nat) (p : Ptr) : MemM (BitVec 32) :=
  atomicLoadAt choice .relaxed 4 p

/-- Runtime v5 performs this source action once; the adapter does not add a second read. -/
theorem kernelCompare_sourceAction (choice : Nat) (p : Ptr) :
    TimedSched.readWord choice p = readAtomicCompareStep choice p := rfl

/-- The compare consumes exactly an existing source atomic-read event. In particular
its final memory includes location creation/update and the selected message's seen id. -/
theorem readAtomicCompareStep_event {choice : Nat} {p : Ptr} {word : BitVec 32}
    {before after : Mem}
    (success : ((readAtomicCompareStep choice p).run before).run =
      some (.ok (word, after))) :
    ∃ b blk o li located pos,
      before.access p (intSize 32) 4 = pure (b, blk, o) ∧
      NoRace before b o (intSize 32) .atomicRead ∧
      ((locIdx b o (intSize 32)).run
        (before.recordAt b o (intSize 32) .atomicRead)).run =
          some (.ok (li, located)) ∧
      (readOpts located li false)[choice]? = some pos ∧
      (intOfBytes 32 ((located.atomics[li]!).msgs[pos]!).bytes).run =
        some (.ok word) ∧
      after = Conc.Proto.loadM located li .relaxed ((located.atomics[li]!).msgs[pos]!) := by
  exact Conc.Proto.atomicLoadAt_ok success

/-- A current-message premise concerns bytes, not an unjustified equality of memory
states. Read-choice/seen updates still follow the event theorem above. -/
theorem selectedMessage_currentValue {messageBytes currentBytes : Array Byte}
    {word : BitVec 32}
    (current : messageBytes = currentBytes)
    (decoded : (intOfBytes 32 messageBytes).run = some (.ok word)) :
    (intOfBytes 32 currentBytes).run = some (.ok word) := by
  simpa only [current] using decoded

end Zig.TimedBody
