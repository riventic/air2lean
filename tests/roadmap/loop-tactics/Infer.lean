import Proofs.Pointers.Gen
import Proofs.Lists.Gen
import ZigLean.Sep.LoopTemplate

/-!
# What `loop_template?` infers, and what it does not

`loop_template?` without an invariant prints suggestions read from one unfolding of the loop
body; it proves nothing and leaves the goal unchanged. These regressions pin its output on two
generated loops (`Pointers.sumTo`, a counter loop with a call; `Lists.sum`, a linked-list walk)
and on hand-written bodies in the generated shapes for the cases it refuses: a signed guard, a
counter that steps away from its bound, a counter that is also reset, and a bound that the loop
changes.
`tests/roadmap/loop-tactics/nested/Proof.lean` covers a translated nested loop.
-/

open Zig Assn

namespace InferTest

/-- The examples below only exercise the report. `loop_template?` leaves the goal unchanged, and
an unsatisfiable precondition then closes it: no loop is proved here. -/
theorem vacuous {α : Type} {c : MemM α} {Q : α → Assn} : TotalTriple (fun _ => False) c Q :=
  fun _ _ _ _ _ hp _ => hp.elim

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): i
  unchanged locals: acc
  measure candidate: fun s => n.toNat - s.i.toNat
  bound invariant candidate: fun s => s.i.toNat ≤ n.toNat
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
-- `while (i < n) : (i += 1) addTo(&acc, i)`: the counter, its bound and the untouched pointer.
example (p : Ptr) (n : BitVec 32) (s : Pointers.sumToLocals) (Q : Pointers.sumToExit × Pointers.sumToLocals → Assn) :
    TotalTriple (fun _ => False) ((Zig.loop (Pointers.sumTo.loop6 n p) Pointers.sumTo.again6).run s) Q := by
  loop_template?
  exact vacuous

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): s, p
  unchanged locals: (none)
  measure: not inferred (no unsigned counter steps towards a fixed bound); supply a ghost measure, e.g. the number of remaining items
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
-- `while (p) |n| : (p = n.next) s += n.val`: no counter; the queue proof
-- (`Queue.lean`) supplies the number of remaining nodes as a ghost measure.
example (s : Lists.sumLocals) (Q : Lists.sumExit × Lists.sumLocals → Assn) :
    TotalTriple (fun _ => False) ((Zig.loop Lists.sum.loop6 Lists.sum.again6).run s) Q := by
  loop_template?
  exact vacuous

/-! ## Refused shapes, hand-written in the generated style -/

structure L where
  i : BitVec 32
  n : BitVec 32
  deriving Inhabited

def signedLoop : MM L Bool := do
  let i ← pure ((← get).i)
  let n ← pure ((← get).n)
  if Zig.lt true i n then do
    let i' ← Zig.add true i (1 : BitVec 32)
    modify (fun s => { s with i := i' })
    pure true
  else pure false

def awayLoop : MM L Bool := do
  let i ← pure ((← get).i)
  let n ← pure ((← get).n)
  if Zig.lt false i n then do
    let i' ← Zig.sub false i (1 : BitVec 32)
    modify (fun s => { s with i := i' })
    pure true
  else pure false

def movingBound : MM L Bool := do
  let i ← pure ((← get).i)
  let n ← pure ((← get).n)
  if Zig.lt false i n then do
    let i' ← Zig.add false i (1 : BitVec 32)
    let n' ← Zig.add false n (1 : BitVec 32)
    modify (fun s => { s with i := i', n := n' })
    pure true
  else pure false

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): i
  unchanged locals: n
  guard Zig.lt: signed comparison, no measure inferred
  measure: not inferred (no unsigned counter steps towards a fixed bound); supply a ghost measure, e.g. the number of remaining items
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
example (s : L) (Q : Bool × L → Assn) :
    TotalTriple (fun _ => False) ((Zig.loop signedLoop id).run s) Q := by
  loop_template?
  exact vacuous

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): i
  unchanged locals: n
  guard Zig.lt: no local steps towards a fixed bound, no measure inferred
  measure: not inferred (no unsigned counter steps towards a fixed bound); supply a ghost measure, e.g. the number of remaining items
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
-- `i` decreases while the guard is `i < n`: no suggestion (this loop runs until `i` underflows).
example (s : L) (Q : Bool × L → Assn) :
    TotalTriple (fun _ => False) ((Zig.loop awayLoop id).run s) Q := by
  loop_template?
  exact vacuous

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): i, n
  unchanged locals: (none)
  guard Zig.lt: the bound of i changes in the loop, no measure inferred
  measure: not inferred (no unsigned counter steps towards a fixed bound); supply a ghost measure, e.g. the number of remaining items
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
example (s : L) (Q : Bool × L → Assn) :
    TotalTriple (fun _ => False) ((Zig.loop movingBound id).run s) Q := by
  loop_template?
  exact vacuous

/-- The counter steps up, but another path resets it: it need not approach the bound. -/
def resetLoop : MM L Bool := do
  let i ← pure ((← get).i)
  let n ← pure ((← get).n)
  if Zig.lt false i n then do
    if i == 7 then modify (fun s => { s with i := 0 })
    else do
      let i' ← Zig.add false i (1 : BitVec 32)
      modify (fun s => { s with i := i' })
    pure true
  else pure false

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): i
  unchanged locals: n
  guard Zig.lt: no local steps towards a fixed bound, no measure inferred
  measure: not inferred (no unsigned counter steps towards a fixed bound); supply a ghost measure, e.g. the number of remaining items
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
example (s : L) (Q : Bool × L → Assn) :
    TotalTriple (fun _ => False) ((Zig.loop resetLoop id).run s) Q := by
  loop_template?
  exact vacuous

-- A goal without a generated loop is rejected.
/-- error: loop_template?: the goal does not mention a Zig.loop -/
#guard_msgs in
example : TotalTriple emp (pure 0 : MemM Nat) (fun _ => emp) := by
  loop_template?
  exact TotalTriple.ret (Q := fun _ => emp) 0

end InferTest
