import ZigLean
import ZigLean.Mem.Lemmas

/-! MM-5 regression: the stack budget (`Zig.enterFrame`, `Mem.withStack`, MM-16).

`down n` has the shape of a generated recursive function that uses memory: it charges a frame,
recurses, and releases the frame. The runs are evaluated (`#guard`); the lemma
`enterFrame_overflow` is checked by the kernel. The stack blocks' part of the budget is in
`tests/roadmap/stack-region/Regressions.lean`. -/

open Zig

def down : Nat → MemM Unit
  | 0 => do enterFrame; leaveFrame
  | n + 1 => do enterFrame; down n; leaveFrame

/-- The outcome of `down n` from a memory with budget `S` (main thread), with its depth after. -/
def outcome (S : Option Nat) (n : Nat) : Option (Except Error Nat) :=
  let m : Mem := match S with
    | some S => ({} : Mem).withStack S
    | none => {}
  (((down n).run m).run).map fun r => r.map (·.2.stackDepth 0)

-- Without a budget (every generated `mem0`) any depth runs.
#guard outcome none 100000 = some (.ok 0)

-- Each frame charges `frameBase = 16` bytes: 6 frames fit in 96 bytes, 7 do not; the frames are
-- released.
#guard outcome (some 96) 5 = some (.ok 0)
#guard outcome (some 96) 6 = some (.error .stackOverflow)

/-- The lemma form: a frame that does not fit overflows. -/
example (m : Mem) (h : (m.stackOf m.current).budget = some 0) :
    (enterFrame.run m).run = some (.error .stackOverflow) :=
  enterFrame_overflow h (by simp [frameBase])

/-- `.stackOverflow` is its own outcome, not a panic or illegal behaviour. -/
example : Error.stackOverflow ≠ .illegal ∧ Error.stackOverflow ≠ .panic := by decide
