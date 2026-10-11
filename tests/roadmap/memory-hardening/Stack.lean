import ZigLean
import ZigLean.Mem.Lemmas

/-! MM-5 regression: the stack budget (`Zig.enterFrame`, `Mem.stackLimit`).

`down n` has the shape of a generated recursive function that uses memory: it charges a frame,
recurses, and releases the frame. The runs are evaluated (`#guard`); the lemma `enterFrame_overflow` is checked by the kernel. -/

open Zig

def down : Nat → MemM Unit
  | 0 => do enterFrame 8; leaveFrame 8
  | n + 1 => do enterFrame 8; down n; leaveFrame 8

/-- The outcome of `down n` from a memory with budget `limit`, with the bytes still charged. -/
def outcome (limit : Option Nat) (n : Nat) : Option (Except Error Nat) :=
  (((down n).run { stackLimit := limit }).run).map fun r => r.map (·.2.stackUsed)

-- Without a budget (every generated `mem0`) any depth runs, and the frames are released.
#guard outcome none 100000 = some (.ok 0)

-- Each frame takes `frameBase + 8 = 24` bytes: 4 frames fit in 96 bytes, 5 do not.
#guard outcome (some 96) 3 = some (.ok 0)
#guard outcome (some 96) 4 = some (.error .stackOverflow)

/-- The lemma form: a frame that does not fit overflows. -/
example (m : Mem) (h : m.stackLimit = some 0) : ((enterFrame 0).run m).run = some (.error .stackOverflow) :=
  enterFrame_overflow h (by simp [frameBase])

/-- `.stackOverflow` is its own outcome, not a panic or illegal behaviour. -/
example : Error.stackOverflow ≠ .illegal ∧ Error.stackOverflow ≠ .panic := by decide
