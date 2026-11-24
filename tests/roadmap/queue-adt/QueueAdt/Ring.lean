import QueueAdt.Gen
import QueueAdt.Window
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Queue

/-!
# The ring buffer of `queue.zig` meets the queue contract (P04)

`QueueAdt/Gen.lean` is the committed translation of `queue.zig` (Zig 0.17.1; retained AIR in
`air/`, checked byte for byte by `check.sh`). `Ring` is a header of a buffer slice, the index
`head` of the front item and the number `len` of items; `push` writes the cell `len` places
after `head`, around the end of the buffer, and `pop` reads the cell at `head` and moves `head`
on, to 0 after the last cell.

`ring q C xs` is the representation predicate: the header at `q` with a buffer of `C` cells
`items`, and `xs` is the window of `len` cells from `head` (`QueueAdt.window`, wrap-around
included). `ringQueue` proves the contract `Zig.Full.QueueImpl` (`ZigLean/Sep/Full/Queue.lean`)
for the generated `Ring_push`, `Ring_pop` and `Ring_count`: each operation is one `fsym` walk of
the generated code (no bounds check and no overflow check fails, it returns), and what the walk
leaves are the facts about `window` (`QueueAdt/Window.lean`: a write behind the last item adds it
at the back; the front item is the cell at `head`).
-/

namespace QueueAdt
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- The header of a ring: the buffer `buf` of `cap` cells, the front index and the count. -/
def hdr (buf : Ptr) (cap head len : BitVec 64) : Ring :=
  { items := { ptr := buf, len := cap }, head := head, len := len }

/-- The ring at `q` has `C` cells and holds `xs`, front first: its header, and its buffer's
cells `items`, of which `xs` are the `len` cells from `head`, around the end. `head` is a cell's
index (0 for a buffer without cells). -/
def ring (q : Ptr) (C : Nat) (xs : List (BitVec 32)) : FAssn :=
  FAssn.ex fun buf : Ptr => FAssn.ex fun cap : BitVec 64 => FAssn.ex fun head : BitVec 64 =>
    FAssn.ex fun len : BitVec 64 => FAssn.ex fun items : List (BitVec 32) =>
      ⟪cap.toNat = C ∧ items.length = C ∧ head.toNat ≤ C - 1 ∧ len.toNat = xs.length ∧
        xs.length ≤ C ∧ xs = window items head.toNat len.toNat⟫ ⋆
      (up (pts q 8 (hdr buf cap head len)) ⋆ up (arr buf items))

attribute [local fsym_arith] List.length_set

/-- **`push`** puts `v` at the back of a ring with room, around the end of the buffer; a full
ring fails with `error.Full` and is unchanged. -/
theorem push_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) (v : BitVec 32) :
    FTotalTriple (ring q C xs) (Ring_push q v) (QueueImpl.Pushed ring q C xs v) := by
  unfold Ring_push
  fsym

/-- **`pop`** takes the front item of a ring and moves the front index on (to 0 after the last
cell); an empty ring gives `null`. -/
theorem pop_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (ring q C xs) (Ring_pop q) (QueueImpl.Popped ring q C xs) := by
  unfold Ring_pop
  fsym

/-- **`count`** returns the number of items. -/
theorem count_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (ring q C xs) (Ring_count q)
      (fun r => ⟪r.toNat = xs.length ∧ xs.length ≤ C⟫ ⋆ ring q C xs) := by
  unfold Ring_count
  fsym

/-- The generated ring buffer is a bounded FIFO queue. -/
def ringQueue : QueueImpl Ptr (BitVec 32) Ring_push Ring_pop Ring_count where
  Rep := ring
  push_spec := push_spec
  pop_spec := pop_spec
  len_spec := count_spec

end QueueAdt
