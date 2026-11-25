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
the generated code (no bounds check and no overflow check fails, it returns). The module supplies
the invariant `ring` and its two updates at the returns (`fsym [pushed_upd v]`, `fsym
[popped_upd]`: the header and the cells after the operation are a ring again, by the facts about
`window` in `QueueAdt/Window.lean`); their index arithmetic is the walk's side goals.
-/

namespace QueueAdt
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- The ring at `q` has `C` cells and holds `xs`, front first: its header, and its buffer's
cells `items`, of which `xs` are the `len` cells from `head`, around the end. `head` is a cell's
index (0 for a buffer without cells). -/
def ring (q : Ptr) (C : Nat) (xs : List (BitVec 32)) : FAssn :=
  FAssn.ex fun buf : Ptr => FAssn.ex fun cap : BitVec 64 => FAssn.ex fun head : BitVec 64 =>
    FAssn.ex fun len : BitVec 64 => FAssn.ex fun items : List (BitVec 32) =>
      ⟪cap.toNat = C ∧ items.length = C ∧ head.toNat ≤ C - 1 ∧ len.toNat ≤ C ∧
        xs = window items head.toNat len.toNat⟫ ⋆
      (up (pts q 8 ({ items := { ptr := buf, len := cap }, head := head, len := len } : Ring)) ⋆
        up (arr buf items))

-- the length of a window, where its start and its count are within the buffer
attribute [local fsym_arith] length_window

/-- The ring after a `push`, as an update of the walk's state at the return: the header with
the count `len' = len + 1` and the cells with `v` written at `i`, the cell after the last item
(`window_push`). -/
theorem pushed_upd {q buf : Ptr} {cap head len len' i : BitVec 64} {items : List (BitVec 32)}
    (v : BitVec 32) (hi : items.length = cap.toNat) (hh : head.toNat < cap.toNat)
    (hn : len.toNat < cap.toNat) (hn' : len'.toNat = len.toNat + 1)
    (hi1 : head.toNat + len.toNat < cap.toNat → i.toNat = head.toNat + len.toNat)
    (hi2 : cap.toNat ≤ head.toNat + len.toNat → i.toNat + cap.toNat = head.toNat + len.toNat) :
    EUpd (up (pts q 8 ({ items := { ptr := buf, len := cap }, head := head, len := len' } : Ring)) ⋆
        up (arr buf (items.set i.toNat v)))
      (QueueImpl.Pushed ring q cap.toNat (window items head.toNat len.toNat) v (.ok ())) :=
  EUpd.of_imp fun _ h => by
    have hp := window_push (items := items) (head := head.toNat) (n := len.toNat)
      (n' := len'.toNat) (i := i.toNat) v (by omega) (by omega) hn' (fun h => hi1 (by omega))
      (fun h => by have := hi2 (by omega); omega)
    have hl : (window items head.toNat len.toNat).length = len.toNat :=
      length_window (by omega) (by omega)
    exact sep_lift.mpr ⟨by omega, ⟨buf, cap, head, len', items.set i.toNat v, sep_lift.mpr
      ⟨⟨rfl, by rw [List.length_set]; exact hi, by omega, by omega, hp⟩, h⟩⟩⟩

/-- The ring after a `pop`, as an update of the walk's state at the return: the header with the
next front index `head'` (0 after the last cell) and the count `len' = len - 1`; the item is the
cell at `head` (`window_cons`). -/
theorem popped_upd {q buf : Ptr} {cap head head' len len' : BitVec 64}
    {items : List (BitVec 32)} (hi : items.length = cap.toNat) (hh : head.toNat < cap.toNat)
    (hn : len.toNat = len'.toNat + 1) (hle : len.toNat ≤ cap.toNat)
    (h1 : head.toNat + 1 = cap.toNat → head'.toNat = 0)
    (h2 : head.toNat + 1 < cap.toNat → head'.toNat = head.toNat + 1) :
    EUpd (up (pts q 8 ({ items := { ptr := buf, len := cap }, head := head', len := len' } : Ring)) ⋆
        up (arr buf items))
      (QueueImpl.Popped ring q cap.toNat (window items head.toNat len.toNat)
        (some (items[head.toNat]'(by omega)))) :=
  EUpd.of_imp fun _ h => by
    have hc := window_cons (items := items) (head := head.toNat) (head' := head'.toNat)
      (n := len.toNat) (n' := len'.toNat) (by omega) hn (by omega) (fun h => h1 (by omega))
      (fun h => h2 (by omega))
    have hl : (window items head'.toNat len'.toNat).length = len'.toNat :=
      length_window (by omega) (by omega)
    exact ⟨window items head'.toNat len'.toNat, sep_lift.mpr ⟨⟨hc, by omega⟩,
      ⟨buf, cap, head', len', items, sep_lift.mpr
        ⟨⟨rfl, hi, by omega, by omega, rfl⟩, h⟩⟩⟩⟩

/-- **`push`** puts `v` at the back of a ring with room, around the end of the buffer; a full
ring fails with `error.Full` and is unchanged. -/
theorem push_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) (v : BitVec 32) :
    FTotalTriple (ring q C xs) (Ring_push q v) (QueueImpl.Pushed ring q C xs v) := by
  unfold Ring_push
  fsym [pushed_upd v]

/-- **`pop`** takes the front item of a ring and moves the front index on (to 0 after the last
cell); an empty ring gives `null`. -/
theorem pop_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (ring q C xs) (Ring_pop q) (QueueImpl.Popped ring q C xs) := by
  unfold Ring_pop
  fsym [popped_upd]

/-- **`count`** returns the number of items. -/
theorem count_spec (q : Ptr) (C : Nat) (xs : List (BitVec 32)) :
    FTotalTriple (ring q C xs) (Ring_count q)
      (fun r => ⟪r.toNat = xs.length ∧ xs.length ≤ C⟫ ⋆ ring q C xs) := by
  unfold Ring_count
  fsym

/-- The generated ring buffer is a bounded FIFO queue whose operations run no step. -/
def ringQueue : QueueImpl Ptr (BitVec 32) Ring_push Ring_pop Ring_count :=
  QueueImpl.ofStepFree ring push_spec pop_spec count_spec

end QueueAdt
