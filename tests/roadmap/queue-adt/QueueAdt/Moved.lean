/-!
# The cells of a shifting array during `pop` (pure; no memory)

`Shift.pop` of `tests/roadmap/queue-adt/queue.zig` moves the items `1 … len - 1` one cell down,
from the front. `moved items i` is the list of cells after the moves of the cells `1 … i - 1`
(`1 ≤ i`): the items `1 … i - 1` in the cells `0 … i - 2`, then the cells from `i - 1` on as they
were. The lemmas are what the loop of `pop` needs:

* `moved_one`: before the first move the cells are unchanged;
* `getElem_moved`: the cells from `i - 1` on are unchanged;
* `moved_step`: one move (cell `i` into cell `i - 1`) is the next `moved`;
* `take_moved`: after the last move the first `len - 1` cells are the items without the front;
* `take_set_succ`: a `push` writes the cell after the items.
-/

namespace QueueAdt

variable {α : Type}

/-- The cells after the moves of the cells `1 … i - 1` one cell down. -/
def moved (items : List α) (i : Nat) : List α :=
  (items.drop 1).take (i - 1) ++ items.drop (i - 1)

theorem length_moved {items : List α} {i : Nat} (h1 : 1 ≤ i) (h : i ≤ items.length) :
    (moved items i).length = items.length := by
  simp only [moved, List.length_append, List.length_take, List.length_drop]
  omega

theorem moved_one (items : List α) : moved items 1 = items := by
  simp [moved]

/-- The cells from `i - 1` on are the items there. -/
theorem getElem_moved {items : List α} {i j : Nat} (hj : i - 1 ≤ j)
    (hl : j < (moved items i).length) :
    (moved items i)[j] = items[j]'(by
      simp only [moved, List.length_append, List.length_take, List.length_drop] at hl; omega) := by
  have hm : ((items.drop 1).take (i - 1)).length ≤ j := by
    simp only [List.length_take, List.length_drop]; omega
  simp only [moved]
  rw [List.getElem_append_right hm, List.getElem_drop]
  congr 1
  simp only [List.length_take, List.length_drop]
  omega

/-- **One move**: the item at `i` written to the cell `i - 1`. -/
theorem moved_step {items : List α} {i : Nat} (h1 : 1 ≤ i) (h : i < items.length) :
    (moved items i).set (i - 1) items[i] = moved items (i + 1) := by
  have hd : items.drop (i - 1) = items[i - 1] :: items.drop i := by
    rw [List.drop_eq_getElem_cons (by omega)]
    congr 2
    omega
  have ht : (items.drop 1).take i = (items.drop 1).take (i - 1) ++ [items[i]] := by
    have h' : i - 1 < (items.drop 1).length := by simp only [List.length_drop]; omega
    have e := List.take_append_getElem h'
    rw [show i - 1 + 1 = i by omega] at e
    rw [← e, List.getElem_drop]
    congr 3
    omega
  have hl : ((items.drop 1).take (i - 1)).length = i - 1 := by
    simp only [List.length_take, List.length_drop]; omega
  simp only [moved, Nat.add_sub_cancel]
  rw [hd, ht, List.set_append_right _ _ (by omega), hl, Nat.sub_self, List.set_cons_zero,
    List.append_assoc, List.singleton_append]

/-- **After the last move** the first `n - 1` cells hold the `n` items without the front. -/
theorem take_moved {items : List α} {n : Nat} (h1 : 1 ≤ n) (h : n ≤ items.length) :
    (moved items n).take (n - 1) = (items.take n).tail := by
  have hl : ((items.drop 1).take (n - 1)).length = n - 1 := by
    simp only [List.length_take, List.length_drop]; omega
  simp only [moved]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.tail_take]

/-- The items of a full prefix: the front and the rest. -/
theorem take_eq_cons {items : List α} {n : Nat} (h1 : 1 ≤ n) (h : n ≤ items.length) :
    items.take n = items[0] :: (items.take n).tail := by
  cases items with
  | nil => simp at h
  | cons a as =>
    cases n with
    | zero => omega
    | succ n => simp

/-- **A write to the cell after the first `n`** appends the item. -/
theorem take_set_succ {items : List α} {n : Nat} (v : α) (h : n < items.length) :
    (items.set n v).take (n + 1) = items.take n ++ [v] := by
  induction items generalizing n with
  | nil => simp at h
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
      rw [ih (by simp only [List.length_cons] at h; omega)]

end QueueAdt
