/-!
# The items of a ring buffer, as a list (pure; no memory)

`window items head n` is the abstract sequence that a ring buffer with the cells `items` holds:
the `n` items from the index `head`, continuing at index 0 after the last cell. The lemmas are
the three facts the queue operations of `tests/roadmap/queue-adt/queue.zig` need, each with its
index arithmetic as linear hypotheses over natural numbers:

* `window_nil`: no items;
* `window_push`: a write to the cell after the last item adds the item at the back;
* `window_cons`: the front item is the cell at `head`, and the rest is the window from the next
  index, which is 0 after the last cell.
-/

namespace QueueAdt

variable {α : Type}

/-- The `n` items of the ring `items` from the index `head`, around the end. -/
def window (items : List α) (head n : Nat) : List α :=
  ((items ++ items).drop head).take n

theorem getElem?_window (items : List α) (head n j : Nat) :
    (window items head n)[j]? =
      if j < n then
        if head + j < items.length then items[head + j]? else items[head + j - items.length]?
      else none := by
  unfold window
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_append]

theorem length_window {items : List α} {head n : Nat} (hh : head ≤ items.length)
    (hn : n ≤ items.length) : (window items head n).length = n := by
  unfold window
  rw [List.length_take, List.length_drop, List.length_append]
  omega

/-- A window of no items is empty. -/
theorem window_nil {items : List α} {head n : Nat} (hn : n = 0) : window items head n = [] := by
  subst hn
  simp [window]

/-- **Push**: the cell `i` after the last of `n < items.length` items from `head` (`head + n`, or
`head + n - items.length` around the end) takes the new back item. -/
theorem window_push {items : List α} {head n n' i : Nat} (v : α) (hh : head < items.length)
    (hn : n < items.length) (hn' : n' = n + 1) (hi1 : head + n < items.length → i = head + n)
    (hi2 : items.length ≤ head + n → i + items.length = head + n) :
    window items head n ++ [v] = window (items.set i v) head n' := by
  subst hn'
  have hlen : (window items head n).length = n := length_window (by omega) (by omega)
  have hi : i < items.length := by omega
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_append, hlen, getElem?_window, getElem?_window, List.length_set]
  by_cases hj : j < n
  · have h1 : j < n + 1 := by omega
    by_cases hw : head + j < items.length
    · have hne : ¬ i = head + j := by omega
      simp [hj, h1, hw, hne]
    · have hne : ¬ i = head + j - items.length := by omega
      simp [hj, h1, hw, hne]
  · by_cases hjn : j = n
    · subst hjn
      have h1 : j < j + 1 := by omega
      by_cases hw : head + j < items.length
      · have he : i = head + j := hi1 hw
        subst he
        simp [h1, hw]
      · have he : head + j - items.length = i := by omega
        simp [h1, hw, he, hi]
    · have h1 : ¬ j < n + 1 := by omega
      have hnone : [v][j - n]? = none := List.getElem?_eq_none (by show 1 ≤ j - n; omega)
      simp [hj, h1, hnone]

/-- **Pop**: the front of `n > 0` items is the cell at `head`; the rest starts at the next index
`head'`, which is 0 after the last cell. -/
theorem window_cons {items : List α} {head head' n n' : Nat} (hh : head < items.length)
    (hn : n = n' + 1) (hle : n ≤ items.length) (h1 : head + 1 = items.length → head' = 0)
    (h2 : head + 1 < items.length → head' = head + 1) :
    window items head n = items[head] :: window items head' n' := by
  subst hn
  apply List.ext_getElem?
  intro j
  cases j with
  | zero =>
    have h0 : (0 : Nat) < n' + 1 := by omega
    simp [getElem?_window, h0, hh]
  | succ k =>
    rw [List.getElem?_cons_succ, getElem?_window, getElem?_window]
    by_cases hk : k < n'
    · have hk1 : k + 1 < n' + 1 := by omega
      by_cases hc : head + 1 = items.length
      · have hw : ¬ head + (k + 1) < items.length := by omega
        have he : head + (k + 1) - items.length = k := by omega
        have hk' : k < items.length := by omega
        have h0 := h1 hc
        subst h0
        simp [hk, hk1, hw, he, hk']
      · have h0 := h2 (by omega)
        subst h0
        have he : head + (k + 1) = head + 1 + k := by omega
        simp [hk, hk1, he]
    · have hk1 : ¬ k + 1 < n' + 1 := by omega
      simp [hk, hk1]

/-- The front item of a nonempty window. -/
theorem window_head? {items : List α} {head n : Nat} (hh : head < items.length) (hn : 0 < n)
    (hle : n ≤ items.length) : (window items head n).head? = some items[head] := by
  rw [window_cons (head' := if head + 1 = items.length then 0 else head + 1) (n' := n - 1) hh
    (by omega) hle (fun h => by simp [h]) (fun h => by simp [Nat.ne_of_lt h])]
  rfl

end QueueAdt
