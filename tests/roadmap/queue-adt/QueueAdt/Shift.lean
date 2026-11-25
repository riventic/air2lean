import QueueAdt.Gen
import QueueAdt.Moved
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Queue

/-!
# The shifting array of `queue.zig` meets the queue contract, with its step counts (P04, P06)

`Shift` is a header of a buffer slice of `u16` cells and the number `len` of items, which are
the first `len` cells, front first. `push` writes the cell `len`; `pop` reads the cell 0 and
moves the cells `1 … len - 1` one cell down in a loop, one body run per item (the moves and the
final test).

`shift q C xs` is the representation predicate. `shiftQueue` proves the contract
`Zig.Full.QueueImpl` (`ZigLean/Sep/Full/Queue.lean`) for the generated `Shift_push`,
`Shift_pop` and `Shift_count` with the declared step counts `pushSteps = 0`,
`popSteps C xs = xs.length` and `lenSteps = 0`: `pop_spec` takes `xs.length` credits and returns
as many receipts. Each operation is one `fsym` walk of the generated code; the module supplies
the invariant `shift`, the loop's invariant `popInv` (the cells after the moves so far,
`QueueAdt.moved`) and the updates at the returns. The loop of `pop` is walked by the counted loop
rule `FTotalTriple.loop_exact` (`pop_loop_exact`).
-/

namespace QueueAdt
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- The array at `q` has `C` cells and holds `xs`, front first: its header, and its buffer's
cells `items`, of which `xs` are the first `len`. -/
def shift (q : Ptr) (C : Nat) (xs : List (BitVec 16)) : FAssn :=
  FAssn.ex fun buf : Ptr => FAssn.ex fun cap : BitVec 64 => FAssn.ex fun len : BitVec 64 =>
    FAssn.ex fun items : List (BitVec 16) =>
      ⟪cap.toNat = C ∧ items.length = C ∧ len.toNat ≤ C ∧ xs.length = len.toNat ∧
        xs = items.take len.toNat⟫ ⋆
      (up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len } : Shift)) ⋆
        up (arr buf items))

attribute [local fsym_arith] List.length_take length_moved

namespace Shift

/-- The array after a `push`: the count `len' = len + 1` and `v` written to the cell `len`
(`take_set_succ`). -/
theorem pushed_upd {q buf : Ptr} {cap len len' : BitVec 64} {items : List (BitVec 16)}
    {xs : List (BitVec 16)} {j : Nat} (v : BitVec 16) (hi : items.length = cap.toNat)
    (hn : len.toNat < cap.toNat) (hn' : len'.toNat = len.toNat + 1) (hj : j = len.toNat)
    (hxs : xs = items.take len.toNat) :
    EUpd (up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len' } : Shift)) ⋆
        up (arr buf (items.set j v)))
      (QueueImpl.Pushed shift q cap.toNat xs v (.ok ())) :=
  EUpd.of_imp fun _ h => by
    subst hj hxs
    have hp := take_set_succ (items := items) (n := len.toNat) v (by omega)
    have hl : (items.take len.toNat).length = len.toNat := by
      rw [List.length_take]; omega
    refine sep_lift.mpr ⟨by omega, ⟨buf, cap, len', items.set len.toNat v, sep_lift.mpr
      ⟨⟨rfl, by rw [List.length_set]; exact hi, by omega, ?_, ?_⟩, h⟩⟩⟩
    · rw [List.length_append, hl, hn']; rfl
    · rw [hn', hp]

/-- The invariant of the loop of `pop` with `n` body runs left before the last one: the cells
`1 … i - 1` are moved (`moved items i`). -/
def popInv (q buf : Ptr) (cap len : BitVec 64) (items : List (BitVec 16)) (s : Shift_popLocals)
    (n : Nat) : FAssn :=
  ⟪n = len.toNat - s.i.toNat ∧ 1 ≤ s.i.toNat ∧ s.i.toNat ≤ len.toNat ∧ len.toNat ≤ cap.toNat ∧
    items.length = cap.toNat⟫ ⋆
  (up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len } : Shift)) ⋆
    up (arr buf (moved items s.i.toNat)))

/-- The loop's exit: every cell is moved. -/
def popPost (q buf : Ptr) (cap len : BitVec 64) (items : List (BitVec 16))
    (r : Shift_popExit × Shift_popLocals) : FAssn :=
  ⟪r.1 = .br21⟫ ⋆
  (up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len } : Shift)) ⋆
    up (arr buf (moved items len.toNat)))

/-- A move: the cell `i` written to the cell `i - 1` gives the cells of the next repetition
(`moved_step`). -/
theorem moved_upd {buf : Ptr} {items : List (BitVec 16)} {i i' j j' : Nat}
    (hl : i' < (moved items i).length) (h1 : 1 ≤ i) (h : i < items.length) (hi' : i' = i)
    (hj : j + 1 = i) (hj' : j' = i + 1) :
    EUpd (up (arr buf ((moved items i).set j (moved items i)[i'])))
      (up (arr buf (moved items j'))) :=
  EUpd.of_imp fun _ hp => by
    subst hi' hj'
    obtain rfl : j = i' - 1 := by omega
    rw [getElem_moved (by omega) (by omega) hl, moved_step h1 h] at hp
    exact hp

/-- The exit: the loop's counter is the count of items. -/
theorem moved_exit_upd {buf : Ptr} {items : List (BitVec 16)} {i n : Nat} (h : i = n) :
    EUpd (up (arr buf (moved items i))) (up (arr buf (moved items n))) :=
  EUpd.of_imp fun _ hp => h ▸ hp

/-- One run of the loop body: one credit, one receipt, one move or the exit. -/
theorem pop_step (q buf : Ptr) (cap len : BitVec 64) (items : List (BitVec 16))
    (s : Shift_popLocals) (n : Nat) :
    FTotalTriple (popInv q buf cap len items s n ⋆ credits 1) ((Shift_pop.loop22 q).run s)
      (fun r => floopExact Shift_pop.again22 (popInv q buf cap len items)
        (popPost q buf cap len items) n r ⋆ spent 1) := by
  unfold Shift_pop.loop22 popInv popPost
  fsym [moved_upd, moved_exit_upd]

/-- **The loop of `pop` with its exact step count**: from `i = 1` it runs its body `len` times
(`len - 1` moves and the final test), for `k = len` credits and as many receipts. -/
theorem pop_loop_exact {mb : Lean.Order.MonoBind (MM Shift_popLocals)} (q buf : Ptr)
    (cap len : BitVec 64) (items : List (BitVec 16)) (k : Nat) (s : Shift_popLocals)
    (hs : s.i = 1) (hi : items.length = cap.toNat) (hn : len.toNat ≤ cap.toNat)
    (h1 : 1 ≤ len.toNat) (hk : k = len.toNat) :
    FTotalTriple ((up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len } : Shift)) ⋆
        up (arr buf items)) ⋆ credits k)
      ((@Zig.loop (MM Shift_popLocals) _ _ mb _ (Shift_pop.loop22 q) Shift_pop.again22).run s)
      (fun r => (FAssn.ex fun t : Shift_popLocals => ⟪r = (.br21, t)⟫ ⋆
        (up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len } : Shift)) ⋆
          up (arr buf (moved items len.toNat)))) ⋆ spent k) := by
  have ek : len.toNat - 1 + 1 = k := by omega
  have hs1 : s.i.toNat = 1 := by simp [hs]
  refine (FTotalTriple.loop_exact (pop_step q buf cap len items) s (len.toNat - 1)).conseq
    (fun _ h => ?_) fun ⟨e, t⟩ _ h => ?_
  · rw [ek]
    refine sep_mono_left (fun _ h => sep_lift.mpr ⟨⟨by omega, by omega, by omega, hn, hi⟩, ?_⟩) h
    rw [hs1, moved_one]
    exact h
  · rw [ek] at h
    refine sep_mono_left (fun _ h => ?_) h
    obtain ⟨he, h⟩ := sep_lift.mp h
    exact ⟨t, sep_lift.mpr ⟨by simp only at he; rw [he], h⟩⟩

/-- The array after a `pop`: the count `len' = len - 1`, the cells after the moves, and the item
is the cell 0 (`take_moved`, `take_eq_cons`). -/
theorem popped_upd {q buf : Ptr} {cap len len' : BitVec 64} {items xs : List (BitVec 16)}
    {z : Nat} (hz' : z < items.length) (hz : z = 0) (hi : items.length = cap.toNat)
    (hn : len.toNat ≤ cap.toNat) (h1 : 1 ≤ len.toNat) (hl' : len'.toNat + 1 = len.toNat)
    (hxs : xs = items.take len.toNat) :
    EUpd (up (pts q 8 ({ items := { ptr := buf, len := cap }, len := len' } : Shift)) ⋆
        up (arr buf (moved items len.toNat)))
      (QueueImpl.Popped shift q cap.toNat xs (some items[z])) :=
  EUpd.of_imp fun _ h => by
    subst hz hxs
    have hc := take_eq_cons (items := items) (n := len.toNat) h1 (by omega)
    have ht := take_moved (items := items) (n := len.toNat) h1 (by omega)
    have hlm := length_moved (items := items) (i := len.toNat) h1 (by omega)
    have hlt : ((items.take len.toNat).tail).length = len'.toNat := by
      rw [List.length_tail, List.length_take]; omega
    refine ⟨(items.take len.toNat).tail, sep_lift.mpr ⟨⟨hc, by omega⟩,
      ⟨buf, cap, len', moved items len.toNat, sep_lift.mpr
        ⟨⟨rfl, by omega, by omega, hlt, ?_⟩, h⟩⟩⟩⟩
    rw [← ht, show len.toNat - 1 = len'.toNat by omega]

/-- **`push`** writes `v` to the cell after the items; a full array fails with `error.Full` and
is unchanged. -/
theorem push_spec (q : Ptr) (C : Nat) (xs : List (BitVec 16)) (v : BitVec 16) :
    FTotalTriple (shift q C xs) (Shift_push q v) (QueueImpl.Pushed shift q C xs v) := by
  unfold Shift_push
  fsym [pushed_upd v]
  -- the walk leaves the update's count premises over the header's words (`¬len = cap`,
  -- `len' = len + 1#64`): bit-vector arithmetic
  all_goals bv_omega

/-- **`pop`** takes the cell 0 and moves the other items one cell down, in exactly `xs.length`
steps (one loop-body run per item); an empty array gives `null` in none. -/
theorem pop_spec (q : Ptr) (C : Nat) (xs : List (BitVec 16)) :
    FTotalTriple (shift q C xs ⋆ credits xs.length) (Shift_pop q)
      (fun r => QueueImpl.Popped shift q C xs r ⋆ spent xs.length) := by
  unfold Shift_pop
  cases xs with
  | nil =>
    simp only [List.length_nil]
    exact FTotalTriple.credits_zero_iff.mpr (by fsym)
  | cons x xs =>
    simp only [List.length_cons]
    fsym [pop_loop_exact, popped_upd]
    -- the walk leaves the front cell's bound (`0 < items.length`) over the facts
    -- `(x :: xs).length = len` and `len ≤ cap = items.length`
    all_goals (simp only [List.length_cons] at *; bv_omega)

/-- **`count`** returns the number of items. -/
theorem count_spec (q : Ptr) (C : Nat) (xs : List (BitVec 16)) :
    FTotalTriple (shift q C xs) (Shift_count q)
      (fun r => ⟪r.toNat = xs.length ∧ xs.length ≤ C⟫ ⋆ shift q C xs) := by
  unfold Shift_count
  fsym

end Shift

/-- The generated shifting array is a bounded FIFO queue whose `pop` runs one step per item. -/
def shiftQueue : QueueImpl Ptr (BitVec 16) Shift_push Shift_pop Shift_count where
  Rep := shift
  pushSteps _ _ _ := 0
  popSteps _ xs := xs.length
  lenSteps _ _ := 0
  push_spec q C xs v := FTotalTriple.credits_zero_iff.mpr (Shift.push_spec q C xs v)
  pop_spec := Shift.pop_spec
  len_spec q C xs := FTotalTriple.credits_zero_iff.mpr (Shift.count_spec q C xs)

end QueueAdt
