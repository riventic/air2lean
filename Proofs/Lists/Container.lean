import Proofs.Lists.Sep
import Proofs.Lists.Append

/-!
# One sequence interface, two verified containers

`SeqImpl` is a reusable contract for a growable sequence of `u32` items. A client sees a handle
type `H`, a representation predicate `Rep h xs` ("the container at `h` holds the abstract sequence
`xs`") and one operation, `add`, whose contract `add_spec` mentions only the abstract sequence:
`add` gives `xs ++ [v]`, or `error.OutOfMemory` and the same `xs`. The memory layout behind `Rep`
is not part of the interface.

Two generated implementations from `examples/lists/lists.zig` satisfy it:

* `linkedSeq`: the singly linked list. `add` is the generated `push`, which puts a node in front;
  the representation stores the abstract sequence reversed (`list hd xs.reverse`), so `push`
  is an add at the abstract end. Proved from `push_spec` with the frame rule.
* `arraySeq`: `std.ArrayListUnmanaged(u32)`. `add` is the generated `append`. Proved from
  `append_run`. The representation requires an items pointer without a block when the capacity
  is zero, so the `ptrOk` premise of `append_run` follows from owned bytes; the `.empty` value
  whose zero-capacity pointer names a constant global is therefore not covered by `arraySeq`.

Clients that are parameterised by `I : SeqImpl` (`tests/roadmap/container-contracts/Clients.lean`)
are proved once and instantiate to both implementations unchanged.
-/

namespace Lists
open Zig Assn

/-- The abstract outcome of an `add` of `v` to the sequence `xs` held at `h`. -/
def Added {H : Type} (Rep : H → List (BitVec 32) → Assn) (h : H) (xs : List (BitVec 32))
    (v : BitVec 32) : Except ErrName H → Assn
  | .ok h' => Rep h' (xs ++ [v])
  | .error e => ⌜e = "OutOfMemory"⌝ ∗ Rep h xs

/-- A verified container of a sequence of `u32` items with an `add` at the end. -/
structure SeqImpl where
  /-- The handle a client keeps. -/
  H : Type
  /-- The container at `h` holds the abstract sequence `xs`. -/
  Rep : H → List (BitVec 32) → Assn
  /-- Add an item at the end; on success the (possibly new) handle. -/
  add : Allocator → H → BitVec 32 → MemM (Except ErrName H)
  /-- The representation is preserved and the sequence grows by `v`, or nothing changes. -/
  add_spec : ∀ a h xs v, Triple (Rep h xs) (add a h v) (Added Rep h xs v)

/-! ## The linked list -/

/-- The linked list at `hd` holds `xs`, last item first. -/
def LList (hd : Option Ptr) (xs : List (BitVec 32)) : Assn := list hd xs.reverse

/-- The generated `push`, with the new head as the handle. -/
def linkedAdd (a : Allocator) (hd : Option Ptr) (v : BitVec 32) :
    MemM (Except ErrName (Option Ptr)) := do
  match ← push a hd v with
  | .ok p => pure (.ok (some p))
  | .error e => pure (.error e)

theorem linkedAdd_spec (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32)) (v : BitVec 32) :
    Triple (LList hd xs) (linkedAdd a hd v) (Added LList hd xs v) := by
  have hpush := Triple.frame (R := LList hd xs) (push_spec a hd v)
  refine Triple.bind (Triple.conseq hpush
    (fun h hp =>
      ⟨Heap.empty, h, (Heap.disjoint_empty h).symm, (Heap.empty_union h).symm, rfl, hp⟩)
    (fun _ _ hq => hq)) ?_
  intro r
  cases r with
  | ok p =>
    refine Triple.conseq (Triple.ret (Q := Added LList hd xs v) (.ok (some p))) ?_
      (fun _ _ hq => hq)
    intro h hp
    show list (some p) (xs ++ [v]).reverse h
    rw [show (xs ++ [v]).reverse = v :: xs.reverse by simp]
    exact ⟨p, hd, rfl, hp⟩
  | error e => exact Triple.ret (Q := Added LList hd xs v) (.error e)

/-- The linked list as a `SeqImpl`. -/
def linkedSeq : SeqImpl where
  H := Option Ptr
  Rep := LList
  add := linkedAdd
  add_spec := linkedAdd_spec

/-! ## `std.ArrayListUnmanaged(u32)` -/

/-- The list header at `p` holds `xs`; a zero capacity has an items pointer without a block. -/
def AList (p : Ptr) (xs : List (BitVec 32)) : Assn := fun h =>
  ∃ ptr cap, (cap.toNat = 0 → ptr.block = none) ∧ alist p ptr cap xs h

/-- The generated `append`; the handle is the header pointer. -/
def arrayAdd (a : Allocator) (p : Ptr) (v : BitVec 32) : MemM (Except ErrName Ptr) := do
  match ← array_list_Aligned_u32_null_append p a v with
  | .ok _ => pure (.ok p)
  | .error e => pure (.error e)

/-- An owned buffer of a positive capacity is in a block of the memory. -/
theorem ptrOk_of_buf {m : Mem} {h : Heap} {ptr : Ptr} {cap : Nat} {xs : List (BitVec 32)}
    (hb : buf ptr cap xs h) (hz : cap = 0 → ptr.block = none)
    (hsub : ∀ l c, h l = some c → m.heap l = some c) : ptrOk m ptr := by
  intro b hpb
  by_cases hc : cap = 0
  · rw [hz hc] at hpb; cases hpb
  · simp only [buf, hc, ↓reduceIte] at hb
    obtain ⟨h0, A, bs, -, hsz, -, b', hpb', -, hcell⟩ := hb
    rw [hpb] at hpb'; cases hpb'
    obtain ⟨c, hl⟩ : ∃ c, h (b, 0) = some c := by
      rw [hcell (b, 0)]
      split
      · exact ⟨_, rfl⟩
      · rename_i hn; exact absurd ⟨rfl, by simp [h0], by simp [h0]; omega⟩ hn
    obtain ⟨blk, hblk, -⟩ := Mem.heap_some (hsub _ _ hl)
    exact (Array.getElem?_eq_some_iff.mp hblk).1

theorem arrayAdd_spec (a : Allocator) (p : Ptr) (xs : List (BitVec 32)) (v : BitVec 32) :
    Triple (AList p xs) (arrayAdd a p v) (Added AList p xs v) := by
  apply Triple.of_run
  intro m hP hF hd hm ⟨ptr, cap, hz, hl⟩ hst
  have hok : ptrOk m ptr := by
    obtain ⟨-, -, hH, hB, dHB, rfl, -, hbf⟩ := hl
    refine ptrOk_of_buf hbf hz (fun l c hc => ?_)
    rw [hm, Heap.union_comm dHB]
    simp [hc]
  obtain ⟨r, m', hr, hst', hL', hd', hm', happ⟩ := append_run a v hl hm hd hst hok
  cases r with
  | ok u =>
    obtain ⟨ptr', cap', hl', -⟩ := happ
    refine ⟨.ok p, m', hL', by simp [arrayAdd, hr], hd', hm',
      ⟨ptr', cap', fun h0 => ?_, hl'⟩, hst'⟩
    have := hl'.1
    simp only [List.length_append, List.length_singleton] at this
    omega
  | error e =>
    obtain ⟨rfl, hl', -⟩ := happ
    exact ⟨.error "OutOfMemory", m', hL', by simp [arrayAdd, hr], hd', hm',
      ⟨Heap.empty, hL', (Heap.disjoint_empty hL').symm, (Heap.empty_union hL').symm,
        ⟨rfl, rfl⟩,
        ptr, cap, hz, hl'⟩, hst'⟩

/-- `std.ArrayListUnmanaged(u32)` as a `SeqImpl`. -/
def arraySeq : SeqImpl where
  H := Ptr
  Rep := AList
  add := arrayAdd
  add_spec := arrayAdd_spec

end Lists
