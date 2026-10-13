import Proofs.Lists.Append

/-!
# One sequence interface, two verified containers, every allocator

`SeqImpl` is a reusable contract for a growable sequence of `u32` items. A client sees a handle
type `H`, a representation predicate `Rep I h xs` ("the container at `h` holds the abstract
sequence `xs`, in grants of the allocator with invariant `I`") and one operation, `add`, whose
contract `add_spec` mentions only the abstract sequence: `add` gives `xs ++ [v]`, or
`error.OutOfMemory` and the same `xs`. The memory layout behind `Rep` is not part of the
interface. `add` takes a `std.mem.Allocator`; `add_spec` holds for every allocator whose
environment entries meet the allocator contract `CAllocSpec` (`Proofs/Lists/Alloc.lean`), with
the room `Room I xs` that the container's request needs of the contract (`FAllocInv.fits`).

Two generated implementations from `examples/lists/lists.zig` (`Proofs/Lists/Open.lean`) satisfy
it:

* `linkedSeq`: the singly linked list. `add` is the generated `push`, which puts a node in front;
  the representation stores the abstract sequence reversed (`LList I hd xs`), so `push` is an
  add at the abstract end. Proved from `Lists.Alloc.push_spec` with the frame rule.
* `arraySeq`: `std.ArrayListUnmanaged(u32)`. `add` is the generated `append`; proved from
  `Lists.Append.append_spec`. The representation `alist I p xs` covers every list, `.empty`
  included.

Clients that are parameterised by `S : SeqImpl` (`tests/roadmap/container-contracts/Clients.lean`)
are proved once and instantiate to both implementations unchanged. These are `CTriple`s
(partial correctness, no panic, one thread), as the allocator contract is.
-/

namespace Lists.Container

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc Lists.Append

/-- The abstract outcome of an `add` of `v` to the sequence `xs` held at `h`. -/
def Added {H : Type} (Rep : H → List (BitVec 32) → FAssn) (h : H) (xs : List (BitVec 32))
    (v : BitVec 32) : Except ErrName H → FAssn
  | .ok h' => Rep h' (xs ++ [v])
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ Rep h xs

variable [Ext]

/-- A verified container of a sequence of `u32` items with an `add` at the end, for every
allocator that meets the allocator contract. -/
structure SeqImpl where
  /-- The handle a client keeps. -/
  H : Type
  /-- The container at `h` holds the abstract sequence `xs`, in grants of `I`'s allocator. -/
  Rep : FAllocInv → H → List (BitVec 32) → FAssn
  /-- What an add to `xs` needs of the allocator's contract (`FAllocInv.fits`). -/
  Room : FAllocInv → List (BitVec 32) → Prop
  /-- Add an item at the end; on success the (possibly new) handle. -/
  add : mem_Allocator → H → BitVec 32 → ConcM Tgt (Except ErrName H)
  /-- The representation is preserved and the sequence grows by `v`, or nothing changes, for
  every allocator that meets the contract. -/
  add_spec : ∀ (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (h : H)
    (xs : List (BitVec 32)) (v : BitVec 32), Room I xs →
    CAllocSpec (CVTable.env (Alloc.env e) fns) ctx I →
    CTriple (I.own ⋆ (Rep I h xs ⋆ vtR vtp fns.toList)) (add ⟨ctx, vtp⟩ h v)
      (fun r => I.own ⋆ (Added (Rep I) h xs v r ⋆ vtR vtp fns.toList))

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)

/-! ## The linked list -/

omit [Ext] in
/-- The linked list at `hd` holds `xs`, last item first. -/
def LList (I : FAllocInv) (hd : Option Ptr) (xs : List (BitVec 32)) : FAssn :=
  Alloc.list I hd xs.reverse

/-- The generated `push`, with the new head as the handle. -/
def linkedAdd (a : mem_Allocator) (hd : Option Ptr) (v : BitVec 32) :
    ConcM Tgt (Except ErrName (Option Ptr)) := do
  match ← push a hd v with
  | .ok p => pure (.ok (some p))
  | .error e => pure (.error e)

theorem linkedAdd_spec (hd : Option Ptr) (xs : List (BitVec 32)) (v : BitVec 32)
    (hfit : I.fits (16 : BitVec 64).toNat 3) (h : CAllocSpec (CVTable.env (Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (LList I hd xs ⋆ vtR vtp fns.toList)) (linkedAdd ⟨ctx, vtp⟩ hd v)
      (fun r => I.own ⋆ (Added (LList I) hd xs v r ⋆ vtR vtp fns.toList)) := by
  refine CTriple.bind ((CTriple.frame (R := LList I hd xs) (push_spec ctx vtp fns I e hd v hfit h)).pre
    fun _ h => ac_cast h (by ac_rfl)) fun r => ?_
  cases r with
  | ok p =>
    refine CTriple.ret' _ fun _ h => ?_
    have h' : (I.own ⋆ ((node I p v hd ⋆ Alloc.list I hd xs.reverse) ⋆ vtR vtp fns.toList)) _ :=
      ac_cast h (by simp only [pushed, LList]; ac_rfl)
    refine sep_mono_right (fun _ h => sep_mono_left (fun _ h => ?_) h) h'
    show Alloc.list I (some p) (xs ++ [v]).reverse _
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    exact ⟨p, hd, sep_lift.mpr ⟨rfl, h⟩⟩
  | error e =>
    refine CTriple.ret' _ fun _ h => ?_
    simp only [pushed] at h
    exact ac_cast h (by simp only [Added]; ac_rfl)

/-- The linked list as a `SeqImpl`. -/
def linkedSeq : SeqImpl where
  H := Option Ptr
  Rep := LList
  Room I _ := I.fits (16 : BitVec 64).toNat 3
  add := linkedAdd
  add_spec ctx vtp fns I e hd xs v hfit h := linkedAdd_spec ctx vtp fns I e hd xs v hfit h

/-! ## `std.ArrayListUnmanaged(u32)` -/

/-- The generated `append`; the handle is the header pointer. -/
def arrayAdd (a : mem_Allocator) (p : Ptr) (v : BitVec 32) : ConcM Tgt (Except ErrName Ptr) := do
  match ← array_list_Aligned_u32_null_append p a v with
  | .ok _ => pure (.ok p)
  | .error e => pure (.error e)

theorem arrayAdd_spec (p : Ptr) (xs : List (BitVec 32)) (v : BitVec 32)
    (hfit : I.fits (4 * growTo (xs.length + 1)) 2)
    (h : CAllocSpec (CVTable.env (Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (alist I p xs ⋆ vtR vtp fns.toList)) (arrayAdd ⟨ctx, vtp⟩ p v)
      (fun r => I.own ⋆ (Added (alist I) p xs v r ⋆ vtR vtp fns.toList)) :=
  CTriple.bind (append_spec ctx vtp fns I e p xs v hfit h) fun r => by
    cases r <;> exact CTriple.ret' _ fun _ h => h

/-- `std.ArrayListUnmanaged(u32)` as a `SeqImpl`. -/
def arraySeq : SeqImpl where
  H := Ptr
  Rep := alist
  Room I xs := I.fits (4 * growTo (xs.length + 1)) 2
  add := arrayAdd
  add_spec ctx vtp fns I e p xs v hfit h := arrayAdd_spec ctx vtp fns I e p xs v hfit h

end Lists.Container
