import ZigLean.Mem.Lemmas

/-!
# Parent-pointer recovery in memory (L11)

The emitter lowers `struct_field_ptr` of a memory pointer to `p.add off` and
`field_parent_ptr` to `q.add (-off)`, with the same exported field offset (`Emit.lean`). A
local whose place escapes (for example through an array element, `ptr_elem_ptr`) is a stack
block, so nested fields and array elements inside structs use this lowering.

* `Ptr.parent_field`: recovering the parent of a field pointer gives the original container
  pointer, of any path (`Ptr.path`), including an array element (`Ptr.parent_elem_field`);
  repeated recovery peels nested paths (`Ptr.parent_path`).
* `parent_store_visible`/`field_store_visible`: a write through the recovered parent's
  field is visible through the original field pointer and conversely, because both are the
  same pointer (same block, same offset). Recovery therefore preserves aliasing.

This is a proof-only module importing `ZigLean.Mem.Lemmas`; it is not imported by `ZigLean`.
-/

namespace Zig

-- `Ptr.add_add`, `Ptr.add_zero` and `Ptr.add_block` are in `ZigLean.Mem.Lemmas`.
attribute [simp] Ptr.add_add

/-- Recovering the parent of a field pointer is the container pointer. -/
@[simp] theorem Ptr.parent_field (p : Ptr) (off : Int) : (p.add off).add (-off) = p := by
  cases p; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega

/-- Projecting the field of a recovered parent is the original field pointer. -/
@[simp] theorem Ptr.field_parent (q : Ptr) (off : Int) : (q.add (-off)).add off = q := by
  cases q; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega

/-- A path of field offsets from a container pointer (nested `struct_field_ptr`). -/
def Ptr.path (p : Ptr) (offs : List Int) : Ptr := offs.foldl Ptr.add p

@[simp] theorem Ptr.path_nil (p : Ptr) : p.path [] = p := rfl

theorem Ptr.path_append (p : Ptr) (xs ys : List Int) :
    p.path (xs ++ ys) = (p.path xs).path ys := by
  simp [Ptr.path, List.foldl_append]

/-- Removing the terminal field step of a nested path leaves the enclosing path: the memory
form of `localParentPath?`'s `path.pop`. -/
theorem Ptr.parent_path (p : Ptr) (offs : List Int) (off : Int) :
    (p.path (offs ++ [off])).add (-off) = p.path offs := by
  rw [Ptr.path_append]
  exact Ptr.parent_field _ off

/-- Peeling a whole nested path, innermost field first, gives the root container. -/
theorem Ptr.parents_path (p : Ptr) (offs : List Int) :
    (offs.reverse.map Neg.neg).foldl Ptr.add (p.path offs) = p := by
  induction offs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    have hp : p.path (x :: xs) = (p.add x).path xs := rfl
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil, hp, ih]
    exact Ptr.parent_field p x

/-- A field of item `i` of an array inside a struct: recovery gives the item pointer. -/
theorem Ptr.parent_elem_field (p : Ptr) (arrayOff : Int) (size : Nat) (i : BitVec 64)
    (off : Int) : (((p.add arrayOff).elem size i).add off).add (-off) =
      (p.add arrayOff).elem size i :=
  Ptr.parent_field _ off

/-- A write through the recovered parent's field is visible through the original field
pointer: both are one pointer, so the store's bytes are the load's bytes. `hnr`: the load
does not race (as in `load_store_same`). -/
theorem parent_store_visible {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {field : Ptr}
    {off : Int} {a a' : Nat} {b : BlockId} {blk : Block} {o : Nat} (v : α)
    (h : m.access field (Enc.size α) a = pure (b, blk, o))
    (h' : m.access field (Enc.size α) a' = pure (b, blk, o))
    (hK : blk.kind ≠ .constGlobal) (hnw : NoRace m b o (Enc.size α) .write)
    (hnr : NoRace ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v))
      b o (Enc.size α) .read) :
    (store a ((field.add (-off)).add off) v).run m =
        pure ((), (m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) ∧
      (load α a' field).run ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) =
        pure (v, ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)).recordAt
          b o (Enc.size α) .read) := by
  rw [Ptr.field_parent]
  exact ⟨store_run v h hK hnw,
    load_store_same v (access_recordAt.trans h) (access_recordAt.trans h') hnr⟩

/-- Conversely, a write through the original field pointer is visible through the recovered
parent's field. -/
theorem field_store_visible {α : Type} [Enc α] [LawfulEnc α] {m : Mem} {field : Ptr}
    {off : Int} {a a' : Nat} {b : BlockId} {blk : Block} {o : Nat} (v : α)
    (h : m.access field (Enc.size α) a = pure (b, blk, o))
    (h' : m.access field (Enc.size α) a' = pure (b, blk, o))
    (hK : blk.kind ≠ .constGlobal) (hnw : NoRace m b o (Enc.size α) .write)
    (hnr : NoRace ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v))
      b o (Enc.size α) .read) :
    (store a field v).run m =
        pure ((), (m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) ∧
      (load α a' ((field.add (-off)).add off)).run
        ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) =
      pure (v, ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)).recordAt
        b o (Enc.size α) .read) := by
  rw [Ptr.field_parent]
  exact ⟨store_run v h hK hnw,
    load_store_same v (access_recordAt.trans h) (access_recordAt.trans h') hnr⟩

end Zig
