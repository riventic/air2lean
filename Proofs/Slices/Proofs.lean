import Proofs.Slices.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Simp

/-!
# Proofs about `examples/slices/slices.zig`

The constant table of `factorial`, the names of `@tagName` and `@errorName` in their global
blocks, pointer arithmetic, and the safety checks of slicing and `@memcpy`.
-/

open Slices Zig

/-- `table[n]`: the table value for `n < 8`. -/
theorem factorial_spec (n : BitVec 64) (h : n.toNat < 8) :
    factorial n = pure ((#v[1, 1, 2, 6, 24, 120, 720, 5040] : Vector (BitVec 16) 8)[n.toNat]) := by
  simp [factorial, zig_unfold, Zig.vindex, h]

/-- `table[n]` for `n >= 8` is out of bounds. -/
theorem factorial_oob (n : BitVec 64) (h : 8 ≤ n.toNat) : factorial n = throw .outOfBounds := by
  have hlt : ¬ n.toNat < 8 := by omega
  simp [factorial, zig_unfold, hlt]

/-- `@tagName`: a slice into the global block of the name. The memory does not change. -/
theorem colorName_red (m : Mem) : (colorName .red).run m = pure (⟨⟨some 2, 0⟩, 3⟩, m) := by
  simp [colorName, zig_unfold, Color.isNamed, Color.tagName]

theorem colorName_blue (m : Mem) : (colorName .blue).run m = pure (⟨⟨some 4, 0⟩, 4⟩, m) := by
  simp [colorName, zig_unfold, Color.isNamed, Color.tagName]

/-- The global block of the name `red`: its bytes and the 0 sentinel. -/
theorem mem0_red : mem0.blocks[2]?.map (·.bytes) = some #[.int 114, .int 101, .int 100, .int 0] := by
  simp [mem0, Mem.ofGlobals, Mem.addGlobal, Enc.encode, intBytes, padTo, intSize, intAlign, alignUp]

/-- `@errorName`: `error.Empty` for `0`, else `error.TooLong`. -/
theorem failName_zero (m : Mem) : (failName 0).run m = pure (⟨⟨some 5, 0⟩, 5⟩, m) := by
  simp [failName, zig_unfold, errorNameOf]

theorem failName_other (n : BitVec 8) (h : n ≠ 0) (m : Mem) :
    (failName n).run m = pure (⟨⟨some 6, 0⟩, 7⟩, m) := by
  have h' : ¬ n = 0#8 := h
  simp [failName, zig_unfold, errorNameOf, h']

/-- `(p + 1)[0]` reads the `u32` 4 bytes after `p`. -/
theorem second_spec (p : Ptr) (m : Mem) (x : BitVec 32)
    (hx : (load (BitVec 32) 4 (p.add 4)).run m = pure (x, m)) :
    (second p).run m = pure (x, m) := by
  have hp : (p.elem 4 1#64).elem 4 0#64 = p.add 4 := by simp [Ptr.elem, Ptr.add]
  simp only [StateT.run] at hx
  simp [second, zig_unfold, hp, hx]

/-- `@memset` of a whole slice. -/
theorem fill_spec (s : Slice) (v : BitVec 8) (m m' : Mem)
    (h : (memset 1 s.ptr s.len (some v)).run m = pure ((), m')) :
    (fill s v).run m = pure ((), m') := by
  simp only [StateT.run] at h
  simp [fill, zig_unfold, h]

theorem lenOr_none (m : Mem) : (lenOr none).run m = pure (0, m) := by
  simp [lenOr, zig_unfold]

theorem lenOr_some (s : Slice) (m : Mem) : (lenOr (some s)).run m = pure (s.len, m) := by
  simp [lenOr, zig_unfold, optPayload]

/-- `s[a..b :0]` with `b < a` panics (`startGreaterThanEnd`). -/
theorem subZ_start (s : Slice) (a b : BitVec 64) (h : b.toNat < a.toNat) (m : Mem) :
    (subZ s a b).run m = throw .outOfBounds := by
  have hle : Zig.le false a b = false := by simp [Zig.le, BitVec.ule]; omega
  simp [subZ, zig_unfold, hle]

/-- `@memcpy` of two slices of different lengths panics (`copyLenMismatch`). -/
theorem copy_len (d s : Slice) (h : d.len ≠ s.len) (m : Mem) :
    (copy d s).run m = throw .panic := by
  simp [copy, zig_unfold, h]

/-- An array with a sentinel is `N + 1` items in memory: the bytes of a `Tag` hold the sentinel
at byte 3, before the field `n`. -/
theorem tag_bytes (a : BitVec 8) :
    Enc.encode ({ name := #v[a, 2, 3, 0], n := 7 } : Tag) =
      #[.int a, .int 2, .int 3, .int 0, .int 7] := by
  simp [Enc.encode, Enc.fields, intBytes, padTo, intSize, intAlign, alignUp, writeBytes]
  apply BitVec.eq_of_toNat_eq; simp; omega
