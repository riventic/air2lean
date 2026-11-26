import ZigLean.EndianLemmas

/-!
# Element-stride vectors in memory

The backends that do not bit-pack a vector's lanes (`ZigLean/Vec.lean`'s `Vec.packedEnc` is the
LLVM backend's layout) keep each integer or float lane at its ABI stride, as the array `[n]T`
does, and pad the vector to its alignment (Zig's `Type.abiSize`/`abiAlignment`):

* `stage2_x86_64`: the alignment is 16 at the baseline CPU (`x86VecAlign`; 32 or 64 with AVX or
  AVX-512, which `x86VecAlign` does not cover) and the size is the lanes' `n * @sizeOf(T)` bytes
  rounded up to it (`x86VecSize`). A `bool` vector is bit-packed there too: `⌈n / 8⌉` bytes at a
  power-of-two alignment up to 64 lanes (`x86BoolVecAlign`, `x86BoolVecSize`; the LLVM layout
  `boolVecLayout`, `x86BoolVec_eq`), and 16-byte aligned above;
* `stage2_c`: the array's size and alignment.

`Vec.stridedEnc n size align` is that encoding for any lane encoding `Enc α`, any size and any
alignment: the image of the array of the lanes, then undefined padding bytes.

* `Vec.stridedEnc_size_encode`, `Vec.stridedEnc_decode_encode`, `Vec.stridedEnc_lawful`: a vector
  has an image of exactly its size, and reads back as stored whenever its lanes do
  (`ZigLean/ReprCast.lean`'s `vector_decode_encode_of`; a float vector without a NaN lane:
  `Vec.stridedEnc_float_decode_encode`);
* `Vec.stridedEnc_cell`: the bytes at `[i * s, (i + 1) * s)` are lane `i`'s (`s` the lane size),
  so a load of the lane type at that offset reads lane `i`;
* `Vec.stridedEnc_set`: a store of the lane's bytes at offset `i * s` leaves the image of
  `v.set i x`: it replaces lane `i` and no other byte (`Vec.set_lane_ne`).

Evidence: `tests/roadmap/vector-layouts/probe_strided.zig` (the stock compilers of Zig
0.14.1–0.17.1, `-fno-llvm`, x86_64-linux) against `ModelStrided.lean`
(`docs/vector-proofs.md` §Element-stride layout). The translator does not use this encoding yet:
`Check.lean`'s `modelLayout` rejects the vectors whose layout differs from the LLVM one.
-/

namespace Zig

/-! ## Layout -/

/-- The ABI alignment of `@Vector(n, T)` with the self-hosted x86_64 backend at the baseline
CPU (no AVX), `T` an integer or float of ABI size `s`. -/
def x86VecAlign (n s : Nat) : Nat := if n = 0 ∨ s = 0 then 1 else 16

/-- The ABI size of `@Vector(n, T)` with the self-hosted x86_64 backend at the baseline CPU:
the lanes at their ABI stride `s`, rounded up to the alignment. -/
def x86VecSize (n s : Nat) : Nat := alignUp (n * s) (x86VecAlign n s)

/-- The ABI alignment of `@Vector(n, bool)` with the self-hosted x86_64 backend at the baseline
CPU (no AVX2). -/
def x86BoolVecAlign (n : Nat) : Nat :=
  if n = 0 then 1 else if n > 64 then 16 else ceilPow2 ((n + 7) / 8)

/-- The ABI size of `@Vector(n, bool)` with the self-hosted x86_64 backend at the baseline CPU:
one bit a lane. -/
def x86BoolVecSize (n : Nat) : Nat := alignUp ((n + 7) / 8) (x86BoolVecAlign n)

theorem le_x86VecSize (n s : Nat) : n * s ≤ x86VecSize n s := le_alignUp _ _

/-- Up to 64 lanes, a `bool` vector has the LLVM backend's size and alignment. -/
theorem x86BoolVec_eq {n : Nat} (h0 : 0 < n) (h : n ≤ 64) :
    x86BoolVecSize n = boolVecLayout n ∧ x86BoolVecAlign n = boolVecLayout n := by
  have key : ∀ k < 65, 0 < k →
      x86BoolVecSize k = boolVecLayout k ∧ x86BoolVecAlign k = boolVecLayout k := by decide
  exact key n (by omega) h0

/-! ## Encoding -/

/-- A vector whose lanes sit at their ABI stride: the image of the array `[n]T` of its lanes
(`Enc (Vector α n)`), then undefined padding bytes up to `size`. A decode reads the array. -/
@[reducible] def Vec.stridedEnc {α : Type} [Enc α] (n size align : Nat) : Enc (Vec α n) where
  size := size
  align := align
  encode v := padTo size (Enc.encode v.lanes)
  decode bs := do
    let lanes ← (Enc.decode (bs.extract 0 (n * Enc.size α)) : Result (Vector α n))
    pure ⟨lanes⟩

private theorem extract_padTo_size (size : Nat) (a : Array Byte) :
    (padTo size a).extract 0 a.size = a := by
  simp [padTo]

section
variable {α : Type} [Enc α] {n : Nat}

/-- The image has exactly `size` bytes when the lanes fit. -/
theorem Vec.stridedEnc_size_encode (size align : Nat) (v : Vec α n)
    (hs : ∀ x ∈ v.lanes.toArray, (Enc.encode x).size = Enc.size α)
    (hfit : n * Enc.size α ≤ size) :
    ((Vec.stridedEnc n size align).encode v).size = size := by
  show (padTo size (Enc.encode v.lanes)).size = size
  have := vector_size_encode_of v.lanes hs
  simp only [padTo, Array.size_append, Array.size_replicate]
  omega

/-- A vector reads back as stored when each of its lanes does. -/
theorem Vec.stridedEnc_decode_encode (size align : Nat) (v : Vec α n)
    (hs : ∀ x ∈ v.lanes.toArray, (Enc.encode x).size = Enc.size α)
    (hd : ∀ x ∈ v.lanes.toArray, (Enc.decode (Enc.encode x) : Result α) = pure x) :
    (Vec.stridedEnc n size align).decode ((Vec.stridedEnc n size align).encode v) = pure v := by
  show (do
    let lanes ← (Enc.decode ((padTo size (Enc.encode v.lanes)).extract 0 (n * Enc.size α)) :
      Result (Vector α n))
    pure (⟨lanes⟩ : Vec α n)) = pure v
  rw [← vector_size_encode_of v.lanes hs, extract_padTo_size, vector_decode_encode_of v.lanes hs hd]
  rfl

/-- The element-stride encoding of lawful lanes is lawful when the lanes fit. -/
theorem Vec.stridedEnc_lawful [LawfulEnc α] (n size align : Nat) (hfit : n * Enc.size α ≤ size) :
    @LawfulEnc (Vec α n) (Vec.stridedEnc n size align) :=
  letI := Vec.stridedEnc (α := α) n size align
  ⟨fun v => Vec.stridedEnc_size_encode size align v (fun x _ => LawfulEnc.size_encode x) hfit,
    fun v => Vec.stridedEnc_decode_encode size align v (fun x _ => LawfulEnc.size_encode x)
      fun x _ => LawfulEnc.decode_encode x⟩

/-- Lane `i`'s cell of the image, the bytes at `[i * s, (i + 1) * s)`, is the lane's image. -/
theorem Vec.stridedEnc_cell (size align : Nat) (v : Vec α n)
    (hs : ∀ x ∈ v.lanes.toArray, (Enc.encode x).size = Enc.size α) (i : Nat) (hi : i < n) :
    ((Vec.stridedEnc n size align).encode v).extract (i * Enc.size α) ((i + 1) * Enc.size α) =
      Enc.encode v.lanes[i] := by
  show (padTo size (Enc.encode v.lanes)).extract _ _ = _
  have hsize := vector_size_encode_of v.lanes hs
  have hle : (i + 1) * Enc.size α ≤ (Enc.encode v.lanes).size := by
    rw [hsize]; exact Nat.mul_le_mul_right _ hi
  have hchunk := flatten_chunk (s := Enc.size α) (v.lanes.toArray.map Enc.encode) i (by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Array.mem_map.1 ha
    exact hs x hx) (by simpa using hi)
  have hpre : (padTo size (Enc.encode v.lanes)).extract (i * Enc.size α) ((i + 1) * Enc.size α) =
      (Enc.encode v.lanes).extract (i * Enc.size α) ((i + 1) * Enc.size α) := by
    apply Array.ext'
    simp only [padTo, Array.toList_extract, Array.toList_append, List.extract_eq_take_drop]
    rw [List.drop_append_of_le_length (by simp; rw [Nat.succ_mul] at hle; omega),
      List.take_append_of_le_length (by simp; rw [Nat.succ_mul] at hle ⊢; omega)]
  rw [hpre]
  show (v.lanes.toArray.map Enc.encode).flatten.extract _ _ = _
  simpa using hchunk

end

private theorem flatten_set {s : Nat} :
    ∀ (l : List (List Byte)) (i : Nat) (a : List Byte), (∀ b ∈ l, b.length = s) → i < l.length →
      (l.set i a).flatten = l.flatten.take (i * s) ++ a ++ l.flatten.drop ((i + 1) * s)
  | [], _, _, _, hi => by simp at hi
  | b :: t, 0, a, h, _ => by
    have hb := h b (by simp)
    simp [List.flatten_cons, ← hb]
  | b :: t, i + 1, a, h, hi => by
    have hb := h b (by simp)
    have ih := flatten_set t i a (fun c hc => h c (by simp [hc])) (by simpa using hi)
    have ht : List.take ((i + 1) * s) (b ++ t.flatten) = b ++ List.take (i * s) t.flatten := by
      rw [show (i + 1) * s = b.length + i * s by rw [hb, Nat.succ_mul]; omega,
        List.take_length_add_append]
    have hd : List.drop ((i + 1 + 1) * s) (b ++ t.flatten) = List.drop ((i + 1) * s) t.flatten := by
      rw [show (i + 1 + 1) * s = b.length + (i + 1) * s by rw [hb, Nat.succ_mul (i + 1)]; omega,
        List.drop_length_add_append]
    simp only [List.set_cons_succ, List.flatten_cons, ih, ht, hd, List.append_assoc]

/-- A store of lane `i`'s bytes at its cell (offset `i * s`) leaves the image of `v.set i x`:
the store replaces lane `i` and no other byte. -/
theorem Vec.stridedEnc_set {α : Type} [Enc α] {n : Nat} (size align : Nat) (v : Vec α n)
    (i : Fin n) (x : α) (hs : ∀ y ∈ v.lanes.toArray, (Enc.encode y).size = Enc.size α)
    (hx : (Enc.encode x).size = Enc.size α) :
    (Vec.stridedEnc n size align).encode (v.set i x) =
      writeBytes ((Vec.stridedEnc n size align).encode v) (i * Enc.size α) (Enc.encode x) := by
  have hs' : ∀ y ∈ (v.set i x).lanes.toArray, (Enc.encode y).size = Enc.size α := by
    intro y hy
    simp only [Vec.set, Vector.toArray_set] at hy
    rcases Array.mem_or_eq_of_mem_set hy with h | rfl
    · exact hs y h
    · exact hx
  have hsize := vector_size_encode_of v.lanes hs
  have hsize' := vector_size_encode_of (v.set i x).lanes hs'
  have hi : (i + 1) * Enc.size α ≤ n * Enc.size α := Nat.mul_le_mul_right _ i.isLt
  have hlists : ∀ a ∈ (v.lanes.toArray.map Enc.encode).toList.map Array.toList,
      a.length = Enc.size α := by
    intro a ha
    simp only [Array.toList_map, List.map_map, List.mem_map, Array.mem_toList_iff] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    simpa using hs y hy
  have hflat : (Enc.encode (v.set i x).lanes : Array Byte).toList =
      (Enc.encode v.lanes : Array Byte).toList.take (i * Enc.size α) ++ (Enc.encode x).toList ++
        (Enc.encode v.lanes : Array Byte).toList.drop ((i + 1) * Enc.size α) := by
    show (((v.set i x).lanes.toArray.map Enc.encode).flatten).toList =
      ((v.lanes.toArray.map Enc.encode).flatten).toList.take _ ++ _ ++
        ((v.lanes.toArray.map Enc.encode).flatten).toList.drop _
    rw [Array.toList_flatten, Array.toList_flatten,
      ← flatten_set _ i (Enc.encode x).toList hlists (by simp)]
    simp [Vec.set, List.map_set]
  show padTo size (Enc.encode (v.set i x).lanes) =
    writeBytes (padTo size (Enc.encode v.lanes)) (i * Enc.size α) (Enc.encode x)
  rw [writeBytes_eq]
  apply Array.ext'
  have hlen : (Enc.encode v.lanes : Array Byte).toList.length = n * Enc.size α := by
    simpa using hsize
  have hk : (i : Nat) * Enc.size α ≤ n * Enc.size α :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt i.isLt)
  have hk1 : ((i : Nat) + 1) * Enc.size α = i * Enc.size α + Enc.size α := Nat.succ_mul _ _
  simp only [padTo, Array.toList_append, Array.toList_extract, List.extract_eq_take_drop,
    Array.size_append, Array.size_replicate, Array.toList_replicate, hsize, hsize', hx, hflat,
    Nat.sub_zero, List.drop_zero]
  rw [List.take_append_of_le_length (by omega), ← hk1,
    List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc, List.append_cancel_left_eq]
  symm
  apply List.take_of_length_le
  simp only [List.length_append, List.length_drop, List.length_replicate, hlen]
  omega

/-- A float vector without a NaN lane reads back as stored, at either byte order (a NaN lane's
bits are undefined in memory, `Float.detMask`). -/
theorem Vec.stridedEnc_float_decode_encode (o : ByteOrder) {fmt : FloatFmt} {n : Nat}
    (size align : Nat) (v : Vec (Float fmt) n) (h : ∀ x ∈ v.lanes.toArray, x.isNaN = false) :
    (@Vec.stridedEnc _ (Zig.floatEncOf o fmt) n size align).decode
      ((@Vec.stridedEnc _ (Zig.floatEncOf o fmt) n size align).encode v) = pure v :=
  @Vec.stridedEnc_decode_encode _ (Zig.floatEncOf o fmt) n size align v
    (fun x _ => floatEncOf_size_encode o fmt x) fun x hx => floatEncOf_decode_encode o fmt (h x hx)

end Zig
