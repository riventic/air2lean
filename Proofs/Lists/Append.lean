import Proofs.Lists.Gen
import ZigLean.Sep

/-!
# `ArrayListUnmanaged(u32).append`

`alist p ptr cap xs`: the list header at `p` (24 bytes: `items.ptr`, `items.len`, `capacity`)
and its buffer at `ptr` (a heap block of `4 * cap` bytes, the first `xs.length` items are `xs`;
no block for `cap = 0`).

* `append_run`: `append` gives `xs ++ [v]`, or `error.OutOfMemory` and the same list. When the
  buffer is full, `ensureTotalCapacityPrecise` allocates a new block, copies the items with a
  `@memcpy` and frees the old block. The `@memcpy` alias check holds because the new block lies
  above every live block (`alloc_run`, `Mem.AddrBelow`).

The items pointer of a list with `cap = 0` points into a block with no bytes (`.empty` points
into a constant global), so no assertion can state that its block exists; `append_run` takes it
as a fact about the memory (`ptrOk`), and gives it back.
-/

namespace Lists
open Zig Assn

/-! ## The header -/

/-- The bytes of a list header. -/
def hdrBytes (ptr : Ptr) (len cap : BitVec 64) : Array Byte :=
  Enc.encode ptr ++ Enc.encode len ++ Enc.encode cap

theorem enc_ptr_size (q : Ptr) : (Enc.encode q).size = 8 := LawfulEnc.size_encode q
theorem enc_u64_size (v : BitVec 64) : (Enc.encode v).size = 8 := LawfulEnc.size_encode v

@[simp] theorem enc_ptr_all (q : Ptr) : (Enc.encode q).extract 0 8 = Enc.encode q := by
  rw [← enc_ptr_size q]; exact Array.extract_size
@[simp] theorem enc_u64_all (v : BitVec 64) : (Enc.encode v).extract 0 8 = Enc.encode v := by
  rw [← enc_u64_size v]; exact Array.extract_size
theorem extract_none (x : Array Byte) {a b : Nat} (h : b ≤ a) : x.extract a b = #[] := by
  simp; omega

theorem hdrBytes_size (ptr : Ptr) (len cap : BitVec 64) : (hdrBytes ptr len cap).size = 24 := by
  simp [hdrBytes, enc_ptr_size, enc_u64_size]

theorem hdr_ptr (ptr : Ptr) (len cap : BitVec 64) :
    (hdrBytes ptr len cap).extract 0 (0 + 8) = Enc.encode ptr := by
  simp [hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

theorem hdr_len (ptr : Ptr) (len cap : BitVec 64) :
    (hdrBytes ptr len cap).extract 8 (8 + 8) = Enc.encode len := by
  simp [hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

theorem hdr_cap (ptr : Ptr) (len cap : BitVec 64) :
    (hdrBytes ptr len cap).extract 16 (16 + 8) = Enc.encode cap := by
  simp [hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

theorem hdr_slice (ptr : Ptr) (len cap : BitVec 64) :
    (hdrBytes ptr len cap).extract 0 (0 + 16) = Enc.encode ptr ++ Enc.encode len := by
  simp [hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

theorem decode_slice (ptr : Ptr) (len : BitVec 64) :
    Enc.decode (Enc.encode ptr ++ Enc.encode len : Array Byte) = (pure ⟨ptr, len⟩ : Result Slice) := by
  show (do pure ⟨← Enc.decode _, ← Enc.decode _⟩ : Result Slice) = _
  rw [show (Enc.encode ptr ++ Enc.encode len : Array Byte).extract 0 8 = Enc.encode ptr by
      simp [Array.extract_append, enc_ptr_size],
    show (Enc.encode ptr ++ Enc.encode len : Array Byte).extract 8 16 = Enc.encode len by
      simp [Array.extract_append, enc_ptr_size, extract_none],
    LawfulEnc.decode_encode, LawfulEnc.decode_encode]
  rfl

theorem decode_hdr (ptr : Ptr) (len cap : BitVec 64) :
    Enc.decode (hdrBytes ptr len cap) =
      (pure { items := ⟨ptr, len⟩, capacity := cap } : Result array_list_Aligned_u32_null) := by
  show (do pure { items := ← Enc.decodeAt _ 0, capacity := ← Enc.decodeAt _ 16 } :
    Result array_list_Aligned_u32_null) = _
  unfold Enc.decodeAt
  rw [show Enc.size Slice = 16 from rfl, show Enc.size (BitVec 64) = 8 from rfl, hdr_slice,
    hdr_cap, decode_slice, LawfulEnc.decode_encode]
  rfl

theorem hdr_set_ptr (ptr ptr' : Ptr) (len cap : BitVec 64) :
    writeBytes (hdrBytes ptr len cap) 0 (Enc.encode ptr') = hdrBytes ptr' len cap := by
  simp [writeBytes, hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

theorem hdr_set_len (ptr : Ptr) (len len' cap : BitVec 64) :
    writeBytes (hdrBytes ptr len cap) 8 (Enc.encode len') = hdrBytes ptr len' cap := by
  simp [writeBytes, hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

theorem hdr_set_cap (ptr : Ptr) (len cap cap' : BitVec 64) :
    writeBytes (hdrBytes ptr len cap) 16 (Enc.encode cap') = hdrBytes ptr len cap' := by
  simp [writeBytes, hdrBytes, Array.extract_append, enc_ptr_size, enc_u64_size, extract_none]

/-! ## Loads from owned bytes -/

section Load
variable {m : Mem} {h hF : Heap}

/-- A load of a `T` at `p + k` from bytes that `h` owns. -/
theorem bytesAt_load_run {T : Type} [Enc T] {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hst : m.Seq)
    {q : Ptr} {k a : Nat} {v : T} (hq : q = p.add k) (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    ∃ m', (load T a q).run m = pure (v, m') ∧ m'.heap = h ∪ hF ∧ m'.Seq ∧
      m'.blocks = m.blocks := by
  obtain ⟨b, blk, hacc, -, -, -, hx⟩ :=
    bytesAt_access (q := q) (k := k) (n := Enc.size T) (a := a) hb hm hq hn hk ha
  have hv' : Enc.decode (blk.bytes.extract (p.off.toNat + k) (p.off.toNat + k + Enc.size T)) =
      pure v := by rw [hx]; exact hv
  refine ⟨_, load_run hacc hv' (noRace_of_singleThread hst.single _ _ _ _), ?_, ?_, rfl⟩
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
  · exact hst.recordAt _ _ _ _

/-- A store of a `T` at `p + k` into bytes that `h` owns. -/
theorem bytesAt_store_run {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hst : m.Seq) {q : Ptr} {k a : Nat} (w : T) (hq : q = p.add k) (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    ∃ m', (store a q w).run m = pure ((), m') ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size ∧ ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
        bytesAt p A S K (writeBytes bs k (Enc.encode w)) h' := by
  have hw := LawfulEnc.size_encode w
  obtain ⟨b, blk, -, hr, h', hd', hm', hb'⟩ := bytesAt_store_core (q := q)
    (bs' := Enc.encode w) hb hm hd hq (by omega) (by omega) ha
    (fun b _ => noRace_of_singleThread hst.single b _ _ _) hK
  refine ⟨_, hr, ⟨singleThread_write (singleThread_recordAt hst.single _ _ _ _) _ _ _ _,
    hst.addr.replace hm hd hb (by omega) hm' hb' rfl⟩, by simp [Mem.write, Mem.recordAt], h', hd',
    hm', hb'⟩

end Load

/-! ## The assertions -/

/-- The list header at `p`: `items = ⟨ptr, len⟩`, `capacity = cap`. -/
def hdr (p ptr : Ptr) (len cap : BitVec 64) : Assn := fun h =>
  ∃ A S K, (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bytesAt p A S K (hdrBytes ptr len cap) h

/-- Item `i` of `bs` is `xs[i]`. -/
def ItemsOk (bs : Array Byte) (xs : List (BitVec 32)) : Prop :=
  ∀ i (hi : i < xs.length), bs.extract (4 * i) (4 * i + 4) = Enc.encode xs[i]

/-- The buffer at `ptr`: a heap block of `4 * cap` bytes that starts with `xs`; no bytes for
`cap = 0`. -/
def buf (ptr : Ptr) (cap : Nat) (xs : List (BitVec 32)) : Assn := fun h =>
  if cap = 0 then h = Heap.empty
  else ptr.off = 0 ∧ ∃ A bs, A % 4 = 0 ∧ bs.size = 4 * cap ∧ ItemsOk bs xs ∧
    bytesAt ptr A (4 * cap) .heap bs h

/-- The list at `p` with the buffer at `ptr` of `cap` items holds `xs`. -/
def alist (p ptr : Ptr) (cap : BitVec 64) (xs : List (BitVec 32)) : Assn := fun h =>
  xs.length ≤ cap.toNat ∧ 4 * cap.toNat < 2 ^ 64 ∧
    (hdr p ptr (BitVec.ofNat 64 xs.length) cap ∗ buf ptr cap.toNat xs) h

/-- `ptrAddr` of the items pointer does not throw: its block exists. -/
def ptrOk (m : Mem) (ptr : Ptr) : Prop := ∀ b, ptr.block = some b → b < m.blocks.size


/-! ## `addOneAssumeCapacity` -/

section Ops
variable {m : Mem} {h hF : Heap} {p ptr : Ptr} {len cap : BitVec 64}

theorem dec_u64 (v : BitVec 64) : Enc.decode (Enc.encode v) = (pure v : Result (BitVec 64)) :=
  LawfulEnc.decode_encode v

/-- `addOneAssumeCapacity` with room for one more item: `len + 1`, and the pointer to item
`len`. -/
theorem addOneAssumeCapacity_run (hh : hdr p ptr len cap h) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hst : m.Seq) (hlt : len.toNat < cap.toNat) :
    ∃ m', (array_list_Aligned_u32_null_addOneAssumeCapacity p).run m =
        pure (ptr.elem 4 len, m') ∧ m'.Seq ∧ m'.blocks.size = m.blocks.size ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ hdr p ptr (len + 1) cap h' := by
  obtain ⟨A, S, K, hA, hK, hb⟩ := hh
  have hs := hdrBytes_size ptr len cap
  have e8 : Enc.size (BitVec 64) = 8 := rfl
  have e16 : Enc.size Slice = 16 := rfl
  have q8 : (p.add 0).add 8 = p.add ((8 : Nat) : Int) := by simp [Ptr.add]
  have q16 : p.add 16 = p.add ((16 : Nat) : Int) := rfl
  have q0 : p.add 0 = p.add ((0 : Nat) : Int) := rfl
  have dlen : Enc.decode ((hdrBytes ptr len cap).extract 8 (8 + Enc.size (BitVec 64))) =
      pure len := by rw [show Enc.size (BitVec 64) = 8 from rfl, hdr_len, dec_u64]
  have dcap : Enc.decode ((hdrBytes ptr len cap).extract 16 (16 + Enc.size (BitVec 64))) =
      pure cap := by rw [show Enc.size (BitVec 64) = 8 from rfl, hdr_cap, dec_u64]
  obtain ⟨m₁, l₁, hm₁, hs₁, hb₁⟩ := bytesAt_load_run (a := 8) hb hm hst q8 (by decide) (by omega)
    (by omega) dlen
  obtain ⟨m₂, l₂, hm₂, hs₂, hb₂⟩ := bytesAt_load_run (a := 8) hb hm₁ hs₁ q16 (by decide) (by omega)
    (by omega) dcap
  obtain ⟨m₃, l₃, hm₃, hs₃, hb₃⟩ := bytesAt_load_run (a := 8) hb hm₂ hs₂ q8 (by decide) (by omega)
    (by omega) dlen
  obtain ⟨m₄, s₄, hs₄, hz₄, h₄, hd₄, hm₄, hb₄⟩ := bytesAt_store_run (a := 8) hb hm₃ hd hs₃ (len + 1#64) q8
    (by decide) (by rw [hs]; decide) (by omega) hK
  rw [hdr_set_len, show (1#64 : BitVec 64) = 1 from rfl] at hb₄
  have hs' := hdrBytes_size ptr (len + 1) cap
  have dlen' : Enc.decode ((hdrBytes ptr (len + 1) cap).extract 8 (8 + Enc.size (BitVec 64))) =
      pure (len + 1) := by rw [show Enc.size (BitVec 64) = 8 from rfl, hdr_len, dec_u64]
  have dsl : Enc.decode ((hdrBytes ptr (len + 1) cap).extract 0 (0 + Enc.size Slice)) =
      (pure ⟨ptr, len + 1⟩ : Result Slice) := by
    rw [show Enc.size Slice = 16 from rfl, hdr_slice, decode_slice]
  obtain ⟨m₅, l₅, hm₅, hs₅, hb₅⟩ := bytesAt_load_run (a := 8) hb₄ hm₄ hs₄ q8 (by decide) (by omega)
    (by omega) dlen'
  obtain ⟨m₆, l₆, hm₆, hs₆, hb₆⟩ := bytesAt_load_run (a := 8) hb₄ hm₅ hs₅ q0 (by decide) (by omega)
    (by omega) dsl
  have hno : len.toNat + 1 < 2 ^ 64 := by have := cap.isLt; omega
  have hl1 : (len + 1).toNat = len.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  refine ⟨m₆, ?_, hs₆, by rw [hb₆, hb₅, hz₄, hb₃, hb₂, hb₁], h₄, hd₄, hm₆,
    A, S, K, hA, hK, hb₄⟩
  simp only [StateT.run] at l₁ l₂ l₃ s₄ l₅ l₆
  have hu1 : len.ult cap = true := by simp [BitVec.ult, hlt]
  have hu2 : len.ult (len + 1#64) = true := by unfold BitVec.ult; rw [show (1#64 : BitVec 64) = 1 from rfl, hl1]; simp
  have hno' : ¬ 18446744073709551615 ≤ len.toNat := by omega
  have hmod : ¬ (len.toNat + 1) % 18446744073709551616 = 0 := by omega
  have hsub : len + 1#64 - 1#64 = len := BitVec.add_sub_cancel len 1#64
  simp [array_list_Aligned_u32_null_addOneAssumeCapacity, zig_unfold, l₁, l₂, l₃, s₄, l₅, l₆,
    debug_assert, Zig.lt, hu1, hu2, hno', hmod, hsub, hl1]

end Ops

end Lists
