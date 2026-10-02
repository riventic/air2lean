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

/-- `ptrAddr` of the items pointer does not throw: its block exists. -/
def ptrOk (m : Mem) (ptr : Ptr) : Prop := ∀ b, ptr.block = some b → b < m.blocks.size

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

/-- A store of the bytes `bs'` at `p + k` into bytes that `h` owns. -/
theorem bytesAt_storeBytes_run {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hst : m.Seq)
    {q : Ptr} {k a : Nat} {bs' : Array Byte} (hq : q = p.add k) (hn : 0 < bs'.size)
    (hk : k + bs'.size ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    ∃ m', (storeBytes q a bs').run m = pure ((), m') ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size ∧ ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
        bytesAt p A S K (writeBytes bs k bs') h' := by
  obtain ⟨b, blk, -, hr, h', hd', hm', hb'⟩ := bytesAt_store_core (q := q) (bs' := bs') hb hm hd
    hq hn hk ha (fun b _ => noRace_of_singleThread hst.single b _ _ _) hK
  exact ⟨_, hr, ⟨singleThread_write (singleThread_recordAt hst.single _ _ _ _) _ _ _ _,
    hst.addr.replace hm hd hb (by omega) hm' hb' rfl⟩, by simp [Mem.write, Mem.recordAt], h', hd',
    hm', hb'⟩

/-- A store of a `T` at `p + k` into bytes that `h` owns. -/
theorem bytesAt_store_run {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hst : m.Seq) {q : Ptr} {k a : Nat} (w : T) (hq : q = p.add k) (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) (hK : K ≠ .constGlobal) :
    ∃ m', (store a q w).run m = pure ((), m') ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size ∧ ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
        bytesAt p A S K (writeBytes bs k (Enc.encode w)) h' := by
  have hw := LawfulEnc.size_encode w
  exact bytesAt_storeBytes_run hb hm hd hst hq (by omega) (by omega) ha hK

/-- `@memmove` of `n` items of 4 bytes from `src` (owned by `h₁`) to `dst` (owned by `h₂`). -/
theorem memmove_two_run {src dst : Ptr} {A₁ S₁ A₂ S₂ : Nat} {K₁ K₂ : BlockKind}
    {bs₁ bs₂ : Array Byte} {h₁ hG h₂ : Heap} (hb₁ : bytesAt src A₁ S₁ K₁ bs₁ h₁)
    (hm₁ : m.heap = h₁ ∪ hG) (hb₂ : bytesAt dst A₂ S₂ K₂ bs₂ h₂) (hm₂ : m.heap = h₂ ∪ hF)
    (hd₂ : Heap.Disjoint h₂ hF) (hst : m.Seq) (n : BitVec 64) (hn : 0 < n.toNat)
    (hk₁ : n.toNat * 4 ≤ bs₁.size) (hk₂ : n.toNat * 4 ≤ bs₂.size)
    (ha₁ : (A₁ + src.off.toNat) % 4 = 0) (ha₂ : (A₂ + dst.off.toNat) % 4 = 0)
    (hK₂ : K₂ ≠ .constGlobal) :
    ∃ m', (memmove 4 4 4 dst src n).run m = pure ((), m') ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size ∧ ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
        bytesAt dst A₂ S₂ K₂ (writeBytes bs₂ 0 (bs₁.extract 0 (n.toNat * 4))) h' := by
  have hpos : 0 < n.toNat * 4 := by omega
  obtain ⟨b₂, blk₂, hacc₂, -, -, -, -⟩ := bytesAt_access (q := dst) (k := 0) (n := n.toNat * 4)
    (a := 4) hb₂ hm₂ (by simp [Ptr.add]) hpos (by omega) (by simpa using ha₂)
  obtain ⟨b₁, blk₁, hacc₁, -, -, -, hx₁⟩ := bytesAt_access (q := src) (k := 0) (n := n.toNat * 4)
    (a := 4) hb₁ hm₁ (by simp [Ptr.add]) hpos (by omega) (by simpa using ha₁)
  simp only [Nat.add_zero, Nat.zero_add] at hx₁ hacc₁ hacc₂
  have hl := loadBytes_run (kind := .read) hacc₁ (noRace_of_singleThread hst.single b₁ _ _ _)
  rw [hx₁] at hl
  have hmr : (m.recordAt b₁ src.off.toNat (n.toNat * 4) .read).heap = h₂ ∪ hF := by
    funext l; rw [Mem.heap_recordAt]; exact congrFun hm₂ l
  obtain ⟨m', hrun, hst', hsz, h', hd', hm', hb'⟩ := bytesAt_storeBytes_run (q := dst) (k := 0)
    (a := 4) (bs' := bs₁.extract 0 (n.toNat * 4)) hb₂ hmr hd₂ (hst.recordAt _ _ _ _)
    (by simp [Ptr.add]) (by simp; omega) (by simp; omega) (by simpa using ha₂) hK₂
  refine ⟨m', ?_, hst', by rw [hsz]; rfl, h', hd', hm', hb'⟩
  have h0 : n.toNat ≠ 0 := by omega
  simp only [StateT.run] at hl hrun
  simp only [memmove, h0, ↓reduceIte, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, ExceptT.bind,
    ExceptT.mk, ExceptT.bindCont, hacc₂, hl, pure, ExceptT.pure, Option.bind_some]
  exact hrun

/-- `alloc(u32, g)`: a new heap block of `4 * g` undefined bytes above every live block, or
`error.OutOfMemory` and the same heap. -/
theorem alloc_slice_run (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF) (hst : m.Seq)
    (a : Allocator) (g : BitVec 64) (hg : 0 < g.toNat) :
    ∃ r m', (a.alloc 4 4 g).run m = pure (r, m') ∧ m'.Seq ∧ m.blocks.size ≤ m'.blocks.size ∧
      match r with
      | .error e => e = "OutOfMemory" ∧ m'.heap = h ∪ hF
      | .ok s => s.len = g ∧ s.ptr.off = 0 ∧ 4 * g.toNat < 2 ^ 64 ∧ ∃ h', Heap.Disjoint (h ∪ h') hF ∧
          m'.heap = (h ∪ h') ∪ hF ∧ Heap.Disjoint h h' ∧ ∃ A, A % 4 = 0 ∧
          bytesAt s.ptr A (4 * g.toNat) .heap (Array.replicate (4 * g.toNat) .undef) h' ∧
          ∀ l c, m.heap l = some c → c.addr + c.size < A := by
  by_cases hbig : 2 ^ 64 ≤ 4 * g.toNat
  · refine ⟨.error "OutOfMemory", m, ?_, hst, Nat.le_refl _, rfl, hm⟩
    simp [Allocator.alloc, hbig, zig_unfold]
  · obtain ⟨r, m', hr, hst', hsz, hpost⟩ := rawAlloc_run hd hm (4 * g.toNat) 4 (by decide) hst
    have hne : ¬ 4 * g.toNat = 0 := by omega
    simp only [StateT.run] at hr
    cases r with
    | none =>
      refine ⟨.error "OutOfMemory", m', ?_, hst', hsz, rfl, hpost⟩
      simp [Allocator.alloc, allocBytes, hbig, hne, zig_unfold, hr]
    | some q =>
      obtain ⟨h0, h', hd', hm', hdd, A, hA, hb, hab⟩ := hpost
      refine ⟨.ok ⟨q, g⟩, m', ?_, hst', hsz, rfl, h0, by omega, h', hd', hm', hdd, A, hA, hb, hab⟩
      simp [Allocator.alloc, allocBytes, hbig, hne, zig_unfold, hr]

/-- `free` of the whole buffer of `cap > 0` items. -/
theorem free_slice_run {ptr : Ptr} {A : Nat} {bs : Array Byte} {cap : BitVec 64}
    (hb : bytesAt ptr A (4 * cap.toNat) .heap bs h) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hsz : bs.size = 4 * cap.toNat) (h0 : ptr.off = 0)
    (hpos : 0 < cap.toNat) (hst : m.Seq) (a : Allocator) {s : Slice} (hs : s = ⟨ptr.elem 4 0, cap⟩) :
    ∃ m', (a.free 4 s).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size := by
  subst hs
  obtain ⟨m', hr, hm', hst', hsz'⟩ := rawFree_run hb hm hd hsz h0 (by omega) hst
  refine ⟨m', ?_, hm', hst', hsz'⟩
  have hne : ¬ 4 * cap.toNat = 0 := by omega
  simp only [StateT.run] at hr ⊢
  simp only [Allocator.free, hne, ↓reduceIte]
  have hq : ∀ q : Ptr, q = ptr → rawFree q (4 * cap.toNat) m = pure ((), m') := by
    rintro q rfl; exact hr
  exact hq _ (by simp [Ptr.elem, Ptr.add])

/-- `ptrAddr` reads the block's address and changes nothing. -/
theorem ptrAddr_run {q : Ptr} {b : BlockId} {blk : Block} (hq : q.block = some b)
    (hb : m.blocks[b]? = some blk) : (ptrAddr q).run m = pure ((blk.addr : Int) + q.off, m) := by
  simp [ptrAddr, hq, hb, zig_unfold]

theorem ptrAddr_none {q : Ptr} (hq : q.block = none) : (ptrAddr q).run m = pure (q.off, m) := by
  simp [ptrAddr, hq, zig_unfold]

/-- `ptrAddr` of a pointer whose block exists does not throw. -/
theorem ptrAddr_ok {q : Ptr} (hq : ptrOk m q) : ∃ x, (ptrAddr q).run m = pure (x, m) := by
  cases hb : q.block with
  | none => exact ⟨_, ptrAddr_none hb⟩
  | some b =>
    obtain ⟨blk, hblk⟩ : ∃ blk, m.blocks[b]? = some blk :=
      ⟨_, Array.getElem?_eq_getElem (hq b hb)⟩
    exact ⟨_, ptrAddr_run hb hblk⟩

theorem ptrLe_run {q r : Ptr} {x y : Int} (hq : (ptrAddr q).run m = pure (x, m))
    (hr : (ptrAddr r).run m = pure (y, m)) : (ptrLe q r).run m = pure (decide (x ≤ y), m) := by
  simp only [StateT.run] at hq hr
  simp [ptrLe, zig_unfold, hq, hr]

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



/-! ## Heaps of three and four parts -/

section Parts
open Heap

theorem heap3 {x a b c : Heap} (hx : x = (a ∪ b) ∪ c) (dab : Disjoint a b) (dac : Disjoint a c)
    (dbc : Disjoint b c) :
    x = a ∪ (b ∪ c) ∧ Disjoint a (b ∪ c) ∧ x = b ∪ (a ∪ c) ∧ Disjoint b (a ∪ c) := by
  refine ⟨by rw [hx, union_assoc], disjoint_union_right.mpr ⟨dab, dac⟩, ?_,
    disjoint_union_right.mpr ⟨dab.symm, dbc⟩⟩
  rw [hx, union_comm dab, union_assoc]

/-- The parts `a`, `b`, `n` and the frame `c`. -/
theorem heap4 {x a b n c : Heap} (hx : x = ((a ∪ b) ∪ n) ∪ c) (dab : Disjoint a b)
    (dan : Disjoint a n) (dbn : Disjoint b n) (dac : Disjoint a c) (dbc : Disjoint b c)
    (dnc : Disjoint n c) :
    x = a ∪ (b ∪ n ∪ c) ∧ Disjoint a (b ∪ n ∪ c) ∧
    x = b ∪ (a ∪ n ∪ c) ∧ Disjoint b (a ∪ n ∪ c) ∧
    x = n ∪ (a ∪ b ∪ c) ∧ Disjoint n (a ∪ b ∪ c) := by
  have e1 : x = a ∪ (b ∪ n ∪ c) := by rw [hx]; simp only [union_assoc]
  have e2 : x = b ∪ (a ∪ n ∪ c) := by
    rw [hx, union_comm dab]; simp only [union_assoc]
  have e3 : x = n ∪ (a ∪ b ∪ c) := by
    rw [hx, union_assoc (a ∪ b) n c, union_left_comm (disjoint_union_left.mpr ⟨dan, dbn⟩),
      ← union_assoc]
  refine ⟨e1, ?_, e2, ?_, e3, ?_⟩
  · exact disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨dab, dan⟩, dac⟩
  · exact disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨dab.symm, dbn⟩, dbc⟩
  · exact disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨dan.symm, dbn.symm⟩, dnc⟩

end Parts

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
    debug_assert, Zig.lt, hu1, hu2, hno', hmod, hsub]

/-! ## `ensureTotalCapacityPrecise` -/

@[simp] theorem Ptr.elem_zero (q : Ptr) (n : Nat) : q.elem n 0#64 = q := by
  simp [Ptr.elem, Ptr.add]

theorem ptrOk_mono {m m' : Mem} {q : Ptr} (h : ptrOk m q) (hs : m.blocks.size ≤ m'.blocks.size) :
    ptrOk m' q := fun b hb => Nat.lt_of_lt_of_le (h b hb) hs

/-- `ensureTotalCapacityPrecise` with `cap < g`: a new buffer of `g` items with the same items,
or `error.OutOfMemory` and the same list. -/
theorem precise_run (a : Allocator) (g : BitVec 64) {xs : List (BitVec 32)} {hH hB : Heap}
    (hh : hdr p ptr len cap hH) (hbf : buf ptr cap.toNat xs hB) (dHB : Heap.Disjoint hH hB)
    (hm : m.heap = (hH ∪ hB) ∪ hF) (hd : Heap.Disjoint (hH ∪ hB) hF) (hst : m.Seq)
    (hok : ptrOk m ptr) (hlen : xs.length = len.toNat) (hle : len.toNat ≤ cap.toNat)
    (hgt : cap.toNat < g.toNat) :
    ∃ r m', (array_list_Aligned_u32_null_ensureTotalCapacityPrecise p a g).run m =
        pure (r, m') ∧ m'.Seq ∧ m.blocks.size ≤ m'.blocks.size ∧ ∃ hH' hB',
      Heap.Disjoint hH' hB' ∧ Heap.Disjoint (hH' ∪ hB') hF ∧ m'.heap = (hH' ∪ hB') ∪ hF ∧
      match r with
      | .ok _ => ∃ ptr', hdr p ptr' len g hH' ∧ buf ptr' g.toNat xs hB' ∧
          4 * g.toNat < 2 ^ 64 ∧ ptrOk m' ptr'
      | .error e => e = "OutOfMemory" ∧ hdr p ptr len cap hH' ∧ buf ptr cap.toNat xs hB' ∧
          ptrOk m' ptr := by
  obtain ⟨A, S, K, hA, hK, hb⟩ := hh
  obtain ⟨dHF, dBF⟩ := Heap.disjoint_union_left.mp hd
  obtain ⟨hmH, -, -, -⟩ := heap3 hm dHB dHF dBF
  have hs := hdrBytes_size ptr len cap
  have e8 : Enc.size (BitVec 64) = 8 := rfl
  have e24 : Enc.size array_list_Aligned_u32_null = 24 := rfl
  have q16 : p.add 16 = p.add ((16 : Nat) : Int) := rfl
  have q0 : p = p.add ((0 : Nat) : Int) := by simp [Ptr.add]
  have dcap : Enc.decode ((hdrBytes ptr len cap).extract 16 (16 + Enc.size (BitVec 64))) =
      pure cap := by rw [e8, hdr_cap, dec_u64]
  have dall : Enc.decode ((hdrBytes ptr len cap).extract 0
      (0 + Enc.size array_list_Aligned_u32_null)) =
      pure ({ items := ⟨ptr, len⟩, capacity := cap } : array_list_Aligned_u32_null) := by
    rw [e24, Nat.zero_add, ← hs, Array.extract_size]; exact decode_hdr ptr len cap
  obtain ⟨m₁, l₁, hm₁, hs₁, hb₁⟩ := bytesAt_load_run (a := 8) hb hmH hst q16 (by decide)
    (by omega) (by omega) dcap
  obtain ⟨m₂, l₂, hm₂, hs₂, hb₂⟩ := bytesAt_load_run (a := 8) hb hm₁ hs₁ q0 (by decide)
    (by omega) (by omega) dall
  have hm₂' : m₂.heap = (hH ∪ hB) ∪ hF := hm₂.trans (hmH.symm.trans hm)
  have hz₂ : m₂.blocks.size = m.blocks.size := by rw [hb₂, hb₁]
  have hge : Zig.ge false cap g = false := by
    simp [Zig.ge, Zig.le, BitVec.ule]; omega
  have hg0 : ¬ g.toNat = 0 := by omega
  obtain ⟨r, m₃, ha₃, hs₃, hz₃, hpost⟩ := alloc_slice_run hd hm₂' hs₂ a g (by omega)
  have hz : m.blocks.size ≤ m₃.blocks.size := hz₂ ▸ hz₃
  simp only [StateT.run] at l₁ l₂ ha₃
  cases r with
  | error e =>
    obtain ⟨rfl, hm₃⟩ := hpost
    refine ⟨.error "OutOfMemory", m₃, ?_, hs₃, hz, hH, hB, dHB, hd, hm₃, rfl, ⟨A, S, K, hA, hK, hb⟩,
      hbf, ptrOk_mono hok hz⟩
    simp [array_list_Aligned_u32_null_ensureTotalCapacityPrecise, zig_unfold, l₁, l₂, hge,
      array_list_Aligned_u32_null_allocatedSlice, Allocator.remap, hg0, ha₃, Zig.unwrapErr]
  | ok sl =>
    obtain ⟨hsl, hoff, hg4, hN, dN, hm₃, dHBN, A', hA', hbN, habove⟩ := hpost
    obtain ⟨dHN, dBN⟩ := Heap.disjoint_union_left.mp dHBN
    obtain ⟨-, dNF⟩ := Heap.disjoint_union_left.mp dN
    obtain ⟨vH, dvH, vB, dvB, vN, dvN⟩ := heap4 hm₃ dHB dHN dBN dHF dBF dNF
    have e16 : Enc.size Slice = 16 := rfl
    have q8 : (p.add 0).add 8 = p.add ((8 : Nat) : Int) := by simp [Ptr.add]
    have q0' : p.add 0 = p.add ((0 : Nat) : Int) := rfl
    have dlen : Enc.decode ((hdrBytes ptr len cap).extract 8 (8 + Enc.size (BitVec 64))) =
        pure len := by rw [e8, hdr_len, dec_u64]
    have dsl : Enc.decode ((hdrBytes ptr len cap).extract 0 (0 + Enc.size Slice)) =
        (pure ⟨ptr, len⟩ : Result Slice) := by
      rw [show Enc.size Slice = 16 from rfl, hdr_slice, decode_slice]
    obtain ⟨m₄, l₄, hm₄, hs₄, hb₄⟩ := bytesAt_load_run (a := 8) hb vH hs₃ q8 (by decide)
      (by omega) (by omega) dlen
    obtain ⟨m₅, l₅, hm₅, hs₅, hb₅⟩ := bytesAt_load_run (a := 8) hb hm₄ hs₄ q0' (by decide)
      (by omega) (by omega) dsl
    have hz₅ : m₅.blocks = m₃.blocks := by rw [hb₅, hb₄]
    have hm₅' : m₅.heap = m₃.heap := hm₅.trans vH.symm
    obtain ⟨bN, blkN, haccN, hblkN, haddrN, -, -⟩ := bytesAt_access (q := sl.ptr) (k := 0)
      (n := 4 * g.toNat) (a := 1) hbN (hm₅'.trans vN) (by simp [Ptr.add]) (by omega) (by simp)
      (Nat.mod_one _)
    have hpN : sl.ptr.block = some bN := (access_eq haccN).1
    have aN : ∀ k : BitVec 64, (ptrAddr (sl.ptr.elem 4 k)).run m₅ =
        pure ((blkN.addr : Int) + (sl.ptr.elem 4 k).off, m₅) := fun k => ptrAddr_run hpN hblkN
    have aN0 : (ptrAddr sl.ptr).run m₅ = pure ((blkN.addr : Int) + sl.ptr.off, m₅) :=
      ptrAddr_run hpN hblkN
    have hbN5 : bN < m₅.blocks.size := (Array.getElem?_eq_some_iff.mp hblkN).1
    have hz5 : m.blocks.size ≤ m₅.blocks.size := by rw [hz₅]; exact hz
    simp only [StateT.run] at l₄ l₅
    have dHN' : Heap.Disjoint hH (hN ∪ hF) := Heap.disjoint_union_right.mpr ⟨dHN, dHF⟩
    by_cases hc0 : cap.toNat = 0
    · -- No buffer yet: nothing to copy and nothing to free.
      have hlen0 : len.toNat = 0 := by omega
      have hl : len = 0#64 := BitVec.eq_of_toNat_eq (by simp [hlen0])
      subst hl
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hxs
      have hB0 : hB = Heap.empty := by simpa [buf, hc0] using hbf
      subst hB0
      obtain ⟨x, aO⟩ := ptrAddr_ok (ptrOk_mono hok hz5)
      have vH' : m₅.heap = hH ∪ (hN ∪ hF) := by
        rw [hm₅', vH]; simp only [Heap.empty_union]
      obtain ⟨m₆, s₆, hs₆, hz₆, hH₆, dH₆, hm₆, hb₆⟩ := bytesAt_store_run (a := 8) hb vH' dHN' hs₅
        sl.ptr (q := (p.add 0).add 0) (k := 0) (by simp [Ptr.add]) (by decide) (by rw [hs]; decide)
        (by omega) hK
      rw [hdr_set_ptr] at hb₆
      obtain ⟨m₇, s₇, hs₇, hz₇, hH₇, dH₇, hm₇, hb₇⟩ := bytesAt_store_run (a := 8) hb₆ hm₆ dH₆ hs₆
        g (q := p.add 16) (k := 16) rfl (by decide)
        (by rw [hdrBytes_size]; decide) (by omega) hK
      rw [hdr_set_cap] at hb₇
      obtain ⟨dHN₇, dHF₇⟩ := Heap.disjoint_union_right.mp dH₇
      have hor : x ≤ (blkN.addr : Int) + sl.ptr.off ∨ (blkN.addr : Int) + sl.ptr.off ≤ x :=
        Int.le_total _ _
      refine ⟨.ok (), m₇, ?_, hs₇, by rw [hz₇, hz₆]; exact hz5, hH₇, hN, dHN₇,
        Heap.disjoint_union_left.mpr ⟨dHF₇, dNF⟩, by rw [hm₇, Heap.union_assoc], sl.ptr,
        ⟨A, S, K, hA, hK, hb₇⟩, ?_, hg4, ?_⟩
      · have r₁ := ptrLe_run aO aN0
        have r₂ := ptrLe_run aN0 aO
        simp only [StateT.run] at s₆ s₇ r₁ r₂
        simp [array_list_Aligned_u32_null_ensureTotalCapacityPrecise, zig_unfold, l₁, l₂, hge,
          array_list_Aligned_u32_null_allocatedSlice, Allocator.remap, hg0, ha₃, l₄, l₅, hsl,
          r₁, r₂, hor, memmove, Allocator.free, hc0, s₆, s₇, Zig.le, BitVec.ule]
      · simp only [buf, hg0, ↓reduceIte]
        exact ⟨hoff, A', _, hA', by simp, fun i hi => absurd hi (by simp), hbN⟩
      · intro b hb'; rw [hpN] at hb'; cases hb'; rw [hz₇, hz₆]; exact hbN5
    · -- A buffer: copy the items to the new block, then free the old block.
      obtain ⟨hoffO, A₀, bs, hA₀, hbsz, hit, hbO⟩ : ptr.off = 0 ∧ ∃ A bs, A % 4 = 0 ∧
          bs.size = 4 * cap.toNat ∧ ItemsOk bs xs ∧ bytesAt ptr A (4 * cap.toNat) .heap bs hB := by
        simpa [buf, hc0] using hbf
      obtain ⟨bO, blkO, haccO, hblkO, haddrO, -, -⟩ := bytesAt_access (q := ptr) (k := 0)
        (n := 4 * cap.toNat) (a := 1) hbO (hm₅'.trans vB) (by simp [Ptr.add]) (by omega)
        (by omega) (Nat.mod_one _)
      have hpO : ptr.block = some bO := (access_eq haccO).1
      -- The old block ends below the new one (`alloc_run`).
      have hcell : m₂.heap (bO, 0) = some ⟨bs[0]!, A₀, 4 * cap.toNat, .heap⟩ := by
        obtain ⟨b', hb', -, hown⟩ := hbO
        rw [hpO] at hb'; cases hb'
        have hB0 : hB (bO, 0) = some ⟨bs[0]!, A₀, 4 * cap.toNat, .heap⟩ := by
          rw [hown]; simp [hoffO, hbsz]; omega
        have hH0 : hH (bO, 0) = none := (dHB (bO, 0)).resolve_right (by rw [hB0]; simp)
        rw [hm₂', Heap.union_apply, Heap.union_apply, hH0, hB0]; rfl
      have hlt := habove _ _ hcell
      simp only at hlt
      have aO1 : (ptrAddr (ptr.elem 4 len)).run m₅ =
          pure ((blkO.addr : Int) + (ptr.elem 4 len).off, m₅) := ptrAddr_run hpO hblkO
      have aO0 : (ptrAddr ptr).run m₅ = pure ((blkO.addr : Int) + ptr.off, m₅) :=
        ptrAddr_run hpO hblkO
      have hle1 : (blkO.addr : Int) + (ptr.elem 4 len).off ≤ (blkN.addr : Int) + sl.ptr.off := by
        simp [Ptr.elem, Ptr.add, hoffO, hoff, haddrO, haddrN]; omega
      obtain ⟨m₆, mv, hs₆, hz₆, hN', dN', hm₆, hbN'⟩ : ∃ m₆,
          (memmove 4 4 4 sl.ptr ptr len).run m₅ = pure ((), m₆) ∧ m₆.Seq ∧
          m₆.blocks.size = m₅.blocks.size ∧ ∃ hN', Heap.Disjoint hN' (hH ∪ hB ∪ hF) ∧
          m₆.heap = hN' ∪ (hH ∪ hB ∪ hF) ∧ bytesAt sl.ptr A' (4 * g.toNat) .heap
            (writeBytes (Array.replicate (4 * g.toNat) .undef) 0
              (bs.extract 0 (len.toNat * 4))) hN' := by
        by_cases hl0 : len.toNat = 0
        · refine ⟨m₅, by simp [memmove, hl0, zig_unfold], hs₅, rfl, hN, dvN, hm₅'.trans vN, ?_⟩
          rw [hl0]; simpa [writeBytes] using hbN
        · exact memmove_two_run hbO (hm₅'.trans vB) hbN (hm₅'.trans vN) dvN hs₅ len (by omega)
            (by omega) (by simp; omega) (by simp [hoffO, hA₀]) (by simp [hoff, hA']) (by decide)
      obtain ⟨dN'HB, dN'F⟩ := Heap.disjoint_union_right.mp dN'
      obtain ⟨dN'H, dN'B⟩ := Heap.disjoint_union_right.mp dN'HB
      have hm₆' : m₆.heap = ((hH ∪ hB) ∪ hN') ∪ hF := by
        rw [hm₆, Heap.union_comm dN', Heap.union_assoc, Heap.union_comm dN'F.symm,
          ← Heap.union_assoc]
      obtain ⟨-, -, wB, dwB, -, -⟩ := heap4 hm₆' dHB dN'H.symm dN'B.symm dHF dBF dN'F
      obtain ⟨m₇, fr, hm₇, hs₇, hz₇⟩ := free_slice_run hbO wB dwB hbsz hoffO (by omega) hs₆ a
        (s := ⟨ptr, cap⟩) (by simp)
      have vH' : m₇.heap = hH ∪ (hN' ∪ hF) := by rw [hm₇]; simp only [Heap.empty_union, Heap.union_assoc]
      have dHN'' : Heap.Disjoint hH (hN' ∪ hF) := Heap.disjoint_union_right.mpr ⟨dN'H.symm, dHF⟩
      obtain ⟨m₈, s₈, hs₈, hz₈, hH₈, dH₈, hm₈, hb₈⟩ := bytesAt_store_run (a := 8) hb vH' dHN'' hs₇
        sl.ptr (q := (p.add 0).add 0) (k := 0) (by simp [Ptr.add]) (by decide) (by rw [hs]; decide)
        (by omega) hK
      rw [hdr_set_ptr] at hb₈
      obtain ⟨m₉, s₉, hs₉, hz₉, hH₉, dH₉, hm₉, hb₉⟩ := bytesAt_store_run (a := 8) hb₈ hm₈ dH₈ hs₈
        g (q := p.add 16) (k := 16) rfl (by decide)
        (by rw [hdrBytes_size]; decide) (by omega) hK
      rw [hdr_set_cap] at hb₉
      obtain ⟨dHN₉, dHF₉⟩ := Heap.disjoint_union_right.mp dH₉
      refine ⟨.ok (), m₉, ?_, hs₉, by rw [hz₉, hz₈, hz₇, hz₆]; exact hz5, hH₉, hN', dHN₉,
        Heap.disjoint_union_left.mpr ⟨dHF₉, dN'F⟩, by rw [hm₉, Heap.union_assoc], sl.ptr,
        ⟨A, S, K, hA, hK, hb₉⟩, ?_, hg4, ?_⟩
      · have r₁ := ptrLe_run aO1 aN0
        have r₂ := ptrLe_run (aN len) aO0
        simp only [StateT.run] at s₈ s₉ r₁ r₂ mv fr
        simp [array_list_Aligned_u32_null_ensureTotalCapacityPrecise, zig_unfold, l₁, l₂, hge,
          array_list_Aligned_u32_null_allocatedSlice, Allocator.remap, hg0, ha₃, l₄, l₅, hsl,
          r₁, r₂, hle1, mv, fr, s₈, s₉, Zig.le, BitVec.ule, show len.toNat ≤ g.toNat by omega]
      · simp only [buf, hg0, ↓reduceIte]
        refine ⟨hoff, A', _, hA', ?_, ?_, hbN'⟩
        · rw [writeBytes_size _ _ _ (by simp; omega)]; simp
        · intro i hi
          rw [extract_writeBytes_in _ _ _ _ _ (by simp; omega) (Nat.zero_le _) (by simp; omega)]
          simp only [Nat.sub_zero, Array.extract_extract]
          rw [Nat.min_eq_left (by omega)]
          simpa using hit i hi
      · intro b hb'; rw [hpN] at hb'; cases hb'; rw [hz₉, hz₈, hz₇, hz₆]; exact hbN5

end Ops

end Lists
