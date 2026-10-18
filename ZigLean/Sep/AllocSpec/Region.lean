import ZigLean.Sep.Base.Pts

/-!
# Region permissions

An allocator hands out byte ranges, not whole blocks: a fixed buffer carves sub-ranges out of
one buffer block, and a page allocator returns a prefix of a mapping. `regionIn p A S K a bs`
owns exactly the bytes `bs` at `p` inside one writable block (address `A`, size `S`, kind `K`),
and the address of `p` is a multiple of `a`. `region p a bs` hides the block.

The lemmas are the region algebra that allocator specifications and proofs need:

* split and join of adjacent ranges (`bytesAt_append`, `regionIn_split`, `regionIn_join`);
* the block of a region in a memory (`bytesAt_block`), so that two regions in the same block
  have the same block data (`bytesAt_meta_eq`) and a hidden region rejoins its neighbours
  (`region_reveal`).

Vocabulary only, no program judgment: the full-state rules for the byte operations on regions
are in `ZigLean/Sep/Full/Region.lean`. Nothing here is reachable from `ZigLean.lean`: it is
proof-only.
-/

namespace Zig

open Assn

/-- `h` owns exactly the bytes `bs` at `p`, in a block that is not a `const` global, with address
`A`, size `S` and kind `K`; the address of `p` is a multiple of `a`. -/
def regionIn (p : Ptr) (A S : Nat) (K : BlockKind) (a : Nat) (bs : Array Byte) : Assn := fun h =>
  (A + p.off.toNat) % a = 0 ∧ K ≠ .constGlobal ∧ bytesAt p A S K bs h

/-- `regionIn` in some block. -/
def region (p : Ptr) (a : Nat) (bs : Array Byte) : Assn := fun h =>
  ∃ A S K, regionIn p A S K a bs h

namespace Region

theorem Heap.sub_refl (h : Heap) : Heap.Sub h h := fun _ _ e => e

theorem Heap.sub_union_left {h₁ h₂ H : Heap} (hs : Heap.Sub (h₁ ∪ h₂) H) : Heap.Sub h₁ H :=
  fun l c e => hs l c (by simp [e])

theorem Heap.sub_union_right {h₁ h₂ H : Heap} (hd : Heap.Disjoint h₁ h₂)
    (hs : Heap.Sub (h₁ ∪ h₂) H) : Heap.Sub h₂ H := by
  intro l c e
  apply hs l c
  rcases hd l with h1 | h1
  · simp [h1, e]
  · rw [h1] at e; cases e

theorem Heap.sub_of_eq {h hF H : Heap} (hm : H = h ∪ hF) : Heap.Sub h H := by
  subst hm; exact fun l c e => by simp [e]

/-! ## Arrays -/

theorem append_getElem! (bs bs' : Array Byte) (i : Nat) :
    (bs ++ bs')[i]! = if i < bs.size then bs[i]! else bs'[i - bs.size]! := by
  by_cases hi : i < bs.size
  · simp only [hi, ↓reduceIte, getElem!_def, Array.getElem?_append_left hi]
  · simp only [hi, ↓reduceIte, getElem!_def, Array.getElem?_append_right (Nat.le_of_not_lt hi)]

theorem extract_append_left (bs bs' : Array Byte) : (bs ++ bs').extract 0 bs.size = bs := by
  simp

theorem extract_append_right (bs bs' : Array Byte) :
    (bs ++ bs').extract bs.size (bs ++ bs').size = bs' := by
  simp

/-! ## Split and join -/

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs bs' : Array Byte} {h : Heap}

/-- `bytesAt` determines its heap. -/
theorem bytesAt_precise {h' : Heap} (h₁ : bytesAt p A S K bs h) (h₂ : bytesAt p A S K bs h') :
    h = h' := by
  obtain ⟨b, hb, -, hl⟩ := h₁
  obtain ⟨b', hb', -, hl'⟩ := h₂
  rw [hb] at hb'; cases hb'
  funext l; rw [hl, hl']

/-- Two adjacent owned ranges of one block are one range. -/
theorem bytesAt_append :
    (bytesAt p A S K bs ∗ bytesAt (p.add bs.size) A S K bs') h ↔ bytesAt p A S K (bs ++ bs') h := by
  constructor
  · rintro ⟨h₁, h₂, -, rfl, hb₁, hb₂⟩
    obtain ⟨b, hpb, h0, -⟩ := id hb₁
    let H : Heap := fun l =>
      if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + (bs ++ bs').size
      then some ⟨(bs ++ bs')[l.2 - p.off.toNat]!, A, S, K⟩ else none
    have hH : bytesAt p A S K (bs ++ bs') H := ⟨b, hpb, h0, fun _ => rfl⟩
    obtain ⟨H₁, H₂, -, hHe, hH₁, hH₂⟩ := bytesAt_split hH (k := bs.size) (by simp)
    rw [extract_append_left] at hH₁
    rw [extract_append_right] at hH₂
    rw [bytesAt_precise hb₁ hH₁, bytesAt_precise hb₂ hH₂, ← hHe]
    exact hH
  · intro hb
    have := bytesAt_split hb (k := bs.size) (by simp)
    rwa [extract_append_left, extract_append_right] at this

theorem bytesAt_pos_off (hb : bytesAt p A S K bs h) : 0 ≤ p.off := by
  obtain ⟨_, _, h0, _⟩ := hb; exact h0

theorem add_off_toNat (p : Ptr) (k : Nat) (h0 : 0 ≤ p.off) : (p.add k).off.toNat = p.off.toNat + k := by
  simp [Ptr.add]; omega

/-- Split a region at `k`. The second part's address must be a multiple of `a'`. -/
theorem regionIn_split (hr : regionIn p A S K a bs h) {k a' : Nat} (hk : k ≤ bs.size)
    (ha' : (A + p.off.toNat + k) % a' = 0) :
    (regionIn p A S K a (bs.extract 0 k) ∗
      regionIn (p.add k) A S K a' (bs.extract k bs.size)) h := by
  obtain ⟨ha, hK, hb⟩ := hr
  have h0 := bytesAt_pos_off hb
  obtain ⟨h₁, h₂, hd, rfl, hb₁, hb₂⟩ := bytesAt_split hb hk
  refine ⟨h₁, h₂, hd, rfl, ⟨ha, hK, hb₁⟩, ⟨?_, hK, hb₂⟩⟩
  rw [add_off_toNat p k h0, ← Nat.add_assoc]; exact ha'

/-- Join two adjacent regions of one block. -/
theorem regionIn_join {a' : Nat} :
    (regionIn p A S K a bs ∗ regionIn (p.add bs.size) A S K a' bs') h →
      regionIn p A S K a (bs ++ bs') h := by
  rintro ⟨h₁, h₂, hd, rfl, ⟨ha, hK, hb₁⟩, ⟨-, -, hb₂⟩⟩
  exact ⟨ha, hK, bytesAt_append.mp ⟨h₁, h₂, hd, rfl, hb₁, hb₂⟩⟩

/-- A smaller alignment. -/
theorem regionIn_weaken {a' : Nat} (hr : regionIn p A S K a bs h) (hdvd : a' ∣ a) :
    regionIn p A S K a' bs h :=
  ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hdvd (Nat.dvd_of_mod_eq_zero hr.1)), hr.2⟩

theorem region_weaken {a' : Nat} (hr : region p a bs h) (hdvd : a' ∣ a) : region p a' bs h := by
  obtain ⟨A, S, K, hr⟩ := hr; exact ⟨A, S, K, regionIn_weaken hr hdvd⟩

theorem region_of_regionIn (hr : regionIn p A S K a bs h) : region p a bs h := ⟨A, S, K, hr⟩

/-- An empty region owns nothing. -/
theorem regionIn_empty_heap (hr : regionIn p A S K a #[] h) : h = Heap.empty := by
  obtain ⟨-, -, b, -, -, hl⟩ := hr
  funext l; rw [hl]; simp [Heap.empty]

theorem regionIn_empty (hb : p.block.isSome) (h0 : 0 ≤ p.off) (ha : (A + p.off.toNat) % a = 0)
    (hK : K ≠ .constGlobal) : regionIn p A S K a #[] Heap.empty := by
  obtain ⟨b, hpb⟩ := Option.isSome_iff_exists.mp hb
  exact ⟨ha, hK, b, hpb, h0, fun l => by simp [Heap.empty]⟩

/-! ## The block of a region in a memory -/

/-- The owned bytes are bytes of a live block of the memory, with the block data. -/
theorem bytesAt_block {m : Mem} (hb : bytesAt p A S K bs h) (hs : Heap.Sub h m.heap)
    (hpos : 0 < bs.size) :
    ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live ∧ blk.addr = A ∧
      blk.bytes.size = S ∧ blk.kind = K ∧ p.off.toNat + bs.size ≤ S := by
  obtain ⟨b, hpb, h0, hl⟩ := id hb
  have cell : ∀ j, j < bs.size → m.heap (b, p.off.toNat + j) = some ⟨bs[j]!, A, S, K⟩ := by
    intro j hj
    apply hs
    rw [hl]; simp [hj]
  obtain ⟨blk, hblk, hlive, _, hc⟩ := Mem.heap_some (cell 0 hpos)
  obtain ⟨blk', hblk', -, hlt, -⟩ := Mem.heap_some (cell (bs.size - 1) (by omega))
  rw [hblk] at hblk'; cases hblk'
  simp only [Cell.mk.injEq] at hc
  obtain ⟨-, hA, hS, hK⟩ := hc
  refine ⟨b, blk, hpb, hblk, hlive, hA.symm, hS.symm, hK.symm, ?_⟩
  omega

/-- Two nonempty owned ranges of one block in a memory have the same block data. -/
theorem bytesAt_meta_eq {m : Mem} {q : Ptr} {A' S' : Nat} {K' : BlockKind} {h' : Heap}
    (hb : bytesAt p A S K bs h) (hs : Heap.Sub h m.heap) (hpos : 0 < bs.size)
    (hb' : bytesAt q A' S' K' bs' h') (hs' : Heap.Sub h' m.heap) (hpos' : 0 < bs'.size)
    (hblk : q.block = p.block) : A' = A ∧ S' = S ∧ K' = K := by
  obtain ⟨b, blk, hpb, hm, -, hA, hS, hK, -⟩ := bytesAt_block hb hs hpos
  obtain ⟨b', blk', hqb, hm', -, hA', hS', hK', -⟩ := bytesAt_block hb' hs' hpos'
  rw [hblk, hpb] at hqb; cases hqb
  rw [hm] at hm'; cases hm'
  exact ⟨hA'.symm.trans hA, hS'.symm.trans hS, hK'.symm.trans hK⟩

/-- A nonempty region in a memory is a `regionIn` of the block it lies in. -/
theorem region_reveal {m : Mem} (hr : region p a bs h) (hs : Heap.Sub h m.heap)
    (hpos : 0 < bs.size) :
    ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live ∧
      p.off.toNat + bs.size ≤ blk.bytes.size ∧ regionIn p blk.addr blk.bytes.size blk.kind a bs h := by
  obtain ⟨A, S, K, hr⟩ := hr
  obtain ⟨b, blk, hpb, hblk, hl, hA, hS, hK, hle⟩ := bytesAt_block hr.2.2 hs hpos
  subst hA hS hK
  exact ⟨b, blk, hpb, hblk, hl, hle, hr⟩

/-- A hidden region rejoins the explicit range right after it, inside a memory (a fixed buffer
taking a freed last allocation back, a page allocator rejoining the rest of a mapping). -/
theorem region_join_of_heap {m : Mem} {a' : Nat}
    (hr : (region p a bs ∗ regionIn (p.add bs.size) A S K a' bs') h) (hs : Heap.Sub h m.heap)
    (hpos : 0 < bs.size) (hpos' : 0 < bs'.size) : regionIn p A S K a (bs ++ bs') h := by
  obtain ⟨h₁, h₂, hd, rfl, ⟨A₀, S₀, K₀, hr₁⟩, hr₂⟩ := hr
  obtain ⟨eA, eS, eK⟩ := bytesAt_meta_eq hr₁.2.2 (Heap.sub_union_left hs) hpos hr₂.2.2
    (Heap.sub_union_right hd hs) hpos' rfl
  subst eA eS eK
  exact regionIn_join ⟨h₁, h₂, hd, rfl, hr₁, hr₂⟩

/-- A whole block (a fresh `alloc`, or an `mmap` mapping) with an aligned address is a region. -/
theorem regionIn_of_block {b : BlockId} (hb : bytesAt ⟨some b, 0⟩ A S K bs h) (ha : A % a = 0)
    (hK : K ≠ .constGlobal) : regionIn ⟨some b, 0⟩ A S K a bs h :=
  ⟨by simpa using ha, hK, hb⟩

theorem Ptr.add_add_nat (q : Ptr) (x y : Nat) :
    (q.add (x : Int)).add (y : Int) = q.add ((x + y : Nat) : Int) := by
  cases q; simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega

/-- A bump step on a free range `bs` (alignment 1) at `q`: `pad` bytes of padding, then a region
of `len` bytes at an `a`-aligned address, then the rest. The pattern of a fixed buffer's
`alloc`. -/
theorem regionIn_carve {q : Ptr} (hr : regionIn q A S K 1 bs h) {pad len : Nat}
    (hfit : pad + len ≤ bs.size) (hal : (A + q.off.toNat + pad) % a = 0) :
    (regionIn q A S K 1 (bs.extract 0 pad) ∗
      (regionIn (q.add ((pad : Nat) : Int)) A S K a ((bs.extract pad bs.size).extract 0 len) ∗
        regionIn (q.add ((pad + len : Nat) : Int)) A S K 1
          ((bs.extract pad bs.size).extract len (bs.extract pad bs.size).size))) h := by
  obtain ⟨h₁, h₂, hd, rfl, hr₁, hr₂⟩ := regionIn_split hr (k := pad) (a' := a) (by omega) hal
  refine ⟨h₁, h₂, hd, rfl, hr₁, ?_⟩
  have := regionIn_split hr₂ (k := len) (a' := 1) (by simp; omega) (Nat.mod_one _)
  rw [Ptr.add_add_nat] at this
  exact this

/-! ## Bytes of the wrappers' byte operations -/

theorem flatten_replicate_single (x : Byte) (n : Nat) :
    (Array.replicate n #[x]).flatten = Array.replicate n x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Array.replicate_succ, Array.flatten_push, ih, Array.replicate_succ, Array.push_eq_append]

theorem enc_size_byte : Enc.size (BitVec 8) = 1 := rfl

/-- The bytes of one `u8` item of `@memset(_, v)`: `v`, or undefined. -/
def memsetItem : Option (BitVec 8) → Array Byte
  | some x => Enc.encode x
  | none => Array.replicate 1 .undef

theorem memsetItem_size (v : Option (BitVec 8)) : (memsetItem v).size = 1 := by
  cases v with
  | none => rfl
  | some x => exact LawfulEnc.size_encode x

theorem writeBytes_zero_empty (bs : Array Byte) : writeBytes bs 0 #[] = bs := by
  simp [writeBytes_eq]

end Region

end Zig
