import ZigLean.Sep.Total

/-!
# Region permissions

An allocator hands out byte ranges, not whole blocks: a fixed buffer carves sub-ranges out of
one buffer block, and a page allocator returns a prefix of a mapping. `regionIn p A S K a bs`
owns exactly the bytes `bs` at `p` inside one writable block (address `A`, size `S`, kind `K`),
and the address of `p` is a multiple of `a`. `region p a bs` hides the block.

The lemmas are the region algebra that `ZigLean/Sep/AllocSpec.lean` and allocator proofs need:

* split and join of adjacent ranges (`bytesAt_append`, `regionIn_split`, `regionIn_join`);
* the block of a region in a memory (`bytesAt_block`), so that two regions in the same block
  have the same block data (`bytesAt_meta_eq`) and a hidden region rejoins its neighbours
  (`region_reveal`);
* total triples for the byte operations of the `std.mem.Allocator` wrappers on regions:
  `@memset(_, undefined)`, `@memcpy` between two regions, and an item store.

Nothing here is reachable from `ZigLean.lean`: it is proof-only.
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

/-- Every cell of `h` is a cell of `H`. -/
def Heap.Sub (h H : Heap) : Prop := ∀ l c, h l = some c → H l = some c

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

/-- Two adjacent owned ranges of one block are one range. -/
theorem bytesAt_append :
    (bytesAt p A S K bs ∗ bytesAt (p.add bs.size) A S K bs') h ↔ bytesAt p A S K (bs ++ bs') h := by
  constructor
  · rintro ⟨h₁, h₂, -, rfl, ⟨b, hpb, h0, hl₁⟩, ⟨b', hpb', -, hl₂⟩⟩
    have hb' : b' = b := by simp only [Ptr.add] at hpb'; rw [hpb] at hpb'; exact (Option.some.inj hpb').symm
    subst hb'
    have hoff : (p.add bs.size).off.toNat = p.off.toNat + bs.size := by simp [Ptr.add]; omega
    refine ⟨b', hpb, h0, fun l => ?_⟩
    rw [Heap.union_apply, hl₁, hl₂, hoff, Array.size_append, append_getElem!]
    by_cases e1 : l.1 = b' ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    · simp only [e1, and_self, ↓reduceIte, Option.some_or,
        show l.2 < p.off.toNat + (bs.size + bs'.size) by omega,
        show l.2 - p.off.toNat < bs.size by omega]
    · simp only [e1, ↓reduceIte, Option.none_or]
      by_cases e2 : l.1 = b' ∧ p.off.toNat + bs.size ≤ l.2 ∧ l.2 < p.off.toNat + bs.size + bs'.size
      · simp only [e2, and_self, ↓reduceIte, show p.off.toNat ≤ l.2 by omega,
          show l.2 < p.off.toNat + (bs.size + bs'.size) by omega,
          show ¬ l.2 - p.off.toNat < bs.size by omega]
        congr 3
        have : l.2 - p.off.toNat - bs.size = l.2 - (p.off.toNat + bs.size) := by omega
        rw [this]
      · have : ¬ (l.1 = b' ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + (bs.size + bs'.size)) := by
          omega
        simp only [e2, this, ↓reduceIte]
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

/-! ## Total triples for the byte operations of the wrappers -/

theorem enc_size_byte : Enc.size (BitVec 8) = 1 := by
  show intSize 8 = 1
  decide

/-- `@memset(region, undefined)` of all `n` bytes. -/
theorem memsetUndef {n : BitVec 64} (hn : n.toNat = bs.size) :
    TotalTriple (region p a bs) (memset (α := BitVec 8) 1 p n none)
      (fun _ => region p a (Array.replicate n.toNat .undef)) := by
  intro m hP hF hd hm hp hst
  by_cases h0 : n.toNat = 0
  · have hbs : bs = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    subst hbs
    refine ⟨(), m, hP, ?_, hd, hm, by rw [h0]; exact hp, hst⟩
    simp [memset, h0, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]
  obtain ⟨A, S, K, hA, hK, hb⟩ := hp
  let bs' : Array Byte := (Array.replicate n.toNat (Array.replicate (Enc.size (BitVec 8)) Byte.undef)).flatten
  have hs' : bs' = Array.replicate n.toNat .undef := by
    apply Array.ext
    · simp [bs', enc_size_byte]
    · intro i h1 h2
      simp only [Array.getElem_replicate]
      have : ∀ x ∈ bs', x = .undef := by
        intro x hx
        simp only [bs', Array.mem_flatten, Array.mem_replicate] at hx
        obtain ⟨a, ⟨-, rfl⟩, hx⟩ := hx
        exact (Array.mem_replicate.mp hx).2
      exact this _ (Array.getElem_mem h1)
  have hsz : bs'.size = bs.size := by rw [hs']; simp [hn]
  have hp0 : p = p.add ((0 : Nat) : Int) := by simp [Ptr.add]
  have ha0 : (A + p.off.toNat + 0) % 1 = 0 := Nat.mod_one _
  obtain ⟨b, blk, hacc, -, -, -, -⟩ := bytesAt_access (q := p) (k := 0) (n := bs'.size) (a := 1)
    hb hm hp0 (by omega) (by omega) ha0
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ := bytesAt_store (q := p) (k := 0) (a := 1)
    (bs' := bs') hb hm hd hp0 (by omega) (by omega) ha0 hst hK
  rw [writeBytes_all hsz] at hb'
  refine ⟨(), m', h', ?_, hd', hm', ⟨A, S, K, hA, hK, hs' ▸ hb'⟩, hst'⟩
  have e : n.toNat * Enc.size (BitVec 8) = bs'.size := by rw [hsz, enc_size_byte]; omega
  simp only [StateT.run] at hrun
  simp only [memset, h0, enc_size_byte, Nat.one_ne_zero, or_self, ↓reduceIte, zig_unfold,
    Nat.mul_one] at hrun ⊢
  have e' : n.toNat = bs'.size := by rw [hsz]; exact hn
  simp only [e', hacc]
  rw [← enc_size_byte]
  exact hrun

/-- A store of an item `v` at byte `o` of a region, aligned to `al`. -/
theorem storeItem {T : Type} [Enc T] [LawfulEnc T] {o al : Nat} (v : T) (hpos : 0 < Enc.size T)
    (ho : o + Enc.size T ≤ bs.size) (hal : al ∣ a) (halo : al ∣ o) :
    TotalTriple (region p a bs) (store al (p.add o) v)
      (fun _ => region p a (writeBytes bs o (Enc.encode v))) := by
  intro m hP hF hd hm hp hst
  obtain ⟨A, S, K, hA, hK, hb⟩ := hp
  have hw := LawfulEnc.size_encode v
  have ha : (A + p.off.toNat + o) % al = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero hA)) halo)
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ :=
    bytesAt_store (q := p.add o) (k := o) (a := al) (bs' := Enc.encode v) hb hm hd rfl
      (by omega) (by omega) ha hst hK
  exact ⟨(), m', h', hrun, hd', hm', ⟨A, S, K, hA, hK, hb'⟩, hst'⟩

theorem writeBytes_zero_empty (bs : Array Byte) : writeBytes bs 0 #[] = bs := by
  simp [writeBytes]

/-- A copy of no bytes does nothing. -/
theorem memmoveZero {P : Assn} {d s : Ptr} {sz da sa : Nat} {n : BitVec 64}
    (h0 : n.toNat * sz = 0) : TotalTriple P (memmove sz da sa d s n) (fun _ => P) := by
  intro m hP hF hd hm hp hst
  refine ⟨(), m, hP, ?_, hd, hm, hp, hst⟩
  have : n.toNat = 0 ∨ sz = 0 := Nat.mul_eq_zero.mp h0
  simp [memmove, this, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]

/-- `@memcpy` of `n` items of `sz` bytes from the region `src` to the start of the region `dst`
(two separate regions). -/
theorem memcpy {d s : Ptr} {a' da sa sz : Nat} {bd bsrc : Array Byte} {n : BitVec 64}
    (hnd : n.toNat * sz ≤ bd.size) (hns : n.toNat * sz ≤ bsrc.size) (hda : da ∣ a)
    (hsa : sa ∣ a') :
    TotalTriple (region d a bd ∗ region s a' bsrc) (memmove sz da sa d s n)
      (fun _ => region d a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz))) ∗
        region s a' bsrc) := by
  intro m hP hF hd hm hp hst
  by_cases h0 : n.toNat = 0 ∨ sz = 0
  · have e : n.toNat * sz = 0 := by rcases h0 with h | h <;> simp [h]
    refine ⟨(), m, hP, ?_, hd, hm, ?_, hst⟩
    · simp [memmove, h0, StateT.run, pure, StateT.pure, ExceptT.pure, ExceptT.mk]
    · rw [e]; simpa [writeBytes_zero_empty] using hp
  have hpos : 0 < n.toNat * sz := Nat.mul_pos (by omega) (by omega)
  obtain ⟨h₁, h₂, hd₁₂, rfl, ⟨A, S, K, hA, hK, hb₁⟩, ⟨A', S', K', hA', hK', hb₂⟩⟩ := hp
  obtain ⟨hd₁F, hd₂F⟩ := Heap.disjoint_union_left.mp hd
  have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
  have hdd₁ : Heap.Disjoint h₁ (h₂ ∪ hF) := Heap.disjoint_union_right.mpr ⟨hd₁₂, hd₁F⟩
  have hm₂ : m.heap = h₂ ∪ (h₁ ∪ hF) := by
    rw [hm, Heap.union_assoc, Heap.union_left_comm hd₁₂]
  have hp0 : ∀ q : Ptr, q = q.add ((0 : Nat) : Int) := fun q => by simp [Ptr.add]
  have haD : (A + d.off.toNat + 0) % da = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hda (Nat.dvd_of_mod_eq_zero (by simpa using hA)))
  have haS : (A' + s.off.toNat + 0) % sa = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hsa (Nat.dvd_of_mod_eq_zero (by simpa using hA')))
  obtain ⟨b, blk, hacc, -, -, -, -⟩ := bytesAt_access (q := d) (k := 0) (n := n.toNat * sz)
    (a := da) hb₁ hm₁ (hp0 d) hpos (by omega) haD
  obtain ⟨b₂, blk₂, hacc₂, -, -, -, hx₂⟩ := bytesAt_access (q := s) (k := 0)
    (n := n.toNat * sz) (a := sa) hb₂ hm₂ (hp0 s) hpos (by omega) haS
  let src := bsrc.extract 0 (0 + n.toNat * sz)
  have hsrc : src.size = n.toNat * sz := by simp [src]; omega
  let recorded := m.recordAt b₂ (s.off.toNat + 0) (n.toNat * sz) AccessKind.read
  have hmr : recorded.heap = h₁ ∪ (h₂ ∪ hF) := by
    funext l; rw [Mem.heap_recordAt]; exact congrFun hm₁ l
  obtain ⟨m', hrun, hst', h', hd', hm', hb'⟩ := bytesAt_store (q := d) (k := 0) (a := da)
    (bs' := src) hb₁ hmr hdd₁ (hp0 d) (by omega) (by omega) haD (hst.recordAt _ _ _ _) hK
  obtain ⟨hd'₂, hd'F⟩ := Heap.disjoint_union_right.mp hd'
  refine ⟨(), m', h' ∪ h₂, ?_, Heap.disjoint_union_left.mpr ⟨hd'F, hd₂F⟩,
    by rw [hm', Heap.union_assoc], ⟨h', h₂, hd'₂, rfl, ⟨A, S, K, hA, hK, ?_⟩,
      ⟨A', S', K', hA', hK', hb₂⟩⟩, hst'⟩
  · have hl := loadBytes_run hacc₂ (noRace_of_singleThread hst.single b₂
      (s.off.toNat + 0) (n.toNat * sz) AccessKind.read)
    rw [hx₂] at hl
    simp only [StateT.run] at hl hrun
    simp only [memmove, h0, ↓reduceIte, StateT.run, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, hacc, hl, pure, ExceptT.pure, Option.bind_some]
    exact hrun
  · simpa [src] using hb'

end Region

end Zig
