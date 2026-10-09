import ZigLean.Sep.Full.Atomic

/-!
# A toy page allocator with an atomic hint (prototype, `docs/sep-full-state.md`)

The shape of `std.heap.PageAllocator.map`'s use of `next_mmap_addr_hint` that `docs/alloc-page.md`
shows cannot be specified with heap-only assertions:

* the hint is a word read and written **atomically** (obstruction O3: its atomic layout must be
  constrained by the precondition and kept by every frame);
* the allocator keeps a **pointer to its last mapping** (here in the plain slot `last`), which it
  reads with `@intFromPtr` on the next call, **after that mapping may have been freed**
  (obstruction O1: the dead block's address must be constrained).

`toyAlloc` reads the hint atomically, reads `last` and its address (a dangling pointer after a
free), checks that the hint is that address plus one page (a panic otherwise, like the
`@ptrFromInt` alignment check of the real code), maps a new page (`alloc`), publishes its end as
the new hint (atomic store) and remembers it in `last`.

The allocator invariant `inv` owns the hint word (`apts`), the slot, and only **knowledge** of the
last mapping's address (`addrOf`, built on `known`), never its bytes. So `free` of the mapping
(`toyFree_spec`) keeps `inv`, and the next `toyAlloc` (`cycle_spec`: alloc, free, alloc) proves.

The two obstruction scenarios are excluded by the precondition (`apts_layout`, `addrOf_block`):
a memory with another atomic location over the hint, or one in which `last`'s block does not
exist, holds no `inv`.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Generic helpers -/

section Helpers

variable {α β : Type} {P Q R : FAssn} {r : Res} {φ : Prop}

theorem lift_fact (h : (⟪φ⟫ ⋆ P) r) : φ := (sep_lift.mp h).1

theorem lift_drop (h : (⟪φ⟫ ⋆ P) r) : P r := (sep_lift.mp h).2

theorem sep_fact_left {ψ : Prop} (h : (P ⋆ R) r) (hp : ∀ r, P r → ψ) : ψ := by
  obtain ⟨r₁, -, -, -, h1, -⟩ := h; exact hp r₁ h1

theorem sep_fact_right {ψ : Prop} (h : (R ⋆ P) r) (hp : ∀ r, P r → ψ) : ψ := by
  obtain ⟨-, r₂, -, -, -, h2⟩ := h; exact hp r₂ h2

/-- A fact that the precondition implies. -/
theorem FTriple.fact {c : MemM α} {S : α → FAssn} (hφ : ∀ r, P r → φ)
    (h : φ → FTriple P c S) : FTriple P c S := by
  intro m r rF hh hp hs
  exact h (hφ r hp) m r rF hh hp hs

theorem FTriple.of_false {c : MemM α} {S : α → FAssn} (h : ∀ r, P r → False) : FTriple P c S :=
  FTriple.fact h fun f => f.elim

theorem up_ex {γ : Type} {P : γ → Assn} : up (Assn.ex P) r ↔ ∃ x, up (P x) r := by
  constructor
  · rintro ⟨⟨x, h⟩, hk⟩; exact ⟨x, h, hk⟩
  · rintro ⟨x, h, hk⟩; exact ⟨⟨x, h⟩, hk⟩

theorem sep_left_comm (h : (P ⋆ (Q ⋆ R)) r) : (Q ⋆ (P ⋆ R)) r :=
  sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' h))

/-- `panic` if `c`. -/
def panicIf (c : Prop) [Decidable c] : MemM Unit := if c then throw .panic else pure ()

theorem FTriple.panicIf {c : Prop} [Decidable c] (hc : ¬ c) :
    FTriple P (Full.panicIf c) (fun _ => P) := by
  unfold Full.panicIf; rw [if_neg hc]; exact FTriple.ret (Q := fun _ => P) ()

/-! Legacy rules, lifted (`FTriple.ofTriple`). -/

theorem FTriple.load' {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTriple (up (pts p a v)) (load T a p) (fun x => ⟪x = v⟫ ⋆ up (pts p a v)) :=
  (FTriple.ofTriple (Triple.load hn) (Tame.load T a p)).post fun _ _ h =>
    sep_lift.mpr (up_lift.mp h)

theorem FTriple.store' {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) (w : T) :
    FTriple (up (pts p a v)) (store a p w) (fun _ => up (pts p a w)) :=
  FTriple.ofTriple (Triple.store hn w) (Tame.store a p w)

theorem FTriple.alloc' (kind : BlockKind) (size align : Nat) (ha : 0 < align)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat =>
      ⟪p.off = 0 ∧ A % align = 0⟫ ⋆ up (bytesAt p A size kind (Array.replicate size .undef))) :=
  (FTriple.ofTriple (Triple.alloc kind size align ha hk) (Tame.alloc kind size align)).conseq
    (fun _ h => up_emp.mpr h)
    (fun _ _ h => by
      obtain ⟨A, h⟩ := up_ex.mp h
      exact ⟨A, sep_lift.mpr (up_lift.mp h)⟩)

theorem FTriple.free' {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) :
    FTriple (up (bytesAt p A S K bs)) (free p) (fun _ => emp) :=
  (FTriple.ofTriple (Triple.free hS h0 hpos) (Tame.free p)).post fun _ _ h => up_emp.mp h

end Helpers

namespace Toy

open Conc Conc.Proto

theorem pure_inj {α : Type} {x y : α} (h : (pure x : Result α) = pure y) : x = y := by
  have := congrArg ExceptT.run h
  simpa [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this

/-! ## The allocator invariant -/

/-- The address of `q` is `a`, as knowledge: a pointer without a block is its offset; a pointer
into block `b` needs `known b A` (true also after `b` was freed). -/
def addrOf (q : Ptr) (a : Int) : FAssn :=
  match q.block with
  | none => ⟪q.off = a⟫
  | some b => FAssn.ex fun A : Nat => ⟪(A : Int) + q.off = a⟫ ⋆ known b A

theorem addrOf_heap {q : Ptr} {a : Int} {r : Res} (h : addrOf q a r) : r.heap = FHeap.empty := by
  obtain ⟨blk, off⟩ := q
  cases blk with
  | none => exact h.2.1
  | some b =>
    obtain ⟨A, h⟩ := h
    obtain ⟨-, k⟩ := sep_lift.mp h
    exact k.1

/-- `@intFromPtr` of a pointer whose address is known (live or freed block). -/
theorem FTriple.ptrAddrOf (q : Ptr) (a : Int) :
    FTriple (addrOf q a) (ptrAddr q) (fun x => ⟪x = a⟫ ⋆ addrOf q a) := by
  obtain ⟨blk, off⟩ := q
  cases blk with
  | none =>
    exact FTriple.of_run fun m r _ hh hp hs =>
      ⟨off, m, r, ptrAddr_none_run m off, hh, sep_lift.mpr ⟨hp.1, hp⟩, hs⟩
  | some b =>
    exact FTriple.of_run fun m r _ hh hp hs => by
      obtain ⟨A, hp'⟩ := hp
      obtain ⟨hA, hk⟩ := sep_lift.mp hp'
      obtain ⟨x, hx, hxa⟩ := hh.know b A (by rw [hk.2]; exact ⟨rfl, rfl⟩)
      exact ⟨_, m, r, ptrAddr_run hx off, hh,
        sep_lift.mpr ⟨by rw [hxa]; exact hA, ⟨A, hp'⟩⟩, hs⟩

/-- The allocator's state: the hint word holds the end of the last mapping, whose address
`last` remembers (knowledge only). -/
def inv (hint last : Ptr) : FAssn :=
  FAssn.ex fun q : Ptr => FAssn.ex fun a : Int =>
    apts hint (BitVec.ofInt 64 (a + 4096)) ⋆ (up (pts last 8 q) ⋆ addrOf q a)

/-- A fresh page mapping, owned by the caller. -/
def newMap (p : Ptr) : FAssn :=
  FAssn.ex fun A : Nat =>
    ⟪p.off = 0 ∧ A % 4096 = 0⟫ ⋆ up (bytesAt p A 4096 .heap (Array.replicate 4096 .undef))

/-! ## The program -/

/-- Read the hint and check it against the last mapping's address (maybe freed). -/
def readHint (hint last : Ptr) : MemM Unit :=
  atomicLoadAt (n := 64) 0 .relaxed 8 hint >>= fun h =>
  load Ptr 8 last >>= fun q =>
  ptrAddr q >>= fun a =>
  panicIf (BitVec.ofInt 64 (a + 4096) ≠ h)

/-- Map a page and take its address. -/
def mapPage : MemM (Ptr × Int) :=
  alloc .heap 4096 4096 >>= fun p =>
  ptrAddr p >>= fun a =>
  pure (p, a)

/-- Publish the new hint and remember the mapping. -/
def publish (hint last p : Ptr) (a : Int) : MemM Unit :=
  atomicStoreAt 0 .relaxed 8 hint (BitVec.ofInt 64 (a + 4096)) >>= fun _ =>
  store 8 last p

def toyAlloc (hint last : Ptr) : MemM Ptr :=
  readHint hint last >>= fun _ =>
  mapPage >>= fun pa =>
  publish hint last pa.1 pa.2 >>= fun _ =>
  pure pa.1

def toyFree (p : Ptr) : MemM Unit := free p

/-! ## Specs -/

/-- The parts of `inv` for a fixed last mapping. -/
def parts (hint last q : Ptr) (a : Int) : FAssn :=
  apts hint (BitVec.ofInt 64 (a + 4096)) ⋆ (up (pts last 8 q) ⋆ addrOf q a)

theorem pts_size : 0 < Enc.size Ptr := by decide

theorem readHint_spec (hint last q : Ptr) (a : Int) :
    FTriple (parts hint last q a) (readHint hint last) (fun _ => parts hint last q a) := by
  unfold readHint parts
  refine FTriple.bind (FTriple.frame (FTriple.atomicLoad hint (BitVec.ofInt 64 (a + 4096)) .relaxed))
    fun h => ?_
  refine FTriple.fact (fun r hr => sep_fact_left hr fun _ x => lift_fact x) fun e => ?_
  subst e
  refine FTriple.pre ?_ (fun r hr => sep_mono_left (fun _ x => lift_drop x) hr)
  refine FTriple.bind (FTriple.pre (FTriple.frame (FTriple.load' (p := last) (a := 8) (v := q) pts_size))
    (fun r hr => sep_left_comm hr)) fun x => ?_
  refine FTriple.fact (fun r hr => sep_fact_left hr fun _ x => lift_fact x) fun e => ?_
  subst e
  refine FTriple.pre ?_ (fun r hr => sep_mono_left (fun _ x => lift_drop x) hr)
  refine FTriple.bind (FTriple.pre (FTriple.frame (FTriple.ptrAddrOf x a))
    (fun r hr => sep_comm (sep_assoc' hr))) fun y => ?_
  refine FTriple.fact (fun r hr => sep_fact_left hr fun _ x => lift_fact x) fun e => ?_
  subst e
  refine FTriple.pre ?_ (fun r hr => sep_mono_left (fun _ x => lift_drop x) hr)
  exact (FTriple.panicIf (by simp)).post fun _ r hr =>
    sep_left_comm (sep_assoc (sep_comm hr))

/-- The cell of an owned legacy byte. -/
theorem up_bytes_cell {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hpos : 0 < bs.size) {r : Res} (h : up (bytesAt p A S K bs) r) :
    ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A := by
  obtain ⟨⟨b', hb', -, hl⟩, -⟩ := h
  rw [hpb] at hb'; cases hb'
  have := hl (b, p.off.toNat)
  simp only [FHeap.erase, true_and, Nat.le_refl, Nat.lt_add_of_pos_right hpos, and_self,
    ↓reduceIte, Option.map_eq_some_iff] at this
  obtain ⟨fc, hfc, he⟩ := this
  exact ⟨_, fc, hfc, by rw [he]⟩

theorem sep_cell_left {P Q : FAssn} {r : Res} {b : BlockId} {A : Nat} (h : (P ⋆ Q) r)
    (hp : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A) :
    ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A := by
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := h
  obtain ⟨x, fc, hx, hA⟩ := hp r₁ h1
  exact ⟨x, fc, by simp [hx], hA⟩

theorem mapPage_spec :
    FTriple emp mapPage (fun pa => newMap pa.1 ⋆ addrOf pa.1 pa.2) := by
  unfold mapPage
  refine FTriple.bind (FTriple.alloc' .heap 4096 4096 (by decide)) fun p => ?_
  refine FTriple.ex fun A => ?_
  refine FTriple.fact (φ := (p.off = 0 ∧ A % 4096 = 0) ∧ ∃ b, p.block = some b)
    (fun r hr => ⟨lift_fact hr, by obtain ⟨⟨b, hb, -⟩, -⟩ := lift_drop hr; exact ⟨b, hb⟩⟩) ?_
  rintro ⟨⟨h0, hA⟩, b, hb⟩
  obtain ⟨blk, off⟩ := p
  simp only at h0 hb
  subst h0 hb
  refine FTriple.know_intro (b := b) (A := A) (fun r hr => ?_) ?_
  · obtain ⟨r₁, r₂, -, rfl, ⟨-, he, -⟩, h2⟩ := hr
    obtain ⟨x, fc, hx, hfa⟩ := up_bytes_cell rfl (by simp) h2
    exact ⟨x, fc, by simp [he, hx, FHeap.empty], hfa⟩
  refine FTriple.bind (FTriple.pre (FTriple.frame (FTriple.ptrAddr (b := b) (A := A) 0))
    (fun r hr => sep_comm hr)) fun y => ?_
  refine FTriple.fact (fun r hr => sep_fact_left hr fun _ x => lift_fact x) fun e => ?_
  exact FTriple.ret' _ fun r hr => sep_comm (sep_mono
    (fun _ k => (⟨A, sep_lift.mpr ⟨e.symm, lift_drop k⟩⟩ : addrOf ⟨some b, 0⟩ y _))
    (fun _ x => (⟨A, x⟩ : newMap ⟨some b, 0⟩ _)) hr)

theorem publish_spec (hint last q p : Ptr) (v : BitVec 64) (a : Int) :
    FTriple (apts hint v ⋆ up (pts last 8 q)) (publish hint last p a)
      (fun _ => apts hint (BitVec.ofInt 64 (a + 4096)) ⋆ up (pts last 8 p)) := by
  unfold publish
  refine FTriple.bind (FTriple.frame (FTriple.atomicStore hint v _ .relaxed)) fun _ => ?_
  exact (FTriple.pre (FTriple.frame (FTriple.store' (p := last) (a := 8) (v := q) pts_size p))
    (fun r hr => sep_comm hr)).post fun _ r hr => sep_comm hr

/-- **`alloc`**: from the invariant, a fresh page, and the invariant again (now about it). -/
theorem toyAlloc_spec (hint last : Ptr) :
    FTriple (inv hint last) (toyAlloc hint last) (fun p => inv hint last ⋆ newMap p) := by
  refine FTriple.ex fun q => FTriple.ex fun a => ?_
  unfold toyAlloc
  refine FTriple.bind (readHint_spec hint last q a) fun _ => ?_
  refine FTriple.bind (FTriple.pre (FTriple.frame (R := parts hint last q a) mapPage_spec)
    (fun r hr => sep_comm (sep_emp.mpr hr))) fun pa => ?_
  -- Forget the old mapping's address at the end.
  refine FTriple.drop (K := fun _ => addrOf q a) ?_ (fun _ _ h => addrOf_heap h)
  refine FTriple.bind (FTriple.pre
    (FTriple.frame (R := addrOf q a ⋆ (newMap pa.1 ⋆ addrOf pa.1 pa.2))
      (publish_spec hint last q pa.1 (BitVec.ofInt 64 (a + 4096)) pa.2))
    (fun r hr => sep_assoc (sep_mono_left (fun _ h => sep_assoc' h) (sep_comm hr)))) fun _ => ?_
  refine FTriple.ret' _ fun r hr => ?_
  -- (H ⋆ L) ⋆ (K ⋆ (N ⋆ O))  ⊢  ((H ⋆ (L ⋆ O)) ⋆ N) ⋆ K
  have h1 := sep_assoc hr
  have h2 := sep_mono_right (fun _ h => sep_mono_right (fun _ h => sep_left_comm h)
    (sep_left_comm h)) h1
  have h3 := sep_mono_right (fun _ h => sep_comm (sep_left_comm h)) (sep_left_comm h2)
  exact sep_mono_left (fun _ h => sep_mono_left (fun _ h => ⟨pa.1, pa.2, h⟩) h) (sep_comm h3)

/-- **`free`** of a page: the invariant does not own it, so it stays. -/
theorem toyFree_spec (hint last p : Ptr) :
    FTriple (inv hint last ⋆ newMap p) (toyFree p) (fun _ => inv hint last) := by
  refine (FTriple.frameL (R := inv hint last) ?_).post fun _ _ h => sep_emp.mp h
  exact FTriple.ex fun A => FTriple.lift fun h0 => FTriple.free' (by simp) h0.1 (by decide)

def cycle (hint last : Ptr) : MemM Ptr :=
  toyAlloc hint last >>= fun p => toyFree p >>= fun _ => toyAlloc hint last

/-- **Free, then reuse** (O1): the second `alloc` reads `last`, which points into the freed page,
and takes its address; the invariant's knowledge `known b A` survived the `free`. -/
theorem cycle_spec (hint last : Ptr) :
    FTriple (inv hint last) (cycle hint last) (fun p => inv hint last ⋆ newMap p) :=
  FTriple.bind (toyAlloc_spec hint last) fun p =>
    FTriple.bind (toyFree_spec hint last p) fun _ => toyAlloc_spec hint last

/-! ## The obstruction scenarios are excluded by the precondition -/

theorem Holds.heap_erase {m : Mem} {r rF : Res} (hh : Holds m r rF) :
    m.heap = r.heap.erase ∪ rF.heap.erase := by
  rw [← fheap_erase, hh.heap, FHeap.erase_union]

theorem Holds.sepL {m : Mem} {P Q : FAssn} {r rF : Res} (hh : Holds m r rF) (h : (P ⋆ Q) r) :
    ∃ r₁ r₂, P r₁ ∧ Q r₂ ∧ Holds m r₁ ⟨r₂.heap ∪ rF.heap, r₂.know.union rF.know⟩ ∧
      Holds m r₂ ⟨r₁.heap ∪ rF.heap, r₁.know.union rF.know⟩ := by
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  obtain ⟨hdisj, hheap, hk, hkF⟩ := hh
  obtain ⟨h1F, h2F⟩ := FHeap.disjoint_union_left.mp hdisj
  refine ⟨r₁, r₂, h1, h2, ⟨FHeap.disjoint_union_right.mpr ⟨hd, h1F⟩, by
    rw [hheap]; exact FHeap.union_assoc .., hk.left, hk.right.union hkF⟩,
    ⟨FHeap.disjoint_union_right.mpr ⟨hd.symm, h2F⟩, by
      rw [hheap, ← FHeap.union_assoc, FHeap.union_comm hd, FHeap.union_assoc], hk.right,
      hk.left.union hkF⟩⟩

/-- **O3.** A memory that holds the hint word as `apts` has no atomic location of another
offset or size over it (`docs/alloc-page.md`'s `odd` memory, with a 4-byte location at the hint,
holds no `inv`, though its heap is that of the program start). -/
theorem apts_layout {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) {p : Ptr}
    {v : BitVec 64} (hp : apts p v r) {b : BlockId} (hpb : p.block = some b) {l : ALoc}
    (hl : l ∈ m.atomics) (hb : l.block = b) (h1 : p.off.toNat < l.off + l.len)
    (h2 : l.off < p.off.toNat + 8) : l.off = p.off.toNat ∧ l.len = 8 := by
  obtain ⟨A, S, K, bs, tg, -, -, hsz, -, htg, hab⟩ := hp
  have ht := tagOk_of_own hh hab hsz htg hpb
  have hmem : ALoc.shape l ∈ shapes m :=
    List.mem_map.mpr ⟨l, Array.mem_toList_iff.mpr hl, rfl⟩
  exact overlap_eq hs.2 (by decide) ht hmem hb h1 h2

theorem inv_no_odd {hint last : Ptr} {m : Mem} (hs : m.FSeq) {b : BlockId}
    (hpb : hint.block = some b) {l : ALoc} (hl : l ∈ m.atomics) (hb : l.block = b)
    (ho : l.off = hint.off.toNat) (hlen : l.len = 4) :
    ¬ ∃ r rF, Holds m r rF ∧ inv hint last r := by
  rintro ⟨r, rF, hh, q, a, hi⟩
  obtain ⟨r₁, _, h1, _, hh₁, _⟩ := Holds.sepL hh hi
  have := apts_layout hh₁ hs h1 hpb hl hb (by omega) (by omega)
  omega

/-- The address knowledge in a held resource is true of the memory. -/
theorem addrOf_block {m : Mem} {r rF : Res} (hh : Holds m r rF) {b : BlockId} {off a : Int}
    (h : addrOf ⟨some b, off⟩ a r) : ∃ blk, m.blocks[b]? = some blk ∧ (blk.addr : Int) + off = a := by
  obtain ⟨A, h⟩ := h
  obtain ⟨hA, hk⟩ := sep_lift.mp h
  obtain ⟨blk, hblk, he⟩ := hh.know b A (by rw [hk.2]; exact ⟨rfl, rfl⟩)
  exact ⟨blk, hblk, by rw [he]; exact hA⟩

/-- **O1.** A memory that holds `inv` has the block of the pointer in `last`, live or freed:
`docs/alloc-page.md`'s `hintedLost` memory (the slot points to a block that does not exist), holds
no `inv`, though its heap is that of the memory after a real `alloc` and `free`. -/
theorem inv_last_block {hint last : Ptr} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hi : inv hint last r) {lb : BlockId} (hlb : last.block = some lb) :
    ∃ q : Ptr, Enc.decode (curBytes m lb last.off.toNat 8) = pure q ∧
      ∀ b, q.block = some b → ∃ blk, m.blocks[b]? = some blk := by
  obtain ⟨q, a, hi⟩ := hi
  obtain ⟨_, r₂, _, h2, _, hh₂⟩ := Holds.sepL hh hi
  obtain ⟨r₃, r₄, h3, h4, hh₃, hh₄⟩ := Holds.sepL hh₂ h2
  refine ⟨q, ?_, fun b hb => ?_⟩
  · obtain ⟨⟨A, S, K, bs, hal, hbs, hdec, hbt, -⟩, -⟩ := h3
    have hm := Holds.heap_erase hh₃
    obtain ⟨b', blk, hacc, hblk, -, -, hx⟩ := bytesAt_access (q := last) (k := 0)
      (n := Enc.size Ptr) (a := 1) hbt hm (by simp [Ptr.add]) (by decide) (by omega)
      (Nat.mod_one _)
    rw [(access_eq hacc).1] at hlb; cases hlb
    have hs8 : Enc.size Ptr = 8 := rfl
    rw [hs8] at hx hbs
    have : bs.extract 0 8 = bs := by rw [← hbs]; simp
    simp only [curBytes, hblk, Option.map_some, Option.getD_some, Nat.add_zero] at hx ⊢
    rw [hx, this]; exact hdec
  · obtain ⟨blk, off⟩ := q
    simp only at hb; subst hb
    obtain ⟨blk', h, -⟩ := addrOf_block hh₄ h4
    exact ⟨blk', h⟩

theorem inv_no_lost {hint last : Ptr} {m : Mem} {lb b : BlockId} (hlb : last.block = some lb)
    {off : Int} (hq : Enc.decode (curBytes m lb last.off.toNat 8) = pure (⟨some b, off⟩ : Ptr))
    (hnone : m.blocks[b]? = none) : ¬ ∃ r rF, Holds m r rF ∧ inv hint last r := by
  rintro ⟨r, rF, hh, hi⟩
  obtain ⟨q, hdec, hblk⟩ := inv_last_block hh hi hlb
  rw [hq] at hdec
  have e : (⟨some b, off⟩ : Ptr) = q := pure_inj hdec
  obtain ⟨blk, h⟩ := hblk b (by rw [← e])
  rw [hnone] at h; cases h

/-! ## Nonvacuity: a memory that holds `inv` -/

/-- The hint word's initial bytes: the end of a (non-existent) mapping at address 0. -/
def enc0 : Array Byte := Enc.encode (BitVec.ofInt 64 ((0 : Int) + 4096))

/-- `last` holds a pointer without a block (no mapping yet). -/
def enc1 : Array Byte := Enc.encode (⟨none, 0⟩ : Ptr)

theorem enc0_size : enc0.size = 8 := LawfulEnc.size_encode (α := BitVec 64) _
theorem enc1_size : enc1.size = 8 := LawfulEnc.size_encode (α := Ptr) _

/-- The two globals at program start: the hint (block 0) and `last` (block 1); no atomic
location. -/
def start : Mem :=
  { blocks := #[⟨enc0, 8, .global, true, 4096⟩, ⟨enc1, 8, .global, true, 4112⟩], nextAddr := 4121 }

def hintP : Ptr := ⟨some 0, 0⟩
def lastP : Ptr := ⟨some 1, 0⟩

/-- The owned bytes of block `b` (address `A`, 8 bytes, a `var` global), with no atomic tag. -/
def glob (b A : Nat) (bs : Array Byte) : FHeap := fun l =>
  if l.1 = b ∧ l.2 < 8 then some ⟨⟨bs[l.2]!, A, 8, .global⟩, none⟩ else none

theorem start_fheap : start.fheap = glob 0 4096 enc0 ∪ glob 1 4112 enc1 := by
  funext ⟨b, o⟩
  simp only [Mem.fheap, FHeap.union_apply, glob]
  rcases b with _ | _ | b
  · by_cases ho : o < 8
    · simp [Mem.heap, start, enc0_size, ho, getElem!_pos, shapes, tagOf]
    · simp [Mem.heap, start, enc0_size, ho]
  · by_cases ho : o < 8
    · simp [Mem.heap, start, enc1_size, ho, getElem!_pos, shapes, tagOf]
    · simp [Mem.heap, start, enc1_size, ho]
  · simp [Mem.heap, start]

theorem glob_abytes {b A : Nat} {bs : Array Byte} (hs : bs.size = 8) :
    abytesAt ⟨some b, 0⟩ A 8 .global bs none ⟨glob b A bs, Know.none⟩ := by
  refine ⟨rfl, b, rfl, Int.le_refl 0, fun ⟨x, y⟩ => ?_⟩
  simp [glob, hs]

theorem start_inv : ∃ r, Holds start r ⟨FHeap.empty, Know.none⟩ ∧ inv hintP lastP r ∧ start.FSeq := by
  have hd : FHeap.Disjoint (glob 0 4096 enc0) (glob 1 4112 enc1) := by
    intro ⟨b, o⟩; by_cases hb : b = 0 <;> simp [glob, hb]
  refine ⟨⟨glob 0 4096 enc0 ∪ (glob 1 4112 enc1 ∪ FHeap.empty),
    Know.none.union (Know.none.union Know.none)⟩, ⟨fun _ => .inr rfl, ?_, ?_, Know.sub_none _⟩,
    ⟨⟨none, 0⟩, 0, ?_⟩, ?_⟩
  · simp [start_fheap]
  · simp [Know.union_none]; exact Know.sub_none _
  · refine ⟨⟨glob 0 4096 enc0, Know.none⟩, ⟨glob 1 4112 enc1 ∪ FHeap.empty, Know.none.union Know.none⟩,
      by simpa using hd, rfl, ?_, ⟨glob 1 4112 enc1, Know.none⟩, ⟨FHeap.empty, Know.none⟩,
      FHeap.disjoint_empty _, rfl, ?_, ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨4096, 8, .global, enc0, none, rfl, by decide, enc0_size,
        LawfulEnc.decode_encode (α := BitVec 64) _, .inl rfl, glob_abytes enc0_size⟩
    · refine ⟨⟨4112, 8, .global, enc1, rfl, enc1_size, LawfulEnc.decode_encode (α := Ptr) _,
        abytesAt_bytesAt (glob_abytes enc1_size), by decide⟩, rfl⟩
  · refine ⟨⟨singleThread_empty rfl (by decide), fun l c hc => ?_⟩, ⟨by simp [shapes, start],
      by simp [shapes, start]⟩⟩
    obtain ⟨blk, hb, -, -, rfl⟩ := Mem.heap_some hc
    rcases l with ⟨_ | _ | b, o⟩ <;> simp [start] at hb <;> subst hb <;> simp [enc0_size, enc1_size, start]

/-- So the specs are not vacuous: at program start the allocator invariant holds, and
`cycle_spec` applies to the real run (alloc, free, alloc). -/
theorem cycle_from_start {p : Ptr} {m' : Mem}
    (h : ((cycle hintP lastP).run start).run = some (.ok (p, m'))) :
    ∃ r', Holds m' r' ⟨FHeap.empty, Know.none⟩ ∧ (inv hintP lastP ⋆ newMap p) r' ∧ m'.FSeq := by
  obtain ⟨r, hh, hi, hs⟩ := start_inv
  have := cycle_spec hintP lastP start r _ hh hi hs
  rw [h] at this
  exact this

end Toy

end Full
end Zig
