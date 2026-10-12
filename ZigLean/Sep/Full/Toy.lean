import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Claims

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
  (FTriple.ofTriple_up (Triple.load hn) (Tame.load T a p) (SizeFree.pts p a v)
    (Keeps.load T a p)).post fun _ _ h => sep_lift.mpr (up_lift.mp h)

theorem FTriple.store' {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {a : Nat} {v : T}
    (hn : 0 < Enc.size T) (w : T) :
    FTriple (up (pts p a v)) (store a p w) (fun _ => up (pts p a w)) :=
  FTriple.ofTriple_up (Triple.store hn w) (Tame.store a p w) (SizeFree.pts p a v) (Keeps.store a p w)

/-- `alloc` of `size > 0` bytes: the bytes and the new block's full extent. -/
theorem FTriple.alloc' (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) := by
  refine FTriple.drop (K := fun _ r => r.heap = FHeap.empty ∧ r.know = Know.none) ?_ (fun _ _ h => h.1)
  refine ((FTriple.ofTriple (E := fun _ => none) (B := fun _ => False)
    (Triple.alloc kind size align ha hk) (Tame.alloc kind size align)
    (fun h hp l c hl => by rw [hp] at hl; cases hl) (fun _ _ _ _ _ _ _ h => by cases h)
    (SizeFree.of_pinned fun h hp l c hl => by rw [hp] at hl; cases hl) (.inl fun _ h => h.elim)).pre
    fun _ h => upE_none.mpr (up_emp.mpr h)).post fun p r h => ?_
  obtain ⟨E', ⟨hq, hk', hg⟩, hcov⟩ := id h
  obtain ⟨A, hq⟩ := hq
  obtain ⟨⟨h0, hA⟩, hb⟩ := Zig.sep_lift.mp hq
  obtain ⟨b, hpb, -, hl⟩ := id hb
  have hc := hl (b, p.off.toNat)
  rw [if_pos ⟨rfl, Nat.le_refl _, by simp; omega⟩] at hc
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, he⟩ := hc
  have hx := upPost_bext (b := b) (S := size) (K := kind) h ⟨_, fc, hfc, by rw [he], by rw [he], fun h => h.elim⟩
  obtain ⟨r₁, r₂, hd, rfl, ⟨r₃, r₄, hd', e, x, hbx⟩, h2⟩ := hx
  obtain ⟨A', x⟩ := up_ex.mp x
  obtain ⟨⟨h0', hA'⟩, x⟩ := up_lift.mp x
  exact ⟨_, r₂, hd, rfl, ⟨A', b, sep_lift.mpr ⟨⟨hpb, h0', hA'⟩, ⟨r₃, r₄, hd', e, x, hbx⟩⟩⟩, h2⟩

/-- `alloc` of no bytes: a pointer to offset 0 of a new block. The block has no byte, so there is
nothing to own (an extent needs a live byte: `Holds.bauth`). -/
theorem FTriple.allocZero (kind : BlockKind) (align : Nat) (ha : 0 < align)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind 0 align) (fun p => ⟪p.block.isSome ∧ p.off = 0⟫) := by
  refine FTriple.drop (K := fun _ r => r.heap = FHeap.empty) ?_ (fun _ _ h => h)
  refine ((FTriple.ofTriple (E := fun _ => none) (B := fun _ => False)
    (Triple.alloc kind 0 align ha hk) (Tame.alloc kind 0 align)
    (fun h hp l c hl => by rw [hp] at hl; cases hl) (fun _ _ _ _ _ _ _ h => by cases h)
    (SizeFree.of_pinned fun h hp l c hl => by rw [hp] at hl; cases hl) (.inl fun _ h => h.elim)).pre
    fun _ h => upE_none.mpr (up_emp.mpr h)).post fun p r h => ?_
  obtain ⟨E', ⟨hq, -, -⟩, -⟩ := h
  obtain ⟨A, hq⟩ := hq
  obtain ⟨⟨h0, -⟩, b, hpb, -, hl⟩ := Zig.sep_lift.mp hq
  have hemp : r.heap = FHeap.empty := funext fun l => by
    have := hl l
    simp only [Array.size_replicate, Nat.add_zero] at this
    rw [if_neg (by omega)] at this
    simp only [FHeap.erase, Option.map_eq_none_iff] at this
    exact this
  exact sep_lift.mpr ⟨⟨by simp [hpb], h0⟩, hemp⟩

/-- A run of `alloc` creates the block it returns. -/
theorem alloc_fresh {kind : BlockKind} {size align : Nat} {m m' : Mem} {p : Ptr} {b : BlockId}
    (h : ((alloc kind size align).run m).run = some (.ok (p, m'))) (hb : p.block = some b) :
    m.blocks.size ≤ b ∧ b < m'.blocks.size := by
  unfold alloc at h
  obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h1
  split at h2
  · obtain ⟨_, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h2
    have e := Conc.Proto.MemM.set_ok h3
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h4
    subst e
    cases hb
    simp [Mem.afterAlloc]
  · exact (Conc.Proto.MemM.throw_ok h2).elim

/-- **`alloc` with the claim on the new block's bytes** (`FTriple.mintClaimOpt`): the bytes, the
full extent and the exclusive claim on `[0, size)`. -/
theorem FTriple.allocC (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ (bext b size kind ⋆ bclaim b 0 size))) := by
  refine (FTriple.mintClaimOpt (fun p => p.block) (fun _ => 0) (fun _ => size)
    (FTriple.alloc' kind size align ha hpos hk) (fun m v m' b h e => alloc_fresh h e)
    fun _ b r _ hq => noCl_ex (fun A => noCl_ex fun b => noCl_sep (noCl_lift _)
      (noCl_sep (noCl_up _) (noCl_bauth _ _ _ _))) r hq b).post fun p r h => ?_
  obtain ⟨A, h⟩ := sep_ex.mp h
  obtain ⟨b, h⟩ := sep_ex.mp h
  obtain ⟨hφ, h⟩ := sep_lift.mp (sep_assoc h)
  rw [hφ.1] at h
  exact ⟨A, b, sep_lift.mpr ⟨hφ, sep_assoc h⟩⟩

/-- `allocStack` (a stack local whose address escapes) with the claim on its bytes. -/
theorem FTriple.allocStackC (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple emp (allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ (bext b size .stack ⋆ bclaim b 0 size))) :=
  FTriple.allocC .stack size align ha hpos

/-- `free` of a whole block, not a `const` global: its bytes and its full extent go. -/
theorem FTriple.free' {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    FTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (free p) (fun _ => emp) := by
  have hcells : ∀ h, bytesAt p A S K bs h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K := by
    intro h hb l c hc
    obtain ⟨b', hb', -, hl⟩ := hb
    rw [hpb] at hb'; cases hb'
    rw [hl l] at hc
    split at hc
    · rename_i hin; cases hc; exact ⟨hin.1, rfl, rfl⟩
    · cases hc
  refine ((FTriple.ofTriple (E := fun x => if x = b then some (S, K) else none) (B := fun x => x = b)
    (Triple.free hS h0 hpos hK) (Tame.free p) (fun h hp l c hc => (hcells h hp l c hc).1)
    (fun h hp l c S' K' hc hE => by
      obtain ⟨e, hs, hk⟩ := hcells h hp l c hc
      simp only [e, if_pos] at hE; cases hE; exact ⟨hs, hk⟩)
    (SizeFree.of_pinned fun h hp l c hc => by simp [(hcells h hp l c hc).1])
    (.inl fun x hx => by simp [hx])).forgetExt.pre fun _ h => up_sep_bext h).post
    fun _ _ h => up_emp.mp h

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
      obtain ⟨x, hx, hxa⟩ := hh.know (.addr b A) (by rw [hk.2.1]; rfl)
      exact ⟨_, m, r, ptrAddr_run hx off, hh,
        sep_lift.mpr ⟨by rw [hxa]; exact hA, ⟨A, hp'⟩⟩, hs⟩

/-- The allocator's state: the hint word holds the end of the last mapping, whose address
`last` remembers (knowledge only). -/
def inv (hint last : Ptr) : FAssn :=
  FAssn.ex fun q : Ptr => FAssn.ex fun a : Int =>
    apts hint (BitVec.ofInt 64 (a + 4096)) ⋆ (up (pts last 8 q) ⋆ addrOf q a)

/-- A fresh page mapping, owned by the caller: its bytes and its full extent. -/
def newMap (p : Ptr) : FAssn :=
  FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
    ⟪p.block = some b ∧ p.off = 0 ∧ A % 4096 = 0⟫ ⋆
      (up (bytesAt p A 4096 .heap (Array.replicate 4096 .undef)) ⋆ bext b 4096 .heap)

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
  refine FTriple.bind (FTriple.alloc' .heap 4096 4096 (by decide) (by decide)) fun p => ?_
  refine FTriple.ex fun A => FTriple.ex fun b => FTriple.lift fun ⟨hb, h0, hA⟩ => ?_
  obtain ⟨blk, off⟩ := p
  simp only at h0 hb
  subst h0 hb
  refine FTriple.know_intro (b := b) (A := A) (fun r hr => ?_) ?_
  · obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hr
    obtain ⟨x, fc, hx, hfa⟩ := up_bytes_cell rfl (by simp) h1
    exact ⟨x, fc, by simp [hx], hfa⟩
  refine FTriple.bind (FTriple.pre (FTriple.frame (FTriple.ptrAddr (b := b) (A := A) 0))
    (fun r hr => sep_comm hr)) fun y => ?_
  refine FTriple.fact (fun r hr => sep_fact_left hr fun _ x => lift_fact x) fun e => ?_
  exact FTriple.ret' _ fun r hr => sep_comm (sep_mono
    (fun _ k => (⟨A, sep_lift.mpr ⟨e.symm, lift_drop k⟩⟩ : addrOf ⟨some b, 0⟩ y _))
    (fun _ x => (⟨A, b, sep_lift.mpr ⟨⟨rfl, rfl, hA⟩, x⟩⟩ : newMap ⟨some b, 0⟩ _)) hr)

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
  exact FTriple.ex fun A => FTriple.ex fun b => FTriple.lift fun h0 => FTriple.free' h0.1 (by simp) h0.2.1 (by decide)

def cycle (hint last : Ptr) : MemM Ptr :=
  toyAlloc hint last >>= fun p => toyFree p >>= fun _ => toyAlloc hint last

/-- **Free, then reuse** (O1): the second `alloc` reads `last`, which points into the freed page,
and takes its address; the invariant's knowledge `known b A` survived the `free`. -/
theorem cycle_spec (hint last : Ptr) :
    FTriple (inv hint last) (cycle hint last) (fun p => inv hint last ⋆ newMap p) :=
  FTriple.bind (toyAlloc_spec hint last) fun p =>
    FTriple.bind (toyFree_spec hint last p) fun _ => toyAlloc_spec hint last

/-! ## The obstruction scenarios are excluded by the precondition -/

theorem Holds.sepL {m : Mem} {P Q : FAssn} {r rF : Res} (hh : Holds m r rF) (h : (P ⋆ Q) r) :
    ∃ r₁ r₂, P r₁ ∧ Q r₂ ∧ Holds m r₁ ⟨r₂.heap ∪ rF.heap, r₂.know.union rF.know, r₂.gh.add rF.gh⟩ ∧
      Holds m r₂ ⟨r₁.heap ∪ rF.heap, r₁.know.union rF.know, r₁.gh.add rF.gh⟩ := by
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  obtain ⟨hdisj, hheap, hk, hkF, hg⟩ := hh
  obtain ⟨h1F, h2F⟩ := FHeap.disjoint_union_left.mp hdisj
  refine ⟨r₁, r₂, h1, h2, ⟨FHeap.disjoint_union_right.mpr ⟨hd, h1F⟩, by
    rw [← FHeap.union_assoc]; exact hheap, hk.left, hk.right.union hkF, GOk.assoc.mp hg⟩,
    ⟨FHeap.disjoint_union_right.mpr ⟨hd.symm, h2F⟩, by
      rw [← FHeap.union_assoc, ← FHeap.union_comm hd]; exact hheap, hk.right,
      hk.left.union hkF, by rw [← GOk.assoc, Ghost.add_comm r₂.gh]; exact hg⟩⟩

/-- **O3.** A memory that holds the hint word as `apts` has no atomic location of another
offset or size over it (`docs/alloc-page.md`'s `odd` memory, with a 4-byte location at the hint,
holds no `inv`, though its heap is that of the program start). -/
theorem apts_layout {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) {p : Ptr}
    {v : BitVec 64} (hp : apts p v r) {b : BlockId} (hpb : p.block = some b) {l : ALoc}
    (hl : l ∈ m.atomics) (hb : l.block = b) (h1 : p.off.toNat < l.off + l.len)
    (h2 : l.off < p.off.toNat + 8) : l.off = p.off.toNat ∧ l.len = 8 := by
  obtain ⟨A, S, K, bs, -, -, hsz, -, hab⟩ := hp
  have hmem : ALoc.shape l ∈ shapes m :=
    List.mem_map.mpr ⟨l, Array.mem_toList_iff.mpr hl, rfl⟩
  -- a byte of the word under `l`: its location is `l`, which its constraint names
  obtain ⟨x, hx1, hx2, hcov⟩ : ∃ x, p.off.toNat ≤ x ∧ x < p.off.toNat + 8 ∧ Covers b x (ALoc.shape l) := by
    by_cases ho : p.off.toNat ≤ l.off
    · exact ⟨l.off, ho, h2, hb, Nat.le_refl _, by have := hs.2.1.1 _ hmem; simp only [ALoc.shape] at this ⊢; omega⟩
    · exact ⟨p.off.toNat, Nat.le_refl _, by omega, hb, by simp only [ALoc.shape]; omega, h1⟩
  have hc := abytesAt_cell hab hpb (l := (b, x)) ⟨rfl, hx1, by rw [hsz]; exact hx2⟩
  have hsat := hh.heap.2 (b, x) _ (by rw [FHeap.union_apply, hc]; rfl)
  have ht := tagOf_of_mem hs.2.1 hmem hcov
  simp only [TagSat, ht, reduceCtorEq, false_or, Option.some.injEq, Prod.mk.injEq] at hsat
  simpa [ALoc.shape] using hsat

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
  obtain ⟨blk, hblk, he⟩ := hh.know (.addr b A) (by rw [hk.2.1]; rfl)
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
  · obtain ⟨A, S, K, bs, hal, hbs, hdec, hbt, -⟩ :=
      upE_fix (SizeFree.pts last 8 q) (fun _ _ _ _ _ _ _ h => by cases h) hh₃ (upE_none.mpr h3)
    have hm := hh₃.fix.heap_exact hh₃.fix_exact hh₃.fix_exactF
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
  { blocks := #[⟨enc0, 8, .global, true, 4096⟩, ⟨enc1, 8, .global, true, 4112⟩] }

def hintP : Ptr := ⟨some 0, 0⟩
def lastP : Ptr := ⟨some 1, 0⟩

/-- The owned bytes of block `b` (address `A`, 8 bytes, a `var` global), with the tag
constraint `tg`. -/
def glob (b A : Nat) (bs : Array Byte) (tg : Option (Nat × Nat)) : FHeap := fun l =>
  if l.1 = b ∧ l.2 < 8 then some ⟨⟨bs[l.2]!, A, 8, .global⟩, tg⟩ else none

theorem start_fheap : start.fheap = glob 0 4096 enc0 none ∪ glob 1 4112 enc1 none := by
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

theorem glob_abytes {b A : Nat} {bs : Array Byte} {tg : Option (Nat × Nat)} (hs : bs.size = 8) :
    abytesAt ⟨some b, 0⟩ A 8 .global bs tg ⟨glob b A bs tg, Know.none, Ghost.unit⟩ := by
  refine ⟨rfl, rfl, b, rfl, Int.le_refl 0, fun ⟨x, y⟩ => ?_⟩
  simp [glob, hs]

theorem start_inv : ∃ r, Holds start r ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧ inv hintP lastP r ∧ start.FSeq := by
  have hd : FHeap.Disjoint (glob 0 4096 enc0 (some (0, 8))) (glob 1 4112 enc1 none) := by
    intro ⟨b, o⟩; by_cases hb : b = 0 <;> simp [glob, hb]
  -- no atomic location at program start: every constraint holds
  have hfm : FMatch start (glob 0 4096 enc0 (some (0, 8)) ∪ glob 1 4112 enc1 none) := by
    refine ⟨fun l => ?_, fun l fc _ => ?_⟩
    · have := (FMatch.fheap start).1 l
      rw [this, start_fheap]
      obtain ⟨b, o⟩ := l
      simp only [FHeap.union_apply, glob]
      split <;> split <;> rfl
    · cases fc.atom with
      | none => trivial
      | some t => exact .inl (by simp [shapes, start, tagOf])
  refine ⟨⟨glob 0 4096 enc0 (some (0, 8)) ∪ (glob 1 4112 enc1 none ∪ FHeap.empty),
    Know.none.union (Know.none.union Know.none), Ghost.unit.add (Ghost.unit.add Ghost.unit)⟩,
    ⟨fun _ => .inr rfl, ?_, ?_, Know.sub_none _, ?_⟩,
    ⟨⟨none, 0⟩, 0, ?_⟩, ?_⟩
  · simpa using hfm
  · simp [Know.union_none]; exact Know.sub_none _
  · simp only [Ghost.add_unit]
    exact GOk.unit _
  · refine ⟨⟨glob 0 4096 enc0 (some (0, 8)), Know.none, Ghost.unit⟩, ⟨glob 1 4112 enc1 none ∪ FHeap.empty, Know.none.union Know.none, Ghost.unit.add Ghost.unit⟩,
      by simpa using hd, rfl, ?_, ⟨glob 1 4112 enc1 none, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, Ghost.unit⟩,
      FHeap.disjoint_empty _, rfl, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨4096, 8, .global, enc0, rfl, by decide, enc0_size,
        LawfulEnc.decode_encode (α := BitVec 64) _, glob_abytes enc0_size⟩
    · refine ⟨⟨4112, 8, .global, enc1, rfl, enc1_size, LawfulEnc.decode_encode (α := Ptr) _,
        abytesAt_bytesAt (glob_abytes enc1_size), by decide⟩, rfl, rfl⟩
  · refine ⟨⟨singleThread_empty rfl (by decide)⟩, ⟨by simp [shapes, start], by simp [shapes, start]⟩, ?_, ?_⟩
    rotate_left
    · intro b blk h1 _
      rcases b with _ | _ | b <;>
        simp only [start, List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.getElem?_nil, Option.some.injEq, reduceCtorEq] at h1 <;>
        first | (subst h1; simp [enc0_size, enc1_size])
    intro b b' blk blk' hbb h1 h2 _
    rcases b with _ | _ | b <;> rcases b' with _ | _ | b' <;>
      simp only [start, List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq] at h1 h2 hbb <;>
      first | exact absurd rfl hbb | (subst h1 h2; simp [Block.clearOf, enc0_size, enc1_size])

/-- So the specs are not vacuous: at program start the allocator invariant holds, and
`cycle_spec` applies to the real run (alloc, free, alloc). -/
theorem cycle_from_start {p : Ptr} {m' : Mem}
    (h : ((cycle hintP lastP).run start).run = some (.ok (p, m'))) :
    ∃ r', Holds m' r' ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧ (inv hintP lastP ⋆ newMap p) r' ∧ m'.FSeq := by
  obtain ⟨r, hh, hi, hs⟩ := start_inv
  have := cycle_spec hintP lastP start r _ hh hi hs
  rw [h] at this
  exact this

end Toy

end Full
end Zig
