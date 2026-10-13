import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Tame
import ZigLean.Sep.Full.ThreadStep
import ZigLean.Mem.Reuse

/-!
# Total full-state rules for the pointer operations of generated code

Native rules (no legacy lifting) for `@intFromPtr` (`ptrAddr`), the model's `@alignCast` check
(`checkAlign`), pointer `==` (`ptrEqAddr`), pointer formation (`ptrProject`), and the byte
operations on owned bytes `bytesAt`: `loadBytes_bytesAt`, `load_bytesAt`, `storeBytes_bytesAt`,
`store_bytesAt`, `memset_bytesAt`, `memmove_bytesAt` (from `Holds.bytesAt_block`, what the
memory has under owned bytes, and `Holds.write`, a write to owned bytes), with `load`/`store`
of `pts` on top. Every typed and region rule (`Typed`, `Try`, `Region`, `AutoPrim`) is one of
these with its labels (`FTotalTriple.of_cases`). A rule takes what it needs of the memory from a
**provider**, a property of every memory that holds the precondition:

* `AddrOf b A P`: block `b` exists at address `A`. Knowledge gives it (`AddrOf.known`), and so
  does an owned cell (`AddrOf.owned`).
* `Reaches b k P`: block `b` exists with at least `k` bytes. An owned byte `j` gives `j + 1`
  (`Reaches.owned`): in-bounds facts come from ownership. A share of the block's extent at bound
  `k` gives `k` (`Reaches.share`): a pointer up to a bound that the program owns no byte below,
  such as a fixed buffer's end when every byte is lent out.

The providers frame (`AddrOf.sepL`, `Reaches.sepL`, and the `…R` versions).
-/

namespace Zig

/-- An aligned part: byte `o` of an `a`-aligned address is `b`-aligned if `b` divides `a` and `o`. -/
theorem mod_add_dvd {A x : Nat} (ha : (A + x) % a = 0) (hb : b ∣ a) (ho : b ∣ o) :
    (A + x + o) % b = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hb (Nat.dvd_of_mod_eq_zero ha)) ho)

namespace Full

open FAssn

/-! ## Providers -/

/-- Every memory that holds `P` has block `b` at address `A`. -/
def AddrOf (b : BlockId) (A : Nat) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ blk, m.blocks[b]? = some blk ∧ blk.addr = A

/-- Every memory that holds `P` has block `b` with at least `k` bytes. -/
def Reaches (b : BlockId) (k : Nat) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ blk, m.blocks[b]? = some blk ∧ k ≤ blk.bytes.size

section Providers

variable {b : BlockId} {A k : Nat} {P R : FAssn}

theorem AddrOf.sepL (h : AddrOf b A P) : AddrOf b A (P ⋆ R) := fun m _ rF hh hp => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1

theorem AddrOf.sepR (h : AddrOf b A P) : AddrOf b A (R ⋆ P) := fun m r rF hh hp =>
  h.sepL m r rF hh (sep_comm hp)

theorem AddrOf.of_imp {P' : FAssn} (h : AddrOf b A P) (hp : ∀ r, P' r → P r) : AddrOf b A P' :=
  fun m r rF hh h' => h m r rF hh (hp r h')

theorem AddrOf.known : AddrOf b A (known b A) := fun _ _ _ hh hp =>
  hh.know (.addr b A) (by rw [hp.2.1]; rfl)

/-- An owned cell of block `b` gives its address. -/
theorem AddrOf.owned (h : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A) :
    AddrOf b A P := fun _ r _ hh hp => by
  obtain ⟨x, fc, hx, rfl⟩ := h r hp
  obtain ⟨blk, hb, -, -, -, ha, -⟩ := hh.block hx
  exact ⟨blk, hb, ha.symm⟩

theorem Reaches.sepL (h : Reaches b k P) : Reaches b k (P ⋆ R) := fun m _ rF hh hp => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1

theorem Reaches.sepR (h : Reaches b k P) : Reaches b k (R ⋆ P) := fun m r rF hh hp =>
  h.sepL m r rF hh (sep_comm hp)

theorem Reaches.of_imp {P' : FAssn} (h : Reaches b k P) (hp : ∀ r, P' r → P r) : Reaches b k P' :=
  fun m r rF hh h' => h m r rF hh (hp r h')

theorem Reaches.mono {k' : Nat} (h : Reaches b k P) (hk : k' ≤ k) : Reaches b k' P :=
  fun m r rF hh hp => by obtain ⟨blk, hb, hs⟩ := h m r rF hh hp; exact ⟨blk, hb, by omega⟩

/-- An owned byte `j` of block `b`: the block has more than `j` bytes. -/
theorem Reaches.owned {j : Nat} (h : ∀ r, P r → ∃ fc, r.heap (b, j) = some fc) :
    Reaches b (j + 1) P := fun _ r _ hh hp => by
  obtain ⟨fc, hx⟩ := h r hp
  obtain ⟨blk, hb, -, hj, -⟩ := hh.block hx
  exact ⟨blk, hb, hj⟩

/-- A share of block `b`'s extent at bound `k`. -/
theorem Reaches.share {q : Frac} : Reaches b k (bshare b q k) := fun _ r _ hh hp => by
  obtain ⟨blk, hb, -, hk, -⟩ := hh.bshare (R := emp) (sep_emp.mpr hp)
  exact ⟨blk, hb, hk⟩

end Providers

/-- Owned cells of a legacy assertion: a cell of the erased heap is a cell of the resource. -/
theorem erase_cell {h : FHeap} {l : Loc} {c : Cell} (hc : h.erase l = some c) :
    ∃ fc, h l = some fc ∧ fc.cell = c := by
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  exact hc

/-- `Holds` reads a memory only through its blocks and its atomic layout. -/
theorem Holds.congrMem {m m' : Mem} {r rF : Res} (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hh : Holds m r rF) : Holds m' r rF := by
  have e1 : m'.heap = m.heap := by funext ⟨x, o⟩; simp only [Mem.heap, hb]
  have e2 : shapes m' = shapes m := by simp only [shapes, ha]
  have e3 : m'.kn = m.kn := by funext f; cases f <;> simp only [Mem.kn, hb]
  obtain ⟨hd, hm, hk, hkF, hg, ht, hcf⟩ := hh
  refine ⟨hd, ?_, e3 ▸ hk, e3 ▸ hkF, hg, fun x => ?_, fun x hx => hcf x (by rw [← hb]; exact hx)⟩
  · unfold FMatch; rw [e1, e2]; exact hm
  · have := ht x; unfold ECell.TrueIn at this ⊢; simpa only [hb] using this

/-! ## Every triple holds under every placement (M05, `ZigLean/Mem/Reuse.lean`) -/

/-- A memory with another placement and provenance mode holds the same resources. -/
theorem Holds.withPlacement {m : Mem} {r rF : Res} (hh : Holds m r rF) (σ : Placement)
    (pm : ProvenanceMode) : Holds (m.withPlacement σ pm) r rF :=
  Holds.congrMem (m := m) rfl rfl hh

theorem _root_.Zig.Mem.FSeq.withPlacement {m : Mem} (hs : m.FSeq) (σ : Placement)
    (pm : ProvenanceMode) : (m.withPlacement σ pm).FSeq :=
  ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩

/-- **A full-state triple holds from a memory with any placement and provenance mode** (the frame
rule, the allocation and free rules and every client spec built from them are
address-independent): a triple quantifies over every `Mem.FSeq` memory, whatever its placement. -/
theorem FTriple.withPlacement {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq)
    (σ : Placement) (pm : ProvenanceMode) :
    match (c.run (m.withPlacement σ pm)).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq :=
  ht _ r rF (hh.withPlacement σ pm) hp (hs.withPlacement σ pm)

/-- **A total full-state triple returns from a memory with any placement and provenance mode**,
with its postcondition. -/
theorem FTotalTriple.withPlacement {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTotalTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) (hs : m.FSeq)
    (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' r', c.run (m.withPlacement σ pm) = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq := by
  obtain ⟨v, m', hr⟩ := ht.2 _ r rF (hh.withPlacement σ pm) hp (hs.withPlacement σ pm)
  have h := ht.1.withPlacement hh hp hs σ pm
  rw [hr] at h
  obtain ⟨r', hh', hq, hs'⟩ := h
  exact ⟨v, m', r', hr, hh', hq, hs'⟩

/-! ## Owned bytes (`docs/sep-full-state.md`)

What the memory has where a resource owns the bytes `bytesAt p A S K bs`, and how a write
changes a resource. The load and store rules below are proved from these on `Holds` directly
(no legacy lifting). A cell of `bytesAt` records its block's size and kind as labels: the memory
matches them only up to `Cell.norm` (`FMatch`), so the rules keep every label as it is. -/

section OwnedBytes

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}

/-- Byte `j` of owned bytes `bytesAt p A S K bs` is a cell of the resource. -/
theorem up_bytesAt_cell {r : Res} {b : BlockId} (hp : up (bytesAt p A S K bs) r)
    (hpb : p.block = some b) {j : Nat} (hj : j < bs.size) :
    ∃ fc, r.heap (b, p.off.toNat + j) = some fc ∧ fc.cell = ⟨bs[j]!, A, S, K⟩ := by
  obtain ⟨⟨b', hb', -, hl⟩, -, -⟩ := hp
  rw [hpb] at hb'; cases hb'
  have e := hl (b, p.off.toNat + j)
  rw [ite_eq_left ⟨rfl, by omega, by omega⟩, Nat.add_sub_cancel_left] at e
  exact erase_cell e

/-- **The block of owned bytes** (`0 < bs.size`): live, at address `A`, of a kind with `K`'s
normal form, with the bytes `bs` at `p`, at or above its first live offset. -/
theorem Holds.bytesAt_block {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : up (bytesAt p A S K bs) r) (hpos : 0 < bs.size) :
    ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live = true ∧ 0 ≤ p.off ∧
      blk.kind.mappedLo ≤ p.off.toNat ∧ p.off.toNat + bs.size ≤ blk.bytes.size ∧ blk.addr = A ∧
      blk.kind.norm = K.norm ∧
      blk.bytes.extract p.off.toNat (p.off.toNat + bs.size) = bs := by
  obtain ⟨b, hpb, h0, -⟩ := hp.1
  have cell : ∀ j (hj : j < bs.size), ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      blk.kind.mappedLo ≤ p.off.toNat + j ∧ blk.addr = A ∧ blk.kind.norm = K.norm ∧
      blk.bytes[p.off.toNat + j]? = some bs[j] := by
    intro j hj
    obtain ⟨fc, hfc, hc⟩ := up_bytesAt_cell hp hpb hj
    obtain ⟨blk, hb, hl, -, hlo, ha, hk⟩ := hh.block hfc
    obtain ⟨c', hc', hn⟩ := hh.cellN hfc
    obtain ⟨blk', hb', -, hx', rfl⟩ := Mem.heap_some hc'
    rw [hb] at hb'; cases hb'
    have hbyte := congrArg Cell.byte hn
    simp only [Cell.norm, hc] at hbyte ha hk
    refine ⟨blk, hb, hl, hlo, ha.symm, hk.symm, ?_⟩
    rw [Array.getElem?_eq_getElem hx', hbyte, getElem!_pos bs j hj]
  obtain ⟨blk, hb, hl, hlo, ha, hk, -⟩ := cell 0 hpos
  obtain ⟨blk', hb', -, -, -, -, hlast⟩ := cell (bs.size - 1) (by omega)
  rw [hb] at hb'; cases hb'
  have hlt := (Array.getElem?_eq_some_iff.mp hlast).1
  refine ⟨b, blk, hpb, hb, hl, h0, by simpa using hlo, by omega, ha, hk, ?_⟩
  apply Array.ext
  · simp only [Array.size_extract]; omega
  · intro j h1 h2
    obtain ⟨blk', hb', -, -, -, -, hx⟩ := cell j h2
    rw [hb] at hb'; cases hb'
    simp only [Array.getElem_extract]
    exact (Array.getElem?_eq_some_iff.mp hx).2

/-- An access to `n > 0` of the owned bytes, from byte `k` on, with an aligned address: it
succeeds in the bytes' block and sees them. -/
theorem Holds.bytesAt_access {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : up (bytesAt p A S K bs) r) {k n al : Nat} (hn : 0 < n) (hk : k + n ≤ bs.size)
    (ha : (A + p.off.toNat + k) % al = 0) :
    ∃ b blk, m.access (p.add k) n al = pure (b, blk, p.off.toNat + k) ∧
      m.blocks[b]? = some blk ∧ blk.kind.norm = K.norm ∧
      blk.bytes.extract (p.off.toNat + k) (p.off.toNat + k + n) = bs.extract k (k + n) := by
  obtain ⟨b, blk, hpb, hb, hl, h0, hlo, hfit, hA, hK, hx⟩ := hh.bytesAt_block hp (by omega)
  have e : (p.add k).off.toNat = p.off.toNat + k := by simp only [Ptr.add]; omega
  refine ⟨b, blk, ?_, hb, hK, ?_⟩
  · have := access_of (m := m) (p := p.add k) (n := n) (a := al) (by simpa using hpb) hb hl
      (by simp only [Ptr.add]; omega) (by simp only [Ptr.add]; omega)
      (by rw [e, hA, ← Nat.add_assoc]; exact ha) (by rw [e]; omega)
    rwa [e] at this
  · rw [← hx, Array.extract_extract]
    congr 1 <;> omega

/-- The resource after a write of `bs'` at byte `o` of block `b`: its cells there hold the new
bytes, with their labels and tags. -/
def Res.writeAt (r : Res) (b : BlockId) (o : Nat) (bs' : Array Byte) : Res :=
  { r with heap := fun l => if l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + bs'.size then
      (r.heap l).map fun fc => { fc with cell := { fc.cell with byte := bs'[l.2 - o]! } }
    else r.heap l }

/-- **A write to owned bytes** (`Mem.write`): the memory after it holds the written resource
(`Res.writeAt`) with the same frame. The written bytes are the resource's, in a live block that
is not a `const` global; the frame, the knowledge and the ghost state stay true (the write keeps
every block's address, liveness, size and kind). -/
theorem Holds.write {m : Mem} {r rF : Res} {b : BlockId} {blk : Block} {o : Nat}
    {bs' : Array Byte} (hh : Holds m r rF) (hb : m.blocks[b]? = some blk) (hl : blk.live = true)
    (hn : o + bs'.size ≤ blk.bytes.size) (hlo : blk.kind.mappedLo ≤ o)
    (hK : blk.kind ≠ .constGlobal) (hown : ∀ i, i < bs'.size → r.heap (b, o + i) ≠ none) :
    Holds (m.write b blk o bs') (r.writeAt b o bs') rF := by
  have hkm : KMono m (m.write b blk o bs') :=
    KMono.set (blk' := { blk with bytes := writeBytes blk.bytes o bs' }) hb rfl hK rfl
  have hin : ∀ l : Loc, l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + bs'.size → r.heap l ≠ none := by
    rintro ⟨x, y⟩ ⟨rfl, h1, h2⟩
    have := hown (y - o) (by omega)
    rwa [show o + (y - o) = y by omega] at this
  refine ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩, hh.know.trans hkm, hh.knowF.trans hkm,
    hh.ghost.keep (KeepsExt.set (nb := { blk with bytes := writeBytes blk.bytes o bs' }) hb rfl
      (writeBytes_size _ _ _ hn) rfl rfl)
      (by simp [Mem.write])⟩
  · -- disjoint: the same cells as `r`
    rcases hh.disj l with e | e
    · left; simp only [Res.writeAt, e, Option.map_none, ite_self]
    · exact .inr e
  · -- the cells up to `Cell.norm`
    rw [Mem.heap_write hb hl hn hlo l]
    by_cases hc : l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + bs'.size
    · obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp (hin l hc)
      obtain ⟨blk', hb', -, -, -, ha, hk⟩ := hh.block (b := l.1) (x := l.2) hfc
      rw [hc.1, hb] at hb'; cases hb'
      simp only [ite_eq_left hc, FHeap.union_apply, Res.writeAt, hfc, Option.map_some, Option.some_or,
        Cell.norm, ha, hk]
    · have hF := hh.heap.1 l
      simp only [ite_eq_right hc, FHeap.union_apply, Res.writeAt] at hF ⊢
      exact hF
  · -- tags: the layout and every cell's tag stay
    show TagSat (shapes m) l.1 l.2 fc.atom
    simp only [FHeap.union_apply, Res.writeAt] at hfc
    split at hfc
    · cases e : r.heap l with
      | none => rw [e, Option.map_none, Option.none_or] at hfc; exact hh.tagF hfc
      | some fc₀ =>
        rw [e, Option.map_some, Option.some_or, Option.some.injEq] at hfc
        subst hfc
        exact hh.heap.2 l fc₀ (by simp [e])
    · exact hh.heap.2 l fc hfc

/-- Owned bytes after a write of `bs'` at byte `k` of them: `writeBytes bs k bs'`. -/
theorem up_bytesAt_writeAt {r : Res} {b : BlockId} {k : Nat} {bs' : Array Byte}
    (hp : up (bytesAt p A S K bs) r) (hpb : p.block = some b) (hk : k + bs'.size ≤ bs.size) :
    up (bytesAt p A S K (writeBytes bs k bs')) (r.writeAt b (p.off.toNat + k) bs') := by
  obtain ⟨⟨b', hb', h0, hl⟩, hkn, hg⟩ := hp
  rw [hpb] at hb'; cases hb'
  refine ⟨⟨b, hpb, h0, fun l => ?_⟩, hkn, hg⟩
  have e := hl l
  have hs := writeBytes_size bs k bs' hk
  simp only [FHeap.erase, Res.writeAt] at e ⊢
  rw [hs]
  by_cases hc : l.1 = b ∧ p.off.toNat + k ≤ l.2 ∧ l.2 < p.off.toNat + k + bs'.size
  · have hin : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size :=
      ⟨hc.1, by omega, by omega⟩
    rw [ite_eq_left hin] at e
    rw [ite_eq_left hc, ite_eq_left hin, writeBytes_getElem! bs k bs' hk,
      ite_eq_left (by omega : k ≤ l.2 - p.off.toNat ∧ l.2 - p.off.toNat < k + bs'.size)]
    cases e' : r.heap l with
    | none => rw [e'] at e; cases e
    | some fc =>
      rw [e'] at e
      simp only [Option.map_some, Option.some.injEq] at e ⊢
      rw [e, show l.2 - (p.off.toNat + k) = l.2 - p.off.toNat - k by omega]
  · rw [ite_eq_right hc, e]
    by_cases hin : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    · rw [ite_eq_left hin, ite_eq_left hin, writeBytes_getElem! bs k bs' hk,
        ite_eq_right (fun h => hc ⟨hin.1, by omega, by omega⟩ :
          ¬ (k ≤ l.2 - p.off.toNat ∧ l.2 - p.off.toNat < k + bs'.size))]
    · rw [ite_eq_right hin, ite_eq_right hin]

end OwnedBytes

/-- **A total triple in one memory**: the run returns, with the postcondition. -/
theorem FTotalTriple.runs {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (ht : FTotalTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r)
    (hs : m.FSeq) : ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq := by
  obtain ⟨v, m', hr⟩ := ht.2 m r rF hh hp hs
  have h := ht.1 m r rF hh hp hs
  rw [hr] at h
  obtain ⟨r', hh', hq, hs'⟩ := h
  exact ⟨v, m', r', hr, hh', hq, hs'⟩

/-- A step that runs as `c'` from a memory `m'` that holds the same resources (for example the
memory after a bookkeeping step that changes no block) has the triple of `c'`. -/
theorem FTotalTriple.of_runEq {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (h : ∀ m r rF, Holds m r rF → P r → m.FSeq →
      ∃ (c' : MemM α) (m' : Mem), c.run m = c'.run m' ∧ Holds m' r rF ∧ m'.FSeq ∧ FTotalTriple P c' Q) :
    FTotalTriple P c Q := by
  refine ⟨fun m r rF hh hp hs => ?_, fun m r rF hh hp hs => ?_⟩ <;>
    obtain ⟨c', m', e, hh', hs', ht⟩ := h m r rF hh hp hs <;> rw [e]
  · exact ht.1 m' r rF hh' hp hs'
  · exact ht.2 m' r rF hh' hp hs'

/-! ## Rules -/

namespace FTotalTriple

variable {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FSeq →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq) :
    FTotalTriple P c Q :=
  ⟨FTriple.of_run h, fun m r rF hh hp hs => by
    obtain ⟨v, m', -, hr, -⟩ := h m r rF hh hp hs; exact ⟨v, m', hr⟩⟩

/-- A step that returns `v` and leaves the memory as it is. -/
theorem of_read {v : α} (h : ∀ m r rF, Holds m r rF → P r → m.FSeq → c.run m = pure (v, m)) :
    FTotalTriple P c (fun x => ⟪x = v⟫ ⋆ P) :=
  of_run fun m r rF hh hp hs => ⟨v, m, r, h m r rF hh hp hs, hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

/-- **A triple by cases of the precondition**: every resource of `P` is one of `P' i`, and the
post of that case gives `Q` (an assertion with existential labels, such as `pts` over
`bytesAt`, takes the rule of its labels). -/
theorem of_cases
    (h : ∀ r, P r → ∃ (P₀ : FAssn) (Q₀ : α → FAssn), FTotalTriple P₀ c Q₀ ∧ P₀ r ∧
      ∀ v r', Q₀ v r' → Q v r') : FTotalTriple P c Q :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨P₀, Q₀, ht, hi, hq⟩ := h r hp
    obtain ⟨v, m', r', hr, hh', h', hs'⟩ := ht.runs hh hi hs
    exact ⟨v, m', r', hr, hh', hq v r' h', hs'⟩

variable {q : Ptr}

/-! ### Loads and stores of owned bytes (native) -/

section OwnedBytes

variable {A S k al : Nat} {K : BlockKind} {bs : Array Byte}

/-- The memory after a recorded access holds what the memory held. -/
theorem _root_.Zig.Full.Holds.recordAt {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (b : BlockId) (o n : Nat) (kd : AccessKind) : Holds (m.recordAt b o n kd) r rF :=
  Holds.congrMem (m := m) rfl rfl hh

theorem _root_.Zig.Mem.FSeq.recordAt' {m : Mem} (hs : m.FSeq) (b : BlockId) (o n : Nat)
    (kd : AccessKind) : (m.recordAt b o n kd).FSeq :=
  ⟨hs.1.recordAt _ _ _ _, hs.2.1, hs.2.2⟩

/-- **Read of `n` owned bytes** from byte `k` on: they stay. -/
theorem loadBytes_bytesAt {n : Nat} (hn : 0 < n) (hk : k + n ≤ bs.size)
    (ha : (A + q.off.toNat + k) % al = 0) :
    FTotalTriple (up (bytesAt q A S K bs)) (Zig.loadBytes (q.add k) n al)
      (fun x => ⟪x = bs.extract k (k + n)⟫ ⋆ up (bytesAt q A S K bs)) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, -, -, hx⟩ := hh.bytesAt_access hp hn hk ha
    exact ⟨_, _, r, loadBytes_run hacc (noRace_of_singleThread hs.1.single _ _ _ _),
      hh.recordAt _ _ _ _, sep_lift.mpr ⟨hx, hp⟩, hs.recordAt' _ _ _ _⟩

/-- **Load of a `T`** at byte `k` of owned bytes that decode to `v` there. -/
theorem load_bytesAt {T : Type} [Enc T] {v : T} (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    FTotalTriple (up (bytesAt q A S K bs)) (Zig.load T al (q.add k))
      (fun x => ⟪x = v⟫ ⋆ up (bytesAt q A S K bs)) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, -, -, hx⟩ := hh.bytesAt_access hp hn hk ha
    exact ⟨v, _, r, load_run hacc (by rw [hx]; exact hv)
      (noRace_of_singleThread hs.1.single _ _ _ _), hh.recordAt _ _ _ _, sep_lift.mpr ⟨rfl, hp⟩,
      hs.recordAt' _ _ _ _⟩

/-- **Store of the bytes `bs'`** at byte `k` of owned bytes, not of a `const` global: the bytes
become `writeBytes bs k bs'`. -/
theorem storeBytes_bytesAt {bs' : Array Byte} (hn : 0 < bs'.size) (hk : k + bs'.size ≤ bs.size)
    (ha : (A + q.off.toNat + k) % al = 0) (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt q A S K bs)) (Zig.storeBytes (q.add k) al bs')
      (fun _ => up (bytesAt q A S K (writeBytes bs k bs'))) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, hb, hKn, -⟩ := hh.bytesAt_access hp hn hk ha
    obtain ⟨hpb, -, hl, -, hfit, -, -⟩ := access_eq hacc
    have hlo := access_lo hacc
    have hK' : blk.kind ≠ .constGlobal := fun e => hK (by
      have h : K.norm = .constGlobal := by rw [← hKn, e]; rfl
      cases K <;> simp_all [BlockKind.norm])
    have hrun := storeBytes_run (kind := .write) hacc hK' (noRace_of_singleThread hs.1.single _ _ _ _)
    have hpb' : q.block = some b := by simpa using hpb
    obtain ⟨-, -, h0, -⟩ := hp.1
    have hfit' : q.off.toNat + k + bs'.size ≤ blk.bytes.size := by
      simp only [Ptr.add] at hfit; omega
    refine ⟨(), _, _, hrun, (hh.recordAt _ _ _ _).write hb hl hfit' hlo hK' fun i hi => ?_,
      up_bytesAt_writeAt hp hpb' hk, ?_⟩
    · obtain ⟨fc, hfc, -⟩ := up_bytesAt_cell hp hpb' (j := k + i) (by omega)
      rw [← Nat.add_assoc] at hfc; rw [hfc]; simp
    · exact ⟨⟨singleThread_write (singleThread_recordAt hs.1.single _ _ _ _) _ _ _ _⟩, hs.2.1,
        (LDMono.set (nb := { blk with bytes := writeBytes blk.bytes (q.off.toNat + k) bs' }) hb id
          rfl (by simp only; rw [writeBytes_size _ _ _ hfit']; exact Nat.le_refl _) rfl) hs.2.2⟩

/-- **Store of a `T`** at byte `k` of owned bytes, not of a `const` global. -/
theorem store_bytesAt {T : Type} [Enc T] (w : T) (hn : 0 < (Enc.encode w).size)
    (hk : k + (Enc.encode w).size ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt q A S K bs)) (Zig.store al (q.add k) w)
      (fun _ => up (bytesAt q A S K (writeBytes bs k (Enc.encode w)))) :=
  storeBytes_bytesAt hn hk ha hK

theorem _root_.Zig.writeBytes_empty {a : Array Byte} {o : Nat} (h : o ≤ a.size) :
    writeBytes a o #[] = a := by
  simp [writeBytes, Array.extract_append_extract, Nat.max_eq_right h]

/-- The bytes `@memset(_, v)` writes for `n` items: `n` copies of `v`'s bytes, or undefined
bytes. -/
def _root_.Zig.memsetBytes {α : Type} [Enc α] (n : Nat) (v : Option α) : Array Byte :=
  (Array.replicate n (match v with
    | some x => Enc.encode x
    | none => Array.replicate (Enc.size α) .undef)).flatten

/-- **`@memset`** of `n` items at byte `k` of owned bytes, not of a `const` global: the bytes
there become `memsetBytes n v` (`hsz`: `v`'s bytes have the item size, which `LawfulEnc` and
undefined bytes give). -/
theorem memset_bytesAt {α : Type} [Enc α] {n : BitVec 64} {v : Option α}
    (hsz : (memsetBytes n.toNat v).size = n.toNat * Enc.size α)
    (hk : k + n.toNat * Enc.size α ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt q A S K bs)) (Zig.memset al (q.add k) n v)
      (fun _ => up (bytesAt q A S K (writeBytes bs k (memsetBytes n.toNat v)))) := by
  by_cases h0 : n.toNat = 0 ∨ Enc.size α = 0
  · have e : memsetBytes n.toNat v = #[] := Array.eq_empty_of_size_eq_zero (by
      rw [hsz]; rcases h0 with h | h <;> simp [h])
    rw [e, writeBytes_empty (by omega)]
    exact of_run fun m r rF hh hp hs =>
      ⟨(), m, r, by simp [Zig.memset, h0, zig_unfold], hh, hp, hs⟩
  have hpos : 0 < n.toNat * Enc.size α := Nat.mul_pos (by omega) (by omega)
  refine of_runEq fun m r rF hh hp hs => ⟨_, m, ?_, hh, hs,
    storeBytes_bytesAt (bs' := memsetBytes n.toNat v) (by omega) (by omega) ha hK⟩
  obtain ⟨b, blk, hacc, -⟩ := hh.bytesAt_access hp hpos hk ha
  cases v <;> simp [Zig.memset, h0, zig_unfold, hacc, memsetBytes]

/-- **`@memmove`** of `n` items of `sz` bytes from byte `j` of the owned bytes `bsrc` to byte `k`
of the separately owned bytes `bd`, not of a `const` global. -/
theorem memmove_bytesAt {d s : Ptr} {A' S' sz da sa j : Nat} {K' : BlockKind} {bd bsrc : Array Byte}
    {n : BitVec 64} (hkd : k + n.toNat * sz ≤ bd.size) (hjs : j + n.toNat * sz ≤ bsrc.size)
    (had : (A + d.off.toNat + k) % da = 0) (has : (A' + s.off.toNat + j) % sa = 0)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt d A S K bd) ⋆ up (bytesAt s A' S' K' bsrc))
      (Zig.memmove sz da sa (d.add k) (s.add j) n)
      (fun _ => up (bytesAt d A S K (writeBytes bd k (bsrc.extract j (j + n.toNat * sz)))) ⋆
        up (bytesAt s A' S' K' bsrc)) := by
  by_cases h0 : n.toNat = 0 ∨ sz = 0
  · have e : n.toNat * sz = 0 := by rcases h0 with h | h <;> simp [h]
    rw [e, Nat.add_zero, show bsrc.extract j j = #[] from Array.eq_empty_of_size_eq_zero (by simp; omega),
      writeBytes_empty (by omega)]
    exact of_run fun m r rF hh hp hs =>
      ⟨(), m, r, by simp [Zig.memmove, h0, zig_unfold], hh, hp, hs⟩
  have hpos : 0 < n.toNat * sz := Nat.mul_pos (by omega) (by omega)
  have hsz : (bsrc.extract j (j + n.toNat * sz)).size = n.toNat * sz := by
    simp only [Array.size_extract]; omega
  have ht : FTotalTriple (up (bytesAt d A S K bd) ⋆ up (bytesAt s A' S' K' bsrc))
      (Zig.loadBytes (s.add j) (n.toNat * sz) sa >>= fun x => Zig.storeBytes (d.add k) da x)
      (fun _ => up (bytesAt d A S K (writeBytes bd k (bsrc.extract j (j + n.toNat * sz)))) ⋆
        up (bytesAt s A' S' K' bsrc)) := by
    refine bind (((loadBytes_bytesAt (q := s) (S := S') (K := K') hpos hjs has).frame
        (R := up (bytesAt d A S K bd))).pre fun _ h => sep_comm h) fun x => ?_
    refine pre (P := ⟪x = bsrc.extract j (j + n.toNat * sz)⟫ ⋆
      (up (bytesAt d A S K bd) ⋆ up (bytesAt s A' S' K' bsrc))) (lift fun hx => ?_) fun r h => ?_
    · subst hx
      exact (storeBytes_bytesAt (q := d) (S := S) (K := K) (by omega) (by omega) had hK).frame
    · obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
      obtain ⟨hx, h1⟩ := sep_lift.mp h1
      exact sep_lift.mpr ⟨hx, sep_comm ⟨r₁, r₂, hd, rfl, h1, h2⟩⟩
  refine of_runEq fun m r rF hh hp hs => ⟨_, m, ?_, hh, hs, ht⟩
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  obtain ⟨b, blk, hacc, -⟩ := (Holds.split hd hh).bytesAt_access h1 hpos hkd had
  simp [Zig.memmove, h0, zig_unfold, hacc]

/-- **`@memmove`** of `n` items of `sz` bytes from byte `j` to byte `k` of the same owned bytes,
not of a `const` global: the ranges may overlap (the bytes are read before they are written). -/
theorem memmove_bytesAt_self {sz da sa j : Nat} {n : BitVec 64}
    (hkd : k + n.toNat * sz ≤ bs.size) (hjs : j + n.toNat * sz ≤ bs.size)
    (had : (A + q.off.toNat + k) % da = 0) (has : (A + q.off.toNat + j) % sa = 0)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt q A S K bs)) (Zig.memmove sz da sa (q.add k) (q.add j) n)
      (fun _ => up (bytesAt q A S K (writeBytes bs k (bs.extract j (j + n.toNat * sz))))) := by
  by_cases h0 : n.toNat = 0 ∨ sz = 0
  · have e : n.toNat * sz = 0 := by rcases h0 with h | h <;> simp [h]
    rw [e, Nat.add_zero, show bs.extract j j = #[] from Array.eq_empty_of_size_eq_zero (by simp; omega),
      writeBytes_empty (by omega)]
    exact of_run fun m r rF hh hp hs =>
      ⟨(), m, r, by simp [Zig.memmove, h0, zig_unfold], hh, hp, hs⟩
  have hpos : 0 < n.toNat * sz := Nat.mul_pos (by omega) (by omega)
  have ht : FTotalTriple (up (bytesAt q A S K bs))
      (Zig.loadBytes (q.add j) (n.toNat * sz) sa >>= fun x => Zig.storeBytes (q.add k) da x)
      (fun _ => up (bytesAt q A S K (writeBytes bs k (bs.extract j (j + n.toNat * sz))))) :=
    bind (loadBytes_bytesAt hpos hjs has) fun _ => lift fun hx => by
      subst hx
      exact storeBytes_bytesAt (by simp only [Array.size_extract]; omega)
        (by simp only [Array.size_extract]; omega) had hK
  refine of_runEq fun m r rF hh hp hs => ⟨_, m, ?_, hh, hs, ht⟩
  obtain ⟨b, blk, hacc, -⟩ := hh.bytesAt_access hp hpos hkd had
  simp [Zig.memmove, h0, zig_unfold, hacc]

end OwnedBytes

/-- An owned typed value is owned bytes that decode to it (`pts`). -/
theorem up_pts_iff_bytesAt {T : Type} [Enc T] {a : Nat} {v : T} {r : Res} :
    up (pts q a v) r ↔ ∃ A S K bs, ((A + q.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧
      Enc.decode bs = pure v ∧ K ≠ .constGlobal) ∧ up (bytesAt q A S K bs) r :=
  ⟨fun ⟨⟨A, S, K, bs, ha, hs, hv, hb, hK⟩, hk, hg⟩ => ⟨A, S, K, bs, ⟨ha, hs, hv, hK⟩, hb, hk, hg⟩,
    fun ⟨A, S, K, bs, ⟨ha, hs, hv, hK⟩, hb, hk, hg⟩ => ⟨⟨A, S, K, bs, ha, hs, hv, hb, hK⟩, hk, hg⟩⟩

/-- **Load** of a typed value (`pts`). -/
theorem load {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (up (pts q a v)) (Zig.load T a q) (fun x => ⟪x = v⟫ ⋆ up (pts q a v)) := by
  refine of_cases fun r hp => ?_
  obtain ⟨A, S, K, bs, ⟨ha, hsz, hv, hK⟩, hb⟩ := up_pts_iff_bytesAt.mp hp
  have t := load_bytesAt (q := q) (k := 0) (al := a) (A := A) (S := S) (K := K) (bs := bs) hn
    (by omega) (by simpa using ha) (by rw [Nat.zero_add, ← hsz, Array.extract_size]; exact hv)
  simp only [Int.natCast_zero, Ptr.add_zero] at t
  refine ⟨_, _, t, hb, fun x r' h => ?_⟩
  obtain ⟨hx, hb'⟩ := sep_lift.mp h
  exact sep_lift.mpr ⟨hx, up_pts_iff_bytesAt.mpr ⟨A, S, K, bs, ⟨ha, hsz, hv, hK⟩, hb'⟩⟩

/-- **Store** of a typed value (`pts`). -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) (w : T) :
    FTotalTriple (up (pts q a v)) (Zig.store a q w) (fun _ => up (pts q a w)) := by
  refine of_cases fun r hp => ?_
  obtain ⟨A, S, K, bs, ⟨ha, hsz, -, hK⟩, hb⟩ := up_pts_iff_bytesAt.mp hp
  have hw := LawfulEnc.size_encode w
  have t := store_bytesAt (q := q) (k := 0) (al := a) (A := A) (S := S) (K := K) (bs := bs) w
    (by omega) (by omega) (by simpa using ha) hK
  simp only [Int.natCast_zero, Ptr.add_zero, writeBytes_all (hw.trans hsz.symm)] at t
  exact ⟨_, _, t, hb, fun _ _ h => up_pts_iff_bytesAt.mpr
    ⟨A, S, K, _, ⟨ha, hw, LawfulEnc.decode_encode w, hK⟩, h⟩⟩

end FTotalTriple

/-! ## Thread rules

Each rule below holds in a thread (`FTTotalTriple`, `ZigLean/Sep/Full/ThreadStep.lean`): a read
that leaves the memory as it is (`FTTotalTriple.of_read`), or a sequential triple of an owned
access (`FTTotalTriple.ofSeq`, `ThreadLocal.load`/`store`; `fsym` makes these from the
sequential rules itself, `Full/AutoThread.lean`). The sequential pointer rules (next section) are
these rules read sequentially (`FTTotalTriple.toFTotalTriple`). -/

/-- The bytes of `pts` at `q`. -/
theorem OwnsPtr.pts {T : Type} [Enc T] {q : Ptr} {a : Nat} {v : T} :
    OwnsPtr (up (Zig.pts q a v)) q (Enc.size T) := by
  rintro b hqb r ⟨⟨A, S, K, bs, -, hs, -, hb, -⟩, -, -⟩
  rw [← hs]; exact bytesAt_has hb hqb

namespace FTTotalTriple

variable {α : Type} {P : FAssn} {q p : Ptr} {b : BlockId} {A K : Nat}

/-- **`@intFromPtr`** of a pointer into block `b` at address `A`. -/
theorem ptrAddr_of (hqb : q.block = some b) (h : AddrOf b A P) :
    FTTotalTriple P (Zig.ptrAddr q) (fun x => ⟪x = (A : Int) + q.off⟫ ⋆ P) := by
  obtain ⟨qb, qo⟩ := q
  simp only at hqb; subst hqb
  refine of_read fun m r rF hh hp _ => ?_
  obtain ⟨blk, hb, rfl⟩ := h m r rF hh hp
  exact ptrAddr_run hb qo

/-- **The model's `@alignCast` check** of a pointer at an address that `al` divides. -/
theorem checkAlign_of {al : Nat} (hqb : q.block = some b) (h : AddrOf b A P)
    (hal : ((A : Int) + q.off) % al = 0) : FTTotalTriple P (checkAlign al q) (fun _ => P) := by
  unfold checkAlign
  refine bind (ptrAddr_of hqb h) fun x => lift fun hx => ?_
  subst hx
  rw [if_neg (by simp [hal])]
  exact ret (Q := fun _ => P) ()

/-- **Pointer `==`** of two pointers into one block: their offsets are equal (MM-4). -/
theorem ptrEqAddr_of (hpb : p.block = some b) (hqb : q.block = some b) (h : AddrOf b A P) :
    FTTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) := by
  unfold ptrEqAddr
  refine bind (ptrAddr_of hpb h) fun x => lift fun hx => ?_
  refine bind (ptrAddr_of hqb h) fun y => lift fun hy => ?_
  subst hx hy
  exact conseq (ret (Q := fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) _)
    (fun _ hh => sep_lift.mpr ⟨by simp, hh⟩) (fun _ _ h => h)

/-- **Pointer formation** (`ptrProject`, MM-3) of a byte offset `k` of `q` that stays within the
first `K` bytes of a block that reaches `K`. -/
theorem ptrProject_of {k : Int} (hqb : q.block = some b) (h : Reaches b K P) (h0 : 0 ≤ q.off)
    (hq : q.off ≤ K) (hk0 : 0 ≤ q.off + k) (hk : q.off + k ≤ K) :
    FTTotalTriple P (ptrProject q (·.add k)) (fun r => ⟪r = q.add k⟫ ⋆ P) :=
  of_read fun m r rF hh hp _ => by
    obtain ⟨blk, hb, hK⟩ := h m r rF hh hp
    exact ptrProject_add_run (inBounds_of hqb hb h0 (by omega))
      (inBounds_of (p := q.add k) hqb hb (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

/-- `ptrProject_of` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_of {size : Nat} {i : BitVec 64} (hqb : q.block = some b)
    (h : Reaches b K P) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ K) :
    FTTotalTriple P (ptrProject q (·.elem size i)) (fun r => ⟪r = q.elem size i⟫ ⋆ P) := by
  have e : (fun x : Ptr => x.elem size i) = (·.add ((size * i.toNat : Nat) : Int)) := by
    funext x; exact Ptr.elem_eq x size i
  rw [e, Ptr.elem_eq]
  exact ptrProject_of hqb h h0 (by omega) (by omega) hk

/- The owned accesses in a thread (`load`, `store`, byte reads and writes, `@memset`,
`@memmove`) are their sequential rules with the locality of the access: `fsym` applies each
sequential rule in a thread goal (`FTTotalTriple.ofSeq`, `Full/AutoThread.lean`), so they have no
copy here. The two below stay for term-level callers: the thread byte rules of `Full/Local` on
the fold lane (`codex/fold`); delete them when those go through `fsym`. -/

section OwnedBytes

variable {S k al : Nat} {K' : BlockKind} {bs : Array Byte}

/-- `FTotalTriple.load_bytesAt` in a thread. -/
theorem load_bytesAt {T : Type} [Enc T] {v : T} (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    FTTotalTriple (up (bytesAt q A S K' bs)) (Zig.load T al (q.add k))
      (fun x => ⟪x = v⟫ ⋆ up (bytesAt q A S K' bs)) :=
  ofSeq (FTotalTriple.load_bytesAt hn hk ha hv) (ThreadLocal.load hn (OwnsPtr.bytesAt_add hk))

/-- `FTotalTriple.storeBytes_bytesAt` in a thread. -/
theorem storeBytes_bytesAt {bs' : Array Byte} (hn : 0 < bs'.size) (hk : k + bs'.size ≤ bs.size)
    (ha : (A + q.off.toNat + k) % al = 0) (hK : K' ≠ .constGlobal) :
    FTTotalTriple (up (bytesAt q A S K' bs)) (Zig.storeBytes (q.add k) al bs')
      (fun _ => up (bytesAt q A S K' (writeBytes bs k bs'))) :=
  ofSeq (FTotalTriple.storeBytes_bytesAt hn hk ha hK)
    (ThreadLocal.storeBytes hn (OwnsPtr.bytesAt_add hk))

end OwnedBytes

end FTTotalTriple

/-! ## Sequential pointer rules -/

namespace FTotalTriple

variable {P : FAssn} {q p : Ptr} {b : BlockId} {A K : Nat}

/-- **`@intFromPtr`** of a pointer into block `b` at address `A`. -/
theorem ptrAddr_of (hqb : q.block = some b) (h : AddrOf b A P) :
    FTotalTriple P (Zig.ptrAddr q) (fun x => ⟪x = (A : Int) + q.off⟫ ⋆ P) :=
  (FTTotalTriple.ptrAddr_of hqb h).toFTotalTriple

/-- **The model's `@alignCast` check** of a pointer at an address that `al` divides. -/
theorem checkAlign_of {al : Nat} (hqb : q.block = some b) (h : AddrOf b A P)
    (hal : ((A : Int) + q.off) % al = 0) : FTotalTriple P (checkAlign al q) (fun _ => P) :=
  (FTTotalTriple.checkAlign_of hqb h hal).toFTotalTriple

/-- **Pointer `==`** of two pointers into one block: their offsets are equal (MM-4). -/
theorem ptrEqAddr_of (hpb : p.block = some b) (hqb : q.block = some b) (h : AddrOf b A P) :
    FTotalTriple P (ptrEqAddr p q) (fun r => ⟪r = decide (p.off = q.off)⟫ ⋆ P) :=
  (FTTotalTriple.ptrEqAddr_of hpb hqb h).toFTotalTriple

/-- **Pointer formation** (`ptrProject`, MM-3) of a byte offset `k` of `q` that stays within the
first `K` bytes of a block that reaches `K`. -/
theorem ptrProject_of {k : Int} (hqb : q.block = some b) (h : Reaches b K P) (h0 : 0 ≤ q.off)
    (hq : q.off ≤ K) (hk0 : 0 ≤ q.off + k) (hk : q.off + k ≤ K) :
    FTotalTriple P (ptrProject q (·.add k)) (fun r => ⟪r = q.add k⟫ ⋆ P) :=
  (FTTotalTriple.ptrProject_of hqb h h0 hq hk0 hk).toFTotalTriple

/-- `ptrProject_of` for an item pointer `q.elem size i`. -/
theorem ptrProject_elem_of {size : Nat} {i : BitVec 64} (hqb : q.block = some b)
    (h : Reaches b K P) (h0 : 0 ≤ q.off) (hk : q.off + ((size * i.toNat : Nat) : Int) ≤ K) :
    FTotalTriple P (ptrProject q (·.elem size i)) (fun r => ⟪r = q.elem size i⟫ ⋆ P) :=
  (FTTotalTriple.ptrProject_elem_of hqb h h0 hk).toFTotalTriple

end FTotalTriple

/-! ## Changing a resource's full extents -/

/-- **The full extents of a resource can change** to any blocks on which the frame has only
dormant claims: ledgers, balances and finiteness only see the frame there. -/
theorem Ghost.ok_exts_change {E E' : BlockId → Option (Nat × BlockKind)} {gF : Ghost}
    (hok : Ghost.Ok (Ghost.exts E) gF)
    (hd : ∀ b, (E' b).isSome → (gF.extent b).Dormant gF.ls) : Ghost.Ok (Ghost.exts E') gF := by
  have hep : ((Ghost.exts E).add gF).ls = gF.ls := Ghost.ls_exts_add
  have hvF : ∀ b, (gF.extent b).Valid ∧ (gF.extent b).TagOk gF.ls := fun b => by
    have hv := hok.1.2.1 b
    have hle : (gF.extent b).Le (((Ghost.exts E).add gF).extent b) := ECell.le_add' _ _
    refine ⟨ECell.Valid.of_add (b := (Ghost.exts E).extent b) ?_,
      ECell.TagOk.of_le (ls' := ((Ghost.exts E).add gF).ls)
        (fun _ _ _ h => by rw [hep]; exact h) hok.1.uniq hle hv.2⟩
    rw [ECell.add_comm]; exact hv.1
  refine ⟨⟨fun γ => ?_, fun b => ?_, hok.1.2.2.1.congr (by rw [Ghost.exts_add_cl, Ghost.exts_add_cl])
    (by rw [Ghost.ls_exts_add, Ghost.ls_exts_add]), by simpa using hok.1.2.2.2⟩, ?_⟩
  · have := hok.1.1 γ; simpa [Ghost.add, Ghost.exts] using this
  · rw [Ghost.ls_exts_add]
    by_cases hb : (E' b).isSome
    · obtain ⟨⟨S, K⟩, hS⟩ := Option.isSome_iff_exists.mp hb
      rw [show (Ghost.add (Ghost.exts E') gF).extent b = (ECell.auth1 S K Frac.one).add (gF.extent b) by
        simp [Ghost.add, Ghost.exts, hS]]
      exact (hd b hb).auth1_ok
    · have hn : E' b = none := by simpa using hb
      rw [show (Ghost.add (Ghost.exts E') gF).extent b = gF.extent b by
        simp [Ghost.add, Ghost.exts, hn]]
      exact hvF b
  · obtain ⟨N, hN⟩ := hok.2
    refine ⟨N, fun γ hγ => ⟨by have := (hN γ hγ).1; simpa [Ghost.add, Ghost.exts] using this,
      fun b e k => ?_, fun γ' e' M e => by
        have := (hN γ hγ).2.2 γ' e' M e; simpa [Ghost.add, Ghost.exts] using this⟩⟩
    have h1 := (hN γ hγ).2.1 b e k
    rw [((Ghost.exts_add_tags E' gF b).2 γ e k).1, ((Ghost.exts_add_tags E' gF b).2 γ e k).2]
    rwa [((Ghost.exts_add_tags E gF b).2 γ e k).1, ((Ghost.exts_add_tags E gF b).2 γ e k).2] at h1

/-- The blocks after `set!` at an existing index. -/
theorem blocks_set_get {m m' : Mem} {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b nb) (x : BlockId) :
    m'.blocks[x]? = if x = b then some nb else m.blocks[x]? := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : x = b
  · subst e; simp [hlt]
  · simp [e, Ne.symm e]

/-- The extent map of one block. -/
def extOne (b : BlockId) (S : Nat) (K : BlockKind) : BlockId → Option (Nat × BlockKind) :=
  fun x => if x = b then some (S, K) else none

/-- The full extent of one block, as the extents of a resource. -/
theorem Ghost.exts_extOne (b : BlockId) (S : Nat) (K : BlockKind) :
    Ghost.exts (extOne b S K) = Ghost.atExt b (ECell.auth1 S K Frac.one) := by
  ext1
  · funext γ; simp [Ghost.atExt, Ghost.exts]
  · funext x; simp only [Ghost.atExt, Ghost.exts, extOne]; split <;> simp_all
  · funext x y; simp [Ghost.atExt, Ghost.exts]
  · simp [Ghost.atExt, Ghost.exts]

end Full
end Zig
