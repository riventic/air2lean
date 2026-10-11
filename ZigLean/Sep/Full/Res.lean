import ZigLean.Sep.Triple

/-!
# Full-state resources (prototype, `docs/sep-full-state.md`)

The assertions of `ZigLean/Sep/` (`Assn`) range over `Mem.heap`, the live bytes. Two parts of
`Mem` that a program can observe are outside it, so no precondition can constrain them and no
frame keeps them (`docs/alloc-page.md`, obstructions O1 and O3):

* **the atomic layout** (`Mem.atomics`): an atomic op at bytes that already carry an atomic
  location of another offset or size throws `.unspecified` if an access to that location is
  concurrent with it, and retires the location otherwise (the mixed-size policy of
  `ZigLean/Mem/Thread.lean`, `retireAt`);
* **the metadata of dead blocks**: `ptrAddr` (`@intFromPtr`) of a pointer into a freed block reads
  the block's address, and throws `.illegal` only if the block does not exist at all.

A full-state resource `Res` has three parts:

* `heap : FHeap`: owned live bytes, each with its legacy `Cell` **and an atomic tag constraint**
  (`FCell.atom`): `some (o, len)` says that the atomic location over the byte is `(o, len)` or
  that there is none; `none` constrains nothing (`TagSat`). The frame rule keeps the frame's
  constraints, and an atomic points-to (`apts`) can require the layout an atomic op leaves.
  A constraint, not an equation: an atomic op on owned bytes may retire a location that also
  covers frame bytes (memory reused for another object), which leaves those bytes without a
  location, and that meets every constraint (`docs/sep-full-state.md` §Atomic tags;
  `tests/roadmap/sep-full/ExactTags.lean` shows that exact tags break the frame rule).
* `know : Know`: **persistent knowledge** of block addresses, `known b A`: block `b` exists and
  has address `A`. Block ids are never reused and a block's address never changes, so this
  knowledge stays true after `free` (it is not ownership: it is duplicable, `known_dup`).
* `gh : Ghost`: ghost epoch ledgers of named grants (§Ghost state below, rules in `Ghost.lean`); no primitive
  reads or changes them.

`Mem.fheap m` is the full heap of a memory (live bytes with their exact tags); a full heap `h`
matches `m` (`FMatch m h`) if its cells are `m`'s live bytes and each byte meets its tag
constraint. `Mem.kn m` is the memory's knowledge (every block, live or dead, with its address).

Nothing here is reachable from `ZigLean.lean`: it is proof-only.
-/

namespace Zig
namespace Full

/-! ## Atomic layout -/

/-- An atomic location's footprint: block, start offset, length. -/
abbrev Shape := BlockId × Nat × Nat

def ALoc.shape (l : ALoc) : Shape := (l.block, l.off, l.len)

/-- The footprints of the atomic locations of `m`, in order. -/
def shapes (m : Mem) : List Shape := m.atomics.toList.map ALoc.shape

/-- The location `s` covers byte `x` of block `b`. -/
def Covers (b x : Nat) (s : Shape) : Prop := s.1 = b ∧ s.2.1 ≤ x ∧ x < s.2.1 + s.2.2

instance (b x : Nat) : DecidablePred (Covers b x) := fun s => by
  unfold Covers; infer_instance

/-- The atomic tag of byte `x` of block `b`: start and length of the first location over it. -/
def tagOf (sh : List Shape) (b x : Nat) : Option (Nat × Nat) :=
  (sh.find? fun s => decide (Covers b x s)).map fun s => (s.2.1, s.2.2)

/-- Two locations of the same block do not overlap. -/
def Apart (s t : Shape) : Prop := s.1 = t.1 → s.2.1 + s.2.2 ≤ t.2.1 ∨ t.2.1 + t.2.2 ≤ s.2.1

/-- The atomic layout is well formed: each location has a byte, no two overlap. Every memory
that the atomic ops reach from one without locations has it (`locIdx` makes a location only where
none overlaps). -/
def ShapesWF (sh : List Shape) : Prop := (∀ s ∈ sh, 0 < s.2.2) ∧ sh.Pairwise Apart

theorem not_apart_of_covers {s t : Shape} {b x : Nat} (hs : Covers b x s) (ht : Covers b x t) :
    ¬ Apart s t := by
  intro h
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨h1', h2', h3'⟩ := ht
  rcases h (h1.trans h1'.symm) with e | e <;> omega

/-- The tag of a byte that a location covers is that location's. -/
theorem tagOf_of_mem {sh : List Shape} (hw : ShapesWF sh) {s : Shape} (hs : s ∈ sh) {b x : Nat}
    (hc : Covers b x s) : tagOf sh b x = some (s.2.1, s.2.2) := by
  obtain ⟨-, hp⟩ := hw
  induction sh with
  | nil => cases hs
  | cons t rest ih =>
    rw [List.pairwise_cons] at hp
    unfold tagOf
    rw [List.find?_cons]
    by_cases ht : Covers b x t
    · simp only [ht, decide_true, Option.map_some]
      rcases List.mem_cons.mp hs with rfl | hr
      · rfl
      · exact absurd (hp.1 s hr) (not_apart_of_covers ht hc)
    · simp only [ht, decide_false]
      rcases List.mem_cons.mp hs with rfl | hr
      · exact absurd hc ht
      · exact ih hr hp.2

theorem tagOf_none {sh : List Shape} {b x : Nat} :
    tagOf sh b x = none ↔ ∀ s ∈ sh, ¬ Covers b x s := by
  unfold tagOf
  simp [List.find?_eq_none]

theorem tagOf_append_single {sh : List Shape} {s : Shape} {b x : Nat} :
    tagOf (sh ++ [s]) b x = (tagOf sh b x).or (if Covers b x s then some (s.2.1, s.2.2) else none) := by
  unfold tagOf
  rw [List.find?_append]
  cases sh.find? (fun s => decide (Covers b x s)) with
  | some t => simp
  | none =>
    by_cases h : Covers b x s <;> simp [h, List.find?_cons]

/-! ## Full cells and heaps -/

/-- A live byte with its legacy cell and its atomic tag. -/
structure FCell where
  cell : Cell
  atom : Option (Nat × Nat)

abbrev FHeap := Loc → Option FCell

namespace FHeap

def empty : FHeap := fun _ => none

def Disjoint (h₁ h₂ : FHeap) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

def union (h₁ h₂ : FHeap) : FHeap := fun l => (h₁ l).or (h₂ l)

instance : Union FHeap := ⟨union⟩

@[simp] theorem union_apply (h₁ h₂ : FHeap) (l : Loc) : (h₁ ∪ h₂) l = (h₁ l).or (h₂ l) := rfl

theorem Disjoint.symm {h₁ h₂ : FHeap} (h : Disjoint h₁ h₂) : Disjoint h₂ h₁ := fun l => (h l).symm

theorem union_comm {h₁ h₂ : FHeap} (h : Disjoint h₁ h₂) : h₁ ∪ h₂ = h₂ ∪ h₁ := by
  funext l; rcases h l with e | e <;> simp [e]

theorem union_assoc (h₁ h₂ h₃ : FHeap) : h₁ ∪ h₂ ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  funext l; simp [Option.or_assoc]

@[simp] theorem empty_union (h : FHeap) : empty ∪ h = h := by funext l; simp [empty]

@[simp] theorem union_empty (h : FHeap) : h ∪ empty = h := by funext l; simp [empty]

theorem disjoint_empty (h : FHeap) : Disjoint h empty := fun _ => Or.inr rfl

theorem disjoint_union_left {h₁ h₂ h₃ : FHeap} :
    Disjoint (h₁ ∪ h₂) h₃ ↔ Disjoint h₁ h₃ ∧ Disjoint h₂ h₃ := by
  constructor
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩ <;> rcases h l with e | e <;> simp_all [Option.or_eq_none_iff]
  · rintro ⟨a, b⟩ l
    rcases a l with e | e
    · rcases b l with e' | e'
      · left; simp [e, e']
      · right; exact e'
    · right; exact e

theorem disjoint_union_right {h₁ h₂ h₃ : FHeap} :
    Disjoint h₁ (h₂ ∪ h₃) ↔ Disjoint h₁ h₂ ∧ Disjoint h₁ h₃ := by
  constructor
  · intro h; have := disjoint_union_left.mp h.symm; exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨a, b⟩; exact (disjoint_union_left.mpr ⟨a.symm, b.symm⟩).symm

/-- The legacy heap of a full heap: the cells without their tags. -/
def erase (h : FHeap) : Heap := fun l => (h l).map (·.cell)

@[simp] theorem erase_union (h₁ h₂ : FHeap) : erase (h₁ ∪ h₂) = erase h₁ ∪ erase h₂ := by
  funext l; simp only [erase, union_apply, Heap.union_apply]; cases h₁ l <;> simp

theorem erase_disjoint {h₁ h₂ : FHeap} (h : Disjoint h₁ h₂) : Heap.Disjoint (erase h₁) (erase h₂) :=
  fun l => by rcases h l with e | e <;> simp [erase, e]

@[simp] theorem erase_empty : erase empty = Heap.empty := rfl

end FHeap

/-- The full heap of `m`: its live bytes, each with its atomic tag. -/
def _root_.Zig.Mem.fheap (m : Mem) : FHeap := fun l =>
  (m.heap l).map fun c => ⟨c, tagOf (shapes m) l.1 l.2⟩

@[simp] theorem fheap_erase (m : Mem) : m.fheap.erase = m.heap := by
  funext l; simp only [FHeap.erase, Mem.fheap, Option.map_map]; cases m.heap l <;> rfl

/-- The tag constraint `t` holds of byte `x` of block `b` in the layout `sh`: `none` constrains
nothing; `some s`: the location over the byte is `s`, or there is none. -/
def TagSat (sh : List Shape) (b x : Nat) : Option (Nat × Nat) → Prop
  | none => True
  | some s => tagOf sh b x = none ∨ tagOf sh b x = some s

/-- A block kind without its mapping start. -/
def _root_.Zig.BlockKind.norm : BlockKind → BlockKind
  | .mapped _ => .mapped 0
  | k => k

/-- A cell without its block's size and mapping start: the byte, the block's address (which
never changes) and the kind's constructor. A frame's cell pins only this, so the owner of a
block's extent (`bext`) can resize it under the frame (`docs/sep-full-state.md` §Block extents). -/
def _root_.Zig.Cell.norm (c : Cell) : Cell := { c with size := 0, kind := c.kind.norm }

/-- The full heap `h` matches `m`: its cells are `m`'s live bytes up to their block's size and
mapping start (`Cell.norm`), and each of its bytes meets its atomic tag constraint. -/
def FMatch (m : Mem) (h : FHeap) : Prop :=
  (∀ l, (m.heap l).map Cell.norm = (h l).map fun fc => fc.cell.norm) ∧
    ∀ l fc, h l = some fc → TagSat (shapes m) l.1 l.2 fc.atom

theorem FMatch.cell {m : Mem} {h : FHeap} (hm : FMatch m h) {l : Loc} {fc : FCell}
    (hl : h l = some fc) : ∃ c, m.heap l = some c ∧ c.norm = fc.cell.norm := by
  have := hm.1 l
  rw [hl] at this
  cases e : m.heap l with
  | none => rw [e] at this; cases this
  | some c => rw [e] at this; exact ⟨c, rfl, Option.some.inj this⟩

theorem FMatch.none {m : Mem} {h : FHeap} (hm : FMatch m h) {l : Loc} (hl : h l = none) :
    m.heap l = none := by
  have := hm.1 l
  rw [hl] at this
  cases e : m.heap l with
  | none => rfl
  | some c => rw [e] at this; cases this

/-- A memory's own full heap (exact tags) matches it. -/
theorem FMatch.fheap (m : Mem) : FMatch m m.fheap := by
  refine ⟨fun l => by simp only [Mem.fheap, Option.map_map]; rfl, fun l fc hl => ?_⟩
  simp only [Mem.fheap, Option.map_eq_some_iff] at hl
  obtain ⟨c, -, rfl⟩ := hl
  cases e : tagOf (shapes m) l.1 l.2 with
  | none => trivial
  | some s => exact .inr e

/-- Two memories with the same live bytes and the same atomic layout have the same full heap. -/
theorem fheap_congr {m m' : Mem} (hh : m'.heap = m.heap) (hs : shapes m' = shapes m) :
    m'.fheap = m.fheap := by
  funext l; simp [Mem.fheap, hh, hs]

/-! ## Knowledge -/

/-- Persistent facts `(b, A)`: block `b` exists and has address `A`. -/
abbrev Know := BlockId → Nat → Prop

namespace Know

def none : Know := fun _ _ => False

def union (k₁ k₂ : Know) : Know := fun b A => k₁ b A ∨ k₂ b A

def Sub (k K : Know) : Prop := ∀ b A, k b A → K b A

theorem union_none (k : Know) : k.union none = k := by
  funext b A; simp [union, none]

theorem none_union (k : Know) : none.union k = k := by
  funext b A; simp [union, none]

theorem union_comm (k₁ k₂ : Know) : k₁.union k₂ = k₂.union k₁ := by
  funext b A; simp [union, or_comm]

theorem union_assoc (k₁ k₂ k₃ : Know) : (k₁.union k₂).union k₃ = k₁.union (k₂.union k₃) := by
  funext b A; simp [union, or_assoc]

theorem union_self (k : Know) : k.union k = k := by funext b A; simp [union]

theorem Sub.union {k₁ k₂ K : Know} (h₁ : Sub k₁ K) (h₂ : Sub k₂ K) : Sub (k₁.union k₂) K :=
  fun b A h => h.elim (h₁ b A) (h₂ b A)

theorem Sub.left {k₁ k₂ K : Know} (h : Sub (k₁.union k₂) K) : Sub k₁ K := fun b A x => h b A (.inl x)

theorem Sub.right {k₁ k₂ K : Know} (h : Sub (k₁.union k₂) K) : Sub k₂ K := fun b A x => h b A (.inr x)

theorem Sub.trans {k K K' : Know} (h : Sub k K) (h' : Sub K K') : Sub k K' :=
  fun b A x => h' b A (h b A x)

theorem sub_none (K : Know) : Sub none K := fun _ _ h => h.elim

end Know

/-- The knowledge of `m`: every block, live or dead, with its address. -/
def _root_.Zig.Mem.kn (m : Mem) : Know := fun b A => ∃ blk, m.blocks[b]? = some blk ∧ blk.addr = A

/-- `m'` keeps every block of `m` at its address. -/
def KMono (m m' : Mem) : Prop := Know.Sub m.kn m'.kn

theorem KMono.refl (m : Mem) : KMono m m := fun _ _ h => h

theorem KMono.trans {m₁ m₂ m₃ : Mem} (h₁ : KMono m₁ m₂) (h₂ : KMono m₂ m₃) : KMono m₁ m₃ :=
  Know.Sub.trans h₁ h₂

theorem KMono.of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : KMono m m' := by
  intro b A hk; simpa [Mem.kn, h] using hk

/-- Replacing block `b` by one with the same address keeps the knowledge. -/
theorem KMono.set {m m' : Mem} {b : BlockId} {blk blk' : Block} (hb : m.blocks[b]? = some blk)
    (ha : blk'.addr = blk.addr) (h : m'.blocks = m.blocks.set! b blk') : KMono m m' := by
  intro b' A ⟨x, hx, hA⟩
  refine ⟨if b' = b then blk' else x, ?_, ?_⟩
  · rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : b = b'
    · subst e
      have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
      simp [hlt]
    · simp [e, Ne.symm e, hx]
  · by_cases e : b' = b
    · subst e; rw [hb] at hx; cases hx; simpa [ha] using hA
    · simpa [e] using hA

/-- Pushing a block keeps the knowledge. -/
theorem KMono.push {m m' : Mem} {nb : Block} (h : m'.blocks = m.blocks.push nb) : KMono m m' := by
  intro b A ⟨x, hx, hA⟩
  refine ⟨x, ?_, hA⟩
  rw [h, Array.getElem?_push]
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hx).1
  simp [Nat.ne_of_lt hlt, hx]

/-! ## Ghost state: epoch ledgers (`docs/sep-full-state.md` §Ghost state)

A ghost cell is an epoch ledger of named grants. `auth` counts authorities `●(e, M)`: the current
epoch `e` and the grant map `M` (grant id ↦ the region it names, a start pointer and a length);
a valid state has at most one per name. `frag (e, i, g)` counts tokens `◯(e, i ↦ g)`. Composition
adds both counts, so it is total; `Ghost.Valid` (part of `Holds`) rules out two authorities, a
token of the current epoch that the map does not record (or two for one id), and tokens of a
later epoch. -/

/-- A region named by a ledger token: its start pointer and its length in bytes. -/
abbrev GRegion := Ptr × Nat

/-- A ledger's grant map: grant id ↦ the region granted under it. -/
abbrev GMap := Nat → Option GRegion

@[ext] structure GCell where
  auth : Nat × GMap → Nat
  frag : Nat × Nat × GRegion → Nat

namespace GCell

def unit : GCell := ⟨fun _ => 0, fun _ => 0⟩

def add (a b : GCell) : GCell := ⟨fun x => a.auth x + b.auth x, fun t => a.frag t + b.frag t⟩

/-- The tokens of epoch `e` agree with the grant map `M`: at most one per id, and only for ids
that `M` maps to that region. -/
def TokOk (c : GCell) (e : Nat) (M : GMap) : Prop :=
  ∀ i g, c.frag (e, i, g) ≤ 1 ∧ (0 < c.frag (e, i, g) → M i = some g)

/-- At most one authority, and if there is one, `●(e, M)`, the tokens of epoch `e` agree with
`M` and there are none of a later epoch. -/
def Valid (c : GCell) : Prop :=
  (∀ x, c.auth x = 0) ∨ ∃ e M, c.auth (e, M) = 1 ∧ (∀ x, x ≠ (e, M) → c.auth x = 0) ∧
    c.TokOk e M ∧ ∀ e' i g, e < e' → c.frag (e', i, g) = 0

theorem add_comm (a b : GCell) : a.add b = b.add a := by
  ext <;> simp [add, Nat.add_comm]

theorem add_assoc (a b c : GCell) : (a.add b).add c = a.add (b.add c) := by
  ext <;> simp [add, Nat.add_assoc]

@[simp] theorem add_unit (a : GCell) : a.add unit = a := by ext <;> simp [add, unit]

@[simp] theorem unit_add (a : GCell) : unit.add a = a := by ext <;> simp [add, unit]

theorem Valid.of_add {a b : GCell} (h : (a.add b).Valid) : a.Valid := by
  rcases h with h | ⟨e, M, h1, h2, h3, h4⟩
  · left; intro x; have := h x; simp only [add] at this; omega
  · by_cases ha : a.auth (e, M) = 1
    · right
      refine ⟨e, M, ha, fun x hx => ?_, fun i g => ?_, fun e' i g he => ?_⟩
      · have := h2 x hx; simp only [add] at this; omega
      · have := h3 i g; simp only [add] at this; exact ⟨by omega, fun hp => this.2 (by omega)⟩
      · have := h4 e' i g he; simp only [add] at this; omega
    · left; intro x
      by_cases hx : x = (e, M)
      · subst hx; simp only [add] at h1; omega
      · have := h2 x hx; simp only [add] at this; omega

end GCell

/-! ## Block extents (`docs/sep-full-state.md` §Block extents)

A block's extent (liveness, size, kind with its mapping start) is a resource, not a property of
the bytes: cells are compared without it (`Cell.norm`, `FMatch`). Per block, an `ECell` holds
authority claims `auth (S, K)` (the exact extent; exclusive, `ECell.Valid`) and fractional
lower-bound shares `sh k` (the block is live with at least `k` bytes). The full extent `bext b S
K` is the authority with all of the fraction (`1`, at bound `0`): only it may shrink or end the
block, and then no other resource holds a share. Shares split off the authority (`bshare`) let a
client keep "the block has at least `off + n` bytes" while it holds a grant. -/

/-- A nonnegative fraction. -/
structure Frac where
  val : Rat
  nonneg : 0 ≤ val

namespace Frac

theorem eq {a b : Frac} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

def zero : Frac := ⟨0, Rat.le_refl⟩

def one : Frac := ⟨1, by decide⟩

def add (a b : Frac) : Frac := ⟨a.val + b.val, by have := a.nonneg; have := b.nonneg; grind⟩

theorem add_comm (a b : Frac) : a.add b = b.add a := eq (by simp only [add]; grind)

theorem add_assoc (a b c : Frac) : (a.add b).add c = a.add (b.add c) := eq (by simp only [add]; grind)

@[simp] theorem add_zero (a : Frac) : a.add zero = a := eq (by simp only [add, zero]; grind)

@[simp] theorem zero_add (a : Frac) : zero.add a = a := eq (by simp only [add, zero]; grind)

end Frac

/-! ## Finite sums of fractions (epoch-tagged shares, `docs/sep-full-state.md` §Epoch-tagged shares) -/

/-- The fraction `f` holds at the bounds below `n`. -/
def ftot (f : Nat → Frac) : Nat → Rat
  | 0 => 0
  | n + 1 => ftot f n + (f n).val

theorem ftot_nonneg (f : Nat → Frac) : ∀ n, 0 ≤ ftot f n
  | 0 => Rat.le_refl
  | n + 1 => by have := ftot_nonneg f n; have := (f n).nonneg; simp only [ftot]; grind

theorem ftot_add (f g : Nat → Frac) : ∀ n, ftot (fun k => (f k).add (g k)) n = ftot f n + ftot g n
  | 0 => by simp only [ftot]; grind
  | n + 1 => by have := ftot_add f g n; simp only [ftot, Frac.add] at *; grind

theorem ftot_mono (f : Nat → Frac) {n N : Nat} (h : n ≤ N) : ftot f n ≤ ftot f N := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]; exact Rat.le_refl
  | succ N ih =>
    rcases Nat.lt_or_ge n (N + 1) with hn | hn
    · have := ih (by omega); have := (f N).nonneg; simp only [ftot]; grind
    · rw [show n = N + 1 by omega]; exact Rat.le_refl

theorem ftot_le {f g : Nat → Frac} (h : ∀ k, (f k).val ≤ (g k).val) : ∀ n, ftot f n ≤ ftot g n
  | 0 => Rat.le_refl
  | n + 1 => by have := ftot_le h n; have := h n; simp only [ftot]; grind

/-- `Σ_{e < E} f e`. -/
def esum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | E + 1 => esum f E + f E

/-- `Σ_{γ < N, e < E} f γ e`. -/
def gsum (f : Nat → Nat → Rat) : Nat → Nat → Rat
  | 0, _ => 0
  | N + 1, E => gsum f N E + esum (f N) E

theorem esum_le {f g : Nat → Rat} (h : ∀ e, f e ≤ g e) : ∀ E, esum f E ≤ esum g E
  | 0 => Rat.le_refl
  | E + 1 => by have := esum_le h E; have := h E; simp only [esum]; grind

theorem esum_nonneg {f : Nat → Rat} (h : ∀ e, 0 ≤ f e) : ∀ E, 0 ≤ esum f E
  | 0 => Rat.le_refl
  | E + 1 => by have := esum_nonneg h E; have := h E; simp only [esum]; grind

theorem esum_add (f g : Nat → Rat) : ∀ E, esum (fun e => f e + g e) E = esum f E + esum g E
  | 0 => by simp only [esum]; grind
  | E + 1 => by have := esum_add f g E; simp only [esum] at *; grind

theorem gsum_le {f g : Nat → Nat → Rat} (h : ∀ γ e, f γ e ≤ g γ e) : ∀ N E, gsum f N E ≤ gsum g N E
  | 0, _ => Rat.le_refl
  | N + 1, E => by
    have := gsum_le h N E; have := esum_le (h N) E; simp only [gsum]; grind

theorem gsum_nonneg {f : Nat → Nat → Rat} (h : ∀ γ e, 0 ≤ f γ e) : ∀ N E, 0 ≤ gsum f N E
  | 0, _ => Rat.le_refl
  | N + 1, E => by
    have := gsum_nonneg h N E; have := esum_nonneg (h N) E; simp only [gsum]; grind

theorem gsum_add (f g : Nat → Nat → Rat) : ∀ N E, gsum (fun γ e => f γ e + g γ e) N E = gsum f N E + gsum g N E
  | 0, _ => by simp only [gsum]; grind
  | N + 1, E => by
    have := gsum_add f g N E; have := esum_add (f N) (g N) E; simp only [gsum] at *; grind

theorem esum_le' {f g : Nat → Rat} : ∀ {E}, (∀ e, e < E → f e ≤ g e) → esum f E ≤ esum g E
  | 0, _ => Rat.le_refl
  | E + 1, h => by
    have := esum_le' (E := E) fun e he => h e (by omega); have := h E (by omega)
    simp only [esum]; grind

/-- A change at one place by at most `δ`. -/
theorem esum_single {f g : Nat → Rat} {e₀ : Nat} {δ : Rat} (hδ : 0 ≤ δ)
    (h : ∀ e, e ≠ e₀ → f e ≤ g e) (h₀ : f e₀ ≤ g e₀ + δ) : ∀ E, esum f E ≤ esum g E + δ
  | 0 => by simp only [esum]; grind
  | E + 1 => by
    simp only [esum]
    by_cases he : E = e₀
    · subst he
      have := esum_le' (f := f) (g := g) (E := E) fun e he' => h e (by omega)
      grind
    · have := esum_single hδ h h₀ E; have := h E he; grind

theorem gsum_le' {f g : Nat → Nat → Rat} : ∀ {N} E, (∀ γ e, γ < N → f γ e ≤ g γ e) → gsum f N E ≤ gsum g N E
  | 0, _, _ => Rat.le_refl
  | N + 1, E, h => by
    have := gsum_le' (N := N) E fun γ e hγ => h γ e (by omega)
    have := esum_le (fun e => h N e (by omega)) E
    simp only [gsum]; grind

/-- A change at one place `(γ₀, e₀)` by at most `δ`. -/
theorem gsum_single {f g : Nat → Nat → Rat} {γ₀ e₀ : Nat} {δ : Rat} (hδ : 0 ≤ δ)
    (h : ∀ γ e, (γ, e) ≠ (γ₀, e₀) → f γ e ≤ g γ e) (h₀ : f γ₀ e₀ ≤ g γ₀ e₀ + δ) :
    ∀ N E, gsum f N E ≤ gsum g N E + δ
  | 0, _ => by simp only [gsum]; grind
  | N + 1, E => by
    simp only [gsum]
    by_cases hN : N = γ₀
    · subst hN
      have := gsum_le' (f := f) (g := g) (N := N) E fun γ e hγ => h γ e (by intro x; cases x; omega)
      have := esum_single hδ (f := f N) (g := g N) (e₀ := e₀) (fun e he => h N e (by
        intro x; cases x; exact he rfl)) h₀ E
      grind
    · have := gsum_single hδ h h₀ N E
      have := esum_le (fun e => h N e (by intro x; cases x; exact hN rfl)) E
      grind

theorem esum_mono {f : Nat → Rat} (h : ∀ e, 0 ≤ f e) {E E' : Nat} (hE : E ≤ E') : esum f E ≤ esum f E' := by
  induction E' with
  | zero => rw [Nat.le_zero.mp hE]; exact Rat.le_refl
  | succ E' ih =>
    rcases Nat.lt_or_ge E (E' + 1) with hn | hn
    · have := ih (by omega); have := h E'; simp only [esum]; grind
    · rw [show E = E' + 1 by omega]; exact Rat.le_refl

theorem gsum_mono {f : Nat → Nat → Rat} (h : ∀ γ e, 0 ≤ f γ e) {N N' E E' : Nat} (hN : N ≤ N')
    (hE : E ≤ E') : gsum f N E ≤ gsum f N' E' := by
  have step : ∀ N, gsum f N E ≤ gsum f N E' := fun N => by
    induction N with
    | zero => exact Rat.le_refl
    | succ N ih => have := esum_mono (h N) hE; simp only [gsum]; grind
  have := step N
  have : gsum f N E' ≤ gsum f N' E' := by
    induction N' with
    | zero => rw [Nat.le_zero.mp hN]; exact Rat.le_refl
    | succ N' ih =>
      rcases Nat.lt_or_ge N (N' + 1) with hn | hn
      · have := ih (by omega); have := esum_nonneg (h N') E'; simp only [gsum]; grind
      · rw [show N = N' + 1 by omega]; exact Rat.le_refl
  grind

theorem le_esum {f : Nat → Rat} (h : ∀ e, 0 ≤ f e) {e : Nat} : ∀ {E}, e < E → f e ≤ esum f E
  | 0, he => absurd he (Nat.not_lt_zero _)
  | E + 1, he => by
    simp only [esum]
    by_cases x : e = E
    · subst x; have := esum_nonneg h e; grind
    · have := le_esum h (e := e) (E := E) (by omega); have := h E; grind

theorem le_gsum {f : Nat → Nat → Rat} (h : ∀ γ e, 0 ≤ f γ e) {γ e E : Nat} (he : e < E) :
    ∀ {N}, γ < N → f γ e ≤ gsum f N E
  | 0, hγ => absurd hγ (Nat.not_lt_zero _)
  | N + 1, hγ => by
    simp only [gsum]
    by_cases x : γ = N
    · subst x; have := gsum_nonneg h γ E; have := le_esum (h γ) he; grind
    · have := le_gsum h (γ := γ) he (N := N) (by omega); have := esum_nonneg (h N) E; grind

theorem gsum_zero {f : Nat → Nat → Rat} (h : ∀ γ e, f γ e ≤ 0) (N E : Nat) : gsum f N E ≤ 0 := by
  have := gsum_le (f := f) (g := fun _ _ => 0) h N E
  have z : ∀ N, gsum (fun _ _ => (0 : Rat)) N E = 0 := fun N => by
    induction N with
    | zero => rfl
    | succ N ih =>
      have ze : ∀ E, esum (fun _ => (0 : Rat)) E = 0 := fun E => by
        induction E with
        | zero => rfl
        | succ E ih => simp only [esum, ih]; grind
      simp only [gsum, ih, ze]; grind
  rw [z] at this; exact this

theorem ftot_zero {f : Nat → Frac} (h : ∀ k, (f k).val = 0) : ∀ n, ftot f n = 0
  | 0 => rfl
  | n + 1 => by simp only [ftot, ftot_zero h n, h n]; grind

theorem le_ftot (f : Nat → Frac) {k : Nat} : ∀ {n}, k < n → (f k).val ≤ ftot f n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [ftot]
    by_cases x : k = n
    · subst x; have := ftot_nonneg f k; grind
    · have := le_ftot f (k := k) (n := n) (by omega); have := (f n).nonneg; grind

theorem ftot_congr {f g : Nat → Frac} (h : ∀ k, (f k).val = (g k).val) : ∀ n, ftot f n = ftot g n
  | 0 => rfl
  | n + 1 => by simp only [ftot, ftot_congr h n, h n]

/-! ## Ledger status and the weight of a tag -/

open Classical in
/-- The weight of the tag `(γ, e)` with tagged fractions `T` and receipts `R` (by bound), below
bound `n`: both (their maximum) while `γ` is at epoch `e`, the receipts once it is past `e`,
nothing while `γ` has no authority (or an earlier one). -/
noncomputable def tagWt (ep : Nat → Nat → Prop) (γ e : Nat) (T R : Nat → Frac) (n : Nat) : Rat :=
  if ep γ e then Max.max (ftot T n) (ftot R n) else if ∃ e', e < e' ∧ ep γ e' then ftot R n else 0

theorem tagWt_nonneg (ep : Nat → Nat → Prop) (γ e : Nat) (T R : Nat → Frac) (n : Nat) :
    0 ≤ tagWt ep γ e T R n := by
  have := ftot_nonneg T n; have := ftot_nonneg R n
  unfold tagWt; split
  · grind
  · split <;> grind

theorem tagWt_mono (ep : Nat → Nat → Prop) (γ e : Nat) (T R : Nat → Frac) {n N : Nat} (h : n ≤ N) :
    tagWt ep γ e T R n ≤ tagWt ep γ e T R N := by
  have := ftot_mono T h; have := ftot_mono R h
  unfold tagWt; split
  · grind
  · split <;> grind

/-- Fewer authorities (each ledger has at most one epoch in `ep`) and smaller fractions weigh
less. -/
theorem tagWt_le {ep ep' : Nat → Nat → Prop} (hsub : ∀ γ e, ep' γ e → ep γ e)
    (huniq : ∀ γ e e', ep γ e → ep γ e' → e = e') {γ e : Nat} {T R T' R' : Nat → Frac}
    (hT : ∀ k, (T' k).val ≤ (T k).val) (hR : ∀ k, (R' k).val ≤ (R k).val) (n : Nat) :
    tagWt ep' γ e T' R' n ≤ tagWt ep γ e T R n := by
  have hTl := ftot_le hT n; have hRl := ftot_le hR n
  have := ftot_nonneg T' n; have := ftot_nonneg R' n
  unfold tagWt
  by_cases h1 : ep' γ e
  · rw [if_pos h1, if_pos (hsub _ _ h1)]; grind
  · rw [if_neg h1]
    by_cases h2 : ∃ e', e < e' ∧ ep' γ e'
    · rw [if_pos h2]
      obtain ⟨e', he, hp⟩ := h2
      have hne : ¬ ep γ e := fun h => by have := huniq _ _ _ h (hsub _ _ hp); omega
      rw [if_neg hne, if_pos ⟨e', he, hsub _ _ hp⟩]; exact hRl
    · rw [if_neg h2]; exact tagWt_nonneg _ _ _ _ _ _

theorem tagWt_ge_T {ep : Nat → Nat → Prop} {γ e : Nat} {T R : Nat → Frac} {n : Nat} (h : ep γ e) :
    ftot T n ≤ tagWt ep γ e T R n := by
  unfold tagWt; rw [if_pos h]; grind

theorem tagWt_ge_R {ep : Nat → Nat → Prop} {γ e : Nat} {T R : Nat → Frac} {n : Nat}
    (h : ep γ e ∨ ∃ e', e < e' ∧ ep γ e') : ftot R n ≤ tagWt ep γ e T R n := by
  unfold tagWt
  by_cases h1 : ep γ e
  · rw [if_pos h1]; grind
  · rw [if_neg h1, if_pos (h.resolve_left h1)]; exact Rat.le_refl

/-- A valid ledger cell has at most one epoch. -/
theorem GCell.Valid.ep_uniq {c : GCell} (h : c.Valid) {e e' : Nat} {M M' : GMap}
    (h1 : 0 < c.auth (e, M)) (h2 : 0 < c.auth (e', M')) : e = e' := by
  rcases h with h | ⟨e₀, M₀, -, h0, -⟩
  · have := h (e, M); omega
  · by_cases x : (e, M) = (e₀, M₀)
    · by_cases y : (e', M') = (e₀, M₀)
      · cases x; cases y; rfl
      · have := h0 _ y; omega
    · have := h0 _ x; omega

/-- The extent claims on one block: authority claims `(S, K) ↦ count`, the fraction held at
each lower bound, and the epoch-tagged fractions and receipts by tag `(γ, e)` and bound
(`docs/sep-full-state.md` §Epoch-tagged shares). -/
@[ext] structure ECell where
  auth : Nat × BlockKind → Nat
  sh : Nat → Frac
  /-- Tagged shares: ledger `γ`, epoch `e`, lower bound `k`. -/
  tsh : Nat → Nat → Nat → Frac
  /-- Receipts of tagged shares lent out: ledger `γ`, epoch `e`, lower bound `k`. -/
  rc : Nat → Nat → Nat → Frac

namespace ECell

def unit : ECell := ⟨fun _ => 0, fun _ => Frac.zero, fun _ _ _ => Frac.zero, fun _ _ _ => Frac.zero⟩

def add (a b : ECell) : ECell :=
  ⟨fun x => a.auth x + b.auth x, fun k => (a.sh k).add (b.sh k),
    fun γ e k => (a.tsh γ e k).add (b.tsh γ e k), fun γ e k => (a.rc γ e k).add (b.rc γ e k)⟩

theorem add_comm (a b : ECell) : a.add b = b.add a := by
  ext <;> simp [add, Nat.add_comm, Frac.add_comm]

theorem add_assoc (a b c : ECell) : (a.add b).add c = a.add (b.add c) := by
  ext <;> simp [add, Nat.add_assoc, Frac.add_assoc]

@[simp] theorem add_unit (a : ECell) : a.add unit = a := by ext <;> simp [add, unit]

@[simp] theorem unit_add (a : ECell) : unit.add a = a := by ext <;> simp [add, unit]

/-- The fraction held at the bounds below `n`. -/
def total (c : ECell) : Nat → Rat
  | 0 => 0
  | n + 1 => c.total n + (c.sh n).val

theorem total_nonneg (c : ECell) : ∀ n, 0 ≤ c.total n
  | 0 => Rat.le_refl
  | n + 1 => by have := total_nonneg c n; have := (c.sh n).nonneg; simp only [total]; grind

theorem total_add (a b : ECell) : ∀ n, (a.add b).total n = a.total n + b.total n
  | 0 => by simp only [total]; grind
  | n + 1 => by have := total_add a b n; simp only [total, add, Frac.add] at *; grind

theorem total_eq (c : ECell) : ∀ n, c.total n = ftot c.sh n
  | 0 => rfl
  | n + 1 => by simp only [total, ftot, total_eq c n]

/-- At most one authority claim, held once, and at most the whole fraction. -/
def Valid (c : ECell) : Prop :=
  (∀ x, c.auth x ≤ 1) ∧ (∀ x y, 0 < c.auth x → 0 < c.auth y → x = y) ∧ ∀ n, c.total n ≤ 1

theorem Valid.of_add {a b : ECell} (h : (a.add b).Valid) : a.Valid := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x => ?_, fun x y hx hy => h2 x y ?_ ?_, fun n => ?_⟩
  · have := h1 x; simp only [add] at this; omega
  · simp only [add]; omega
  · simp only [add]; omega
  · have := h3 n; rw [total_add] at this; have := total_nonneg b n; grind

theorem valid_unit : unit.Valid :=
  ⟨fun _ => Nat.zero_le _, fun _ _ h => absurd h (Nat.lt_irrefl 0), fun n => by
    have : ∀ n, unit.total n = 0 := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [total, ih]; show (0 : Rat) + 0 = 0; grind
    rw [this]; decide⟩

/-! ### Claims under a ledger status

`ep γ e` says that ledger `γ`'s authority is at epoch `e` (`Ghost.ep`). A tagged share `(γ, e)`
is a live claim while `ep γ e`; a receipt `(γ, e)` while `ep γ e` or `γ` is at a later epoch.
Other tagged claims are dormant: they are neither counted nor required to be true. -/

/-- A claim at bound `k` that is live under `ep`: an untagged share, a tagged share of the current
epoch, or a receipt of the current or a past epoch. -/
def Req (ep : Nat → Nat → Prop) (c : ECell) (k : Nat) : Prop :=
  0 < (c.sh k).val ∨ ∃ γ e, (ep γ e ∧ 0 < (c.tsh γ e k).val) ∨
    ((ep γ e ∨ ∃ e', e < e' ∧ ep γ e') ∧ 0 < (c.rc γ e k).val)

/-- `c` holds a live claim under `ep` (an authority claim or a live share). -/
def Claims (ep : Nat → Nat → Prop) (c : ECell) : Prop :=
  (∃ S K, 0 < c.auth (S, K)) ∨ ∃ k, c.Req ep k

/-- The fraction counted below bound `n`, with the tags `(γ, e)`, `γ < N`, `e < E`. -/
noncomputable def wsum (ep : Nat → Nat → Prop) (c : ECell) (n N E : Nat) : Rat :=
  c.total n + gsum (fun γ e => tagWt ep γ e (c.tsh γ e) (c.rc γ e) n) N E

/-- No tagged claim of an epoch after the current one. -/
def FutZ (ep : Nat → Nat → Prop) (c : ECell) : Prop :=
  ∀ γ e e' k, ep γ e → e < e' → (c.tsh γ e' k).val = 0 ∧ (c.rc γ e' k).val = 0

/-- The counted fraction is at most the whole, and no tag of a future epoch exists. -/
def TagOk (ep : Nat → Nat → Prop) (c : ECell) : Prop :=
  (∀ n N E, c.wsum ep n N E ≤ 1) ∧ c.FutZ ep

/-- **The claims `c` on block `b` are true in `m` under `ep`**: an authority claim `(S, K)`
names a live block of size `S` and kind `K`, a live claim at bound `k` a live block of at least
`k` bytes; in both cases the block has a live byte (`mappedLo < size`). -/
def TrueIn (ep : Nat → Nat → Prop) (m : Mem) (b : BlockId) (c : ECell) : Prop :=
  (∀ (S : Nat) (K : BlockKind), 0 < c.auth (S, K) → ∃ blk : Block, m.blocks[b]? = some blk ∧
      blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K ∧ K.mappedLo < S) ∧
    (∀ k : Nat, c.Req ep k → ∃ blk : Block, m.blocks[b]? = some blk ∧ blk.live = true ∧
      k ≤ blk.bytes.size ∧ blk.kind.mappedLo < blk.bytes.size)

/-- `a`'s claims are among `b`'s. -/
def Le (a b : ECell) : Prop :=
  (∀ x, a.auth x ≤ b.auth x) ∧ (∀ k, (a.sh k).val ≤ (b.sh k).val) ∧
    (∀ γ e k, (a.tsh γ e k).val ≤ (b.tsh γ e k).val) ∧ ∀ γ e k, (a.rc γ e k).val ≤ (b.rc γ e k).val

theorem le_add (a b : ECell) : a.Le (a.add b) := by
  refine ⟨fun x => by simp only [add]; omega, fun k => ?_, fun γ e k => ?_, fun γ e k => ?_⟩ <;>
    simp only [add, Frac.add] <;> grind [Frac.nonneg]

theorem le_add' (a b : ECell) : b.Le (a.add b) := add_comm b a ▸ le_add b a

theorem Le.refl (a : ECell) : a.Le a :=
  ⟨fun _ => Nat.le_refl _, fun _ => Rat.le_refl, fun _ _ _ => Rat.le_refl, fun _ _ _ => Rat.le_refl⟩

theorem Le.trans {a b c : ECell} (h₁ : a.Le b) (h₂ : b.Le c) : a.Le c :=
  ⟨fun x => Nat.le_trans (h₁.1 x) (h₂.1 x), fun k => Rat.le_trans (h₁.2.1 k) (h₂.2.1 k),
    fun γ e k => Rat.le_trans (h₁.2.2.1 γ e k) (h₂.2.2.1 γ e k),
    fun γ e k => Rat.le_trans (h₁.2.2.2 γ e k) (h₂.2.2.2 γ e k)⟩

theorem Req.mono {ep ep' : Nat → Nat → Prop} {a b : ECell} {k : Nat} (hep : ∀ γ e, ep γ e → ep' γ e)
    (hle : a.Le b) (h : a.Req ep k) : b.Req ep' k := by
  rcases h with h | ⟨γ, e, ⟨he, h⟩ | ⟨he, h⟩⟩
  · exact .inl (by have := hle.2.1 k; grind)
  · exact .inr ⟨γ, e, .inl ⟨hep _ _ he, by have := hle.2.2.1 γ e k; grind⟩⟩
  · refine .inr ⟨γ, e, .inr ⟨?_, by have := hle.2.2.2 γ e k; grind⟩⟩
    rcases he with he | ⟨e', h1, h2⟩
    · exact .inl (hep _ _ he)
    · exact .inr ⟨e', h1, hep _ _ h2⟩

theorem Req_add {ep : Nat → Nat → Prop} {a b : ECell} {k : Nat} :
    (a.add b).Req ep k ↔ a.Req ep k ∨ b.Req ep k := by
  constructor
  · intro h
    have pos : ∀ x y : Frac, 0 < (x.add y).val → 0 < x.val ∨ 0 < y.val := fun x y h => by
      simp only [Frac.add] at h; have := x.nonneg; have := y.nonneg; grind
    rcases h with h | ⟨γ, e, ⟨he, h⟩ | ⟨he, h⟩⟩
    · rcases pos _ _ h with h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
    · rcases pos _ _ h with h | h
      · exact .inl (.inr ⟨γ, e, .inl ⟨he, h⟩⟩)
      · exact .inr (.inr ⟨γ, e, .inl ⟨he, h⟩⟩)
    · rcases pos _ _ h with h | h
      · exact .inl (.inr ⟨γ, e, .inr ⟨he, h⟩⟩)
      · exact .inr (.inr ⟨γ, e, .inr ⟨he, h⟩⟩)
  · rintro (h | h)
    · exact h.mono (fun _ _ h => h) (le_add a b)
    · exact h.mono (fun _ _ h => h) (le_add' a b)

theorem TrueIn.of_le {ep ep' : Nat → Nat → Prop} {m : Mem} {x : BlockId} {a b : ECell}
    (hep : ∀ γ e, ep γ e → ep' γ e) (hle : a.Le b) (h : b.TrueIn ep' m x) : a.TrueIn ep m x :=
  ⟨fun S K hp => h.1 S K (Nat.lt_of_lt_of_le hp (hle.1 _)), fun k hk => h.2 k (hk.mono hep hle)⟩

theorem total_le {a b : ECell} (hle : a.Le b) (n : Nat) : a.total n ≤ b.total n := by
  rw [total_eq, total_eq]; exact ftot_le hle.2.1 n

theorem total_mono (c : ECell) {n N : Nat} (h : n ≤ N) : c.total n ≤ c.total N := by
  rw [total_eq, total_eq]; exact ftot_mono _ h

/-- Fewer epochs (each ledger has at most one) and fewer claims count less. -/
theorem wsum_le {ep ep' : Nat → Nat → Prop} (hsub : ∀ γ e, ep γ e → ep' γ e)
    (huniq : ∀ γ e e', ep' γ e → ep' γ e' → e = e') {a b : ECell} (hle : a.Le b) (n N E : Nat) :
    a.wsum ep n N E ≤ b.wsum ep' n N E := by
  have := total_le hle n
  have := gsum_le (fun γ e => tagWt_le (ep := ep') (ep' := ep) hsub huniq (γ := γ) (e := e)
    (hle.2.2.1 γ e) (hle.2.2.2 γ e) n) N E
  simp only [wsum]; grind

theorem wsum_mono (ep : Nat → Nat → Prop) (c : ECell) {n n' N N' E E' : Nat} (hn : n ≤ n')
    (hN : N ≤ N') (hE : E ≤ E') : c.wsum ep n N E ≤ c.wsum ep n' N' E' := by
  have := c.total_mono hn
  have := gsum_le (fun γ e => tagWt_mono ep γ e (c.tsh γ e) (c.rc γ e) hn) N E
  have := gsum_mono (fun γ e => tagWt_nonneg ep γ e (c.tsh γ e) (c.rc γ e) n') hN hE
  simp only [wsum]; grind

theorem TagOk.of_le {ep ep' : Nat → Nat → Prop} (hsub : ∀ γ e, ep γ e → ep' γ e)
    (huniq : ∀ γ e e', ep' γ e → ep' γ e' → e = e') {a b : ECell} (hle : a.Le b)
    (h : b.TagOk ep') : a.TagOk ep := by
  refine ⟨fun n N E => Rat.le_trans (wsum_le hsub huniq hle n N E) (h.1 n N E),
    fun γ e e' k he hlt => ?_⟩
  have := h.2 γ e e' k (hsub _ _ he) hlt
  have := hle.2.2.1 γ e' k; have := hle.2.2.2 γ e' k
  have := (a.tsh γ e' k).nonneg; have := (a.rc γ e' k).nonneg
  grind

/-- A live claim counts. -/
theorem Req.pos {ep : Nat → Nat → Prop} {c : ECell} {k : Nat} (h : c.Req ep k) :
    ∃ N E, 0 < c.wsum ep (k + 1) N E := by
  have hg : ∀ N E, 0 ≤ gsum (fun γ e => tagWt ep γ e (c.tsh γ e) (c.rc γ e) (k + 1)) N E :=
    gsum_nonneg fun γ e => tagWt_nonneg _ _ _ _ _ _
  have ht := c.total_nonneg (k + 1)
  rcases h with h | ⟨γ, e, ⟨he, h⟩ | ⟨he, h⟩⟩
  · refine ⟨0, 0, ?_⟩
    have := le_ftot c.sh (k := k) (n := k + 1) (by omega)
    rw [← total_eq] at this
    have := hg 0 0; simp only [wsum]; grind
  · refine ⟨γ + 1, e + 1, ?_⟩
    have h1 := le_ftot (c.tsh γ e) (k := k) (n := k + 1) (by omega)
    have h2 := tagWt_ge_T (T := c.tsh γ e) (R := c.rc γ e) (n := k + 1) he
    have h3 := le_gsum (f := fun γ e => tagWt ep γ e (c.tsh γ e) (c.rc γ e) (k + 1))
      (fun γ e => tagWt_nonneg _ _ _ _ _ _) (γ := γ) (e := e) (E := e + 1) (by omega) (N := γ + 1) (by omega)
    simp only [wsum]; grind
  · refine ⟨γ + 1, e + 1, ?_⟩
    have h1 := le_ftot (c.rc γ e) (k := k) (n := k + 1) (by omega)
    have h2 := tagWt_ge_R (T := c.tsh γ e) (R := c.rc γ e) (n := k + 1) he
    have h3 := le_gsum (f := fun γ e => tagWt ep γ e (c.tsh γ e) (c.rc γ e) (k + 1))
      (fun γ e => tagWt_nonneg _ _ _ _ _ _) (γ := γ) (e := e) (E := e + 1) (by omega) (N := γ + 1) (by omega)
    simp only [wsum]; grind

theorem Claims.mono {ep ep' : Nat → Nat → Prop} {a b : ECell} (hep : ∀ γ e, ep γ e → ep' γ e)
    (hle : a.Le b) (h : a.Claims ep) : b.Claims ep' := by
  rcases h with ⟨S, K, h⟩ | ⟨k, h⟩
  · exact .inl ⟨S, K, Nat.lt_of_lt_of_le h (hle.1 _)⟩
  · exact .inr ⟨k, h.mono hep hle⟩

/-- **Dormant claims** under `ep`: no authority claim, no live share, and no tag of a future
epoch. A resource holding `bext` leaves the frame only dormant claims on the block
(`full_excl`). -/
def Dormant (ep : Nat → Nat → Prop) (d : ECell) : Prop :=
  (∀ x, d.auth x = 0) ∧ (∀ k, ¬ d.Req ep k) ∧ d.FutZ ep

/-- The weight of a tag of dormant claims is zero. -/
theorem Dormant.wt_zero {ep : Nat → Nat → Prop} {d : ECell} (hd : d.Dormant ep) {c : ECell}
    (hc : ∀ γ e k, (c.tsh γ e k).val = 0 ∧ (c.rc γ e k).val = 0) (γ e n : Nat) :
    tagWt ep γ e ((c.add d).tsh γ e) ((c.add d).rc γ e) n ≤ 0 := by
  have nr := fun k => hd.2.1 k
  unfold tagWt
  split
  · rename_i h
    have hT : ∀ k, ((c.add d).tsh γ e k).val = 0 := fun k => by
      have := (d.tsh γ e k).nonneg
      have : ¬ 0 < (d.tsh γ e k).val := fun p => nr k (.inr ⟨γ, e, .inl ⟨h, p⟩⟩)
      simp only [add, Frac.add, (hc γ e k).1]; grind
    have hR : ∀ k, ((c.add d).rc γ e k).val = 0 := fun k => by
      have := (d.rc γ e k).nonneg
      have : ¬ 0 < (d.rc γ e k).val := fun p => nr k (.inr ⟨γ, e, .inr ⟨.inl h, p⟩⟩)
      simp only [add, Frac.add, (hc γ e k).2]; grind
    rw [ftot_zero hT, ftot_zero hR]; grind
  · split
    · rename_i _ h
      have hR : ∀ k, ((c.add d).rc γ e k).val = 0 := fun k => by
        have := (d.rc γ e k).nonneg
        have : ¬ 0 < (d.rc γ e k).val := fun p => nr k (.inr ⟨γ, e, .inr ⟨.inr h, p⟩⟩)
        simp only [add, Frac.add, (hc γ e k).2]; grind
      rw [ftot_zero hR]; grind
    · grind

end ECell

/-- Ghost state: ledgers by ghost name (`GName := Nat`) and extent claims by block. -/
@[ext] structure Ghost where
  led : Nat → GCell
  extent : BlockId → ECell

namespace Ghost

def unit : Ghost := ⟨fun _ => GCell.unit, fun _ => ECell.unit⟩

def add (g₁ g₂ : Ghost) : Ghost := ⟨fun γ => (g₁.led γ).add (g₂.led γ), fun b => (g₁.extent b).add (g₂.extent b)⟩

/-- Ledger `γ`'s authority is at epoch `e`. -/
def ep (g : Ghost) (γ e : Nat) : Prop := ∃ M, 0 < (g.led γ).auth (e, M)

/-- Every ledger is valid, and every block's claims are valid and count at most the whole
fraction under the ledgers' epochs (`ECell.TagOk`). -/
def Valid (g : Ghost) : Prop :=
  (∀ γ, (g.led γ).Valid) ∧ ∀ b, (g.extent b).Valid ∧ (g.extent b).TagOk g.ep

/-- Finitely many names in use, by ledgers and by tags (a fresh name exists). -/
def Fin (g : Ghost) : Prop :=
  ∃ N, ∀ γ, N ≤ γ → g.led γ = GCell.unit ∧
    ∀ b e k, ((g.extent b).tsh γ e k).val = 0 ∧ ((g.extent b).rc γ e k).val = 0

/-- `g₁` and `g₂` compose: their sum is valid and finite. -/
def Ok (g₁ g₂ : Ghost) : Prop := Valid (add g₁ g₂) ∧ Fin (add g₁ g₂)

theorem add_comm (g₁ g₂ : Ghost) : g₁.add g₂ = g₂.add g₁ := by
  ext1
  · funext γ; exact GCell.add_comm _ _
  · funext b; exact ECell.add_comm _ _

theorem add_assoc (g₁ g₂ g₃ : Ghost) : (g₁.add g₂).add g₃ = g₁.add (g₂.add g₃) := by
  ext1
  · funext γ; exact GCell.add_assoc _ _ _
  · funext b; exact ECell.add_assoc _ _ _

@[simp] theorem add_unit (g : Ghost) : g.add unit = g := by ext1 <;> funext x <;> simp [add, unit]

@[simp] theorem unit_add (g : Ghost) : unit.add g = g := by ext1 <;> funext x <;> simp [add, unit]

theorem ep_add {a b : Ghost} {γ e : Nat} (h : a.ep γ e) : (a.add b).ep γ e := by
  obtain ⟨M, h⟩ := h; exact ⟨M, by simp only [add, GCell.add]; omega⟩

theorem ep_add' {a b : Ghost} {γ e : Nat} (h : b.ep γ e) : (a.add b).ep γ e := by
  obtain ⟨M, h⟩ := h; exact ⟨M, by simp only [add, GCell.add]; omega⟩

/-- A ledger cell has at most one epoch. -/
theorem Valid.ep_uniq {g : Ghost} (h : g.Valid) {γ e e' : Nat} (h1 : g.ep γ e) (h2 : g.ep γ e') :
    e = e' := by
  obtain ⟨M, h1⟩ := h1; obtain ⟨M', h2⟩ := h2
  exact (h.1 γ).ep_uniq h1 h2

theorem Ok.assoc {a b c : Ghost} : Ok (a.add b) c ↔ Ok a (b.add c) := by
  unfold Ok; rw [add_assoc]

theorem Ok.comm {a b : Ghost} : Ok a b ↔ Ok b a := by
  unfold Ok; rw [add_comm]

/-- Ghost state can be dropped: validity and finiteness are closed under removing a part. -/
theorem Ok.mono {a b c : Ghost} (h : Ok (a.add b) c) : Ok a c := by
  have hV := h.1
  obtain ⟨⟨hv, hx⟩, N, hN⟩ := h
  have eL : ∀ γ, ((a.add b).add c).led γ = ((a.led γ).add (c.led γ)).add (b.led γ) := fun γ => by
    simp only [add]; rw [GCell.add_assoc, GCell.add_comm (b.led γ), ← GCell.add_assoc]
  have eX : ∀ x, ((a.add b).add c).extent x = ((a.extent x).add (c.extent x)).add (b.extent x) :=
    fun x => by
      simp only [add]; rw [ECell.add_assoc, ECell.add_comm (b.extent x), ← ECell.add_assoc]
  have hsub : ∀ γ e, (a.add c).ep γ e → ((a.add b).add c).ep γ e := fun γ e ⟨M, h⟩ =>
    ⟨M, by rw [eL]; simp only [add, GCell.add] at h ⊢; omega⟩
  have hle : ∀ x, ((a.add c).extent x).Le (((a.add b).add c).extent x) := fun x => by
    rw [eX]; exact ECell.le_add _ _
  refine ⟨⟨fun γ => ?_, fun x => ⟨?_, ECell.TagOk.of_le hsub (fun _ _ _ => hV.ep_uniq) (hle x)
    (hx x).2⟩⟩, N, fun γ hγ => ⟨?_, fun x e k => ?_⟩⟩
  · have := hv γ
    rw [eL] at this
    exact GCell.Valid.of_add this
  · have := (hx x).1
    rw [eX] at this
    exact ECell.Valid.of_add this
  · have := (hN γ hγ).1
    simp only [add, GCell.add, GCell.unit, GCell.mk.injEq] at this ⊢
    obtain ⟨h1, h2⟩ := this
    exact ⟨funext fun x => by have := congrFun h1 x; omega,
      funext fun x => by have := congrFun h2 x; omega⟩
  · have := (hN γ hγ).2 x e k
    have := (hle x).2.2.1 γ e k; have := (hle x).2.2.2 γ e k
    have := (((a.add c).extent x).tsh γ e k).nonneg; have := (((a.add c).extent x).rc γ e k).nonneg
    grind

end Ghost

/-- The extent claims of `g` are true in `m` under `g`'s ledgers (`ECell.TrueIn`). -/
def ExtTrue (m : Mem) (g : Ghost) : Prop := ∀ b, (g.extent b).TrueIn g.ep m b

def KeepsExt (m m' : Mem) : Prop :=
  ∀ (b : BlockId) (blk : Block), m.blocks[b]? = some blk → blk.live = true → ∃ blk', m'.blocks[b]? = some blk' ∧
    blk'.live = true ∧ blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind

theorem KeepsExt.refl (m : Mem) : KeepsExt m m := fun _ blk h hl => ⟨blk, h, hl, rfl, rfl⟩

theorem KeepsExt.trans {m₁ m₂ m₃ : Mem} (h₁ : KeepsExt m₁ m₂) (h₂ : KeepsExt m₂ m₃) : KeepsExt m₁ m₃ :=
  fun b blk hb hl => by
    obtain ⟨blk', hb', hl', hs, hk⟩ := h₁ b blk hb hl
    obtain ⟨blk'', hb'', hl'', hs', hk'⟩ := h₂ b blk' hb' hl'
    exact ⟨blk'', hb'', hl'', hs'.trans hs, hk'.trans hk⟩

theorem KeepsExt.of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : KeepsExt m m' :=
  fun _ blk hb hl => ⟨blk, by rw [h]; exact hb, hl, rfl, rfl⟩

/-- Replacing a block by one with the same liveness, size and kind keeps every extent. -/
theorem KeepsExt.set {m m' : Mem} {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : nb.live = blk.live) (hs : nb.bytes.size = blk.bytes.size) (hk : nb.kind = blk.kind)
    (h : m'.blocks = m.blocks.set! b nb) : KeepsExt m m' := by
  intro b' x hx hlx
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : b = b'
  · subst e
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    rw [hb] at hx; cases hx
    exact ⟨nb, by simp [hlt], by rw [hl]; exact hlx, hs, hk⟩
  · exact ⟨x, by simp [e, hx], hlx, rfl, rfl⟩

/-- Pushing a block keeps every extent. -/
theorem KeepsExt.push {m m' : Mem} {nb : Block} (h : m'.blocks = m.blocks.push nb) : KeepsExt m m' := by
  intro b x hx hl
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hx).1
  exact ⟨x, by rw [h, Array.getElem?_push]; simp [Nat.ne_of_lt hlt, hx], hl, rfl, rfl⟩

theorem ExtTrue.keep {m m' : Mem} {g : Ghost} (h : ExtTrue m g) (hk : KeepsExt m m') :
    ExtTrue m' g := fun b => by
  obtain ⟨ha, hs⟩ := h b
  refine ⟨fun S K hp => ?_, fun k hp => ?_⟩
  · obtain ⟨blk, hb, hl, hS, hK, hlo⟩ := ha S K hp
    obtain ⟨blk', hb', hl', hs', hk'⟩ := hk b blk hb hl
    exact ⟨blk', hb', hl', hs'.trans hS, hk'.trans hK, hlo⟩
  · obtain ⟨blk, hb, hl, hkS, hlo⟩ := hs k hp
    obtain ⟨blk', hb', hl', hs', hk'⟩ := hk b blk hb hl
    exact ⟨blk', hb', hl', by omega, by rw [hk', hs']; exact hlo⟩

theorem ExtTrue.of_add {m : Mem} {a b : Ghost} (h : ExtTrue m (a.add b)) : ExtTrue m a :=
  fun x => ECell.TrueIn.of_le (fun _ _ h => Ghost.ep_add h) (ECell.le_add _ _) (h x)

/-- The ghost states of a resource and its frame compose, and their extent claims are true. -/
def GOk (m : Mem) (g gF : Ghost) : Prop := Ghost.Ok g gF ∧ ExtTrue m (g.add gF)

theorem GOk.assoc {m : Mem} {a b c : Ghost} : GOk m (a.add b) c ↔ GOk m a (b.add c) := by
  unfold GOk; rw [Ghost.add_assoc, Ghost.Ok.assoc]

theorem GOk.mono {m : Mem} {a b c : Ghost} (h : GOk m (a.add b) c) : GOk m a c := by
  refine ⟨Ghost.Ok.mono h.1, ?_⟩
  have e : (a.add b).add c = (a.add c).add b := by
    rw [Ghost.add_assoc, Ghost.add_comm b, ← Ghost.add_assoc]
  have := h.2; rw [e] at this; exact ExtTrue.of_add this

theorem GOk.keep {m m' : Mem} {g gF : Ghost} (h : GOk m g gF) (hk : KeepsExt m m') : GOk m' g gF :=
  ⟨h.1, h.2.keep hk⟩

/-- A ghost state without extent claims composes in every memory where it composes in one. -/
theorem GOk.of_unit {m : Mem} {gF : Ghost} (h : GOk m Ghost.unit gF) (m' : Mem)
    (hF : ExtTrue m' gF) : GOk m' Ghost.unit gF := ⟨h.1, by simpa using hF⟩

/-! ## Resources and assertions -/


structure Res where
  heap : FHeap
  know : Know
  gh : Ghost

abbrev FAssn := Res → Prop

namespace FAssn

/-- No bytes, no knowledge and no ghost state. -/
def emp : FAssn := fun r => r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.unit

/-- A fact that owns nothing. -/
def lift (φ : Prop) : FAssn := fun r => φ ∧ emp r

def sep (P Q : FAssn) : FAssn := fun r =>
  ∃ r₁ r₂, FHeap.Disjoint r₁.heap r₂.heap ∧
    r = ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩ ∧ P r₁ ∧ Q r₂

def ex {γ : Type} (P : γ → FAssn) : FAssn := fun r => ∃ x, P x r

/-- A legacy assertion, on the bytes without their tags (any atomic layout), with no knowledge
and no ghost state. -/
def up (P : Assn) : FAssn := fun r => P r.heap.erase ∧ r.know = Know.none ∧ r.gh = Ghost.unit

end FAssn

scoped infixr:35 " ⋆ " => FAssn.sep
scoped notation "⟪" φ "⟫" => FAssn.lift φ

open FAssn

/-- **Persistent knowledge** (`□ blockAddr b A`): block `b` exists, at address `A`. Owns no
bytes; true in every later memory (`KMono`), also after `free`. -/
def known (b : BlockId) (A : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ (r.know = fun b' A' => b' = b ∧ A' = A) ∧ r.gh = Ghost.unit

/-- `h` owns exactly the bytes `bs` at `p` (block address `A`, size `S`, kind `K`), each with the
atomic tag `tg`. -/
def abytesAt (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (tg : Option (Nat × Nat)) :
    FAssn := fun r =>
  r.know = Know.none ∧ r.gh = Ghost.unit ∧ ∃ b, p.block = some b ∧ 0 ≤ p.off ∧ ∀ l : Loc, r.heap l =
    if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    then some ⟨⟨bs[l.2 - p.off.toNat]!, A, S, K⟩, tg⟩ else none

/-- **Atomic points-to** `p ↦ₐ v` for a 64-bit word: the 8 bytes at the 8-aligned `p` hold `v`,
and their tag constraint is the location `(p.off, 8)`: the layout over them is that location or
none (no atomic op yet). So an atomic op on it never hits the mixed-size policy (O3). -/
def apts (p : Ptr) (v : BitVec 64) : FAssn := fun r => ∃ A S K bs,
  (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bs.size = 8 ∧ intOfBytes 64 bs = pure v ∧
  abytesAt p A S K bs (some (p.off.toNat, 8)) r

section Laws

variable {P Q R : FAssn} {r : Res}

theorem res_eta (r : Res) : r = ⟨r.heap, r.know, r.gh⟩ := rfl

theorem sep_comm : (P ⋆ Q) r → (Q ⋆ P) r := by
  rintro ⟨r₁, r₂, hd, rfl, hp, hq⟩
  exact ⟨r₂, r₁, hd.symm, by rw [FHeap.union_comm hd, Know.union_comm, Ghost.add_comm], hq, hp⟩

theorem sep_assoc : ((P ⋆ Q) ⋆ R) r → (P ⋆ (Q ⋆ R)) r := by
  rintro ⟨r₁₂, r₃, hd, rfl, ⟨r₁, r₂, hd', rfl, hp, hq⟩, hr⟩
  obtain ⟨hd₁₃, hd₂₃⟩ := FHeap.disjoint_union_left.mp hd
  exact ⟨r₁, ⟨r₂.heap ∪ r₃.heap, r₂.know.union r₃.know, r₂.gh.add r₃.gh⟩,
    FHeap.disjoint_union_right.mpr ⟨hd', hd₁₃⟩,
    by simp only [FHeap.union_assoc, Know.union_assoc, Ghost.add_assoc], hp, r₂, r₃, hd₂₃, rfl, hq, hr⟩

theorem sep_assoc' : (P ⋆ (Q ⋆ R)) r → ((P ⋆ Q) ⋆ R) r := by
  rintro ⟨r₁, r₂₃, hd, rfl, hp, ⟨r₂, r₃, hd', rfl, hq, hr⟩⟩
  obtain ⟨hd₁₂, hd₁₃⟩ := FHeap.disjoint_union_right.mp hd
  exact ⟨⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩, r₃,
    FHeap.disjoint_union_left.mpr ⟨hd₁₃, hd'⟩,
    by simp only [FHeap.union_assoc, Know.union_assoc, Ghost.add_assoc], ⟨r₁, r₂, hd₁₂, rfl, hp, hq⟩, hr⟩

theorem sep_mono {P' Q' : FAssn} (hp : ∀ r, P r → P' r) (hq : ∀ r, Q r → Q' r) :
    (P ⋆ Q) r → (P' ⋆ Q') r := by
  rintro ⟨r₁, r₂, hd, rfl, a, b⟩
  exact ⟨r₁, r₂, hd, rfl, hp _ a, hq _ b⟩

theorem sep_mono_left (hp : ∀ r, P r → Q r) : (P ⋆ R) r → (Q ⋆ R) r :=
  sep_mono hp (fun _ h => h)

theorem sep_mono_right (hq : ∀ r, Q r → R r) : (P ⋆ Q) r → (P ⋆ R) r :=
  sep_mono (fun _ h => h) hq

theorem sep_emp : (P ⋆ emp) r ↔ P r := by
  constructor
  · rintro ⟨r₁, r₂, -, rfl, hp, h2, k2, g2⟩
    rw [h2, k2, g2, FHeap.union_empty, Know.union_none, Ghost.add_unit]; exact hp
  · intro hp
    exact ⟨r, ⟨FHeap.empty, Know.none, Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Know.union_none, Ghost.add_unit], hp, rfl, rfl, rfl⟩

theorem sep_lift {φ : Prop} : (⟪φ⟫ ⋆ P) r ↔ φ ∧ P r := by
  constructor
  · rintro ⟨r₁, r₂, -, rfl, ⟨hφ, h1, k1, g1⟩, hp⟩
    rw [h1, k1, g1, FHeap.empty_union, Know.none_union, Ghost.unit_add]; exact ⟨hφ, hp⟩
  · rintro ⟨hφ, hp⟩
    exact ⟨⟨FHeap.empty, Know.none, Ghost.unit⟩, r, (FHeap.disjoint_empty _).symm,
      by rw [FHeap.empty_union, Know.none_union, Ghost.unit_add], ⟨hφ, rfl, rfl, rfl⟩, hp⟩

theorem sep_ex {γ : Type} {P : γ → FAssn} : (ex P ⋆ Q) r ↔ ∃ x, (P x ⋆ Q) r := by
  constructor
  · rintro ⟨r₁, r₂, hd, rfl, ⟨x, hp⟩, hq⟩; exact ⟨x, r₁, r₂, hd, rfl, hp, hq⟩
  · rintro ⟨x, r₁, r₂, hd, rfl, hp, hq⟩; exact ⟨r₁, r₂, hd, rfl, ⟨x, hp⟩, hq⟩

/-- Knowledge is duplicable. -/
theorem known_dup {b : BlockId} {A : Nat} (h : known b A r) : (known b A ⋆ known b A) r := by
  obtain ⟨hh, hk, hg⟩ := h
  refine ⟨r, r, fun _ => .inl (by rw [hh]; rfl), ?_, ⟨hh, hk, hg⟩, ⟨hh, hk, hg⟩⟩
  obtain ⟨rh, rk, rg⟩ := r
  simp only at hh hg ⊢
  subst hh hg
  rw [FHeap.union_empty, Know.union_self, Ghost.add_unit]

/-- A legacy separating conjunction is a full one (the tags split with the bytes). -/
theorem up_sep {P Q : Assn} (h : up (P ∗ Q) r) : (up P ⋆ up Q) r := by
  obtain ⟨⟨h₁, h₂, hd, he, hp, hq⟩, hk, hg⟩ := h
  let f₁ : FHeap := fun l => if h₁ l = Option.none then Option.none else r.heap l
  let f₂ : FHeap := fun l => if h₁ l = Option.none then r.heap l else Option.none
  have hl : ∀ l, r.heap.erase l = (h₁ ∪ h₂) l := fun l => congrFun he l
  have e₁ : f₁.erase = h₁ := by
    funext l
    have := hl l
    simp only [FHeap.erase, Heap.union_apply] at this ⊢
    by_cases n : h₁ l = Option.none
    · simp [f₁, n]
    · simp only [f₁, n, ↓reduceIte]
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp n
      rw [this, hc]; rfl
  have e₂ : f₂.erase = h₂ := by
    funext l
    have := hl l
    simp only [FHeap.erase, Heap.union_apply] at this ⊢
    by_cases n : h₁ l = Option.none
    · simp only [f₂, n, ↓reduceIte]; rw [this, n]; rfl
    · simp only [f₂, n, ↓reduceIte]
      rcases hd l with e | e
      · exact absurd e n
      · rw [e]; rfl
  refine ⟨⟨f₁, Know.none, Ghost.unit⟩, ⟨f₂, Know.none, Ghost.unit⟩, fun l => ?_, ?_,
    ⟨show P f₁.erase by rw [e₁]; exact hp, rfl, rfl⟩, ⟨show Q f₂.erase by rw [e₂]; exact hq, rfl, rfl⟩⟩
  · by_cases n : h₁ l = Option.none
    · left; simp [f₁, n]
    · right; simp [f₂, n]
  · rw [res_eta r, hk, hg, Know.union_self, Ghost.add_unit]
    congr 1
    funext l
    by_cases n : h₁ l = Option.none <;> simp [f₁, f₂, n]

/-- And back. -/
theorem sep_up {P Q : Assn} (h : (up P ⋆ up Q) r) : up (P ∗ Q) r := by
  obtain ⟨r₁, r₂, hd, rfl, ⟨hp, k1, g1⟩, ⟨hq, k2, g2⟩⟩ := h
  refine ⟨⟨_, _, FHeap.erase_disjoint hd, FHeap.erase_union _ _, hp, hq⟩, ?_, ?_⟩
  · simp only [k1, k2, Know.union_none]
  · simp only [g1, g2, Ghost.add_unit]

theorem up_lift {φ : Prop} {P : Assn} : up (⌜φ⌝ ∗ P) r ↔ φ ∧ up P r := by
  constructor
  · rintro ⟨h, hk⟩; obtain ⟨hφ, hp⟩ := Zig.sep_lift.mp h; exact ⟨hφ, hp, hk⟩
  · rintro ⟨hφ, hp, hk⟩; exact ⟨Zig.sep_lift.mpr ⟨hφ, hp⟩, hk⟩

theorem up_emp : up Assn.emp r ↔ emp r := by
  constructor
  · rintro ⟨h, hk⟩
    refine ⟨funext fun l => ?_, hk⟩
    have := congrFun h l
    simp only [FHeap.erase, Heap.empty, Option.map_eq_none_iff] at this
    exact this
  · rintro ⟨h, hk⟩; exact ⟨by rw [h]; rfl, hk⟩

theorem up_ex {γ : Type} {P : γ → Assn} : up (Assn.ex P) r ↔ ∃ x, up (P x) r := by
  constructor
  · rintro ⟨⟨x, h⟩, hk⟩; exact ⟨x, h, hk⟩
  · rintro ⟨x, h, hk⟩; exact ⟨⟨x, h⟩, hk⟩

/-- An atomic word's bytes, as legacy owned bytes. -/
theorem abytesAt_bytesAt {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {tg : Option (Nat × Nat)} (h : abytesAt p A S K bs tg r) : bytesAt p A S K bs r.heap.erase := by
  obtain ⟨-, -, b, hb, h0, hl⟩ := h
  refine ⟨b, hb, h0, fun l => ?_⟩
  simp only [FHeap.erase, hl l]
  split <;> rfl

/-! ### `⋆` as an associative, commutative operation (`ac_rfl` on `FAssn`) -/

theorem sep_comm_eq (P Q : FAssn) : (P ⋆ Q) = (Q ⋆ P) :=
  funext fun _ => propext ⟨sep_comm, sep_comm⟩

theorem sep_assoc_eq (P Q R : FAssn) : ((P ⋆ Q) ⋆ R) = (P ⋆ (Q ⋆ R)) :=
  funext fun _ => propext ⟨sep_assoc, sep_assoc'⟩

instance : Std.Associative (α := FAssn) (· ⋆ ·) := ⟨sep_assoc_eq⟩
instance : Std.Commutative (α := FAssn) (· ⋆ ·) := ⟨sep_comm_eq⟩

theorem sep_left_comm_eq (P Q R : FAssn) : (P ⋆ (Q ⋆ R)) = (Q ⋆ (P ⋆ R)) := by ac_rfl

theorem sep_ex_eq {γ : Type} (P : γ → FAssn) (Q : FAssn) :
    (FAssn.ex P ⋆ Q) = FAssn.ex fun x => P x ⋆ Q :=
  funext fun _ => propext sep_ex

/-- Rewrite a held assertion along an equation (`ac_rfl`). -/
theorem of_eq {P Q : FAssn} {r : Res} (e : P = Q) (h : P r) : Q r := e ▸ h

end Laws

/-! ## Cells with their block's actual extent -/

/-- `h` with each cell's size and kind read from `m` (the cells of `FMatch` up to `Cell.norm`
become exactly `m`'s live bytes, `Holds.fix_exact`). -/
def FHeap.fix (m : Mem) (h : FHeap) : FHeap := fun l => (h l).map fun fc =>
  match m.blocks[l.1]? with
  | some blk => ⟨{ fc.cell with size := blk.bytes.size, kind := blk.kind }, fc.atom⟩
  | none => fc

/-- `r` with its cells' sizes and kinds read from `m`. -/
def Res.fix (m : Mem) (r : Res) : Res := ⟨r.heap.fix m, r.know, r.gh⟩

theorem FHeap.fix_none {m : Mem} {h : FHeap} {l : Loc} : h.fix m l = none ↔ h l = none := by
  simp [FHeap.fix]

theorem FHeap.fix_disjoint {m : Mem} {h₁ h₂ : FHeap} (hd : FHeap.Disjoint h₁ h₂) :
    FHeap.Disjoint (h₁.fix m) (h₂.fix m) := fun l => by
  rcases hd l with e | e
  · exact .inl (FHeap.fix_none.mpr e)
  · exact .inr (FHeap.fix_none.mpr e)

theorem FHeap.fix_union (m : Mem) (h₁ h₂ : FHeap) : (h₁ ∪ h₂).fix m = h₁.fix m ∪ h₂.fix m := by
  funext l; simp only [FHeap.fix, FHeap.union_apply]; cases h₁ l <;> rfl

/-! ## Extent assertions -/

namespace ECell

/-- The authority over extent `(S, K)` holding the fraction `q` (at bound `0`). -/
def auth1 (S : Nat) (K : BlockKind) (q : Frac) : ECell :=
  ⟨fun x => if x = (S, K) then 1 else 0, fun k => if k = 0 then q else Frac.zero,
    fun _ _ _ => Frac.zero, fun _ _ _ => Frac.zero⟩

/-- A share: the fraction `q` at the lower bound `k`. -/
def share (q : Frac) (k : Nat) : ECell :=
  ⟨fun _ => 0, fun k' => if k' = k then q else Frac.zero, fun _ _ _ => Frac.zero, fun _ _ _ => Frac.zero⟩

/-- A tagged share: the fraction `q` at the lower bound `k`, tagged `(γ, e)`. -/
def tshare (γ e : Nat) (q : Frac) (k : Nat) : ECell :=
  ⟨fun _ => 0, fun _ => Frac.zero, fun γ' e' k' => if γ' = γ ∧ e' = e ∧ k' = k then q else Frac.zero,
    fun _ _ _ => Frac.zero⟩

/-- A receipt: the fraction `q` lent at the lower bound `k` as a share tagged `(γ, e)`. -/
def rcpt (γ e : Nat) (q : Frac) (k : Nat) : ECell :=
  ⟨fun _ => 0, fun _ => Frac.zero, fun _ _ _ => Frac.zero,
    fun γ' e' k' => if γ' = γ ∧ e' = e ∧ k' = k then q else Frac.zero⟩

/-- A share with an optional tag. -/
def shareT : Option (Nat × Nat) → Frac → Nat → ECell
  | none, q, k => share q k
  | some (γ, e), q, k => tshare γ e q k

@[simp] theorem shareT_none (q : Frac) (k : Nat) : shareT none q k = share q k := rfl

@[simp] theorem shareT_some (γ e : Nat) (q : Frac) (k : Nat) : shareT (some (γ, e)) q k = tshare γ e q k := rfl

theorem auth1_total (S : Nat) (K : BlockKind) (n : Nat) :
    (auth1 S K Frac.one).total (n + 1) = 1 := by
  induction n with
  | zero => simp only [total, auth1, if_pos, Frac.one]; grind
  | succ n ih => rw [total, ih]; simp only [auth1, Frac.zero]; grind

theorem auth1_valid (S : Nat) (K : BlockKind) : (auth1 S K Frac.one).Valid := by
  refine ⟨fun x => by simp only [auth1]; split <;> omega,
    fun x y hx hy => by simp only [auth1] at hx hy; split at hx <;> split at hy <;> simp_all,
    fun n => ?_⟩
  cases n with
  | zero => simp only [total]; decide
  | succ n => rw [auth1_total]; decide

theorem auth1_add_tsh (S : Nat) (K : BlockKind) (q : Frac) (d : ECell) :
    ((auth1 S K q).add d).tsh = d.tsh := by funext γ e k; simp [add, auth1]

theorem auth1_add_rc (S : Nat) (K : BlockKind) (q : Frac) (d : ECell) :
    ((auth1 S K q).add d).rc = d.rc := by funext γ e k; simp [add, auth1]

theorem wsum_auth1_add (ep : Nat → Nat → Prop) (S : Nat) (K : BlockKind) (q : Frac) (d : ECell)
    (n N E : Nat) : ((auth1 S K q).add d).wsum ep n N E = (auth1 S K q).total n + d.wsum ep n N E := by
  simp only [wsum, total_add, auth1_add_tsh, auth1_add_rc]; grind

theorem Dormant.sh_zero {ep : Nat → Nat → Prop} {d : ECell} (hd : d.Dormant ep) (k : Nat) :
    (d.sh k).val = 0 := by
  have := (d.sh k).nonneg; have : ¬ 0 < (d.sh k).val := fun h => hd.2.1 k (.inl h); grind

theorem Dormant.wsum_le {ep : Nat → Nat → Prop} {d : ECell} (hd : d.Dormant ep) (n N E : Nat) :
    d.wsum ep n N E ≤ 0 := by
  have ht : d.total n = 0 := by rw [total_eq, ftot_zero hd.sh_zero]
  have := gsum_zero (f := fun γ e => tagWt ep γ e (d.tsh γ e) (d.rc γ e) n) (fun γ e => by
    have := hd.wt_zero (c := unit) (fun _ _ _ => ⟨rfl, rfl⟩) γ e n; simpa using this) N E
  simp only [wsum]; grind

/-- The full authority and dormant claims compose. -/
theorem Dormant.auth1_ok {ep : Nat → Nat → Prop} {d : ECell} (hd : d.Dormant ep) {S : Nat}
    {K : BlockKind} : ((auth1 S K Frac.one).add d).Valid ∧ ((auth1 S K Frac.one).add d).TagOk ep := by
  have ea : ((auth1 S K Frac.one).add d).auth = (auth1 S K Frac.one).auth := by
    funext x; simp [add, hd.1 x]
  have hw : ∀ n N E, ((auth1 S K Frac.one).add d).wsum ep n N E ≤ 1 := fun n N E => by
    rw [wsum_auth1_add]
    have := hd.wsum_le n N E; have := (auth1_valid S K).2.2 n; grind
  refine ⟨⟨fun x => by rw [ea]; exact (auth1_valid S K).1 x,
    fun x y hx hy => (auth1_valid S K).2.1 x y (by rw [← ea]; exact hx) (by rw [← ea]; exact hy),
    fun n => ?_⟩, hw, fun γ e e' k he hlt => ?_⟩
  · have := hw n 0 0; simp only [wsum, gsum] at this; grind
  · rw [auth1_add_tsh, auth1_add_rc]; exact hd.2.2 γ e e' k he hlt

/-- A live claim of the full authority with dormant claims is the authority's share at `0`. -/
theorem Dormant.req_auth1 {ep : Nat → Nat → Prop} {d : ECell} (hd : d.Dormant ep) {S : Nat}
    {K : BlockKind} {q : Frac} {k : Nat} (h : ((auth1 S K q).add d).Req ep k) : k = 0 := by
  rcases Req_add.mp h with h | h
  · rcases h with h | ⟨γ, e, ⟨-, h⟩ | ⟨-, h⟩⟩
    · simp only [auth1] at h; split at h
      · assumption
      · simp [Frac.zero] at h
    · simp [auth1, Frac.zero] at h
    · simp [auth1, Frac.zero] at h
  · exact absurd h (hd.2.1 k)

/-- Claims that are not live, with no tag of a future epoch, are dormant. -/
theorem dormant_of_not_claims {ep : Nat → Nat → Prop} {c : ECell} (h : ¬ c.Claims ep) (hf : c.FutZ ep) :
    c.Dormant ep :=
  ⟨fun x => Nat.eq_zero_of_not_pos fun hp => h (.inl ⟨x.1, x.2, hp⟩), fun k hk => h (.inr ⟨k, hk⟩), hf⟩

/-- **The full authority leaves only dormant claims**: what composes validly with `bext`'s
claims holds no authority claim, no live share and no tag of a future epoch. -/
theorem dormant_of_auth1 {ep : Nat → Nat → Prop} {d : ECell} {S : Nat} {K : BlockKind}
    (hv : ((auth1 S K Frac.one).add d).Valid) (ht : ((auth1 S K Frac.one).add d).TagOk ep) :
    d.Dormant ep := by
  obtain ⟨h1, h2, -⟩ := hv
  refine ⟨fun x => ?_, fun k hk => ?_, fun γ e e' k he hlt => ?_⟩
  · have := h1 x
    by_cases hx : x = (S, K)
    · subst hx; simp [add, auth1] at this; omega
    · rcases Nat.eq_zero_or_pos (d.auth x) with h | h
      · exact h
      · exact absurd (h2 (S, K) x (by simp [add, auth1]; omega) (by simp only [add]; omega)).symm hx
  · obtain ⟨N, E, hp⟩ := hk.pos
    have := ht.1 (k + 1) N E
    rw [wsum_auth1_add, auth1_total] at this
    grind
  · have := ht.2 γ e e' k he hlt
    rwa [auth1_add_tsh, auth1_add_rc] at this

end ECell

/-- The ghost state with the extent cell `c` at block `b` and nothing else. -/
def Ghost.atExt (b : BlockId) (c : ECell) : Ghost :=
  ⟨fun _ => GCell.unit, fun b' => if b' = b then c else ECell.unit⟩

theorem Ghost.atExt_add (b : BlockId) (c c' : ECell) :
    (Ghost.atExt b c).add (Ghost.atExt b c') = Ghost.atExt b (c.add c') := by
  ext1
  · funext γ; simp [Ghost.add, Ghost.atExt]
  · funext b'; simp only [Ghost.add, Ghost.atExt]; split <;> simp

/-- **The authority over block `b`'s extent with the fraction `q`**: `b` is live, `S` bytes,
kind `K` (mapping start included); shares of `1 - q` are out. Owns no bytes. -/
def bauth (b : BlockId) (S : Nat) (K : BlockKind) (q : Frac) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atExt b (ECell.auth1 S K q)

/-- **The full extent of block `b`**: the authority with every share back. Only it changes the
block's size or start, or ends it (`docs/sep-full-state.md` §Block extents). -/
def bext (b : BlockId) (S : Nat) (K : BlockKind) : FAssn := bauth b S K Frac.one

/-- **A share of block `b`'s extent**: a positive fraction `q`; `b` is live with at least `k`
bytes while the share is held. With a tag `t = some (γ, e)` (`docs/sep-full-state.md`
§Epoch-tagged shares) the share counts and is true only while ledger `γ` is at epoch `e`. -/
def bshare (b : BlockId) (q : Frac) (k : Nat) (t : Option (Nat × Nat) := none) : FAssn := fun r =>
  0 < q.val ∧ r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atExt b (ECell.shareT t q k)

/-- **A receipt** for the fraction `q` of block `b`'s extent lent at bound `k` as a share tagged
`(γ, e)`: it cancels against that share (`EUpd.returnT`) or, once ledger `γ` is past epoch `e`,
turns back into an untagged share (`EUpd.revoke`). -/
def brcpt (b : BlockId) (q : Frac) (k γ e : Nat) : FAssn := fun r =>
  0 < q.val ∧ r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atExt b (ECell.rcpt γ e q k)

/-- Extents of the blocks `E` (full), as one ghost state. -/
def Ghost.exts (E : BlockId → Option (Nat × BlockKind)) : Ghost :=
  ⟨fun _ => GCell.unit, fun b => match E b with
    | some (S, K) => ECell.auth1 S K Frac.one
    | none => ECell.unit⟩

/-- A legacy assertion with the full extents `E` of its blocks (`FTriple.ofTriple`). -/
def upE (P : Assn) (E : BlockId → Option (Nat × BlockKind)) : FAssn := fun r =>
  P r.heap.erase ∧ r.know = Know.none ∧ r.gh = Ghost.exts E

theorem Ghost.ep_exts_add {E : BlockId → Option (Nat × BlockKind)} {g : Ghost} :
    ((Ghost.exts E).add g).ep = g.ep := by
  funext γ e; simp [Ghost.ep, Ghost.add, Ghost.exts]

theorem Ghost.exts_add_tags (E : BlockId → Option (Nat × BlockKind)) (g : Ghost) (b : BlockId) :
    ((Ghost.exts E).add g).extent b = ((Ghost.exts E).extent b).add (g.extent b) ∧
    (∀ γ e k, ((((Ghost.exts E).add g).extent b).tsh γ e k).val = ((g.extent b).tsh γ e k).val ∧
      ((((Ghost.exts E).add g).extent b).rc γ e k).val = ((g.extent b).rc γ e k).val) := by
  refine ⟨rfl, fun γ e k => ?_⟩
  simp only [Ghost.add, Ghost.exts, ECell.add]
  split <;> simp [ECell.auth1, ECell.unit]

@[simp] theorem Ghost.exts_none : Ghost.exts (fun _ => none) = Ghost.unit := by
  ext1 <;> funext x <;> rfl

theorem upE_none {P : Assn} {r : Res} : upE P (fun _ => none) r ↔ up P r := by
  simp [upE, up]


end Full
end Zig
