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

/-- The extent claims on one block: authority claims `(S, K) ↦ count` and the fraction held at
each lower bound. -/
@[ext] structure ECell where
  auth : Nat × BlockKind → Nat
  sh : Nat → Frac

namespace ECell

def unit : ECell := ⟨fun _ => 0, fun _ => Frac.zero⟩

def add (a b : ECell) : ECell := ⟨fun x => a.auth x + b.auth x, fun k => (a.sh k).add (b.sh k)⟩

theorem add_comm (a b : ECell) : a.add b = b.add a := by
  ext x <;> simp [add, Nat.add_comm, Frac.add_comm]

theorem add_assoc (a b c : ECell) : (a.add b).add c = a.add (b.add c) := by
  ext x <;> simp [add, Nat.add_assoc, Frac.add_assoc]

@[simp] theorem add_unit (a : ECell) : a.add unit = a := by ext x <;> simp [add, unit]

@[simp] theorem unit_add (a : ECell) : unit.add a = a := by ext x <;> simp [add, unit]

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

end ECell

/-- Ghost state: ledgers by ghost name (`GName := Nat`) and extent claims by block. -/
@[ext] structure Ghost where
  led : Nat → GCell
  extent : BlockId → ECell

namespace Ghost

def unit : Ghost := ⟨fun _ => GCell.unit, fun _ => ECell.unit⟩

def add (g₁ g₂ : Ghost) : Ghost := ⟨fun γ => (g₁.led γ).add (g₂.led γ), fun b => (g₁.extent b).add (g₂.extent b)⟩

def Valid (g : Ghost) : Prop := (∀ γ, (g.led γ).Valid) ∧ ∀ b, (g.extent b).Valid

/-- Finitely many names in use (a fresh name exists). -/
def Fin (g : Ghost) : Prop := ∃ N, ∀ γ, N ≤ γ → g.led γ = GCell.unit

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

theorem Ok.assoc {a b c : Ghost} : Ok (a.add b) c ↔ Ok a (b.add c) := by
  unfold Ok; rw [add_assoc]

theorem Ok.comm {a b : Ghost} : Ok a b ↔ Ok b a := by
  unfold Ok; rw [add_comm]

/-- Ghost state can be dropped: validity and finiteness are closed under removing a part. -/
theorem Ok.mono {a b c : Ghost} (h : Ok (a.add b) c) : Ok a c := by
  obtain ⟨⟨hv, hx⟩, N, hN⟩ := h
  refine ⟨⟨fun γ => ?_, fun x => ?_⟩, N, fun γ hγ => ?_⟩
  · have := hv γ
    have e : ((a.add b).add c).led γ = ((a.led γ).add (c.led γ)).add (b.led γ) := by
      simp only [add]; rw [GCell.add_assoc, GCell.add_comm (b.led γ), ← GCell.add_assoc]
    rw [e] at this
    exact GCell.Valid.of_add this
  · have := hx x
    have e : ((a.add b).add c).extent x = ((a.extent x).add (c.extent x)).add (b.extent x) := by
      simp only [add]; rw [ECell.add_assoc, ECell.add_comm (b.extent x), ← ECell.add_assoc]
    rw [e] at this
    exact ECell.Valid.of_add this
  · have := hN γ hγ
    simp only [add, GCell.add, GCell.unit, GCell.mk.injEq] at this ⊢
    obtain ⟨h1, h2⟩ := this
    exact ⟨funext fun x => by have := congrFun h1 x; omega,
      funext fun x => by have := congrFun h2 x; omega⟩

end Ghost

/-- The extent claims of `e` are true in `m`: an authority claim `(S, K)` names a live block of
size `S` and kind `K`, and a share at bound `k` a live block of at least `k` bytes; in both cases
the block has a live byte (`mappedLo < size`). -/
def ExtTrue (m : Mem) (e : BlockId → ECell) : Prop :=
  ∀ b : BlockId, (∀ (S : Nat) (K : BlockKind), 0 < (e b).auth (S, K) → ∃ blk : Block, m.blocks[b]? = some blk ∧ blk.live = true ∧
      blk.bytes.size = S ∧ blk.kind = K ∧ K.mappedLo < S) ∧
    (∀ k : Nat, 0 < ((e b).sh k).val → ∃ blk : Block, m.blocks[b]? = some blk ∧ blk.live = true ∧
      k ≤ blk.bytes.size ∧ blk.kind.mappedLo < blk.bytes.size)

/-- `m'` keeps every block that is live in `m`: live, with the same size and kind. -/
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

theorem ExtTrue.keep {m m' : Mem} {e : BlockId → ECell} (h : ExtTrue m e) (hk : KeepsExt m m') :
    ExtTrue m' e := fun b => by
  obtain ⟨ha, hs⟩ := h b
  refine ⟨fun S K hp => ?_, fun k hp => ?_⟩
  · obtain ⟨blk, hb, hl, hS, hK, hlo⟩ := ha S K hp
    obtain ⟨blk', hb', hl', hs', hk'⟩ := hk b blk hb hl
    exact ⟨blk', hb', hl', hs'.trans hS, hk'.trans hK, hlo⟩
  · obtain ⟨blk, hb, hl, hkS, hlo⟩ := hs k hp
    obtain ⟨blk', hb', hl', hs', hk'⟩ := hk b blk hb hl
    exact ⟨blk', hb', hl', by omega, by rw [hk', hs']; exact hlo⟩

theorem ExtTrue.of_add {m : Mem} {a b : Ghost} (h : ExtTrue m (a.add b).extent) : ExtTrue m a.extent :=
  fun x => by
    obtain ⟨ha, hs⟩ := h x
    refine ⟨fun S K hp => ha S K (by simp only [Ghost.add, ECell.add]; omega), fun k hp => hs k ?_⟩
    simp only [Ghost.add, ECell.add, Frac.add]
    have := ((b.extent x).sh k).nonneg; grind

/-- The ghost states of a resource and its frame compose, and their extent claims are true. -/
def GOk (m : Mem) (g gF : Ghost) : Prop := Ghost.Ok g gF ∧ ExtTrue m (g.add gF).extent

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
    (hF : ExtTrue m' gF.extent) : GOk m' Ghost.unit gF := ⟨h.1, by simpa using hF⟩

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
  ⟨fun x => if x = (S, K) then 1 else 0, fun k => if k = 0 then q else Frac.zero⟩

/-- A share: the fraction `q` at the lower bound `k`. -/
def share (q : Frac) (k : Nat) : ECell := ⟨fun _ => 0, fun k' => if k' = k then q else Frac.zero⟩

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
bytes while the share is held. -/
def bshare (b : BlockId) (q : Frac) (k : Nat) : FAssn := fun r =>
  0 < q.val ∧ r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atExt b (ECell.share q k)

/-- Extents of the blocks `E` (full), as one ghost state. -/
def Ghost.exts (E : BlockId → Option (Nat × BlockKind)) : Ghost :=
  ⟨fun _ => GCell.unit, fun b => match E b with
    | some (S, K) => ECell.auth1 S K Frac.one
    | none => ECell.unit⟩

/-- A legacy assertion with the full extents `E` of its blocks (`FTriple.ofTriple`). -/
def upE (P : Assn) (E : BlockId → Option (Nat × BlockKind)) : FAssn := fun r =>
  P r.heap.erase ∧ r.know = Know.none ∧ r.gh = Ghost.exts E

@[simp] theorem Ghost.exts_none : Ghost.exts (fun _ => none) = Ghost.unit := by
  ext1 <;> funext x <;> rfl

theorem upE_none {P : Assn} {r : Res} : upE P (fun _ => none) r ↔ up P r := by
  simp [upE, up]


end Full
end Zig
