import ZigLean.Sep.Triple

/-!
# Full-state resources (prototype, `docs/sep-full-state.md`)

The assertions of `ZigLean/Sep/` (`Assn`) range over `Mem.heap`, the live bytes. Two parts of
`Mem` that a program can observe are outside it, so no precondition can constrain them and no
frame keeps them (`docs/alloc-page.md`, obstructions O1 and O3):

* **the atomic layout** (`Mem.atomics`): an atomic op at bytes that already carry an atomic
  location of another offset or size throws `.unspecified` (the mixed-size policy of
  `ZigLean/Mem/Thread.lean`);
* **the metadata of dead blocks**: `ptrAddr` (`@intFromPtr`) of a pointer into a freed block reads
  the block's address, and throws `.illegal` only if the block does not exist at all.

A full-state resource `Res` has three parts:

* `heap : FHeap`: owned live bytes, each with its legacy `Cell` **and its atomic tag**
  (`FCell.atom`: the start and length of the atomic location over the byte, or `none`). Owning a
  byte owns its atomic layout, so the frame rule keeps the layout of the frame's bytes, and an
  atomic points-to (`apts`) can require the layout an atomic op needs.
* `know : Know`: **persistent knowledge** of block addresses, `known b A`: block `b` exists and
  has address `A`. Block ids are never reused and a block's address never changes, so this
  knowledge stays true after `free` (it is not ownership: it is duplicable, `known_dup`).
* `gh : Ghost`: ghost epoch ledgers (§Ghost state below, rules in `Ghost.lean`); no primitive
  reads or changes them.

`Mem.fheap m` is the full heap of a memory (live bytes with their tags); `Mem.kn m` its
knowledge (every block, live or dead, with its address).

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

A ghost cell is an epoch ledger. `auth` counts authorities `●(e, n)` (epoch `e`, `n` tokens
outstanding); a valid state has at most one per name. `frag e` counts tokens `◯e`. Composition
adds both counts, so it is total; `Ghost.Valid` (part of `Holds`) rules out two authorities, more
tokens of the current epoch than the authority admits, and tokens of a later epoch. -/

@[ext] structure GCell where
  auth : Nat × Nat → Nat
  frag : Nat → Nat

namespace GCell

def unit : GCell := ⟨fun _ => 0, fun _ => 0⟩

def add (a b : GCell) : GCell := ⟨fun x => a.auth x + b.auth x, fun e => a.frag e + b.frag e⟩

/-- At most one authority, and if there is one, `●(e, n)`, at most `n` tokens of epoch `e` and
none of a later one. -/
def Valid (c : GCell) : Prop :=
  (∀ x, c.auth x = 0) ∨ ∃ e n, c.auth (e, n) = 1 ∧ (∀ x, x ≠ (e, n) → c.auth x = 0) ∧
    c.frag e ≤ n ∧ ∀ e', e < e' → c.frag e' = 0

theorem add_comm (a b : GCell) : a.add b = b.add a := by
  ext <;> simp [add, Nat.add_comm]

theorem add_assoc (a b c : GCell) : (a.add b).add c = a.add (b.add c) := by
  ext <;> simp [add, Nat.add_assoc]

@[simp] theorem add_unit (a : GCell) : a.add unit = a := by ext <;> simp [add, unit]

@[simp] theorem unit_add (a : GCell) : unit.add a = a := by ext <;> simp [add, unit]

theorem Valid.of_add {a b : GCell} (h : (a.add b).Valid) : a.Valid := by
  rcases h with h | ⟨e, n, h1, h2, h3, h4⟩
  · left; intro x; have := h x; simp only [add] at this; omega
  · by_cases ha : a.auth (e, n) = 1
    · right
      refine ⟨e, n, ha, fun x hx => ?_, ?_, fun e' he => ?_⟩
      · have := h2 x hx; simp only [add] at this; omega
      · simp only [add] at h3; omega
      · have := h4 e' he; simp only [add] at this; omega
    · left; intro x
      by_cases hx : x = (e, n)
      · subst hx; simp only [add] at h1; omega
      · have := h2 x hx; simp only [add] at this; omega

end GCell

/-- Ghost names (`GName := Nat`) to ledgers. -/
abbrev Ghost := Nat → GCell

namespace Ghost

def unit : Ghost := fun _ => GCell.unit

def add (g₁ g₂ : Ghost) : Ghost := fun γ => (g₁ γ).add (g₂ γ)

def Valid (g : Ghost) : Prop := ∀ γ, (g γ).Valid

/-- Finitely many names in use (a fresh name exists). -/
def Fin (g : Ghost) : Prop := ∃ N, ∀ γ, N ≤ γ → g γ = GCell.unit

/-- `g₁` and `g₂` compose: their sum is valid and finite. -/
def Ok (g₁ g₂ : Ghost) : Prop := Valid (add g₁ g₂) ∧ Fin (add g₁ g₂)

theorem add_comm (g₁ g₂ : Ghost) : g₁.add g₂ = g₂.add g₁ := by
  funext γ; exact GCell.add_comm _ _

theorem add_assoc (g₁ g₂ g₃ : Ghost) : (g₁.add g₂).add g₃ = g₁.add (g₂.add g₃) := by
  funext γ; exact GCell.add_assoc _ _ _

@[simp] theorem add_unit (g : Ghost) : g.add unit = g := by funext γ; simp [add, unit]

@[simp] theorem unit_add (g : Ghost) : unit.add g = g := by funext γ; simp [add, unit]

theorem Ok.assoc {a b c : Ghost} : Ok (a.add b) c ↔ Ok a (b.add c) := by
  unfold Ok; rw [add_assoc]

theorem Ok.comm {a b : Ghost} : Ok a b ↔ Ok b a := by
  unfold Ok; rw [add_comm]

/-- Ghost state can be dropped: validity and finiteness are closed under removing a part. -/
theorem Ok.mono {a b c : Ghost} (h : Ok (a.add b) c) : Ok a c := by
  obtain ⟨hv, N, hN⟩ := h
  refine ⟨fun γ => ?_, N, fun γ hγ => ?_⟩
  · have := hv γ
    have e : ((a.add b).add c) γ = ((a γ).add (c γ)).add (b γ) := by
      simp only [add]; rw [GCell.add_assoc, GCell.add_comm (b γ), ← GCell.add_assoc]
    rw [e] at this
    exact GCell.Valid.of_add this
  · have := hN γ hγ
    simp only [add, GCell.add, GCell.unit, GCell.mk.injEq] at this ⊢
    obtain ⟨h1, h2⟩ := this
    exact ⟨funext fun x => by have := congrFun h1 x; omega,
      funext fun x => by have := congrFun h2 x; omega⟩

end Ghost

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
and their atomic layout is either none (no atomic op yet) or exactly one location `(p.off, 8)`.
So an atomic op on it never hits the mixed-size policy (O3). -/
def apts (p : Ptr) (v : BitVec 64) : FAssn := fun r => ∃ A S K bs tg,
  (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bs.size = 8 ∧ intOfBytes 64 bs = pure v ∧
  (tg = none ∨ tg = some (p.off.toNat, 8)) ∧ abytesAt p A S K bs tg r

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

end Full
end Zig
