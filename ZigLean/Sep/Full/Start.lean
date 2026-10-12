import ZigLean.Sep.Full.Init

/-!
# Programs run from program start (`docs/sep-full-state.md`, `ZigLean/Sep/Full/Init.lean`)

A client of a global proves a triple about its own resource, typically `up (pts p a v)` for the
global's typed value, not about `globals gs`. This module connects the two once, for every
program:

* `globals_pick`: global `j` out of `globals gs` (`gblock`), with the others as a frame;
* `gblock_pts`: a non-`const` global whose initial bytes decode to `v` owns `up (pts ⟨some j, 0⟩ a v)`,
  with its address knowledge and full extent left over (`gblock_rest`);
* `globals_pts`: both at once;
* `FTotalTriple.run_init`: a total triple about the program's entry, from the memory at program
  start, returns and ends in its postcondition (the total form of `FTriple.run_init`).

A theorem about a run from program start is then the client's triple, framed by the rest of the
globals (`FTotalTriple.frame`), weakened by `globals_pts` and applied by `run_init`.
-/

namespace Zig
namespace Full

open FAssn

variable {α : Type}

/-- **Adequacy at program start, total form**: a total triple whose precondition is the globals
returns from the memory at program start, under every placement, and ends in its postcondition. -/
theorem FTotalTriple.run_init {c : MemM α} {Q : α → FAssn} (σ : Placement)
    (gs : List (Array Byte × Nat × BlockKind)) (h : Mem.GlobalsFit gs)
    (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) (ht : FTotalTriple (globals gs) c Q) :
    ∃ v m', (c.run (Mem.ofGlobals σ gs)).run = some (.ok (v, m')) ∧
      ∃ r', Holds m' r' ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧ Q v r' ∧ m'.FSeq := by
  have hi := initRes_holds σ gs hK
  obtain ⟨v, m', hr⟩ := ht.2 _ _ _ hi.1 hi.2 (Mem.init_fseq σ gs h)
  have hq := FTriple.run_init σ gs h hK ht.1
  rw [hr] at hq
  exact ⟨v, m', hr, hq⟩

/-- Global `j` (`gs[j]? = some (bs, a, K)`) and the other globals. -/
theorem globals_pick {gs : List (Array Byte × Nat × BlockKind)} {j : Nat} {bs : Array Byte}
    {a : Nat} {K : BlockKind} (hj : gs[j]? = some (bs, a, K)) :
    globals gs = (gblock j bs a K ⋆ sepN gs.length fun i => if i = j then emp else
      match gs[i]? with | some (bs, a, K) => gblock i bs a K | none => emp) := by
  have hl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
  unfold globals
  rw [sepN_pick hl, hj]; rfl

/-- What a global keeps besides its bytes: the knowledge of its address and its full extent. -/
def gblock_rest (j : BlockId) (S : Nat) (K : BlockKind) : FAssn :=
  FAssn.ex fun A => known j A ⋆ gext j S K

/-- **A global's typed value**: a global whose initial bytes `bs` decode to `v` (a non-`const`
one with a positive alignment) owns `up (pts ⟨some j, 0⟩ a v)`. -/
theorem gblock_pts {T : Type} [Enc T] {j : BlockId} {bs : Array Byte} {a : Nat} {K : BlockKind}
    {v : T} (hs : bs.size = Enc.size T) (hv : Enc.decode bs = pure v) (hK : K ≠ .constGlobal)
    (ha : 0 < a) {r : Res} (h : gblock j bs a K r) :
    (up (pts ⟨some j, 0⟩ a v) ⋆ gblock_rest j bs.size K) r := by
  obtain ⟨A, r₁, r₂, hd, rfl, ⟨hA, he⟩, hrest⟩ := h
  obtain ⟨r₃, r₄, hd', rfl, ⟨hb, hk, hg⟩, h4⟩ := hrest
  have e₁ : r₁.heap = FHeap.empty := he.1
  refine ⟨r₃, r₄, ?_, ?_, ⟨⟨A, bs.size, K, bs, by simpa using hA ha, hs, hv, hb, hK⟩, hk, hg⟩, A, h4⟩
  · exact hd'
  · obtain ⟨-, ek, eg⟩ := he
    cases r₁; simp only at e₁ ek eg; subst e₁ ek eg
    simp [FHeap.empty_union, Know.none_union, Ghost.unit_add]

/-- **A global's typed value at program start**: `globals_pick` and `gblock_pts`. -/
theorem globals_pts {T : Type} [Enc T] {gs : List (Array Byte × Nat × BlockKind)} {j : Nat}
    {bs : Array Byte} {a : Nat} {K : BlockKind} {v : T} (hj : gs[j]? = some (bs, a, K))
    (hs : bs.size = Enc.size T) (hv : Enc.decode bs = pure v) (hK : K ≠ .constGlobal) (ha : 0 < a)
    {r : Res} (h : globals gs r) :
    (up (pts ⟨some j, 0⟩ a v) ⋆ (gblock_rest j bs.size K ⋆ sepN gs.length fun i => if i = j then emp
      else match gs[i]? with | some (bs, a, K) => gblock i bs a K | none => emp)) r := by
  rw [globals_pick hj] at h
  exact sep_assoc (sep_mono_left (fun _ => gblock_pts hs hv hK ha) h)

end Full
end Zig
