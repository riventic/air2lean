import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Extent

/-!
# Pinned blocks: legacy steps on blocks whose full extent is held

(`docs/sep-full-state.md` §Block extents.) A legacy assertion whose bytes all lie in one block
`b` whose full extent `bext b S K` is held next to it is *pinned*: its cells' sizes are the
block's. Such an assertion lifts to the full-state logic with the pinned bridge
(`FTotalTriple.ofTotal`, `E = {b ↦ (S, K)}`), and the program may change the block's extent
(`munmap`, `mremap`): the post gets the block's new full extent back from the cells it owns
(`upPost_bext`).

* `CTriple.step_bext`: one legacy step on a pinned assertion, with the extent read back from the
  post's cells.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Updates that forget -/

/-- A lifted post with its extents forgotten. -/
theorem EUpd.upPost_up {Q : Assn} {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)} :
    EUpd (upPost Q B E) (up Q) := fun m r rF hh h hs => by
  obtain ⟨E', ⟨hq, hk, hg⟩, -⟩ := h
  have := EUpd.drop (P := up Q) (K := fun r => r.heap = FHeap.empty ∧ r.know = Know.none)
    (fun _ h => h) m r rF hh ⟨⟨r.heap, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, Ghost.exts E'⟩,
      FHeap.disjoint_empty _, by rw [res_eta r, hk, hg]; simp [Know.union_none], ⟨hq, rfl, rfl⟩, rfl, rfl⟩ hs
  exact this

theorem upPost.mono {Q Q' : Assn} {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)}
    {r : Res} (h : upPost Q B E r) (hq : Q' r.heap.erase) : upPost Q' B E r := by
  obtain ⟨E', ⟨-, hk, hg⟩, hc⟩ := h
  exact ⟨E', ⟨hq, hk, hg⟩, hc⟩

/-- The full extent of `b` only. -/
def ext1 (b : BlockId) (S : Nat) (K : BlockKind) : BlockId → Option (Nat × BlockKind) :=
  fun x => if x = b then some (S, K) else none

/-! ## Cells of legacy byte assertions -/

theorem bytesAt_of_cell {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hb : bytesAt p A S K bs h) {l : Loc} {c : Cell} (hl : h l = some c) :
    p.block = some l.1 ∧ c.size = S ∧ c.kind = K := by
  obtain ⟨b, hpb, -, hh⟩ := hb
  rw [hh l] at hl
  split at hl
  · rename_i hc; cases hl; exact ⟨by rw [hc.1]; exact hpb, rfl, rfl⟩
  · cases hl

/-- The first cell of a nonempty region, as a cell of the resource. -/
theorem regionIn_first {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte} {X : Assn} {r : Res}
    (hpos : 0 < bs.size) (h : (regionIn p A S K a bs ∗ X) r.heap.erase) :
    ∃ b, p.block = some b ∧ ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.size = S ∧ fc.cell.kind = K := by
  obtain ⟨h₁, h₂, -, he, ⟨-, -, b, hpb, -, hl⟩, -⟩ := h
  refine ⟨b, hpb, p.off.toNat, ?_⟩
  have e : r.heap.erase (b, p.off.toNat) = some ⟨bs[0]!, A, S, K⟩ := by
    rw [he, Heap.union_apply, hl]; simp [hpos]
  simp only [FHeap.erase, Option.map_eq_some_iff] at e
  obtain ⟨fc, hfc, hc⟩ := e
  exact ⟨fc, hfc, by rw [hc], by rw [hc]⟩

/-! ## A legacy step on a pinned assertion -/

theorem ext1_isSome {b x : BlockId} {S : Nat} {K : BlockKind} (h : x = b) : (ext1 b S K x).isSome := by
  subst h; simp [ext1]

/-- **A legacy step on an assertion pinned by `bext b S K`** (all of `X`'s cells lie in `b` and
record `(S, K)`), whose post keeps a cell of `b` recording `(S', K')`: the post gets `bext b S'
K'`. -/
theorem CTriple.step_bext {Tgt α β : Type} {H : FAssn} {X : Assn} {c : MemM α} {Y : α → Assn}
    {f : α → ConcM Tgt β} {R : β → FAssn} {b : BlockId} {S S' : Nat} {K K' : BlockKind}
    (ht : TotalTriple X c Y) (hc : Tame c)
    (hX : ∀ h, X h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K)
    (hY : ∀ v h, Y v h → ∃ x c, h (b, x) = some c ∧ c.size = S' ∧ c.kind = K')
    (hf : ∀ v, CTriple (H ⋆ (up (Y v) ⋆ bext b S' K')) (f v) R) :
    CTriple (H ⋆ (up X ⋆ bext b S K)) (ConcM.liftMem c >>= f) R := by
  refine CTriple.pre (CTriple.step (E := ext1 b S K) (B := fun x => x = b) ht hc
    (fun h hx l c hl => (hX h hx l c hl).1)
    (fun h hx l c S₀ K₀ hl he => by
      obtain ⟨e1, e2, e3⟩ := hX h hx l c hl
      simp only [ext1, e1, if_pos, Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨e2.trans he.1, e3.trans he.2⟩)
    (SizeFree.of_pinned fun h hx l c hl => ext1_isSome (hX h hx l c hl).1)
    (.inl fun _ h => ext1_isSome h) fun v => ?_) fun _ h => sep_mono_right (fun _ y => up_sep_bext y) h
  refine CTriple.eupd (EUpd.frameL (P := upPost (Y v) _ _) fun m r rF hh hp hs => ?_) (hf v)
  obtain ⟨x, cl, hcl, hs', hk'⟩ := hY v _ (by obtain ⟨E', ⟨hq, -⟩, -⟩ := hp; exact hq)
  simp only [FHeap.erase, Option.map_eq_some_iff] at hcl
  obtain ⟨fc, hfc, rfl⟩ := hcl
  exact EUpd.drop (fun _ h => h) m r rF hh
    (upPost_bext hp ⟨x, fc, hfc, hs', hk', fun h => ext1_isSome h⟩) hs

end Full
end Zig
