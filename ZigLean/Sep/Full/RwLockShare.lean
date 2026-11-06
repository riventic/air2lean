import ZigLean.Sep.Full.ThreadOwned
import ZigLean.Sep.Full.RwLock

/-!
# A reader/writer lock's protected resource at a fraction

The part of the reader/writer lock contract (`RwLockImpl`, design on the PR of the RwLock track,
maintainer decision 2026-11-06 on #637, option A) that is pure resource algebra: a shared holder
holds the protected resource at a fraction, as read shares of its cells (`Res.lean` §Read shares).

* `Res.frac q r`: the heap of `r` at fraction `q`, as read shares, with no exclusive cell, no
  knowledge and no other ghost state. The protected resource of a reader/writer lock is a heap
  resource (`Res.HeapOnly`): a fraction of a credit or a ledger token has no meaning, and every
  protected resource of the RwLock clients is one.
* `Res.frac_add`: two fractions of one resource compose to their sum, so any number of shared
  holders split and join one resource (`Res.frac_half`: the free lock's fraction halves at each
  shared acquire, so no bound on the readers is needed for the fractions).
* `Res.frac_share_valid`: the fractions of one resource compose to a valid share while they sum
  to at most the whole.

What converts the whole fraction to and from the exclusive heap of `r` in a proof (the writer's
acquire after the last reader, the first reader's acquire after the writer) is the logic's
whole-share conversion (`ZigLean/Sep/Full/Share.lean`, F3), not this algebra.
-/

namespace Zig
namespace Full

/-- `r` is a heap resource: no knowledge, no ghost state (module doc). -/
def Res.HeapOnly (r : Res) : Prop := r.know = Know.none ∧ r.gh = Ghost.unit

/-- The read shares of the heap `h` at fraction `q`: the cell of each byte of `h`. -/
noncomputable def FHeap.shares (q : Frac) (h : FHeap) : Loc → SCell := fun l =>
  match h l with
  | some c => SCell.of c q
  | none => SCell.zero

/-- **The heap of `r` at fraction `q`** (module doc): read shares only. -/
noncomputable def Res.frac (q : Frac) (r : Res) : Res :=
  ⟨FHeap.empty, Know.none, { Ghost.unit with share := r.heap.shares q }⟩

/-- The shares of a heap at a fraction of at most the whole are valid. -/
theorem FHeap.shares_valid {q : Frac} (hq : q.val ≤ 1) (h : FHeap) (l : Loc) :
    (h.shares q l).Valid := by
  simp only [FHeap.shares]
  split
  · exact SCell.valid_of hq
  · exact SCell.valid_zero

namespace Res

@[simp] theorem frac_heap (q : Frac) (r : Res) : (r.frac q).heap = FHeap.empty := rfl

@[simp] theorem frac_know (q : Frac) (r : Res) : (r.frac q).know = Know.none := rfl

@[simp] theorem frac_share (q : Frac) (r : Res) : (r.frac q).gh.share = r.heap.shares q := rfl

/-- **Split and join**: two fractions of one resource compose to their sum. -/
theorem frac_add (q₁ q₂ : Frac) (r : Res) :
    rsum (r.frac q₁) (r.frac q₂) = r.frac (q₁.add q₂) := by
  have hs : ∀ l, ((r.heap.shares q₁ l).add (r.heap.shares q₂ l)) = r.heap.shares (q₁.add q₂) l := by
    intro l
    simp only [FHeap.shares]
    split
    · exact SCell.of_add _ _ _
    · exact SCell.zero_add _
  have hg : (r.frac q₁).gh.add (r.frac q₂).gh = (r.frac (q₁.add q₂)).gh := by
    have hu := Ghost.add_unit Ghost.unit
    refine Ghost.ext ?_ ?_ ?_ ?_ ?_
    · show (Ghost.unit.add Ghost.unit).led = Ghost.unit.led; rw [hu]
    · show (Ghost.unit.add Ghost.unit).extent = Ghost.unit.extent; rw [hu]
    · show (Ghost.unit.add Ghost.unit).cl = Ghost.unit.cl; rw [hu]
    · show (Ghost.unit.add Ghost.unit).ac = Ghost.unit.ac; rw [hu]
    · funext l; exact hs l
  simp only [rsum, frac, FHeap.empty_union, Know.union_none]
  exact congrArg (Res.mk FHeap.empty Know.none) hg

/-- **A shared acquire's split**: the free lock's fraction `q` is two halves, one for the new
shared holder and one that the lock keeps, so there is room for any number of shared holders. -/
theorem frac_half (q : Frac) (r : Res) : r.frac q = rsum (r.frac q.half) (r.frac q.half) := by
  rw [frac_add, Frac.half_add_half]

/-- **The fractions of one resource compose to a valid share** while they sum to at most the
whole. -/
theorem frac_share_valid {q₁ q₂ : Frac} (hq : (q₁.add q₂).val ≤ 1) (r : Res) (l : Loc) :
    ((rsum (r.frac q₁) (r.frac q₂)).gh.share l).Valid := by
  rw [frac_add]; exact FHeap.shares_valid hq r.heap l

/-- At the whole fraction, each byte of `r` is held whole: the shares are exact
(`SCell.Total`, the accounting `SMatch` asks for). -/
theorem frac_one_total (r : Res) (l : Loc) : (r.heap.shares Frac.one l).Total := by
  simp only [FHeap.shares]
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

end Res

end Full
end Zig
