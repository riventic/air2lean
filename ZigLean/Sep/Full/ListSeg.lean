import ZigLean.Sep.Full.Logic

/-!
# The library list family (P09 S3, `docs/invariant-synthesis.md`)

A singly linked list of nodes `N p v q`, stated once for every node layout: `N p v q` is the node
at `p` with the item `v` and the next pointer `q` (a `?*Node`, `Option Ptr`), and whatever else its
owner keeps with it. `listSeg N hd tl vs` is the segment from `hd` to `tl` holding `vs` (its last
node points to `tl`); the list at `hd` is the segment that ends at `null`, `listSeg N hd none vs`.

The generator (`air2lean-invgen`, the list-walk family) states a walk's invariant over this family
with the node layout it reads off the walk's body, as a function of the node, the item and the
next pointer: the `next` field (`up (pts (next p) a q)`), then the item's field, if the body reads
one (`up (pts (item p) a' v)`), then the rest of what the owner keeps (`D p v`, or `X p` with an
item field), in this order. A client whose node is that layout (a reducible definition, so that
its list unifies with the generated one) gets the generated invariants.

`fsym` walks the family by the definition's cases (`ledger #list-walk-step`): the cursor's test
splits the ghost list, a repetition folds a node back by the constructors, and a node joins a
segment at its end by the update `listSeg_snoc_upd`.
-/

namespace Zig.Full
open FAssn

variable {V : Type} (N : Ptr → V → Option Ptr → FAssn)

/-- The segment from `hd` to `tl` of nodes `N` holds `vs`; its last node points to `tl`. -/
def listSeg : Option Ptr → Option Ptr → List V → FAssn
  | hd, tl, [] => ⟪hd = tl⟫
  | hd, tl, v :: vs => FAssn.ex fun p => FAssn.ex fun q =>
      ⟪hd = some p⟫ ⋆ (N p v q ⋆ listSeg q tl vs)

variable {N}

/-- A node joins a segment at its end. -/
theorem listSeg_snoc {q : Option Ptr} {p : Ptr} {v : V} :
    ∀ {hd : Option Ptr} {ys : List V} {r : Res},
      (listSeg N hd (some p) ys ⋆ N p v q) r → listSeg N hd q (ys ++ [v]) r
  | _, [], _, h => by
    obtain ⟨rfl, hn⟩ := sep_lift.mp h
    exact ⟨p, q, sep_lift.mpr ⟨rfl, sep_comm (sep_lift.mpr ⟨rfl, hn⟩)⟩⟩
  | _, y :: ys, _, h => by
    obtain ⟨p', h⟩ := sep_ex.mp h
    obtain ⟨q', h⟩ := sep_ex.mp h
    obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨p', q', sep_lift.mpr ⟨hp, sep_mono_right (fun _ => listSeg_snoc) (sep_assoc h)⟩⟩

/-- A nonempty segment, with its first node's pointers as witnesses. -/
theorem listSeg_cons {hd tl : Option Ptr} {z : V} {zs : List V} {R : FAssn} {r : Res}
    (h : (listSeg N hd tl (z :: zs) ⋆ R) r) :
    ∃ p q, hd = some p ∧ (N p z q ⋆ (listSeg N q tl zs ⋆ R)) r := by
  obtain ⟨p, h⟩ := sep_ex.mp h
  obtain ⟨q, h⟩ := sep_ex.mp h
  obtain ⟨hp, h⟩ := sep_lift.mp (sep_assoc h)
  exact ⟨p, q, hp, sep_assoc h⟩

/-- `listSeg_snoc` as an update: a caller's update of `fsym` (`fsym [listSeg_snoc_upd]`) at a
walk's repetition that has passed the node, until the updates registry (P09-E5) takes it. -/
theorem listSeg_snoc_upd {hd q : Option Ptr} {p : Ptr} {v : V} {ys : List V} :
    EUpd (listSeg N hd (some p) ys ⋆ N p v q) (listSeg N hd q (ys ++ [v])) :=
  EUpd.of_imp fun _ h => listSeg_snoc h

end Zig.Full
