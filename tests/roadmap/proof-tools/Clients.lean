import ZigLean.Sep.Automation
import ZigLean.Sep.Total

open Zig Assn

-- A rule's implicit pointer is constrained by the command before frame matching.
example (p q : Ptr) (old w : BitVec 32) :
    Triple (pts q 4 old ∗ pts p 4 old) (store 4 p w)
      (fun _ => pts q 4 old ∗ pts p 4 w) := by
  sep_frame (Triple.store (by decide) w)

-- Mutate the first array while preserving a second array and another client resource.
-- The client chooses its own pre/post ordering; sep_frame infers both unused resources.
example (p q : Ptr) (xs ys : List (BitVec 32)) (R : Assn) (i : BitVec 64)
    (hi : i.toNat < xs.length) (w : BitVec 32) :
    Triple ((arr q ys ∗ R) ∗ arr p xs) (store 4 (p.elem 4 i) w)
      (fun _ => R ∗ (arr p (xs.set i.toNat w) ∗ arr q ys)) := by
  sep_frame ((TotalTriple.arr_store (p := p) (vs := xs) (a := 4) (i := i)
    (by decide) (by decide) (by decide) hi w).toPartial)

-- The same mutation also has total correctness; framing preserves that stronger claim.
example (p : Ptr) (xs : List (BitVec 32)) (R : Assn) (i : BitVec 64)
    (hi : i.toNat < xs.length) (w : BitVec 32) :
    TotalTriple (arr p xs ∗ R) (store 4 (p.elem 4 i) w)
      (fun _ => arr p (xs.set i.toNat w) ∗ R) :=
  (TotalTriple.arr_store (by decide) (by decide) (by decide) hi w).frame

-- A store followed by another store needs successful intermediate results.
example (p : Ptr) (old first last : BitVec 32) :
    TotalTriple (pts p 4 old) (store 4 p first >>= fun _ => store 4 p last)
      (fun _ => pts p 4 last) := by
  exact TotalTriple.bind (TotalTriple.store (by decide) first)
    (fun _ => TotalTriple.store (by decide) last)
