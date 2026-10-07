import ZigLean.Sep.Array.Reassemble
import Proofs.Slices.Gen

/-!
Two clients of the scalar array interface use the existing generated public
`examples/slices/slices.zig` bodies. No generated body is copied or hand-replaced.
These are sequential memory contracts; no new exporter/source correspondence
qualification is claimed by this fixture.
-/

open Zig Assn

-- The public generated pointer-index reader preserves its array and an independent frame.
theorem generated_at_array (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64)
    (hi : i.toNat < xs.length) (R : Assn) :
    Triple (arr p xs ∗ R) (Slices.«at» p i)
      (fun v => (⌜v = xs[i.toNat]⌝ ∗ arr p xs) ∗ R) := by
  have hbody : Slices.«at» p i = load (BitVec 32) 4 (p.elem 4 i) := by
    funext m
    cases hload : ((load (BitVec 32) 4 (p.elem 4 i)).run m).run with
    | none =>
      simp only [ExceptT.run, StateT.run] at hload
      simp [Slices.«at», zig_unfold, hload]
    | some result =>
      simp only [ExceptT.run, StateT.run] at hload
      cases result with
      | error e => simp [Slices.«at», zig_unfold, hload]
      | ok pair =>
        obtain ⟨value, nextMem⟩ := pair
        simp [Slices.«at», zig_unfold, hload]
  rw [hbody]
  exact Triple.frame (R := R) (Triple.arr_read (by decide) (by decide) hi)

-- The public generated fixed-capacity byte update reads a selected value, increments
-- modulo 256, stores through the shared interface, then returns element 3.
theorem generated_bumpAt_array (p : Ptr) (xs : List (BitVec 8)) (i : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (R : Assn) :
    Triple (arr p xs ∗ R) (Slices.bumpAt p i)
      (fun v => (⌜v = (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))[3]'(by simp only [List.length_set]; omega)⌝ ∗
        arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) ∗ R) := by
  have hi4 : i.toNat < 4 := by omega
  have hbody : Slices.bumpAt p i = (do
      let v ← load (BitVec 8) 1 (p.elem 1 i)
      store 1 (p.elem 1 i) (Zig.addWrap v 1)
      load (BitVec 8) 1 (p.elem 1 3)) := by
    funext m
    cases hload : ((load (BitVec 8) 1 (p.elem 1 i)).run m).run with
    | none =>
      simp only [ExceptT.run, StateT.run] at hload
      simp [Slices.bumpAt, zig_unfold, hi4, hload]
    | some result =>
      simp only [ExceptT.run, StateT.run] at hload
      cases result with
      | error e => simp [Slices.bumpAt, zig_unfold, hi4, hload]
      | ok pair =>
        obtain ⟨value, afterLoad⟩ := pair
        cases hstore : ((store 1 (p.elem 1 i) (Zig.addWrap value 1)).run afterLoad).run with
        | none =>
          simp only [ExceptT.run, StateT.run, BitVec.ofNat_eq_ofNat] at hstore
          simp [Slices.bumpAt, zig_unfold, hi4, hload, hstore]
        | some stored =>
          simp only [ExceptT.run, StateT.run, BitVec.ofNat_eq_ofNat] at hstore
          cases stored with
          | error e => simp [Slices.bumpAt, zig_unfold, hi4, hload, hstore]
          | ok pair' =>
            obtain ⟨unit, afterStore⟩ := pair'
            cases unit
            cases hlast : ((load (BitVec 8) 1 (p.elem 1 3)).run afterStore).run with
            | none =>
              simp only [ExceptT.run, StateT.run, BitVec.ofNat_eq_ofNat] at hlast
              simp [Slices.bumpAt, zig_unfold, hi4, hload, hstore, hlast]
            | some loaded =>
              simp only [ExceptT.run, StateT.run, BitVec.ofNat_eq_ofNat] at hlast
              cases loaded with
              | error e => simp [Slices.bumpAt, zig_unfold, hi4, hload, hstore, hlast]
              | ok pair'' =>
                obtain ⟨last, afterRead⟩ := pair''
                simp [Slices.bumpAt, zig_unfold, hi4, hload, hstore, hlast]
  rw [hbody]
  refine Triple.bind (Triple.frame (R := R) (Triple.arr_read (by decide) (by decide) hi))
    (fun v => ?_)
  refine Triple.conseq (Triple.lift (P := arr p xs ∗ R) (φ := v = xs[i.toNat]) (fun hv => ?_)) ?_
    (fun _ _ hp => hp)
  · subst v
    refine Triple.bind (Triple.arr_store_reassemble (by decide) (by decide) hi
      (Zig.addWrap xs[i.toNat] 1)) (fun _ => ?_)
    exact Triple.frame (R := R) (Triple.arr_read (by decide) (by decide)
      (by simp only [List.length_set]; rw [hlen]; decide))
  · intro h hp
    sep_normalize at hp ⊢
    exact hp

-- The two clients can be called sequentially with unrelated allocated blocks.
example (p q : Ptr) (xs : List (BitVec 8)) (ys : List (BitVec 32)) (i j : BitVec 64)
    (hlen : xs.length = 4) (hi : i.toNat < xs.length) (hj : j.toNat < ys.length) :
    Triple (arr p xs ∗ arr q ys)
      (Slices.bumpAt p i >>= fun _ => Slices.«at» q j)
      (fun v => (⌜v = ys[j.toNat]⌝ ∗ arr q ys) ∗
        arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) := by
  refine Triple.bind (generated_bumpAt_array p xs i hlen hi (arr q ys)) (fun result => ?_)
  refine Triple.conseq (Triple.lift
    (P := arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1)) ∗ arr q ys)
    (φ := result = (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))[3]'(by simp only [List.length_set]; omega))
    (fun _ => ?_)) ?_ (fun _ _ hp => hp)
  · have rule : Triple
        (arr q ys ∗ arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1)))
        (Slices.«at» q j)
        (fun v => (⌜v = ys[j.toNat]⌝ ∗ arr q ys) ∗
          arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1))) :=
      generated_at_array q ys j hj
        (arr p (xs.set i.toNat (Zig.addWrap xs[i.toNat] 1)))
    exact Triple.conseq rule (fun h hp => by
      sep_normalize at hp ⊢
      exact hp) (fun _ _ hp => hp)
  · intro h hp
    sep_normalize at hp ⊢
    exact hp
