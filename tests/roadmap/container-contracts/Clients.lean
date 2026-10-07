import Proofs.Lists.Container

/-!
Two clients of the sequence interface `Lists.SeqImpl`. Each is a program over an arbitrary
`I : SeqImpl` and is proved once, from `I.add_spec` and the generic `Triple` rules only: no proof
here unfolds `I.Rep`, `LList`, `AList` or a generated body. The same client theorems are then
instantiated, unchanged, to the generated linked list (`linkedSeq`, `push`) and the generated
`std.ArrayListUnmanaged(u32).append` (`arraySeq`), two different memory representations of the
same abstract sequence.

* `addAll` adds every item: on success the container holds `xs ++ vs`, after `OutOfMemory`
  it holds `xs` followed by a prefix of `vs` (`addAll_spec`). Its functional property, the item
  total, is a statement about abstract lists only (`addAll_total`).
* `addEvens` (a Lean client modelled on the loop of `evens` in `examples/lists/lists.zig`, not
  the generated `evens` body) adds the even items: every
  outcome keeps `xs` as a prefix, and success gives exactly `xs ++ evens` (`addEvens_spec`).

These are sequential partial-correctness contracts on existing generated model bodies; no new
exporter/source correspondence qualification is claimed.
-/

open Zig Assn Lists

namespace ContainerClients

/-! ## Client 1: add all items -/

/-- Add every item of `vs`; the last handle and whether every add succeeded. -/
def addAll (I : SeqImpl) (a : Allocator) :
    I.H → List (BitVec 32) → MemM (I.H × Except ErrName Unit)
  | h, [] => pure (h, .ok ())
  | h, v :: vs => do
    match ← I.add a h v with
    | .ok h' => addAll I a h' vs
    | .error e => pure (h, .error e)

/-- After adding `vs` to `xs`: all of `vs` on success, a prefix of `vs` after `OutOfMemory`. -/
def Filled (I : SeqImpl) (xs vs : List (BitVec 32)) (r : I.H × Except ErrName Unit) : Assn :=
  fun hp => ∃ ys, ys <+: vs ∧
    (match r.2 with | .ok _ => ys = vs | .error e => e = "OutOfMemory") ∧ I.Rep r.1 (xs ++ ys) hp

theorem addAll_spec (I : SeqImpl) (a : Allocator) (h : I.H) (xs vs : List (BitVec 32)) :
    Triple (I.Rep h xs) (addAll I a h vs) (Filled I xs vs) := by
  induction vs generalizing h xs with
  | nil =>
    refine Triple.conseq (Triple.ret (Q := Filled I xs []) (h, .ok ())) ?_ (fun _ _ hq => hq)
    intro hp hr
    exact ⟨[], List.prefix_refl _, rfl, by simpa using hr⟩
  | cons v vs ih =>
    refine Triple.bind (I.add_spec a h xs v) ?_
    intro r
    cases r with
    | ok h' =>
      refine Triple.conseq (ih h' (xs ++ [v])) (fun _ hp => hp) ?_
      rintro ⟨h'', res⟩ hp ⟨ys, hpre, hres, hrep⟩
      refine ⟨v :: ys, List.cons_prefix_cons.mpr ⟨rfl, hpre⟩, ?_, by simpa using hrep⟩
      cases res with
      | ok u => exact congrArg (v :: ·) hres
      | error e => exact hres
    | error e =>
      refine Triple.conseq (Triple.ret (Q := Filled I xs (v :: vs)) (h, .error e)) ?_
        (fun _ _ hq => hq)
      intro hp hpre
      obtain ⟨he, hrep⟩ := sep_lift.mp hpre
      exact ⟨[], List.nil_prefix, he, by simpa using hrep⟩

/-- The total of the items, as natural numbers. -/
def total (xs : List (BitVec 32)) : Nat := (xs.map BitVec.toNat).sum

/-- Client 1's functional property, about abstract sequences only: a successful `addAll`
holds a sequence whose total is that of `xs` plus that of `vs`. -/
theorem addAll_total (I : SeqImpl) (a : Allocator) (h : I.H) (xs vs : List (BitVec 32)) :
    Triple (I.Rep h xs) (addAll I a h vs)
      (fun r hp => ∃ zs, I.Rep r.1 zs hp ∧
        (r.2 = .ok () → total zs = total xs + total vs)) := by
  refine Triple.conseq (addAll_spec I a h xs vs) (fun _ hp => hp) ?_
  rintro ⟨h', res⟩ hp ⟨ys, -, hres, hrep⟩
  refine ⟨xs ++ ys, hrep, fun hok => ?_⟩
  cases hok
  cases hres
  simp [total]

/-! ## Client 2: add the even items, keeping the prefix -/

/-- The even items of `vs`. -/
def evens (vs : List (BitVec 32)) : List (BitVec 32) := vs.filter (fun v => v % 2 == 0)

/-- Add the even items of `vs` (modelled on the loop of `evens` in `lists.zig`). -/
def addEvens (I : SeqImpl) (a : Allocator) :
    I.H → List (BitVec 32) → MemM (I.H × Except ErrName Unit)
  | h, [] => pure (h, .ok ())
  | h, v :: vs =>
    if v % 2 == 0 then do
      match ← I.add a h v with
      | .ok h' => addEvens I a h' vs
      | .error e => pure (h, .error e)
    else addEvens I a h vs

/-- After `addEvens`: `xs` is kept as a prefix, the rest is a prefix of the even items of `vs`,
and all of them on success. -/
def Kept (I : SeqImpl) (xs vs : List (BitVec 32)) (r : I.H × Except ErrName Unit) : Assn :=
  fun hp => ∃ zs, xs <+: zs ∧ zs <+: xs ++ evens vs ∧
    (match r.2 with | .ok _ => zs = xs ++ evens vs | .error e => e = "OutOfMemory") ∧
    I.Rep r.1 zs hp

theorem addEvens_spec (I : SeqImpl) (a : Allocator) (h : I.H) (xs vs : List (BitVec 32)) :
    Triple (I.Rep h xs) (addEvens I a h vs) (Kept I xs vs) := by
  induction vs generalizing h xs with
  | nil =>
    refine Triple.conseq (Triple.ret (Q := Kept I xs []) (h, .ok ())) ?_ (fun _ _ hq => hq)
    intro hp hr
    exact ⟨xs, List.prefix_refl _, by simp [evens], by simp [evens], hr⟩
  | cons v vs ih =>
    by_cases hv : (v % 2 == 0) = true
    · have he : evens (v :: vs) = v :: evens vs := by
        simp only [evens, List.filter_cons, hv, ↓reduceIte]
      show Triple _ (if v % 2 == 0 then _ else _) _
      simp only [hv, ↓reduceIte]
      refine Triple.bind (I.add_spec a h xs v) ?_
      intro r
      cases r with
      | ok h' =>
        refine Triple.conseq (ih h' (xs ++ [v])) (fun _ hp => hp) ?_
        rintro ⟨h'', res⟩ hp ⟨zs, hxs, hzs, hres, hrep⟩
        refine ⟨zs, (List.prefix_append xs [v]).trans hxs, ?_, ?_, hrep⟩
        · simpa [he] using hzs
        · cases res with
          | ok u => simpa [he] using hres
          | error e => exact hres
      | error e =>
        refine Triple.conseq (Triple.ret (Q := Kept I xs (v :: vs)) (h, .error e)) ?_
          (fun _ _ hq => hq)
        intro hp hpre
        obtain ⟨he', hrep⟩ := sep_lift.mp hpre
        exact ⟨xs, List.prefix_refl _, List.prefix_append _ _, he', hrep⟩
    · have he : evens (v :: vs) = evens vs := by
        simp only [evens, List.filter_cons, hv, Bool.false_eq_true, ↓reduceIte]
      show Triple _ (if v % 2 == 0 then _ else _) _
      simp only [hv, Bool.false_eq_true, ↓reduceIte]
      refine Triple.conseq (ih h xs) (fun _ hp => hp) ?_
      rintro r hp hk
      simpa [Kept, he] using hk

/-! ## Both clients against both generated containers -/

/-- `push` items onto a generated linked list. -/
theorem linked_addAll (a : Allocator) (hd : Option Ptr) (xs vs : List (BitVec 32)) :
    Triple (LList hd xs) (addAll linkedSeq a hd vs) (Filled linkedSeq xs vs) :=
  addAll_spec linkedSeq a hd xs vs

/-- `append` items to a generated `ArrayListUnmanaged(u32)`. -/
theorem array_addAll (a : Allocator) (p : Ptr) (xs vs : List (BitVec 32)) :
    Triple (AList p xs) (addAll arraySeq a p vs) (Filled arraySeq xs vs) :=
  addAll_spec arraySeq a p xs vs

theorem linked_addAll_total (a : Allocator) (hd : Option Ptr) (xs vs : List (BitVec 32)) :
    Triple (LList hd xs) (addAll linkedSeq a hd vs)
      (fun r hp => ∃ zs, LList r.1 zs hp ∧ (r.2 = .ok () → total zs = total xs + total vs)) :=
  addAll_total linkedSeq a hd xs vs

theorem array_addAll_total (a : Allocator) (p : Ptr) (xs vs : List (BitVec 32)) :
    Triple (AList p xs) (addAll arraySeq a p vs)
      (fun r hp => ∃ zs, AList r.1 zs hp ∧ (r.2 = .ok () → total zs = total xs + total vs)) :=
  addAll_total arraySeq a p xs vs

theorem linked_addEvens (a : Allocator) (hd : Option Ptr) (xs vs : List (BitVec 32)) :
    Triple (LList hd xs) (addEvens linkedSeq a hd vs) (Kept linkedSeq xs vs) :=
  addEvens_spec linkedSeq a hd xs vs

theorem array_addEvens (a : Allocator) (p : Ptr) (xs vs : List (BitVec 32)) :
    Triple (AList p xs) (addEvens arraySeq a p vs) (Kept arraySeq xs vs) :=
  addEvens_spec arraySeq a p xs vs

/-- The interface gives no more than it states: after `OutOfMemory` a client cannot claim
every item was added. -/
example : True := by
  fail_if_success
    have : ∀ (I : SeqImpl) a h xs vs,
        Triple (I.Rep h xs) (addAll I a h vs) (fun r => I.Rep r.1 (xs ++ vs)) :=
      fun I a h xs vs => addAll_spec I a h xs vs
  trivial

/-- From no bytes, pushing `vs` builds a linked list that holds `vs` (last item first). -/
theorem linked_build (a : Allocator) (vs : List (BitVec 32)) :
    Triple emp (addAll linkedSeq a none vs) (Filled linkedSeq [] vs) :=
  Triple.conseq (linked_addAll a none [] vs) (fun _ hp => ⟨rfl, hp⟩) (fun _ _ hq => hq)

end ContainerClients
