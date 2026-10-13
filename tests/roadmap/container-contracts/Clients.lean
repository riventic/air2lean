import Proofs.Lists.Container

/-!
Two clients of the sequence interface `Lists.Container.SeqImpl`. Each is a program over an
arbitrary `S : SeqImpl` and is proved once, from `S.add_spec` and the generic `CTriple` rules
only: no proof here unfolds `S.Rep`, `LList`, `alist` or a generated body. The same client
theorems are then instantiated, unchanged, to the generated linked list (`linkedSeq`, `push`)
and the generated `std.ArrayListUnmanaged(u32).append` (`arraySeq`), two different memory
representations of the same abstract sequence. Every theorem holds for every allocator whose
environment entries meet the allocator contract `CAllocSpec` (`Proofs/Lists/Alloc.lean`), with
the room each add needs of it (`SeqImpl.Room`).

* `addAll` adds every item: on success the container holds `xs ++ vs`, after `OutOfMemory`
  it holds `xs` followed by a prefix of `vs` (`addAll_spec`). Its functional property, the item
  total, is a statement about abstract lists only (`addAll_total`).
* `addEvens` (a Lean client modelled on the loop of `evens` in `examples/lists/lists.zig`, not
  the generated `evens` body) adds the even items: every
  outcome keeps `xs` as a prefix, and success gives exactly `xs ++ evens` (`addEvens_spec`).

These are sequential partial-correctness contracts (`CTriple`, one thread) on existing
generated model bodies; no new exporter/source correspondence qualification is claimed.
-/

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc Lists.Append Lists.Container

namespace ContainerClients

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt)

/-! ## Client 1: add all items -/

/-- Add every item of `vs`; the last handle and whether every add succeeded. -/
def addAll (S : SeqImpl) (a : mem_Allocator) :
    S.H → List (BitVec 32) → ConcM Tgt (S.H × Except ErrName Unit)
  | h, [] => pure (h, .ok ())
  | h, v :: vs => do
    match ← S.add a h v with
    | .ok h' => addAll S a h' vs
    | .error e => pure (h, .error e)

/-- After adding `vs` to `xs`: all of `vs` on success, a prefix of `vs` after `OutOfMemory`. -/
def Filled (S : SeqImpl) (I : FAllocInv) (xs vs : List (BitVec 32)) (r : S.H × Except ErrName Unit) :
    FAssn :=
  FAssn.ex fun ys => ⟪ys <+: vs ∧ (match r.2 with | .ok _ => ys = vs | .error e => e = "OutOfMemory")⟫ ⋆
    S.Rep I r.1 (xs ++ ys)

theorem addAll_spec (S : SeqImpl) (h : S.H) (xs vs : List (BitVec 32))
    (hroom : ∀ n, n < vs.length → S.Room I (xs ++ vs.take n))
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (S.Rep I h xs ⋆ vtR vtp fns.toList)) (addAll S ⟨ctx, vtp⟩ h vs)
      (fun r => I.own ⋆ (Filled S I xs vs r ⋆ vtR vtp fns.toList)) := by
  induction vs generalizing h xs with
  | nil =>
    refine CTriple.ret' _ fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
    exact ⟨[], sep_lift.mpr ⟨⟨List.prefix_refl _, rfl⟩, by rwa [List.append_nil]⟩⟩
  | cons v vs ih =>
    refine CTriple.bind (S.add_spec ctx vtp fns I e h xs v (by simpa using hroom 0 (by simp)) hI)
      fun r => ?_
    cases r with
    | ok h' =>
      refine (ih h' (xs ++ [v]) fun n hn => ?_).post fun r _ hp =>
        sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
      · simpa using hroom (n + 1) (by simp; omega)
      · obtain ⟨ys, hp⟩ := hp
        obtain ⟨⟨hpre, hres⟩, hrep⟩ := sep_lift.mp hp
        refine ⟨v :: ys, sep_lift.mpr ⟨⟨List.cons_prefix_cons.mpr ⟨rfl, hpre⟩, ?_⟩, by simpa using hrep⟩⟩
        obtain ⟨h'', res⟩ := r
        cases res with
        | ok u => exact congrArg (v :: ·) hres
        | error e => exact hres
    | error e =>
      refine CTriple.ret' _ fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
      obtain ⟨he, hrep⟩ := sep_lift.mp hp
      exact ⟨[], sep_lift.mpr ⟨⟨List.nil_prefix, he⟩, by rwa [List.append_nil]⟩⟩

/-- The total of the items, as natural numbers. -/
def total (xs : List (BitVec 32)) : Nat := (xs.map BitVec.toNat).sum

/-- Client 1's functional property, about abstract sequences only: a successful `addAll`
holds a sequence whose total is that of `xs` plus that of `vs`. -/
theorem addAll_total (S : SeqImpl) (h : S.H) (xs vs : List (BitVec 32))
    (hroom : ∀ n, n < vs.length → S.Room I (xs ++ vs.take n))
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (S.Rep I h xs ⋆ vtR vtp fns.toList)) (addAll S ⟨ctx, vtp⟩ h vs)
      (fun r => I.own ⋆ ((FAssn.ex fun zs => ⟪r.2 = .ok () → total zs = total xs + total vs⟫ ⋆
        S.Rep I r.1 zs) ⋆ vtR vtp fns.toList)) := by
  refine (addAll_spec ctx vtp fns I e S h xs vs hroom hI).post fun r _ hp =>
    sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
  obtain ⟨ys, hp⟩ := hp
  obtain ⟨⟨-, hres⟩, hrep⟩ := sep_lift.mp hp
  refine ⟨xs ++ ys, sep_lift.mpr ⟨fun hok => ?_, hrep⟩⟩
  obtain ⟨h', res⟩ := r
  cases hok
  cases hres
  simp [total]

/-! ## Client 2: add the even items, keeping the prefix -/

/-- The even items of `vs`. -/
def evens (vs : List (BitVec 32)) : List (BitVec 32) := vs.filter (fun v => v % 2 == 0)

/-- Add the even items of `vs` (modelled on the loop of `evens` in `lists.zig`). -/
def addEvens (S : SeqImpl) (a : mem_Allocator) :
    S.H → List (BitVec 32) → ConcM Tgt (S.H × Except ErrName Unit)
  | h, [] => pure (h, .ok ())
  | h, v :: vs =>
    if v % 2 == 0 then do
      match ← S.add a h v with
      | .ok h' => addEvens S a h' vs
      | .error e => pure (h, .error e)
    else addEvens S a h vs

/-- After `addEvens`: `xs` is kept as a prefix, the rest is a prefix of the even items of `vs`,
and all of them on success. -/
def Kept (S : SeqImpl) (I : FAllocInv) (xs vs : List (BitVec 32)) (r : S.H × Except ErrName Unit) :
    FAssn :=
  FAssn.ex fun zs => ⟪xs <+: zs ∧ zs <+: xs ++ evens vs ∧
    (match r.2 with | .ok _ => zs = xs ++ evens vs | .error e => e = "OutOfMemory")⟫ ⋆ S.Rep I r.1 zs

theorem addEvens_spec (S : SeqImpl) (h : S.H) (xs vs : List (BitVec 32))
    (hroom : ∀ n, n < (evens vs).length → S.Room I (xs ++ (evens vs).take n))
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (S.Rep I h xs ⋆ vtR vtp fns.toList)) (addEvens S ⟨ctx, vtp⟩ h vs)
      (fun r => I.own ⋆ (Kept S I xs vs r ⋆ vtR vtp fns.toList)) := by
  induction vs generalizing h xs with
  | nil =>
    refine CTriple.ret' _ fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
    exact ⟨xs, sep_lift.mpr ⟨⟨List.prefix_refl _, by simp [evens], by simp [evens]⟩, hp⟩⟩
  | cons v vs ih =>
    by_cases hv : (v % 2 == 0) = true
    · have he : evens (v :: vs) = v :: evens vs := by
        simp only [evens, List.filter_cons, hv, ↓reduceIte]
      rw [he] at hroom
      show CTriple _ (if v % 2 == 0 then _ else _) _
      simp only [hv, ↓reduceIte]
      refine CTriple.bind (S.add_spec ctx vtp fns I e h xs v (by simpa using hroom 0 (by simp)) hI)
        fun r => ?_
      cases r with
      | ok h' =>
        refine (ih h' (xs ++ [v]) fun n hn => ?_).post fun r _ hp =>
          sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
        · simpa using hroom (n + 1) (by simp; omega)
        · obtain ⟨zs, hp⟩ := hp
          obtain ⟨⟨hxs, hzs, hres⟩, hrep⟩ := sep_lift.mp hp
          refine ⟨zs, sep_lift.mpr ⟨⟨(List.prefix_append xs [v]).trans hxs, ?_, ?_⟩, hrep⟩⟩
          · simpa [he] using hzs
          · obtain ⟨h'', res⟩ := r
            cases res with
            | ok u => simpa [he] using hres
            | error e => exact hres
      | error e =>
        refine CTriple.ret' _ fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp
        obtain ⟨he', hrep⟩ := sep_lift.mp hp
        exact ⟨xs, sep_lift.mpr ⟨⟨List.prefix_refl _, List.prefix_append _ _, he'⟩, hrep⟩⟩
    · have he : evens (v :: vs) = evens vs := by
        simp only [evens, List.filter_cons, hv, Bool.false_eq_true, ↓reduceIte]
      rw [he] at hroom
      show CTriple _ (if v % 2 == 0 then _ else _) _
      simp only [hv, Bool.false_eq_true, ↓reduceIte]
      refine (ih h xs hroom).post fun r _ hp => ?_
      simpa only [Kept, he] using hp

/-! ## Both clients against both generated containers, for every allocator -/

/-- `push` items onto a generated linked list. -/
theorem linked_addAll (hd : Option Ptr) (xs vs : List (BitVec 32))
    (hfit : I.fits (16 : BitVec 64).toNat 3) (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (LList I hd xs ⋆ vtR vtp fns.toList)) (addAll linkedSeq ⟨ctx, vtp⟩ hd vs)
      (fun r => I.own ⋆ (Filled linkedSeq I xs vs r ⋆ vtR vtp fns.toList)) :=
  addAll_spec ctx vtp fns I e linkedSeq hd xs vs (fun _ _ => hfit) hI

/-- `append` items to a generated `ArrayListUnmanaged(u32)`. -/
theorem array_addAll (p : Ptr) (xs vs : List (BitVec 32))
    (hfit : ∀ n, n < vs.length → I.fits (4 * growTo ((xs ++ vs.take n).length + 1)) 2)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (alist I p xs ⋆ vtR vtp fns.toList)) (addAll arraySeq ⟨ctx, vtp⟩ p vs)
      (fun r => I.own ⋆ (Filled arraySeq I xs vs r ⋆ vtR vtp fns.toList)) :=
  addAll_spec ctx vtp fns I e arraySeq p xs vs hfit hI

theorem linked_addAll_total (hd : Option Ptr) (xs vs : List (BitVec 32))
    (hfit : I.fits (16 : BitVec 64).toNat 3) (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (LList I hd xs ⋆ vtR vtp fns.toList)) (addAll linkedSeq ⟨ctx, vtp⟩ hd vs)
      (fun r => I.own ⋆ ((FAssn.ex fun zs => ⟪r.2 = .ok () → total zs = total xs + total vs⟫ ⋆
        LList I r.1 zs) ⋆ vtR vtp fns.toList)) :=
  addAll_total ctx vtp fns I e linkedSeq hd xs vs (fun _ _ => hfit) hI

theorem array_addAll_total (p : Ptr) (xs vs : List (BitVec 32))
    (hfit : ∀ n, n < vs.length → I.fits (4 * growTo ((xs ++ vs.take n).length + 1)) 2)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (alist I p xs ⋆ vtR vtp fns.toList)) (addAll arraySeq ⟨ctx, vtp⟩ p vs)
      (fun r => I.own ⋆ ((FAssn.ex fun zs => ⟪r.2 = .ok () → total zs = total xs + total vs⟫ ⋆
        alist I r.1 zs) ⋆ vtR vtp fns.toList)) :=
  addAll_total ctx vtp fns I e arraySeq p xs vs hfit hI

theorem linked_addEvens (hd : Option Ptr) (xs vs : List (BitVec 32))
    (hfit : I.fits (16 : BitVec 64).toNat 3) (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (LList I hd xs ⋆ vtR vtp fns.toList)) (addEvens linkedSeq ⟨ctx, vtp⟩ hd vs)
      (fun r => I.own ⋆ (Kept linkedSeq I xs vs r ⋆ vtR vtp fns.toList)) :=
  addEvens_spec ctx vtp fns I e linkedSeq hd xs vs (fun _ _ => hfit) hI

theorem array_addEvens (p : Ptr) (xs vs : List (BitVec 32))
    (hfit : ∀ n, n < (evens vs).length →
      I.fits (4 * growTo ((xs ++ (evens vs).take n).length + 1)) 2)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ (alist I p xs ⋆ vtR vtp fns.toList)) (addEvens arraySeq ⟨ctx, vtp⟩ p vs)
      (fun r => I.own ⋆ (Kept arraySeq I xs vs r ⋆ vtR vtp fns.toList)) :=
  addEvens_spec ctx vtp fns I e arraySeq p xs vs hfit hI

/-- The interface gives no more than it states: after `OutOfMemory` a client cannot claim
every item was added. -/
example : True := by
  fail_if_success
    have : ∀ (S : SeqImpl) ctx vtp fns I e h xs vs hroom hI,
        CTriple (I.own ⋆ (S.Rep I h xs ⋆ vtR vtp fns.toList)) (addAll S ⟨ctx, vtp⟩ h vs)
          (fun r => I.own ⋆ (S.Rep I r.1 (xs ++ vs) ⋆ vtR vtp fns.toList)) :=
      fun S ctx vtp fns I e h xs vs hroom hI => addAll_spec ctx vtp fns I e S h xs vs hroom hI
  trivial

/-- From no list, pushing `vs` builds a linked list that holds `vs` (last item first). -/
theorem linked_build (vs : List (BitVec 32)) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple (I.own ⋆ vtR vtp fns.toList) (addAll linkedSeq ⟨ctx, vtp⟩ none vs)
      (fun r => I.own ⋆ (Filled linkedSeq I [] vs r ⋆ vtR vtp fns.toList)) :=
  (linked_addAll ctx vtp fns I e none [] vs hfit hI).pre fun _ hp =>
    sep_mono_right (fun _ hp => (sep_lift.mpr ⟨rfl, hp⟩ : (⟪(none : Option Ptr) = none⟫ ⋆ _) _)) hp

end ContainerClients
