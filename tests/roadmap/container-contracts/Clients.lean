import Proofs.Lists.Container

/-!
Two clients of the sequence interface `Lists.Container.SeqImpl`. Each is a program over an
arbitrary `S : SeqImpl` and is proved once, from `S.add_spec` and the generic `CTriple` rules
only: no proof here unfolds `S.Rep`, `LList`, `alist` or a generated body. The same client
theorems are then instantiated, unchanged, to the generated linked list (`linkedSeq`, `push`)
and the generated `std.ArrayListUnmanaged(u32).append` (`arraySeq`), two different memory
representations of the same abstract sequence. Every theorem holds for every allocator whose
environment entries meet the allocator contract `CAllocSpec` (`Proofs/Lists/Alloc.lean`), with
the room each add needs of it (`SeqImpl.Room`). Each add takes one fee `I.fee φ` of the
allocator (`docs/sep-full-state.md` §The fee of a grant): a client brings one per item it may
add (`fees I φ n`) and gets back the fees of the adds that did not happen.

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

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-! ## Client 1: add all items -/

/-- Add every item of `vs`; the last handle and whether every add succeeded. -/
def addAll (S : SeqImpl) (a : mem_Allocator) :
    S.H → List (BitVec 32) → ConcM Tgt (S.H × Except ErrName Unit)
  | h, [] => pure (h, .ok ())
  | h, v :: vs => do
    match ← S.add a h v with
    | .ok h' => addAll S a h' vs
    | .error e => pure (h, .error e)

/-- After adding `vs` to `xs`: all of `vs` on success, a prefix `ys` of `vs` after
`OutOfMemory`, and the fees of the items not added. -/
def Filled (S : SeqImpl) (I : FAllocInv) (φ : Frac) (xs vs : List (BitVec 32))
    (r : S.H × Except ErrName Unit) : FAssn :=
  FAssn.ex fun ys => ⟪ys <+: vs ∧ (match r.2 with | .ok _ => ys = vs | .error e => e = "OutOfMemory")⟫ ⋆
    (fees I φ (vs.length - ys.length) ⋆ S.Rep I φ r.1 (xs ++ ys))

theorem addAll_spec (S : SeqImpl) (h : S.H) (xs vs : List (BitVec 32))
    (hroom : ∀ n, n < vs.length → S.Room I (xs ++ vs.take n))
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (S.Rep I φ h xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addAll S ⟨ctx, vtp⟩ h vs)
      (fun r => (I.own ⋆ (Filled S I φ xs vs r ⋆ vtR vtp fns.toList)) ⋆ plain) := by
  induction vs generalizing h xs with
  | nil =>
    refine CTriple.ret' _ fun _ hp => sep_mono_left (fun _ hp => sep_mono_right (fun _ hp =>
      sep_mono_left (fun _ hp => ?_) (Full.sep_assoc' hp)) hp) hp
    refine ⟨[], sep_lift.mpr ⟨⟨List.prefix_refl _, rfl⟩, ?_⟩⟩
    rw [List.append_nil]
    exact hp
  | cons v vs ih =>
    refine CTriple.bind ((CTriple.frame (R := fees I φ vs.length)
      (S.add_spec ctx vtp fns I e φ h xs v (by simpa using hroom 0 (by simp)) hI)).pre
      fun _ hp => ac_cast hp (by simp only [List.length_cons, fees_succ]; ac_rfl)) fun r => ?_
    cases r with
    | ok h' =>
      refine ((ih h' (xs ++ [v]) fun n hn => ?_).pre fun _ hp => ac_cast hp
        (by simp only [Added]; ac_rfl)).post fun r _ hp => sep_mono_left (fun _ hp =>
          sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp) hp
      · simpa using hroom (n + 1) (by simp; omega)
      · obtain ⟨ys, hp⟩ := hp
        obtain ⟨⟨hpre, hres⟩, hrep⟩ := sep_lift.mp hp
        refine ⟨v :: ys, sep_lift.mpr ⟨⟨List.cons_prefix_cons.mpr ⟨rfl, hpre⟩, ?_⟩, by simpa using hrep⟩⟩
        obtain ⟨h'', res⟩ := r
        cases res with
        | ok u => exact congrArg (v :: ·) hres
        | error e => exact hres
    | error e =>
      refine CTriple.ret' _ fun _ hp => ?_
      obtain ⟨he, hp⟩ := sep_lift.mp (ac_cast hp (Q := ⟪e = "OutOfMemory"⟫ ⋆
        ((I.own ⋆ ((fees I φ (vs.length + 1) ⋆ S.Rep I φ h xs) ⋆ vtR vtp fns.toList)) ⋆ plain))
        (by simp only [Added, fees_succ]; ac_rfl))
      refine sep_mono_left (fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp =>
        ⟨[], sep_lift.mpr ⟨⟨List.nil_prefix, he⟩, ?_⟩⟩) hp) hp) hp
      rw [List.append_nil]
      exact hp

/-- The total of the items, as natural numbers. -/
def total (xs : List (BitVec 32)) : Nat := (xs.map BitVec.toNat).sum

/-- Client 1's functional property, about abstract sequences only: a successful `addAll`
holds a sequence whose total is that of `xs` plus that of `vs`; the fees of the items not added
come back. -/
theorem addAll_total (S : SeqImpl) (h : S.H) (xs vs : List (BitVec 32))
    (hroom : ∀ n, n < vs.length → S.Room I (xs ++ vs.take n))
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (S.Rep I φ h xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addAll S ⟨ctx, vtp⟩ h vs)
      (fun r => (I.own ⋆ ((FAssn.ex fun zs => ⟪r.2 = .ok () → total zs = total xs + total vs⟫ ⋆
        (fees I φ (xs.length + vs.length - zs.length) ⋆ S.Rep I φ r.1 zs)) ⋆ vtR vtp fns.toList)) ⋆
        plain) := by
  refine (addAll_spec ctx vtp fns I e φ S h xs vs hroom hI).post fun r _ hp => sep_mono_left
    (fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp) hp
  obtain ⟨ys, hp⟩ := hp
  obtain ⟨⟨-, hres⟩, hrep⟩ := sep_lift.mp hp
  have e : xs.length + vs.length - (xs ++ ys).length = vs.length - ys.length := by
    rw [List.length_append]; omega
  refine ⟨xs ++ ys, sep_lift.mpr ⟨fun hok => ?_, by rwa [e]⟩⟩
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
and all of them on success; the fees of the even items not added come back. -/
def Kept (S : SeqImpl) (I : FAllocInv) (φ : Frac) (xs vs : List (BitVec 32))
    (r : S.H × Except ErrName Unit) : FAssn :=
  FAssn.ex fun zs => ⟪xs <+: zs ∧ zs <+: xs ++ evens vs ∧
    (match r.2 with | .ok _ => zs = xs ++ evens vs | .error e => e = "OutOfMemory")⟫ ⋆
    (fees I φ (xs.length + (evens vs).length - zs.length) ⋆ S.Rep I φ r.1 zs)

theorem addEvens_spec (S : SeqImpl) (h : S.H) (xs vs : List (BitVec 32))
    (hroom : ∀ n, n < (evens vs).length → S.Room I (xs ++ (evens vs).take n))
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ (evens vs).length ⋆ (S.Rep I φ h xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addEvens S ⟨ctx, vtp⟩ h vs)
      (fun r => (I.own ⋆ (Kept S I φ xs vs r ⋆ vtR vtp fns.toList)) ⋆ plain) := by
  induction vs generalizing h xs with
  | nil =>
    refine CTriple.ret' _ fun _ hp => sep_mono_left (fun _ hp => sep_mono_right (fun _ hp =>
      sep_mono_left (fun _ hp => ?_) (Full.sep_assoc' hp)) hp) hp
    refine ⟨xs, sep_lift.mpr ⟨⟨List.prefix_refl _, by simp [evens], by simp [evens]⟩, ?_⟩⟩
    simpa [evens] using hp
  | cons v vs ih =>
    by_cases hv : (v % 2 == 0) = true
    · have he : evens (v :: vs) = v :: evens vs := by
        simp only [evens, List.filter_cons, hv, ↓reduceIte]
      rw [he] at hroom
      show CTriple _ (if v % 2 == 0 then _ else _) _
      simp only [hv, ↓reduceIte]
      refine CTriple.bind ((CTriple.frame (R := fees I φ (evens vs).length)
        (S.add_spec ctx vtp fns I e φ h xs v (by simpa using hroom 0 (by simp)) hI)).pre
        fun _ hp => ac_cast hp (by simp only [he, List.length_cons, fees_succ]; ac_rfl)) fun r => ?_
      cases r with
      | ok h' =>
        refine ((ih h' (xs ++ [v]) fun n hn => ?_).pre fun _ hp => ac_cast hp
          (by simp only [Added]; ac_rfl)).post fun r _ hp => sep_mono_left (fun _ hp =>
            sep_mono_right (fun _ hp => sep_mono_left (fun _ hp => ?_) hp) hp) hp
        · simpa using hroom (n + 1) (by simp; omega)
        · obtain ⟨zs, hp⟩ := hp
          obtain ⟨⟨hxs, hzs, hres⟩, hrep⟩ := sep_lift.mp hp
          have e : xs.length + (evens (v :: vs)).length - zs.length =
              (xs ++ [v]).length + (evens vs).length - zs.length := by
            simp only [he, List.length_cons, List.length_append, List.length_nil]; omega
          refine ⟨zs, sep_lift.mpr ⟨⟨(List.prefix_append xs [v]).trans hxs, ?_, ?_⟩, by rwa [e]⟩⟩
          · simpa [he] using hzs
          · obtain ⟨h'', res⟩ := r
            cases res with
            | ok u => simpa [he] using hres
            | error e => exact hres
      | error e' =>
        refine CTriple.ret' _ fun _ hp => ?_
        obtain ⟨he', hp⟩ := sep_lift.mp (ac_cast hp (Q := ⟪e' = "OutOfMemory"⟫ ⋆
          ((I.own ⋆ ((fees I φ ((evens vs).length + 1) ⋆ S.Rep I φ h xs) ⋆ vtR vtp fns.toList)) ⋆
            plain))
          (by simp only [Added, fees_succ]; ac_rfl))
        refine sep_mono_left (fun _ hp => sep_mono_right (fun _ hp => sep_mono_left (fun _ hp =>
          ⟨xs, sep_lift.mpr ⟨⟨List.prefix_refl _, List.prefix_append _ _, he'⟩, ?_⟩⟩) hp) hp) hp
        have e : xs.length + (evens (v :: vs)).length - xs.length = (evens vs).length + 1 := by
          simp only [he, List.length_cons]; omega
        rwa [e]
    · have he : evens (v :: vs) = evens vs := by
        simp only [evens, List.filter_cons, hv, Bool.false_eq_true, ↓reduceIte]
      rw [he] at hroom
      show CTriple _ (if v % 2 == 0 then _ else _) _
      simp only [hv, Bool.false_eq_true, ↓reduceIte]
      refine ((ih h xs hroom).pre fun _ hp => by rwa [he] at hp).post fun r _ hp => ?_
      simpa only [Kept, he] using hp

/-! ## Both clients against both generated containers, for every allocator -/

/-- `push` items onto a generated linked list. -/
theorem linked_addAll (hd : Option Ptr) (xs vs : List (BitVec 32))
    (hfit : I.fits (16 : BitVec 64).toNat 3) (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (LList I φ hd xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addAll linkedSeq ⟨ctx, vtp⟩ hd vs)
      (fun r => (I.own ⋆ (Filled linkedSeq I φ xs vs r ⋆ vtR vtp fns.toList)) ⋆ plain) :=
  addAll_spec ctx vtp fns I e φ linkedSeq hd xs vs (fun _ _ => hfit) hI

/-- `append` items to a generated `ArrayListUnmanaged(u32)`. -/
theorem array_addAll (p : Ptr) (xs vs : List (BitVec 32))
    (hfit : ∀ n, n < vs.length → I.fits (4 * growTo ((xs ++ vs.take n).length + 1)) 2)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (AList I φ p xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addAll arraySeq ⟨ctx, vtp⟩ p vs)
      (fun r => (I.own ⋆ (Filled arraySeq I φ xs vs r ⋆ vtR vtp fns.toList)) ⋆ plain) :=
  addAll_spec ctx vtp fns I e φ arraySeq p xs vs hfit hI

theorem linked_addAll_total (hd : Option Ptr) (xs vs : List (BitVec 32))
    (hfit : I.fits (16 : BitVec 64).toNat 3) (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (LList I φ hd xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addAll linkedSeq ⟨ctx, vtp⟩ hd vs)
      (fun r => (I.own ⋆ ((FAssn.ex fun zs => ⟪r.2 = .ok () → total zs = total xs + total vs⟫ ⋆
        (fees I φ (xs.length + vs.length - zs.length) ⋆ LList I φ r.1 zs)) ⋆ vtR vtp fns.toList)) ⋆
        plain) :=
  addAll_total ctx vtp fns I e φ linkedSeq hd xs vs (fun _ _ => hfit) hI

theorem array_addAll_total (p : Ptr) (xs vs : List (BitVec 32))
    (hfit : ∀ n, n < vs.length → I.fits (4 * growTo ((xs ++ vs.take n).length + 1)) 2)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (AList I φ p xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addAll arraySeq ⟨ctx, vtp⟩ p vs)
      (fun r => (I.own ⋆ ((FAssn.ex fun zs => ⟪r.2 = .ok () → total zs = total xs + total vs⟫ ⋆
        (fees I φ (xs.length + vs.length - zs.length) ⋆ AList I φ r.1 zs)) ⋆ vtR vtp fns.toList)) ⋆
        plain) :=
  addAll_total ctx vtp fns I e φ arraySeq p xs vs hfit hI

theorem linked_addEvens (hd : Option Ptr) (xs vs : List (BitVec 32))
    (hfit : I.fits (16 : BitVec 64).toNat 3) (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ (evens vs).length ⋆ (LList I φ hd xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addEvens linkedSeq ⟨ctx, vtp⟩ hd vs)
      (fun r => (I.own ⋆ (Kept linkedSeq I φ xs vs r ⋆ vtR vtp fns.toList)) ⋆ plain) :=
  addEvens_spec ctx vtp fns I e φ linkedSeq hd xs vs (fun _ _ => hfit) hI

theorem array_addEvens (p : Ptr) (xs vs : List (BitVec 32))
    (hfit : ∀ n, n < (evens vs).length →
      I.fits (4 * growTo ((xs ++ (evens vs).take n).length + 1)) 2)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ (evens vs).length ⋆ (AList I φ p xs ⋆ vtR vtp fns.toList))) ⋆ plain)
      (addEvens arraySeq ⟨ctx, vtp⟩ p vs)
      (fun r => (I.own ⋆ (Kept arraySeq I φ xs vs r ⋆ vtR vtp fns.toList)) ⋆ plain) :=
  addEvens_spec ctx vtp fns I e φ arraySeq p xs vs hfit hI

/-- The interface gives no more than it states: after `OutOfMemory` a client cannot claim
every item was added. -/
example : True := by
  fail_if_success
    have : ∀ (S : SeqImpl) ctx vtp fns I e φ h xs vs hroom hI,
        CTriple ((I.own ⋆ (fees I φ vs.length ⋆ (S.Rep I φ h xs ⋆ vtR vtp fns.toList))) ⋆ plain)
          (addAll S ⟨ctx, vtp⟩ h vs)
          (fun r => (I.own ⋆ (S.Rep I φ r.1 (xs ++ vs) ⋆ vtR vtp fns.toList)) ⋆ plain) :=
      fun S ctx vtp fns I e φ h xs vs hroom hI => addAll_spec ctx vtp fns I e φ S h xs vs hroom hI
  trivial

/-- From no list, pushing `vs` builds a linked list that holds `vs` (last item first). -/
theorem linked_build (vs : List (BitVec 32)) (hfit : I.fits (16 : BitVec 64).toNat 3)
    (hI : CAllocSpec (CVTable.env (Lists.Alloc.env e) fns) ctx I) :
    CTriple ((I.own ⋆ (fees I φ vs.length ⋆ vtR vtp fns.toList)) ⋆ plain)
      (addAll linkedSeq ⟨ctx, vtp⟩ none vs)
      (fun r => (I.own ⋆ (Filled linkedSeq I φ [] vs r ⋆ vtR vtp fns.toList)) ⋆ plain) :=
  (linked_addAll ctx vtp fns I e φ none [] vs hfit hI).pre fun _ hp =>
    sep_mono_left (fun _ hp => sep_mono_right (fun _ hp => sep_mono_right (fun _ hp =>
      (sep_lift.mpr ⟨rfl, hp⟩ : (⟪(none : Option Ptr) = none⟫ ⋆ _) _)) hp) hp) hp

end ContainerClients
