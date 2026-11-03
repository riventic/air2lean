import Proofs.Lists.Append

/-!
# An `append` loop for every allocator (M03)

`appendEach` calls the translated `ArrayListUnmanaged(u32).append` of the open translation
(`Proofs/Lists/Open.lean`) once per value and keeps going after `error.OutOfMemory`, as a caller
that reports each failure would. `appendEach_spec` holds for every allocator that meets the
allocator contract `CAllocSpec` (`Proofs/Lists/Append.lean`), so for every failure decision the
allocator makes: any number of failures in one run, at any attempts. The allocator's failures
include the OS primitives' failures under every `Mem.allocPolicy` (`docs/allocation-policy.md`),
and a full-state triple holds from every memory, whatever its policy.

Each attempt's result is `ok` or `OutOfMemory`, never a panic or `.illegal`. Each failed
attempt leaves the list exactly as it was (`append_spec`'s `.error` case), so the final list is
the original one followed by exactly the values whose `append` succeeded (`succeeded`). The fee
of the list's buffer comes back after every attempt.

Like `append_spec` this is a `CTriple` (partial correctness, no panic): the allocator contract
is one, so a client of an arbitrary allocator gets no more.
-/

namespace Lists.Append

open Zig Zig.Full Zig.Full.FAssn Lists.Open Lists.Alloc

/-- Append each value with the translated `append`; an `OutOfMemory` is a reported result and
the loop goes on with the next value. -/
def appendEach [Ext] (p : Ptr) (a : mem_Allocator) :
    List (BitVec 32) → ConcM Tgt (List (Except ErrName Unit))
  | [] => pure []
  | v :: vs => do
    let r ← array_list_Aligned_u32_null_append p a v
    let rs ← appendEach p a vs
    pure (r :: rs)

/-- The values whose `append` succeeded, in order. -/
def succeeded : List (BitVec 32) → List (Except ErrName Unit) → List (BitVec 32)
  | v :: vs, .ok _ :: rs => v :: succeeded vs rs
  | _ :: vs, .error _ :: rs => succeeded vs rs
  | _, _ => []

/-- One result per value, each `ok` or `OutOfMemory`. -/
def Reported (vs : List (BitVec 32)) (rs : List (Except ErrName Unit)) : Prop :=
  rs.length = vs.length ∧ ∀ r ∈ rs, r = .ok () ∨ r = .error "OutOfMemory"

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-- **The `append` loop** reports one result per value, each `ok` or `OutOfMemory`, and leaves
the list holding the original items followed by the values whose `append` succeeded, with the
fee back, for every allocator that meets the contract. `hfit`: the allocator's room for every
capacity the list can grow to on the way (`growTo`, as in `append_spec`). -/
theorem appendEach_spec (p : Ptr) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    ∀ (vs xs : List (BitVec 32)),
      (∀ n, xs.length ≤ n → n < xs.length + vs.length → I.fits (4 * growTo (n + 1)) 2) →
      CTriple (I.own ⋆ (I.fee φ ⋆ (alist I φ p xs ⋆ vtR vtp fns.toList)))
        (appendEach p ⟨ctx, vtp⟩ vs)
        (fun rs => ⟪Reported vs rs⟫ ⋆
          (I.own ⋆ (I.fee φ ⋆ (alist I φ p (xs ++ succeeded vs rs) ⋆ vtR vtp fns.toList))))
  | [], xs, _ => CTriple.ret' _ fun _ hr =>
      sep_lift.mpr ⟨⟨rfl, by simp⟩, by simpa [succeeded] using hr⟩
  | v :: vs, xs, hfit => by
    have ih_ok := appendEach_spec p h vs (xs ++ [v]) fun n h1 h2 =>
      hfit n (by simp at h1; omega) (by simp at h2 ⊢; omega)
    have ih_err := appendEach_spec p h vs xs fun n h1 h2 => hfit n h1 (by simp; omega)
    rw [appendEach]
    refine CTriple.bind (append_spec ctx vtp fns I e φ p xs v
      (hfit _ (Nat.le_refl _) (by simp)) h) fun r => ?_
    cases r with
    | ok u =>
      refine CTriple.bind ih_ok fun rs => CTriple.ret' _ fun _ hr => ?_
      obtain ⟨⟨hlen, hall⟩, hr⟩ := sep_lift.mp hr
      refine sep_lift.mpr ⟨⟨by simp [hlen], ?_⟩, by simpa [succeeded] using hr⟩
      intro r hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact .inl rfl
      · exact hall r hr'
    | error e' =>
      show CTriple (I.own ⋆ (I.fee φ ⋆ ((⟪e' = "OutOfMemory"⟫ ⋆ alist I φ p xs) ⋆
        vtR vtp fns.toList))) _ _
      rw [show (I.own ⋆ (I.fee φ ⋆ ((⟪e' = "OutOfMemory"⟫ ⋆ alist I φ p xs) ⋆
          vtR vtp fns.toList))) = (⟪e' = "OutOfMemory"⟫ ⋆
          (I.own ⋆ (I.fee φ ⋆ (alist I φ p xs ⋆ vtR vtp fns.toList)))) by ac_rfl]
      refine CTriple.lift fun he => CTriple.bind ih_err fun rs => CTriple.ret' _ fun _ hr => ?_
      obtain ⟨⟨hlen, hall⟩, hr⟩ := sep_lift.mp hr
      refine sep_lift.mpr ⟨⟨by simp [hlen], ?_⟩, by simpa [succeeded] using hr⟩
      intro r hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact .inr (by rw [he])
      · exact hall r hr'

end Lists.Append
