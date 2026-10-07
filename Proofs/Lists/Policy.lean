import Proofs.Lists.Append

/-!
# An `append` loop under every allocation policy (M03)

`appendEach` calls the translated `ArrayListUnmanaged(u32).append` once per value and keeps
going after `error.OutOfMemory`, as a caller that reports each failure would. `appendEach_run`
holds for every memory, so for every `Mem.allocPolicy`: request cap, finite failure list,
arbitrary failure oracle and live-heap budget, together with the legacy `Mem.failAt`. It has
no success, resource or default-policy premise and allows any number of failures in one run.

Each attempt's result is `ok` or `OutOfMemory`, never a panic or `.illegal`. Each failed
attempt leaves the list exactly as it was (`append_run`'s `.error` case), so the final list is
the original one followed by exactly the values whose `append` succeeded.
-/

namespace Lists
open Zig Assn

/-- Append each value with the translated `append`; an `OutOfMemory` is a reported result and
the loop goes on with the next value. -/
def appendEach (p : Ptr) (a : Allocator) : List (BitVec 32) → MemM (List (Except ErrName Unit))
  | [] => pure []
  | v :: vs => do
    let r ← array_list_Aligned_u32_null_append p a v
    let rs ← appendEach p a vs
    pure (r :: rs)

/-- The values whose `append` succeeded, in order. -/
def appended : List (BitVec 32) → List (Except ErrName Unit) → List (BitVec 32)
  | v :: vs, .ok _ :: rs => v :: appended vs rs
  | _ :: vs, .error _ :: rs => appended vs rs
  | _, _ => []

/-- Resource-independent safety of the loop: an actual result, one per value, each `ok` or
`OutOfMemory`; a well-formed list holding the original items and the appended values; the
frame and the sequential memory invariant kept. -/
theorem appendEach_run (a : Allocator) (vs : List (BitVec 32)) {m : Mem} {hF hL : Heap}
    {p ptr : Ptr} {cap : BitVec 64} {xs : List (BitVec 32)}
    (hl : alist p ptr cap xs hL) (hm : m.heap = hL ∪ hF) (hd : Heap.Disjoint hL hF)
    (hst : m.Seq) (hok : ptrOk m ptr) :
    ∃ rs m', (appendEach p a vs).run m = pure (rs, m') ∧ m'.Seq ∧ rs.length = vs.length ∧
      (∀ r ∈ rs, r = .ok () ∨ r = .error "OutOfMemory") ∧
      ∃ hL' ptr' cap', Heap.Disjoint hL' hF ∧ m'.heap = hL' ∪ hF ∧
        alist p ptr' cap' (xs ++ appended vs rs) hL' ∧ ptrOk m' ptr' := by
  induction vs generalizing m hL ptr cap xs with
  | nil =>
    exact ⟨[], m, rfl, hst, rfl, by simp, hL, ptr, cap, hd, hm, by simpa [appended] using hl, hok⟩
  | cons v vs ih =>
    obtain ⟨r, m₁, hr, hst₁, hL₁, hd₁, hm₁, happ⟩ := append_run a v hl hm hd hst hok
    have step : ∀ {ys : List (BitVec 32)} {ptr₁ : Ptr} {cap₁ : BitVec 64},
        (r = .ok () ∨ r = .error "OutOfMemory") → alist p ptr₁ cap₁ ys hL₁ → ptrOk m₁ ptr₁ →
        (∀ rs, xs ++ appended (v :: vs) (r :: rs) = ys ++ appended vs rs) →
        ∃ rs m', (appendEach p a (v :: vs)).run m = pure (rs, m') ∧ m'.Seq ∧
          rs.length = (v :: vs).length ∧ (∀ r ∈ rs, r = .ok () ∨ r = .error "OutOfMemory") ∧
          ∃ hL' ptr' cap', Heap.Disjoint hL' hF ∧ m'.heap = hL' ∪ hF ∧
            alist p ptr' cap' (xs ++ appended (v :: vs) rs) hL' ∧ ptrOk m' ptr' := by
      intro ys ptr₁ cap₁ hr₁ hl₁ hok₁ hys
      obtain ⟨rs, m₂, hrs, hst₂, hlen, hall, hL₂, ptr₂, cap₂, hd₂, hm₂, hl₂, hok₂⟩ :=
        ih hl₁ hm₁ hd₁ hst₁ hok₁
      refine ⟨r :: rs, m₂, ?_, hst₂, by simp [hlen], ?_, hL₂, ptr₂, cap₂, hd₂, hm₂, ?_, hok₂⟩
      · simp only [StateT.run] at hr hrs
        simp [appendEach, zig_unfold, hr, hrs, ExceptT.bindCont]
      · intro r' hr'
        rcases List.mem_cons.mp hr' with rfl | h
        · exact hr₁
        · exact hall r' h
      · rw [hys rs]; exact hl₂
    cases r with
    | ok u =>
      obtain ⟨ptr₁, cap₁, hl₁, hok₁⟩ := happ
      exact step (.inl rfl) hl₁ hok₁ (fun _ => by simp [appended])
    | error e =>
      obtain ⟨rfl, hl₁, hok₁⟩ := happ
      exact step (.inr rfl) hl₁ hok₁ (fun _ => by simp [appended])

/-- The same statement with the allocator environment made explicit: for every policy `P`
(cap, failure list, failure oracle, budget) and legacy failure index `f`. -/
theorem appendEach_anyPolicy (P : AllocPolicy) (f : Option Nat) (a : Allocator)
    (vs : List (BitVec 32)) {m : Mem} {hF hL : Heap} {p ptr : Ptr} {cap : BitVec 64}
    {xs : List (BitVec 32)}
    (hl : alist p ptr cap xs hL) (hm : m.heap = hL ∪ hF) (hd : Heap.Disjoint hL hF)
    (hst : m.Seq) (hok : ptrOk m ptr) :
    ∃ rs m', (appendEach p a vs).run { m with allocPolicy := P, failAt := f } = pure (rs, m') ∧
      m'.Seq ∧ rs.length = vs.length ∧ (∀ r ∈ rs, r = .ok () ∨ r = .error "OutOfMemory") ∧
      ∃ hL' ptr' cap', Heap.Disjoint hL' hF ∧ m'.heap = hL' ∪ hF ∧
        alist p ptr' cap' (xs ++ appended vs rs) hL' ∧ ptrOk m' ptr' :=
  appendEach_run a vs hl hm hd ⟨hst.single, hst.addr⟩ hok

end Lists
