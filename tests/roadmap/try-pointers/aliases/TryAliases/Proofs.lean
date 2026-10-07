import TryAliases.Gen
import TryPointers.AliasProofs

/-! Whole-union memory rules for the generated `twoPaths` and `resetOnError` definitions,
translated from the hand-written `try_aliases.*` AIR (compiler export pending).

* `twoPaths p p y`: one union reached through both pointer-try operands. Both results address
  the same payload; the write through the first is what the second reads.
* `twoPaths a b y` with separately owned unions: the write lands only in `a`, the read comes
  only from `b`. An error on either path writes nothing and returns that path's error.
* `resetOnError`: on error the error name is read before the `errdefer` overwrites the
  addressed union with `.ok fallback`; the returned error is the original one. Success
  returns the payload address and leaves the union unchanged. -/

open Zig
open scoped Zig
open TryPointersAliasProofs

namespace TryAliasesProofs

/-! ## One union, two pointer paths -/

theorem twoPaths_same_run {p : Ptr} {u : Except ErrName (BitVec 8)} {y : BitVec 8} {m : Mem}
    {h hF : Heap} (hp : pts p 2 u h) (hdom : admitted u) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryAliases.twoPaths p p y).run m = pure (writeView y u, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ pts p 2 (writeView y u) h' ∧ m'.Seq := by
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_discard_run hp hm hs
  rw [u8_size] at h₁
  obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_finiteTry_run (d := domain) hp tag_align tag_off hdom hm₁ hs₁
  cases u with
  | error e =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ :=
      pts_finiteErrCode_run (d := domain) hp tag_align tag_off (hdom e rfl) hm₂ hs₂
    refine ⟨m₃, h, ?_, hd, hm₃, hp, hs₃⟩
    simp only [StateT.run] at h₁ h₂ h₃
    simp [TryAliases.twoPaths, tryView, writeView, zig_unfold, h₁, h₂, h₃]
  | ok x =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ := pts_discard_run hp hm₂ hs₂
    rw [u8_size] at h₃
    obtain ⟨m₄, h₄, hm₄, hs₄⟩ :=
      pts_finiteTry_run (d := domain) hp tag_align tag_off hdom hm₃ hs₃
    obtain ⟨m₅, h₅, hs₅, h', hd', hm₅, hp'⟩ :=
      pts_payload_store_run hp pay_align pay_off pay_size hm₄ hd hs₄ y
    obtain ⟨m₆, h₆, hm₆, hs₆⟩ := pts_payload_load_run hp' pay_align pay_off pay_size hm₅ hs₅
    refine ⟨m₆, h', ?_, hd', hm₆, hp', hs₆⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅ h₆
    simp [TryAliases.twoPaths, tryView, writeView, zig_unfold, h₁, h₂, h₃, h₄, h₅, h₆]

theorem twoPaths_same_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hdom : admitted u) :
    Triple (pts p 2 u) (TryAliases.twoPaths p p y)
      (fun r => ⌜r = writeView y u⌝ ∗ pts p 2 (writeView y u)) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := twoPaths_same_run hp hdom hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

/-! ## Two separately owned unions -/

/-- The result of `twoPaths a b y`: the first error, else the second union's payload. -/
def twoResult : Except ErrName (BitVec 8) → Except ErrName (BitVec 8) → Except ErrName (BitVec 8)
  | .error e, _ => .error e
  | .ok _, .error e => .error e
  | .ok _, .ok z => .ok z

/-- The first union afterwards: written only when both pointer-tries succeed. -/
def firstAfter (y : BitVec 8) : Except ErrName (BitVec 8) → Except ErrName (BitVec 8) →
    Except ErrName (BitVec 8)
  | .ok _, .ok _ => .ok y
  | u, _ => u

theorem twoPaths_distinct_run {a b : Ptr} {u w : Except ErrName (BitVec 8)} {y : BitVec 8}
    {m : Mem} {h hF : Heap} (hpre : (pts a 2 u ∗ pts b 2 w) h) (hu : admitted u)
    (hw : admitted w) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryAliases.twoPaths a b y).run m = pure (twoResult u w, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
      (pts a 2 (firstAfter y u w) ∗ pts b 2 w) h' ∧ m'.Seq := by
  obtain ⟨ha, hb, hab, rfl, hpa, hpb⟩ := hpre
  obtain ⟨haF, hbF⟩ := Heap.disjoint_union_left.mp hd
  have hma : m.heap = ha ∪ (hb ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_discard_run hpa hma hs
  rw [u8_size] at h₁
  obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_finiteTry_run (d := domain) hpa tag_align tag_off hu hm₁ hs₁
  cases u with
  | error e =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ :=
      pts_finiteErrCode_run (d := domain) hpa tag_align tag_off (hu e rfl) hm₂ hs₂
    refine ⟨m₃, ha ∪ hb, ?_, hd, by rw [hm₃, Heap.union_assoc], ⟨ha, hb, hab, rfl, hpa, hpb⟩, hs₃⟩
    simp only [StateT.run] at h₁ h₂ h₃
    simp [TryAliases.twoPaths, tryView, twoResult, zig_unfold, h₁, h₂, h₃]
  | ok x =>
    -- Switch ownership focus to the second union.
    have hmb : m₂.heap = hb ∪ (ha ∪ hF) := by rw [hm₂, Heap.union_left_comm hab]
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ := pts_discard_run hpb hmb hs₂
    rw [u8_size] at h₃
    obtain ⟨m₄, h₄, hm₄, hs₄⟩ :=
      pts_finiteTry_run (d := domain) hpb tag_align tag_off hw hm₃ hs₃
    cases w with
    | error e =>
      obtain ⟨m₅, h₅, hm₅, hs₅⟩ :=
        pts_finiteErrCode_run (d := domain) hpb tag_align tag_off (hw e rfl) hm₄ hs₄
      refine ⟨m₅, ha ∪ hb, ?_, hd, by rw [hm₅, Heap.union_left_comm hab.symm, Heap.union_assoc],
        ⟨ha, hb, hab, rfl, hpa, hpb⟩, hs₅⟩
      simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅
      simp [TryAliases.twoPaths, tryView, twoResult, zig_unfold, h₁, h₂, h₃, h₄, h₅]
    | ok z =>
      have hma' : m₄.heap = ha ∪ (hb ∪ hF) := by rw [hm₄, Heap.union_left_comm hab.symm]
      obtain ⟨m₅, h₅, hs₅, ha', hdA, hm₅, hpa'⟩ :=
        pts_payload_store_run hpa pay_align pay_off pay_size hma'
          (Heap.disjoint_union_right.mpr ⟨hab, haF⟩) hs₄ y
      obtain ⟨hAb, hAF⟩ := Heap.disjoint_union_right.mp hdA
      have hmb' : m₅.heap = hb ∪ (ha' ∪ hF) := by rw [hm₅, Heap.union_left_comm hAb]
      obtain ⟨m₆, h₆, hm₆, hs₆⟩ := pts_payload_load_run hpb pay_align pay_off pay_size hmb' hs₅
      refine ⟨m₆, ha' ∪ hb, ?_, Heap.disjoint_union_left.mpr ⟨hAF, hbF⟩,
        by rw [hm₆, Heap.union_left_comm hAb.symm, Heap.union_assoc],
        ⟨ha', hb, hAb, rfl, hpa', hpb⟩, hs₆⟩
      simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅ h₆
      simp [TryAliases.twoPaths, tryView, twoResult, zig_unfold, h₁, h₂, h₃, h₄, h₅, h₆]

theorem twoPaths_distinct_owned (a b : Ptr) (u w : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hu : admitted u) (hw : admitted w) :
    Triple (pts a 2 u ∗ pts b 2 w) (TryAliases.twoPaths a b y)
      (fun r => ⌜r = twoResult u w⌝ ∗ (pts a 2 (firstAfter y u w) ∗ pts b 2 w)) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := twoPaths_distinct_run hp hu hw hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

/-! ## errdefer rewriting the addressed union -/

/-- The union after `resetOnError p f`: overwritten with `.ok f` on the error path only. -/
def resetAfter (f : BitVec 8) : Except ErrName (BitVec 8) → Except ErrName (BitVec 8)
  | .ok x => .ok x
  | .error _ => .ok f

theorem resetOnError_run {p : Ptr} {u : Except ErrName (BitVec 8)} {f : BitVec 8} {m : Mem}
    {h hF : Heap} (hp : pts p 2 u h) (hdom : admitted u) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryAliases.resetOnError p f).run m = pure (tryView (BitVec 8) p u, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ pts p 2 (resetAfter f u) h' ∧ m'.Seq := by
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_discard_run hp hm hs
  rw [u8_size] at h₁
  obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_finiteTry_run (d := domain) hp tag_align tag_off hdom hm₁ hs₁
  cases u with
  | error e =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ :=
      pts_finiteErrCode_run (d := domain) hp tag_align tag_off (hdom e rfl) hm₂ hs₂
    -- The errdefer's whole-union store uses the finite-domain dictionary; for a success
    -- value it writes exactly the generic encoding.
    obtain ⟨m₄, h₄, hs₄, h', hd', hm₄, hp'⟩ :=
      pts_store_run hp hm₃ hd (by decide) hs₃ (.ok f : Except ErrName (BitVec 8))
    have h₄' : (letI : Enc (Except ErrName (BitVec 8)) :=
        errorUnionEnc domain (inferInstance : Enc (BitVec 8))
      Zig.store (α := Except ErrName (BitVec 8)) 2 p (.ok f)).run m₃ = pure ((), m₄) := h₄
    refine ⟨m₄, h', ?_, hd', hm₄, hp', hs₄⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄'
    simp [TryAliases.resetOnError, tryView, zig_unfold, h₁, h₂, h₃, h₄']
  | ok x =>
    refine ⟨m₂, h, ?_, hd, hm₂, hp, hs₂⟩
    simp only [StateT.run] at h₁ h₂
    simp [TryAliases.resetOnError, tryView, zig_unfold, h₁, h₂]

theorem resetOnError_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (f : BitVec 8)
    (hdom : admitted u) :
    Triple (pts p 2 u) (TryAliases.resetOnError p f)
      (fun r => ⌜r = tryView (BitVec 8) p u⌝ ∗ pts p 2 (resetAfter f u)) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := resetOnError_run hp hdom hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

end TryAliasesProofs
