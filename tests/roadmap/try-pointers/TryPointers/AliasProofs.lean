import TryPointers.Gen
import ZigLean.Sep.TryAlias

/-! Whole-union memory rules for the actual retained generated `writeAlias`, `cleanup` and
`coldPayload` definitions. Unlike `Proofs.lean` (tag/readable-byte ownership of `payload8` and
`payload64`), these own the typed union `pts p 2 u`, so they state what the payload aliases
observe and what the cleanup paths write:

* `writeAlias`: both pointer-try results address the same payload. A write through the first
  is the value read through the second and is left in the union; the tag is not written.
  An error returns the original name and writes nothing.
* `cleanup` with distinct counters: success runs only `defer`; error runs `errdefer` and
  `defer`, returns the original error, and leaves the union unchanged.
* `cleanup` with one counter passed for both cleanup pointers (aliased cleanup targets):
  error increments that counter twice, success once.
* `coldPayload`: the cold error body runs its `errdefer`; success returns the payload address.

The result value is captured before cleanup runs. Counter increments use `add_safe`, so each
rule requires the counter to have room for its increments. -/

open Zig
open scoped Zig

namespace TryPointersAliasProofs

/-- The finite domain declared by every retained source AIR function. -/
abbrev domain : ErrorDomain := ⟨#["Bad", "Other"], by decide, by decide⟩

def admitted (u : Except ErrName (BitVec 8)) : Prop :=
  ∀ e, u = .error e → domain.names.contains e = true

/-- `add_safe` of 1 does not overflow below the maximum, in the form simp reaches. -/
theorem no_overflow {k : BitVec 32} (hk : k.toNat + 1 < 2 ^ 32) : ¬ 4294967295 ≤ k.toNat := by
  omega

theorem no_overflow_succ {k : BitVec 32} (hk : k.toNat + 2 < 2 ^ 32) :
    ¬ 4294967295 ≤ (k.toNat + 1) % 4294967296 := by
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem u8_offsets : errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8)) = (0, 2) :=
  rfl

theorem u8_size : Enc.size (Except ErrName (BitVec 8)) = 4 := rfl

theorem tag_align : Nat.min 2 2 ∣ 2 := by decide
theorem tag_off : Nat.min 2 2 ∣ (errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8))).1 := by
  rw [u8_offsets]; decide
theorem pay_align : 1 ∣ 2 := by decide
theorem pay_off : 1 ∣ (errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8))).2 := by
  decide
theorem pay_size : 0 < Enc.size (BitVec 8) := by decide

/-! ## Two pointer-try results alias -/

theorem writeAlias_run {p : Ptr} {u : Except ErrName (BitVec 8)} {y : BitVec 8} {m : Mem}
    {h hF : Heap} (hp : pts p 2 u h) (hdom : admitted u) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryPointers.writeAlias p y).run m = pure (writeView y u, m') ∧
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
    simp [TryPointers.writeAlias, tryView, writeView, zig_unfold, h₁, h₂, h₃]
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
    simp [TryPointers.writeAlias, tryView, writeView, zig_unfold, h₁, h₂, h₃, h₄, h₅, h₆]

theorem writeAlias_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8)
    (hdom : admitted u) :
    Triple (pts p 2 u) (TryPointers.writeAlias p y)
      (fun r => ⌜r = writeView y u⌝ ∗ pts p 2 (writeView y u)) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := writeAlias_run hp hdom hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

/-! ## Cleanup paths -/

/-- A `u32` counter load, then a store of any value, on the owned counter. -/
theorem bump_run {c : Ptr} {k : BitVec 32} {m : Mem} {h hF : Heap}
    (hp : pts c 4 k h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m₁, (load (BitVec 32) 4 c).run m = pure (k, m₁) ∧
      ∀ w : BitVec 32, ∃ m₂, (store 4 c w).run m₁ = pure ((), m₂) ∧ m₂.Seq ∧
        ∃ h', Heap.Disjoint h' hF ∧ m₂.heap = h' ∪ hF ∧ pts c 4 w h' := by
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_load_run hp hm (by decide) hs
  exact ⟨m₁, h₁, fun w => pts_store_run hp hm₁ hd (by decide) hs₁ w⟩

private theorem rot {a b c F : Heap} (hab : Heap.Disjoint a b) (hac : Heap.Disjoint a c)
    (hbc : Heap.Disjoint b c) : a ∪ (b ∪ (c ∪ F)) = c ∪ (a ∪ (b ∪ F)) := by
  funext l
  rcases hab l with x | x <;> rcases hac l with y | y <;> rcases hbc l with z | z <;> simp [x, y, z]

private theorem regroup {a b c F : Heap} (hab : Heap.Disjoint a b) (hac : Heap.Disjoint a c)
    (hbc : Heap.Disjoint b c) : b ∪ (c ∪ (a ∪ F)) = (a ∪ (b ∪ c)) ∪ F := by
  funext l
  rcases hab l with x | x <;> rcases hac l with y | y <;> rcases hbc l with z | z <;> simp [x, y, z]

private theorem disj3 {a b c F : Heap} (haF : Heap.Disjoint a F) (hbF : Heap.Disjoint b F)
    (hcF : Heap.Disjoint c F) : Heap.Disjoint (a ∪ (b ∪ c)) F :=
  Heap.disjoint_union_left.mpr ⟨haF, Heap.disjoint_union_left.mpr ⟨hbF, hcF⟩⟩

/-- Distinct counters. Success runs `defer` only and returns the payload read before cleanup.
Error runs `errdefer` then `defer`, returns the original error and leaves the union intact. -/
theorem cleanup_run {p o e : Ptr} {u : Except ErrName (BitVec 8)} {c k : BitVec 32} {m : Mem}
    {h hF : Heap} (hpre : (pts p 2 u ∗ (pts o 4 c ∗ pts e 4 k)) h) (hdom : admitted u)
    (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryPointers.cleanup p o e).run m = pure (u, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
      (pts p 2 u ∗ (pts o 4 (c + 1) ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1))) h' ∧
      m'.Seq := by
  obtain ⟨hu, hoe, hd1, rfl, hp, ho', he', hd2, rfl, ho, he⟩ := hpre
  obtain ⟨huo, hue⟩ := Heap.disjoint_union_right.mp hd1
  obtain ⟨huF, hoeF⟩ := Heap.disjoint_union_left.mp hd
  obtain ⟨hoF, heF⟩ := Heap.disjoint_union_left.mp hoeF
  have hmu : m.heap = hu ∪ (ho' ∪ (he' ∪ hF)) := by rw [hm, Heap.union_assoc, Heap.union_assoc]
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_discard_run hp hmu hs
  rw [u8_size] at h₁
  obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_finiteTry_run (d := domain) hp tag_align tag_off hdom hm₁ hs₁
  cases u with
  | error name =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ :=
      pts_finiteErrCode_run (d := domain) hp tag_align tag_off (hdom name rfl) hm₂ hs₂
    -- errdefer: the error counter.
    have hme : m₃.heap = he' ∪ (hu ∪ (ho' ∪ hF)) := by rw [hm₃, rot huo hue hd2]
    obtain ⟨m₄, h₄, hst₄⟩ := bump_run he hme
      (Heap.disjoint_union_right.mpr ⟨hue.symm, Heap.disjoint_union_right.mpr ⟨hd2.symm, heF⟩⟩) hs₃
    obtain ⟨m₅, h₅, hs₅, he'', hdE, hm₅, he₂⟩ := hst₄ (k + 1#32)
    obtain ⟨hEu, hEoF⟩ := Heap.disjoint_union_right.mp hdE
    obtain ⟨hEo, hEF⟩ := Heap.disjoint_union_right.mp hEoF
    -- defer: the ordinary counter.
    have hmo : m₅.heap = ho' ∪ (he'' ∪ (hu ∪ hF)) := by rw [hm₅, rot hEu hEo huo]
    obtain ⟨m₆, h₆, hst₆⟩ := bump_run ho hmo
      (Heap.disjoint_union_right.mpr ⟨hEo.symm, Heap.disjoint_union_right.mpr ⟨huo.symm, hoF⟩⟩) hs₅
    obtain ⟨m₇, h₇, hs₇, ho'', hdO, hm₇, ho₂⟩ := hst₆ (c + 1#32)
    obtain ⟨hOE, hOuF⟩ := Heap.disjoint_union_right.mp hdO
    obtain ⟨hOu, hOF⟩ := Heap.disjoint_union_right.mp hOuF
    refine ⟨m₇, hu ∪ (ho'' ∪ he''), ?_, disj3 huF hOF hEF,
      by rw [hm₇, regroup hOu.symm hEu.symm hOE],
      ⟨hu, ho'' ∪ he'', Heap.disjoint_union_right.mpr ⟨hOu.symm, hEu.symm⟩, rfl, hp,
        ho'', he'', hOE, rfl, ho₂, he₂⟩, hs₇⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
    simp [TryPointers.cleanup, tryView, zig_unfold, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      no_overflow hc, no_overflow hk]
  | ok x =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ := pts_payload_load_run hp pay_align pay_off pay_size hm₂ hs₂
    have hmo : m₃.heap = ho' ∪ (hu ∪ (he' ∪ hF)) := by
      rw [hm₃, Heap.union_left_comm huo]
    obtain ⟨m₄, h₄, hst₄⟩ := bump_run ho hmo
      (Heap.disjoint_union_right.mpr ⟨huo.symm, Heap.disjoint_union_right.mpr ⟨hd2, hoF⟩⟩) hs₃
    obtain ⟨m₅, h₅, hs₅, ho'', hdO, hm₅, ho₂⟩ := hst₄ (c + 1#32)
    obtain ⟨hOu, hOeF⟩ := Heap.disjoint_union_right.mp hdO
    obtain ⟨hOe, hOF⟩ := Heap.disjoint_union_right.mp hOeF
    refine ⟨m₅, hu ∪ (ho'' ∪ he'), ?_, disj3 huF hOF heF,
      by rw [hm₅, Heap.union_left_comm hOu, Heap.union_assoc, Heap.union_assoc],
      ⟨hu, ho'' ∪ he', Heap.disjoint_union_right.mpr ⟨hOu.symm, hue⟩, rfl, hp,
        ho'', he', hOe, rfl, ho₂, he⟩, hs₅⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅
    simp [TryPointers.cleanup, tryView, zig_unfold, h₁, h₂, h₃, h₄, h₅, no_overflow hc]

theorem cleanup_owned (p o e : Ptr) (u : Except ErrName (BitVec 8)) (c k : BitVec 32)
    (hdom : admitted u) (hc : c.toNat + 1 < 2 ^ 32) (hk : k.toNat + 1 < 2 ^ 32) :
    Triple (pts p 2 u ∗ (pts o 4 c ∗ pts e 4 k)) (TryPointers.cleanup p o e)
      (fun r => ⌜r = u⌝ ∗
        (pts p 2 u ∗ (pts o 4 (c + 1) ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1)))) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := cleanup_run hp hdom hc hk hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

/-- Aliased cleanup targets: one counter is passed for both `ordinary` and `on_error`.
Error increments it twice (errdefer, then defer), success once. -/
theorem cleanup_shared_run {p c : Ptr} {u : Except ErrName (BitVec 8)} {k : BitVec 32} {m : Mem}
    {h hF : Heap} (hpre : (pts p 2 u ∗ pts c 4 k) h) (hdom : admitted u)
    (hk : k.toNat + 2 < 2 ^ 32) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryPointers.cleanup p c c).run m = pure (u, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
      (pts p 2 u ∗ pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1)) h' ∧
      m'.Seq := by
  obtain ⟨hu, hc, hd1, rfl, hp, hcnt⟩ := hpre
  obtain ⟨huF, hcF⟩ := Heap.disjoint_union_left.mp hd
  have hmu : m.heap = hu ∪ (hc ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_discard_run hp hmu hs
  rw [u8_size] at h₁
  obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_finiteTry_run (d := domain) hp tag_align tag_off hdom hm₁ hs₁
  have hk1 : k.toNat + 1 < 2 ^ 32 := by omega
  cases u with
  | error name =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ :=
      pts_finiteErrCode_run (d := domain) hp tag_align tag_off (hdom name rfl) hm₂ hs₂
    have hmc : m₃.heap = hc ∪ (hu ∪ hF) := by rw [hm₃, Heap.union_left_comm hd1]
    obtain ⟨m₄, h₄, hst₄⟩ := bump_run hcnt hmc
      (Heap.disjoint_union_right.mpr ⟨hd1.symm, hcF⟩) hs₃
    obtain ⟨m₅, h₅, hs₅, hc', hdC, hm₅, hcnt'⟩ := hst₄ (k + 1#32)
    obtain ⟨m₆, h₆, hst₆⟩ := bump_run hcnt' hm₅ hdC hs₅
    obtain ⟨m₇, h₇, hs₇, hc'', hdC', hm₇, hcnt''⟩ := hst₆ (k + 1#32 + 1#32)
    obtain ⟨hCu, hCF⟩ := Heap.disjoint_union_right.mp hdC'
    refine ⟨m₇, hu ∪ hc'', ?_, Heap.disjoint_union_left.mpr ⟨huF, hCF⟩,
      by rw [hm₇, Heap.union_left_comm hCu, Heap.union_assoc],
      ⟨hu, hc'', hCu.symm, rfl, hp, hcnt''⟩, hs₇⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
    simp [TryPointers.cleanup, tryView, zig_unfold, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      no_overflow hk1, no_overflow_succ hk]
  | ok x =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ := pts_payload_load_run hp pay_align pay_off pay_size hm₂ hs₂
    have hmc : m₃.heap = hc ∪ (hu ∪ hF) := by rw [hm₃, Heap.union_left_comm hd1]
    obtain ⟨m₄, h₄, hst₄⟩ := bump_run hcnt hmc
      (Heap.disjoint_union_right.mpr ⟨hd1.symm, hcF⟩) hs₃
    obtain ⟨m₅, h₅, hs₅, hc', hdC, hm₅, hcnt'⟩ := hst₄ (k + 1#32)
    obtain ⟨hCu, hCF⟩ := Heap.disjoint_union_right.mp hdC
    refine ⟨m₅, hu ∪ hc', ?_, Heap.disjoint_union_left.mpr ⟨huF, hCF⟩,
      by rw [hm₅, Heap.union_left_comm hCu, Heap.union_assoc],
      ⟨hu, hc', hCu.symm, rfl, hp, hcnt'⟩, hs₅⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅
    simp [TryPointers.cleanup, tryView, zig_unfold, h₁, h₂, h₃, h₄, h₅, no_overflow hk1]

theorem cleanup_shared_owned (p c : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 2 < 2 ^ 32) :
    Triple (pts p 2 u ∗ pts c 4 k) (TryPointers.cleanup p c c)
      (fun r => ⌜r = u⌝ ∗
        (pts p 2 u ∗ pts c 4 (match u with | .ok _ => k + 1 | .error _ => k + 1 + 1))) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := cleanup_shared_run hp hdom hk hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

/-- The cold error body runs its `errdefer`; success returns the payload address untouched. -/
theorem coldPayload_run {p e : Ptr} {u : Except ErrName (BitVec 8)} {k : BitVec 32} {m : Mem}
    {h hF : Heap} (hpre : (pts p 2 u ∗ pts e 4 k) h) (hdom : admitted u)
    (hk : k.toNat + 1 < 2 ^ 32) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) :
    ∃ m' h', (TryPointers.coldPayload p e).run m = pure (tryView (BitVec 8) p u, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
      (pts p 2 u ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1)) h' ∧ m'.Seq := by
  obtain ⟨hu, hc, hd1, rfl, hp, hcnt⟩ := hpre
  obtain ⟨huF, hcF⟩ := Heap.disjoint_union_left.mp hd
  have hmu : m.heap = hu ∪ (hc ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_discard_run hp hmu hs
  rw [u8_size] at h₁
  obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_finiteTry_run (d := domain) hp tag_align tag_off hdom hm₁ hs₁
  cases u with
  | error name =>
    obtain ⟨m₃, h₃, hm₃, hs₃⟩ :=
      pts_finiteErrCode_run (d := domain) hp tag_align tag_off (hdom name rfl) hm₂ hs₂
    have hmc : m₃.heap = hc ∪ (hu ∪ hF) := by rw [hm₃, Heap.union_left_comm hd1]
    obtain ⟨m₄, h₄, hst₄⟩ := bump_run hcnt hmc
      (Heap.disjoint_union_right.mpr ⟨hd1.symm, hcF⟩) hs₃
    obtain ⟨m₅, h₅, hs₅, hc', hdC, hm₅, hcnt'⟩ := hst₄ (k + 1#32)
    obtain ⟨hCu, hCF⟩ := Heap.disjoint_union_right.mp hdC
    refine ⟨m₅, hu ∪ hc', ?_, Heap.disjoint_union_left.mpr ⟨huF, hCF⟩,
      by rw [hm₅, Heap.union_left_comm hCu, Heap.union_assoc],
      ⟨hu, hc', hCu.symm, rfl, hp, hcnt'⟩, hs₅⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄ h₅
    simp [TryPointers.coldPayload, tryView, zig_unfold, h₁, h₂, h₃, h₄, h₅, no_overflow hk]
  | ok x =>
    refine ⟨m₂, hu ∪ hc, ?_, hd, by rw [hm₂, Heap.union_assoc],
      ⟨hu, hc, hd1, rfl, hp, hcnt⟩, hs₂⟩
    simp only [StateT.run] at h₁ h₂
    simp [TryPointers.coldPayload, tryView, zig_unfold, h₁, h₂]

theorem coldPayload_owned (p e : Ptr) (u : Except ErrName (BitVec 8)) (k : BitVec 32)
    (hdom : admitted u) (hk : k.toNat + 1 < 2 ^ 32) :
    Triple (pts p 2 u ∗ pts e 4 k) (TryPointers.coldPayload p e)
      (fun r => ⌜r = tryView (BitVec 8) p u⌝ ∗
        (pts p 2 u ∗ pts e 4 (match u with | .ok _ => k | .error _ => k + 1))) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ := coldPayload_run hp hdom hk hm hd hs
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

end TryPointersAliasProofs
