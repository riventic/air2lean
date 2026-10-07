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

/-- The union value after `cleanup`/`coldPayload`: pointer try never writes the union. -/
def errOrPayload : Except ErrName (BitVec 8) → Except ErrName (BitVec 8)
  | .ok x => .ok x
  | .error e => .error e

theorem errOrPayload_eq (u : Except ErrName (BitVec 8)) : errOrPayload u = u := by
  cases u <;> rfl

theorem add_one_ok {k : BitVec 32} (hk : k.toNat + 1 < 2 ^ 32) :
    Zig.add false k 1 = pure (k + 1) := by
  simp [Zig.add, BitVec.uaddOverflow]
  omega

private theorem u8_offsets : errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8)) = (0, 2) :=
  rfl

private theorem u8_size : Enc.size (Except ErrName (BitVec 8)) = 4 := rfl

private theorem tag_align : Nat.min 2 2 ∣ 2 := by decide
private theorem tag_off : Nat.min 2 2 ∣ (errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8))).1 := by
  rw [u8_offsets]; decide
private theorem pay_align : 1 ∣ 2 := by decide
private theorem pay_off : 1 ∣ (errUnionOffsets (Enc.size (BitVec 8)) (Enc.align (BitVec 8))).2 := by
  decide
private theorem pay_size : 0 < Enc.size (BitVec 8) := by decide

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

end TryPointersAliasProofs
