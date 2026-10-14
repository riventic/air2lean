import ZigLean.Sep.Full.Word

/-!
# The `Box` of `handoff`, abstractly

`handoff` (examples/sync, Zig 0.16.0 and 0.17.0 `std.Io`; examples/threadsync, Zig 0.15.2
`std.Thread`) is the same program in each version: `main` and a producer share a `Box` with a
mutex, a condition (state and epoch), an event, `v` and `ready`. The versions differ in the
`Box`'s layout (0.16.0 has `io` first), in the mutex's contended value, and in the generated code
of the sync objects (proved once per version against the contracts `MutexImpl`, `CondImpl`,
`EventImpl`). `Layout` is the part of the layout that the protocol (`Proofs/Handoff/Protocol.lean`)
reads; each version's walk (`Proofs/Sync/Handoff.lean`, `Proofs/Threadsync/Handoff.lean`) gives its
own and checks the facts by `decide`.
-/

namespace Zig
namespace Handoff

open Conc

/-- The `Box`'s layout (module doc): its size and alignment, the length of the `io` prefix (`0`
when there is none), and the offsets of the mutex, the condition's state (its epoch follows), the
event, `v` and `ready`; the mutex's contended value `c`. -/
structure Layout where
  size : Nat
  align : Nat
  io : Nat
  mo : Nat
  so : Nat
  vo : Nat
  xo : Nat
  ro : Nat
  c : Nat
  c_ok : c = 1 ∨ c = 2 ∨ c = 3
  /-- The parts are in this order, 4-aligned, and in the `Box`. -/
  ok : io ≤ mo ∧ mo + 4 ≤ so ∧ so + 8 = vo ∧ vo + 4 ≤ xo ∧ xo + 4 ≤ ro ∧ ro + 1 ≤ size ∧
    mo % 4 = 0 ∧ so % 4 = 0 ∧ xo % 4 = 0 ∧ 0 < align ∧ 4 ∣ align

/-- The `Box` (block 0). -/
def bPtr : Ptr := ⟨some 0, 0⟩

namespace Layout

variable (Lo : Layout)

/-- The condition's state, its epoch and the event. -/
def WS : Word 32 4 := { b := 0, o := Lo.so }
def WE : Word 32 4 := { b := 0, o := Lo.so + 4 }
def WV : Word 32 4 := { b := 0, o := Lo.vo }

/-- The bytes of the three shared words: `so .. so + 12`. -/
def BoxW (l : Zig.Loc) : Prop := l.1 = 0 ∧ Lo.so ≤ l.2 ∧ l.2 < Lo.so + 12

instance (l : Zig.Loc) : Decidable (Lo.BoxW l) := by unfold BoxW; infer_instance

theorem ws_box {l : Zig.Loc} (h : Lo.WS.In l) : Lo.BoxW l := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by simp [WS] at h3; omega⟩

theorem we_box {l : Zig.Loc} (h : Lo.WE.In l) : Lo.BoxW l := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by simp [WE] at h2; omega, by simp [WE] at h3; omega⟩

theorem wv_box {l : Zig.Loc} (h : Lo.WV.In l) : Lo.BoxW l := by
  have := Lo.ok
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by simp [WV] at h2; omega, by simp [WV] at h3; omega⟩

/-- A byte of the three words is in one of them. -/
theorem box_cases {l : Zig.Loc} (h : Lo.BoxW l) : Lo.WS.In l ∨ Lo.WE.In l ∨ Lo.WV.In l := by
  have := Lo.ok
  obtain ⟨h1, h2, h3⟩ := h
  by_cases a : l.2 < Lo.so + 4
  · exact .inl ⟨h1, h2, a⟩
  · by_cases b : l.2 < Lo.so + 8
    · exact .inr (.inl ⟨h1, by simp [WE]; omega, by simp [WE]; omega⟩)
    · exact .inr (.inr ⟨h1, by simp [WV]; omega, by simp [WV]; omega⟩)

end Layout

end Handoff
end Zig
