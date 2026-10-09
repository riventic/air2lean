import ZigLean.Sep.Full.Triple
import ZigLean.Os.Mmap

/-!
# More `Tame` programs, and the `tame` tactic

`Tame c` (`ZigLean/Sep/Full/Triple.lean`): `c` keeps the atomic layout and every block's address,
so a legacy triple of `c` lifts to a full-state one (`FTriple.ofTriple`, `FTotalTriple.ofTotal`).
This file adds the control flow of normalized generated code (`throw`, `if`, `match`,
`Option.elim`, `<$>`), `@ptrFromInt`, and the OS page mappings of premise OSM-01 (`Os.mmap`,
`Os.munmap`, `Os.mremap`: they push blocks, or replace a block by one at the same address).

`tame` proves `Tame c` for a `MemM` program built from these, after the generated function is
normalized to its `MemM` program (`gen_norm`-style `simp` with `ZigLean/Sep/AllocSpec/Norm.lean`).
-/

namespace Zig
namespace Full
namespace Tame

open Conc

variable {α β : Type}

theorem throw (e : Error) : Tame (throw e : MemM α) := fun _ _ _ h =>
  (Proto.MemM.throw_ok h).elim

theorem ite {c : Prop} [Decidable c] {x y : MemM α} (hx : Tame x) (hy : Tame y) :
    Tame (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem elim {o : Option β} {x : MemM α} {f : β → MemM α} (hx : Tame x) (hf : ∀ b, Tame (f b)) :
    Tame (o.elim x f) := by
  cases o
  · exact hx
  · exact hf _

theorem map {f : α → β} {x : MemM α} (hx : Tame x) : Tame (f <$> x) := by
  rw [map_eq_pure_bind]; exact bind hx fun _ => pure' _

theorem get : Tame (get : MemM Mem) := fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Proto.MemM.get_ok h; exact ⟨rfl, KMono.refl _⟩

theorem ptrFromAddr (n : Nat) : Tame (Zig.ptrFromAddr n) := fun m v m' h => by
  rcases ptrFromAddr_run n m with ⟨w, hw⟩ | hw <;> rw [hw] at h
  · obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok (m := m) (x := w) (a := v) (by exact h)
    exact ⟨rfl, KMono.refl _⟩
  · exact (Proto.MemM.throw_ok (m := m) (e := Error.unspecified) (a := v) (by exact h)).elim

/-- A step that only replaces block `b` by one at the same address (and may push blocks). -/
theorem of_blocks {c : MemM α}
    (h : ∀ m v m', (c.run m).run = some (.ok (v, m')) → m'.atomics = m.atomics ∧ KMono m m') :
    Tame c := of_eq h

theorem recordAccess (b o n : Nat) (k : AccessKind) : Tame (Zig.recordAccess b o n k) :=
  of_eq fun m v m' h => by
    obtain ⟨-, rfl⟩ := Proto.recordAccess_ok h
    exact ⟨rfl, KMono.of_blocks rfl⟩

end Tame

/-- `Tame` goals of normalized generated code. Callees are taken from the hypotheses
(`have := …` the callee's `Tame` lemma first). -/
macro "tame" : tactic => `(tactic| repeat' (first
  | (guard_target = ∀ _, _; intro)
  | with_reducible exact Tame.pure' _
  | with_reducible exact Tame.throw _
  | with_reducible exact Tame.lift _
  | with_reducible exact Tame.get
  | with_reducible exact Tame.load _ _ _
  | with_reducible exact Tame.store _ _ _
  | with_reducible exact Tame.loadBytes _ _ _ _
  | with_reducible exact Tame.storeBytes _ _ _ _
  | with_reducible exact Tame.alloc _ _ _
  | with_reducible exact Tame.free _
  | with_reducible exact Tame.ptrAddr _
  | with_reducible exact Tame.ptrFromAddr _
  | with_reducible exact Tame.recordAccess _ _ _ _
  | with_reducible apply_assumption
  | with_reducible apply Tame.map
  | with_reducible apply Tame.ite
  | with_reducible apply Tame.elim
  | with_reducible apply Tame.bind
  | split))

end Full
end Zig
