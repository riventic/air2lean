import ZigLean.Conc.Spec.Sys

/-!
# Counting threads, and views that merge

Two small libraries for the sync specs whose invariants count threads or merge views
(`WaitGroupSpec`, `CondSpec`; `docs/thread-specs.md`).

* `tsum N g`: the sum of `g u` over the threads `u < N`. The most general clients of these specs
  run `N` threads, for every `N`, so that a count of the threads at some place is a number.
  `tsum_tset` is how a count changes when one thread moves.
* `Lat X`: a join semilattice of views. A release write puts the writer's view into a message
  joined with the message's old view (an RMW continues a release sequence), and an acquire read
  joins the message's view into the reader's. `Lat.le` is the order: `a` happens before what a
  thread with view `b` sees.
-/

namespace Zig
namespace Spec

/-- `omega` after unfolding `Tid` (`omega` does not see through the abbreviation). -/
macro "tomega" : tactic => `(tactic| ((try simp only [Tid] at *) <;> omega))

/-! ## Sums over the threads below `N` -/

/-- The sum of `g u` over the threads `u < N`. -/
def tsum (N : Nat) (g : Nat → Nat) : Nat := ((List.range N).map g).sum

@[simp] theorem tsum_zero (g : Nat → Nat) : tsum 0 g = 0 := rfl

theorem tsum_succ (N : Nat) (g : Nat → Nat) : tsum (N + 1) g = tsum N g + g N := by
  simp [tsum, List.range_succ]

theorem tsum_congr {N : Nat} {g h : Nat → Nat} (e : ∀ u, u < N → g u = h u) :
    tsum N g = tsum N h := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [tsum_succ, tsum_succ, ih fun u hu => e u (by omega), e N (by omega)]

theorem tsum_le {N : Nat} {g h : Nat → Nat} (e : ∀ u, u < N → g u ≤ h u) :
    tsum N g ≤ tsum N h := by
  induction N with
  | zero => exact Nat.le_refl _
  | succ N ih =>
    rw [tsum_succ, tsum_succ]
    exact Nat.add_le_add (ih fun u hu => e u (by omega)) (e N (by omega))

theorem tsum_add (N : Nat) (g h : Nat → Nat) :
    tsum N (fun u => g u + h u) = tsum N g + tsum N h := by
  induction N with
  | zero => rfl
  | succ N ih => rw [tsum_succ, tsum_succ, tsum_succ, ih]; omega

/-- One summand is at most the sum. -/
theorem le_tsum {N : Nat} (g : Nat → Nat) {u : Nat} (hu : u < N) : g u ≤ tsum N g := by
  revert hu
  induction N with
  | zero => intro hu; omega
  | succ N ih =>
    intro hu
    rw [tsum_succ]
    by_cases h : u = N
    · subst h; omega
    · have := ih (by omega); omega

theorem tsum_eq_zero {N : Nat} {g : Nat → Nat} (h : ∀ u, u < N → g u = 0) : tsum N g = 0 := by
  rw [tsum_congr (h := fun _ => 0) h]
  clear h
  induction N with
  | zero => rfl
  | succ N ih => rw [tsum_succ, ih]

/-- A positive sum has a positive summand. -/
theorem exists_of_tsum_pos {N : Nat} {g : Nat → Nat} (h : 0 < tsum N g) : ∃ u, u < N ∧ 0 < g u := by
  refine Classical.byContradiction fun hn => ?_
  have : tsum N g = 0 := tsum_eq_zero fun u hu => by
    cases hg : g u with
    | zero => rfl
    | succ k => exact absurd ⟨u, hu, by omega⟩ hn
  omega

/-- **How a sum changes when thread `t` moves from `f t` to `c`.** -/
theorem tsum_tset {β : Type} {N : Nat} (g : β → Nat) (f : Nat → β) {t : Nat} (ht : t < N) (c : β) :
    tsum N (fun u => g (tset f t c u)) + g (f t) = tsum N (fun u => g (f u)) + g c := by
  revert ht
  induction N with
  | zero => intro ht; omega
  | succ N ih =>
    intro ht
    rw [tsum_succ, tsum_succ]
    by_cases hN : N = t
    · subst hN
      rw [tset_self, tsum_congr (h := fun u => g (f u)) fun u hu => by rw [tset_ne _ _ (Nat.ne_of_lt hu)]]
      omega
    · have := ih (by omega)
      rw [tset_ne _ _ hN]
      omega

/-- A sum of indicators of a property that at most one thread has is at most `1`. -/
theorem tsum_le_one {N : Nat} {g : Nat → Nat} (hg : ∀ u, g u ≤ 1)
    (h : ∀ u v, 0 < g u → 0 < g v → u = v) : tsum N g ≤ 1 := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [tsum_succ]
    by_cases hN : g N = 0
    · rw [hN]; exact ih
    · have : tsum N g = 0 := tsum_eq_zero fun u hu => by
        cases hg' : g u with
        | zero => rfl
        | succ k => exact absurd (h u N (by omega) (by omega)) (by omega)
      have := hg N
      omega

/-! ## Join semilattices of views -/

/-- A join semilattice (module doc). -/
structure Lat (X : Type) where
  join : X → X → X
  assoc : ∀ a b c, join (join a b) c = join a (join b c)
  comm : ∀ a b, join a b = join b a
  idem : ∀ a, join a a = a

namespace Lat

variable {X : Type} (L : Lat X)

/-- `a ≤ b`: `b` already contains `a`. -/
def le (a b : X) : Prop := L.join a b = b

variable {L}

theorem le_refl (a : X) : L.le a a := L.idem a

theorem le_trans {a b c : X} (h1 : L.le a b) (h2 : L.le b c) : L.le a c := by
  unfold le at *
  rw [← h2, ← L.assoc, h1]

theorem le_join_left (a b : X) : L.le a (L.join a b) := by
  unfold le; rw [← L.assoc, L.idem]

theorem le_join_right (a b : X) : L.le b (L.join a b) := by
  rw [L.comm]; exact le_join_left b a

theorem join_le {a b c : X} (ha : L.le a c) (hb : L.le b c) : L.le (L.join a b) c := by
  unfold le at *
  rw [L.assoc, hb, ha]

theorem le_join_of_le_left {a b : X} (c : X) (h : L.le a b) : L.le a (L.join b c) :=
  le_trans h (le_join_left b c)

theorem le_join_of_le_right {a c : X} (b : X) (h : L.le a c) : L.le a (L.join b c) :=
  le_trans h (le_join_right b c)

end Lat

end Spec
end Zig
