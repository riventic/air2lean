/-!
# Sums over threads and over writes

A small library for the invariants of the full-state logic that count: `tsum N g` is the sum of
`g u` over `u < N` (threads, or the writes of a word). The counting invariant of the
multi-waiter condition (`ZigLean/Sep/Full/CondInv.lean`) uses it for the number of registered
waiters and of pending claims, and for the signals posted after a write.

* `tsum_upd`: how a sum changes when one point changes.
* `tsum_ext`: a sum over a support bound does not depend on the bound.
* `tsum_tag`: a sum over writes is at most a sum over threads, when each write with a positive
  weight has its own thread (a thread names at most one write, its tag).
* `le_add_tsum_up`: a sequence grows by at most the sum of its increases.

This is the home of the sum. The legacy `Zig.Spec.tsum` of the retired `Conc/Spec` layer
(`docs/thread-specs.md`) was the same definition.
-/

namespace Zig
namespace Full

/-- The sum of `g u` over `u < N`. -/
def tsum (N : Nat) (g : Nat → Nat) : Nat := ((List.range N).map g).sum

@[simp] theorem tsum_zero (g : Nat → Nat) : tsum 0 g = 0 := rfl

theorem tsum_succ (N : Nat) (g : Nat → Nat) : tsum (N + 1) g = tsum N g + g N := by
  simp [tsum, List.range_succ, List.sum_append]

theorem tsum_congr {N : Nat} {g h : Nat → Nat} (e : ∀ u, u < N → g u = h u) :
    tsum N g = tsum N h := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [tsum_succ, tsum_succ, ih (fun u hu => e u (by omega)), e N (by omega)]

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

theorem le_tsum {N : Nat} (g : Nat → Nat) {u : Nat} (hu : u < N) : g u ≤ tsum N g := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [tsum_succ]
    by_cases h : u = N
    · subst h; omega
    · have := ih (by omega); omega

theorem tsum_eq_zero {N : Nat} {g : Nat → Nat} (h : ∀ u, u < N → g u = 0) : tsum N g = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [tsum_succ, ih (fun u hu => h u (by omega)), h N (by omega)]

theorem exists_of_tsum_pos {N : Nat} {g : Nat → Nat} (h : 0 < tsum N g) :
    ∃ u, u < N ∧ 0 < g u := by
  induction N with
  | zero => simp at h
  | succ N ih =>
    rw [tsum_succ] at h
    by_cases hN : 0 < g N
    · exact ⟨N, by omega, hN⟩
    · obtain ⟨u, hu, hp⟩ := ih (by omega)
      exact ⟨u, by omega, hp⟩

/-- **A support bound does not matter**: past `N` the summand is `0`. -/
theorem tsum_ext {N N' : Nat} {g : Nat → Nat} (hN : N ≤ N') (h0 : ∀ u, N ≤ u → g u = 0) :
    tsum N' g = tsum N g := by
  induction N' with
  | zero => obtain rfl : N = 0 := by omega
            rfl
  | succ N' ih =>
    by_cases e : N = N' + 1
    · rw [e]
    · rw [tsum_succ, ih (by omega), h0 N' (by omega), Nat.add_zero]

/-- **One point changes**: the sum moves by the difference at that point. -/
theorem tsum_upd {N : Nat} {g g' : Nat → Nat} {t : Nat} (ht : t < N)
    (h : ∀ u, u ≠ t → g' u = g u) : tsum N g' + g t = tsum N g + g' t := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [tsum_succ, tsum_succ]
    by_cases e : t = N
    · subst e
      rw [tsum_congr (fun u hu => h u (by omega))]
      omega
    · have := ih (by omega)
      rw [h N (Ne.symm e)]
      omega

/-- The sum of one point. -/
theorem tsum_point {N t : Nat} (ht : t < N) (a : Nat) :
    tsum N (fun u => if u = t then a else 0) = a := by
  have := tsum_upd (g := fun _ => 0) (g' := fun u => if u = t then a else 0) ht
    (fun u hu => by simp [hu])
  rw [tsum_eq_zero (fun _ _ => rfl)] at this
  simpa using this

/-- A sum is at most another plus the excess at one point. -/
theorem tsum_le_add_point {N t : Nat} {g h : Nat → Nat} (ht : t < N)
    (e : ∀ u, u < N → u ≠ t → g u ≤ h u) : tsum N g ≤ tsum N h + g t := by
  have : tsum N g ≤ tsum N (fun u => h u + if u = t then g t else 0) :=
    tsum_le fun u hu => by
      by_cases hut : u = t
      · subst hut; simp
      · simp [hut]; exact e u hu hut
  rw [tsum_add, tsum_point ht] at this
  exact this

/-- **Writes with their own threads.** If every point `q < Q` with a positive weight `f q` has a
thread `v < N` tagged `q` whose `g v` is at least `f q`, then the weights sum to at most the
sum of `g`. -/
theorem tsum_tag {Q N : Nat} {f g : Nat → Nat} (tag : Nat → Option Nat)
    (h : ∀ q, q < Q → 0 < f q → ∃ v, v < N ∧ tag v = some q ∧ f q ≤ g v) :
    tsum Q f ≤ tsum N g := by
  -- the threads tagged below `Q`
  have key : ∀ Q', Q' ≤ Q → tsum Q' f ≤
      tsum N (fun v => match tag v with | some q => if q < Q' then g v else 0 | none => 0) := by
    intro Q' hQ'
    induction Q' with
    | zero => exact Nat.zero_le _
    | succ Q' ih =>
      have hsplit : tsum N (fun v => match tag v with
            | some q => if q < Q' + 1 then g v else 0 | none => 0) =
          tsum N (fun v => match tag v with | some q => if q < Q' then g v else 0 | none => 0) +
          tsum N (fun v => if tag v = some Q' then g v else 0) := by
        rw [← tsum_add]
        refine tsum_congr fun v _ => ?_
        rcases hv : tag v with _ | q
        · simp
        · simp only [Option.some.injEq]
          by_cases h1 : q = Q'
          · subst h1; simp
          · by_cases h2 : q < Q'
            · simp [h1, h2, show q < Q' + 1 by omega]
            · simp [h1, h2, show ¬ q < Q' + 1 by omega]
      rw [tsum_succ, hsplit]
      refine Nat.add_le_add (ih (by omega)) ?_
      by_cases hf : 0 < f Q'
      · obtain ⟨v, hv, htag, hle⟩ := h Q' (by omega) hf
        have := le_tsum (fun v => if tag v = some Q' then g v else 0) hv
        simp only [htag, ite_true] at this
        omega
      · omega
  refine Nat.le_trans (key Q (Nat.le_refl _)) (tsum_le fun v _ => ?_)
  rcases tag v with _ | q
  · exact Nat.zero_le _
  · dsimp only; split <;> omega

/-- **A sequence grows by at most its increases**: `a n` is at most `a k` plus the increases of
the steps `q` with `k < q < n + 1`. -/
theorem le_add_tsum_up (a : Nat → Nat) {k n : Nat} (hk : k ≤ n) :
    a n ≤ a k + tsum (n + 1) (fun q => if k < q then a q - a (q - 1) else 0) := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            exact Nat.le_add_right _ _
  | succ n ih =>
    by_cases e : k = n + 1
    · subst e; exact Nat.le_add_right _ _
    · have := ih (by omega)
      rw [tsum_succ]
      simp only [show k < n + 1 by omega, ite_true, Nat.add_sub_cancel]
      omega

/-- **Counting a list**: the points below `N` that are in a list without duplicates, all of
whose members are below `N`, are as many as its length. -/
theorem tsum_mem {N : Nat} {l : List Nat} (hl : l.Nodup) (hN : ∀ u ∈ l, u < N) :
    tsum N (fun u => if u ∈ l then 1 else 0) = l.length := by
  induction l with
  | nil => exact tsum_eq_zero fun u _ => by simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have hsplit : tsum N (fun u => if u ∈ a :: l then 1 else 0) =
        tsum N (fun u => if u ∈ l then 1 else 0) + tsum N (fun u => if u = a then 1 else 0) := by
      rw [← tsum_add]
      refine tsum_congr fun u _ => ?_
      by_cases h : u = a
      · subst h; simp [ha]
      · simp [h]
    rw [hsplit, ih hl' (fun u hu => hN u (List.mem_cons_of_mem _ hu)),
      tsum_point (hN a (List.mem_cons_self ..)) 1, List.length_cons]

end Full
end Zig
