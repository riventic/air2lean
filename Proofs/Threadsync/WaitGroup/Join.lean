import Proofs.Threadsync.WaitGroup.Read

/-!
# `main`'s joins in `waitGroup`'s protocol

After its read of the `Tally` (`rdd`), `main` joins task 1 and then task 2. Both tasks are
`fin` and lock-`gone` then (`proto.fin`, which `WP.joinC` gives).

- **The first join** (`wp_join1`): `main` takes task 1's part (`FLock.Inv.join`). The threads'
  shape records task 1 as joined exactly at `j1`, the shape's third case. The rest of `U` stays by
  `U_main` (a join keeps the blocks, atomics, footprint and heap, keeps as many threads, and its
  clocks grow), and then `main`'s new part by `U_part`.
- **The second join** (`wp_join2`): every thread record is `main`'s and joined. So every other
  thread is joined (`joinedAll`), and the end of a block races with no access
  (`freeRaces_of_joined`). These are the premises of `wp_free` and of `main`'s post `QM`.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Threadsync.WG

/-- **`main`'s join of task 1** at `rdd`: it takes the task's part, and task 1 is joined at
`j1`. -/
theorem wp_join1 {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM : Res} {w : Bool}
    (hi : proto.inv (upd G 0 (gO rM { ph := .rdd, wk := w })) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m' rM', n = k + 1 → m'.current = 0 →
      proto.inv (upd G₁ 0 (gO rM' { ph := .j1, wk := w })) m' → Q ((), s) G₁ m' k) :
    proto.WP 0 ((joinC 1 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  have hX0 : (G₁ 0).2 = { ph := .rdd, wk := w } := by rw [hg]; rfl
  obtain ⟨h00, hs3, hr1, hr2, ht1, ht2⟩ :=
    shape3 hu.shape (by rw [hX0]; exact (by decide : 3 ≤ Ph.rdd.rank))
  rw [hX0] at hr1
  have hr1': m₁.threads[1]? = some { spawner := 0, joined := false } := hr1
  refine ⟨fun _ => ⟨by show (0 : Nat) < 1; decide, by rw [hs3]; decide, ⟨rfl, .inl rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr1']⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₁ with current := 0 }) hr1' rfl rfl, fun m' hj => ?_⟩⟩
  have h10 : (1 : ThreadId) ≠ 0 := by decide
  have hl := hL.join (t := 0) (u := 1) (g := gO (rsum rM (L.own G₁ m₁ 1)) { ph := .j1, wk := w })
    h10 h10 (by rw [hg]; rfl) hfin.1 hj (by show _ = rsum (G₁ 0).1.part _; rw [hg]; rfl) rfl rfl
    fun r hR => R_upd0 hR
  obtain ⟨rec, hrec, -, hm'⟩ := join_eq hj
  obtain rfl : rec = _ := Option.some.inj (hrec.symm.trans hr1')
  have hcur : m'.current = 0 := by rw [hm']
  have hth : m'.threads = m₁.threads.set! 1 { spawner := 0, joined := true } := by rw [hm']
  have hclk : ∀ u : ThreadId, VClock.le (m₁.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hm']; show VClock.le _ ((m₁.clocks.set! 0 _)[u]!) = true
    rw [Proto.getElem!_set!_ite]
    split
    · rename_i hu0; obtain ⟨rfl, -⟩ := hu0
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  have hsh : Shape (fun u => (upd G₁ 0 ((G₁ 0).1, { ph := .j1, wk := w }) u).2) m' := by
    obtain ⟨-, -, hn, -⟩ := hu.shape
    have hX : ∀ u, u ≠ 0 → upd G₁ 0 ((G₁ 0).1, { ph := .j1, wk := w }) u = G₁ u :=
      fun u h => upd_ne _ _ h
    refine ⟨?_, by dsimp only; rw [upd_self]; rfl, fun u hu3 => ?_, .inr (.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
    · rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg (by decide)]
      exact h00
    · dsimp only; rw [hX u (by unfold ThreadId at *; omega)]; exact hn u hu3
    · rw [hth, Array.size_set!, hs3]
    · dsimp only; rw [upd_self]; exact (by decide : 3 ≤ Ph.j1.rank)
    · dsimp only; rw [hX 1 h10]; exact ht1
    · dsimp only; rw [hX 2 (by decide)]; exact ht2
    · rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_pos rfl,
        if_pos (by rw [hs3]; decide)]
      rfl
    · rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg (by decide)]
      exact hr2
  have hU := U_main (x₁ := { ph := .j1, wk := w }) hu (by rw [hm']) (by rw [hm']) (by rw [hm'])
    (fun l => by rw [hm']; rfl) (by rw [hth, Array.size_set!]) (by rw [hm'])
    (Nat.le_of_eq (by rw [hm'])) hclk (congrArg X.e hX0).symm rfl rfl
    (congrArg (fun x : X => x.ph.wa) hX0).symm (congrArg X.wk hX0).symm
    (by rw [hX0]; rfl) hsh (fun _ => by
      obtain ⟨a, b, c, d, f, k⟩ := hu.done (by rw [hX0]; exact (by decide : 6 ≤ Ph.rdd.rank))
      exact ⟨a, b, VClock.le_trans c (hclk 0), VClock.le_trans d (hclk 0),
        fun j hj hs => VClock.le_trans (f j hj hs) (hclk 0), k⟩)
  have hp := U_part (t := 0) (r := rsum rM (L.own G₁ m₁ 1)) hU hcur
    (by rw [upd_self, hg]; exact (by decide : LPh.out ≠ .gone)) (by rw [upd_self, upd_upd, hg]; exact hl)
  rw [upd_self, upd_upd, hg] at hp
  exact h k G₁ m' (rsum rM (L.own G₁ m₁ 1)) hk hcur ⟨rX, hl, hp⟩

/-- **`main`'s join of task 2** at `j1`: then every thread record is `main`'s and joined. -/
theorem wp_join2 {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {rM : Res} {w : Bool}
    (hi : proto.inv (upd G 0 (gO rM { ph := .j1, wk := w })) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k G₁ m', n = k + 1 → BlkOk m' → (∀ b k, m'.freeRaces b k = false) → joinedAll 0 m' →
      Q ((), s) G₁ m' k) :
    proto.WP 0 ((joinC 2 : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.joinC fun k hk => ⟨_, hi, fun G₁ m₁ hg hi₁ => ?_⟩
  obtain ⟨rX, hL, hu⟩ := hi₁
  have hX0 : (G₁ 0).2 = { ph := .j1, wk := w } := by rw [hg]; rfl
  obtain ⟨h00, hs3, hr1, hr2, -, -⟩ :=
    shape3 hu.shape (by rw [hX0]; exact (by decide : 3 ≤ Ph.j1.rank))
  rw [hX0] at hr1
  refine ⟨fun _ => ⟨by show (0 : Nat) < 2; decide, by rw [hs3]; decide, ⟨rfl, .inr rfl, rfl⟩,
    by simp [Thread.joinValid, Mem.isGated, hr2]⟩, fun _ => ⟨fun _ =>
    join_run (m := { m₁ with current := 0 }) hr2 rfl rfl, fun m' hj => ?_⟩⟩
  obtain ⟨rec, hrec, -, hm'⟩ := join_eq hj
  obtain rfl : rec = _ := Option.some.inj (hrec.symm.trans hr2)
  have hcur : m'.current = 0 := by rw [hm']
  have hth : m'.threads = m₁.threads.set! 2 { spawner := 0, joined := true } := by rw [hm']
  have hsz : m'.threads.size = 3 := by rw [hth, Array.size_set!, hs3]
  have hall : ∀ i (hi : i < m'.threads.size),
      m'.threads[i]? = some { spawner := 0, joined := true } := fun i hi => by
    rw [hsz] at hi
    rw [hth, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    rcases lt3 hi with rfl | rfl | rfl
    · rw [if_neg (by decide)]; exact h00
    · rw [if_neg (by decide)]; exact hr1
    · rw [if_pos rfl, if_pos (by rw [hs3]; decide)]
  refine h k G₁ m' hk (by rw [hm']; exact hu.blk) (fun b k' => freeRaces_of_joined ?_
    fun u hu' => .inr ⟨_, hall u hu', hcur.symm, rfl, rfl⟩) fun r hr _ => ?_
  · rw [hm']; show (m₁.clocks.set! 0 _).size = (m₁.threads.set! 2 _).size
    rw [Array.size_set!, Array.size_set!, hL.w.csize]
  · obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
    rw [Option.some.inj ((Array.getElem?_eq_getElem hi').symm.trans (hall i hi'))]

end Threadsync.WG
