import ZigLean.Sep.Full.LockProd

/-!
# The two-lock product over a spawn

(ledger #two-lock-product, item (5).) A spawn by `t` (`Thread.forkWith`) adds a thread record,
forks the new thread's clock from `t`'s and makes `t` the current thread; `t` gives the new thread a
part of its part, and the new thread starts out of every lock's code. `FLock.Inv.fork`
(`ZigLean/Sep/Full/Lock.lean`) keeps one lock's invariant over it. This file keeps the two-lock
product (`ZigLean/Sep/Full/LockProd.lean`), once for every pair of locks and every client:

- `FLock.Keeps.fork`: what the product keeps of the other lock `B` (`FLock.Keeps`), at the same
  free and holders' resources, and `B`'s side is the same (`FLock.side`). `t` is out of `B`'s code,
  and so are its new ghost value and the new thread's, holding nothing; `B`'s resource is kept
  (`hRk`, as `FLock.Inv.fork`'s).
- `FLock.Pair.U_fork`: the product's rest for `A` (`FLock.Pair.U`), when the client's own `U` is
  kept (`hcl`, the shape of the other `Pair` builders' premise: `U_relabel`, `U_stable`).
- `FLock.Pair.fork`: `A`'s invariant and the product's rest together, the invariant of a protocol
  with two locks after the spawn (`FLock.Inv.fork` for `A`).

The memory-level fact of the spawn is the one `FLock.Inv.fork` takes: the run of
`Thread.forkWith gt` at `{ m with current := t }`.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {B : FLock γ} {G : ThreadId → γ} {m m' : Mem}

/-- **A spawn keeps what the product keeps of `B`** (module doc), at the same free resource `rL`
and holders' resources `rH`, and `B`'s side is the same: the new thread holds nothing of `B`, the
holders' clocks grow, and `B`'s word stays (`LockWord.WInv.fork`). -/
theorem Keeps.fork {rL rH rX : Res} {t c : ThreadId} {g₁ g₀ : γ} {gt : Bool}
    (hk : B.Keeps G m rL rH rX) (hout : B.ph (G t) = .out)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (h₁ : B.ph g₁ = .out) (h₁h : B.held g₁ = rnil)
    (h₀ : B.ph g₀ = .out) (h₀h : B.held g₀ = rnil)
    (hRk : ∀ r, B.R G r → B.R (upd (upd G c g₀) t g₁) r) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps (upd (upd G c g₀) t g₁) m' rL rH rX := by
  have hfa := hk.facts
  obtain ⟨ht, hjt⟩ := hfa.w.live t (by show B.ph (G t) ≠ .gone; rw [hout]; decide)
  have hcs := hfa.w.csize
  have hheldt : B.held (G t) = rnil := hfa.idle t (by rw [hout]; rfl)
  have hjb := joinedB_fork hf
  obtain ⟨-, hw, hown⟩ := hfa.w.fork (gt := gt) (by exact hout) hf
  have hownR : ∀ u, u < m.threads.size → m'.OwnsRes u (B.heldOf G m u) :=
    fun u hu => (hk.owns u hu).fork hcs hu hf
  have hownC : m'.OwnsRes c (B.heldOf G m t) := (hk.owns t ht).fork_child hcs hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have hct : m.threads.size ≠ t := fun h => by rw [h] at ht; exact Nat.lt_irrefl _ ht
  have hGc : B.ph (G m.threads.size) = .gone := by
    cases hx : B.ph (G m.threads.size) <;> first | rfl |
      exact absurd (hfa.w.live _ (by simp only [pl]; rw [hx]; decide)).1 (Nat.lt_irrefl _)
  have hpl : B.pl (upd (upd G m.threads.size g₀) t g₁) = upd (B.pl G) m.threads.size .out := by
    funext u; simp only [pl, upd]
    by_cases h1 : u = t
    · simp [h1, h₁, hout, Ne.symm hct]
    · by_cases h2 : u = m.threads.size
      · simp [h1, h2, h₀, hct]
      · simp [h1, h2]
  have hphu : ∀ u, (B.ph (upd (upd G m.threads.size g₀) t g₁ u)).held = true ↔
      (B.ph (G u)).held = true := by
    intro u
    have := congrFun hpl u; simp only [pl] at this; rw [this, LockWord.upd_apply]
    split
    · rename_i h; subst h; rw [hGc]; decide
    · exact Iff.rfl
  have hfree := free_iff_of (L := B) hphu
  have hheldG : ∀ u, B.held (upd (upd G m.threads.size g₀) t g₁ u) = B.held (G u) := fun u => by
    by_cases h1 : u = t
    · rw [h1, upd_self, h₁h, hheldt]
    · rw [upd_ne _ _ h1]
      by_cases h2 : u = m.threads.size
      · rw [h2, upd_self, h₀h, hfa.held_out (Nat.le_refl _)]
      · rw [upd_ne _ _ h2]
  have hheldOf : B.heldOf (upd (upd G m.threads.size g₀) t g₁) { m with
      current := t,
      clocks := (m.clocks.set! t (VClock.bump (m.clocks[t]!) t)).push (VClock.bump (m.clocks[t]!) t),
      threads := m.threads.push { spawner := t, joined := false, gated := gt } } =
      B.heldOf G m := funext fun u => by
    unfold heldOf; rw [hjb, hheldG u]
  have hNew : B.heldOf G m m.threads.size = rnil := by
    unfold heldOf; rw [joinedB_out (Nat.le_refl _), hfa.held_out (Nat.le_refl _)]; rfl
  have hPar : B.heldOf G m t = rnil := by
    unfold heldOf; rw [hjt, hheldt]; rfl
  refine ⟨by rw [side, side, FLock.wordR_congr (L := B) (m := m) rfl],
    ⟨by rw [hpl]; exact hw, hfa.loff, fun hF' => ?_,
      fun h => hfa.busy (fun h' => h (hfree.mpr h')), fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩,
    ?_, fun u hu => ?_, hk.hoff, hk.xdisj, hk.xoff⟩
  · obtain ⟨h1, h2⟩ := hfa.free (hfree.mp hF')
    exact ⟨hRk rL h1, by rw [hpl]; exact ⟨hown _ _ h2.1, hown _ _ h2.2⟩⟩
  · by_cases h1 : u = t
    · rw [hheldG u, h1, hheldt]; exact FHeap.disjoint_empty _
    · by_cases h2 : u = m.threads.size
      · rw [hheldG u, h2, hfa.held_out (Nat.le_refl _)]; exact FHeap.disjoint_empty _
      · rw [upd_ne _ _ h1, upd_ne _ _ h2]; exact hfa.pdisj u
  · rw [hheldG u]; exact hfa.idle u (held_false_of_iff (hphu u) hu)
  · rw [hphu] at hu
    rw [hheldG u]; exact hRk _ (hfa.res u hu)
  · rw [hheldOf]
    show sepN (m.threads.push _).size (partOf (B.heldOf G m)) rH
    rw [Array.size_push]
    exact ⟨rnil, rH, fun _ => .inl rfl, (rnil_rsum rH).symm, hNew.symm, hk.held⟩
  · rw [hheldOf]
    have hu' : u < m.threads.size + 1 := by simpa only [Array.size_push] using hu
    by_cases h1 : u < m.threads.size
    · exact hownR u h1
    · obtain rfl : u = m.threads.size := by omega
      rw [hNew]; rw [hPar] at hownC; exact hownC

namespace Pair

variable {A : FLock γ}

/-- **A spawn keeps the product's rest for `A`** (module doc), when the client's own `U` is kept
(`hcl`: it gets what the product has, `B`'s side and `B` kept before and after the spawn). -/
theorem U_fork {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res} {t c : ThreadId} {g₁ g₀ : γ}
    {gt : Bool} (hU : Pair.U B U G rXA m) (hout : B.ph (G t) = .out)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (h₁ : B.ph g₁ = .out) (h₁h : B.held g₁ = rnil)
    (h₀ : B.ph g₀ = .out) (h₀h : B.held g₀ = rnil)
    (hRk : ∀ r, B.R G r → B.R (upd (upd G c g₀) t g₁) r)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → B.Keeps (upd (upd G c g₀) t g₁) m' rL rH rX → U G rX m →
      U (upd (upd G c g₀) t g₁) rX m') :
    Pair.U B U (upd (upd G c g₀) t g₁) rXA m' := by
  obtain ⟨sB, rL, rH, rX, rfl, hs, hk, hu⟩ := hU
  obtain ⟨he, hk'⟩ := hk.fork hout hf h₁ h₁h h₀ h₀h hRk
  exact ⟨sB, rL, rH, rX, rfl, by rw [he]; exact hs, hk', hcl sB rL rH rX rfl hs hk hk' hu⟩

/-- **A spawn keeps the invariant of a protocol with two locks** (module doc): `A`'s invariant
(`FLock.Inv.fork`) and the product's rest for `A` (`U_fork`). `t` is out of both locks' code; it
keeps `part g₁` and the new thread gets `part g₀` (the two locks have one part, `FLock.Pair.part`,
so the split is stated at `A`), both out of both locks' code and holding nothing; both locks'
resources are kept (`hRA`, `hRB`), and the client's own `U` (`hcl`). -/
theorem fork {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res} {t c : ThreadId} {g₁ g₀ : γ}
    {gt : Bool} (hi : A.Inv G rXA m) (hU : Pair.U B U G rXA m)
    (houtA : A.ph (G t) = .out) (houtB : B.ph (G t) = .out)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m')))
    (hsplit : A.part (G t) = rsum (A.part g₁) (A.part g₀))
    (hd : FHeap.Disjoint (A.part g₁).heap (A.part g₀).heap)
    (hA₁ : A.ph g₁ = .out) (hA₁h : A.held g₁ = rnil)
    (hA₀ : A.ph g₀ = .out) (hA₀h : A.held g₀ = rnil)
    (hB₁ : B.ph g₁ = .out) (hB₁h : B.held g₁ = rnil)
    (hB₀ : B.ph g₀ = .out) (hB₀h : B.held g₀ = rnil)
    (hRA : ∀ r, A.R G r → A.R (upd (upd G c g₀) t g₁) r)
    (hRB : ∀ r, B.R G r → B.R (upd (upd G c g₀) t g₁) r)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → B.Keeps (upd (upd G c g₀) t g₁) m' rL rH rX → U G rX m →
      U (upd (upd G c g₀) t g₁) rX m') :
    A.Inv (upd (upd G c g₀) t g₁) rXA m' ∧ Pair.U B U (upd (upd G c g₀) t g₁) rXA m' :=
  ⟨hi.fork houtA hf hsplit hd hA₁ hA₁h hA₀ hA₀h hRA,
    U_fork hU houtB hf hB₁ hB₁h hB₀ hB₀h hRB hcl⟩

end Pair

end FLock

end Full
end Zig
