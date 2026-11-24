import ZigLean.Sep.Full.LockProd

/-!
# The two-lock product over a thread's end and a join

(ledger #two-lock-product, item (5).) A protocol's invariant is kept when a thread that is out of
every lock's code ends (its ghost value goes to `gone` and keeps its part for the joiner; the
memory stays), and when a thread joins an ended one (the memory marks it joined, the joiner's clock
takes the ended thread's, and the joiner's part takes the ended thread's). For one lock these are
`FLock.Inv.ghost` and `FLock.Inv.join`. This file gives them for the lock the product keeps in the
other lock's view, and for the product.

- `FLock.Keeps.ghost`, `Keeps.join`: what the product keeps of `B` (`FLock.Facts.ghost`,
  `Facts.join`, `ZigLean/Sep/Full/LockProd.lean`). No thread that ends or joins holds `B`, so the
  holders' resources and their owners' clocks stay (`Mem.OwnsRes.join_other`), and a join keeps
  the blocks, so `B`'s side stays (`joinedB_join`, `ZigLean/Sep/Full/LockWord.lean`).
- `FLock.Pair.U_ghost`, `U_join`: the product's rest, when the client's own `U` is kept.
- `FLock.Pair.inv_ghost`, `inv_join`: `A`'s invariant with the product's rest, over each.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {B : FLock γ} {G : ThreadId → γ} {m : Mem} {rL rH rX : Res}

/-- **The end of thread `t`, which is out of `B`'s code, keeps what the product keeps of `B`**
(`Facts.ghost`): `t` held nothing of `B`, so the holders' resources stay. -/
theorem Keeps.ghost {t : ThreadId} {g : γ} (hk : B.Keeps G m rL rH rX) (hph : B.ph (G t) = .out)
    (hg : B.ph g = .out ∨ B.ph g = .gone ∨ B.ph g = .away) (hheld : B.held g = rnil)
    (hRk : ∀ r, B.R G r → B.R (upd G t g) r) : B.Keeps (upd G t g) m rL rH rX := by
  have hht : B.held (G t) = rnil := hk.facts.idle t (by rw [hph]; rfl)
  have he : B.heldOf (upd G t g) m = B.heldOf G m := funext fun w => by
    unfold heldOf
    by_cases e : w = t
    · rw [e, upd_self, hheld, hht]
    · rw [upd_ne _ _ e]
  exact ⟨hk.facts.ghost hph hg hheld hRk, by rw [he]; exact hk.held, by rw [he]; exact hk.owns,
    hk.hoff, hk.xdisj, hk.xoff⟩

/-- **A join of `u` by `t`, both out of `B`'s code, keeps what the product keeps of `B`**
(`Facts.join`), at the same side: neither holds a resource of `B`, every other thread's clock
still owns what it holds (`Mem.OwnsRes.join_other`), and the blocks stay. -/
theorem Keeps.join {m' : Mem} {t u : ThreadId} {g : γ} (hk : B.Keeps G m rL rH rX) (hut : u ≠ t)
    (hu0 : u ≠ 0) (hout : B.ph (G t) = .out) (huo : B.ph (G u) = .gone)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hgo : B.ph g = .out) (hgh : B.held g = rnil) (hRk : ∀ r, B.R G r → B.R (upd G t g) r) :
    side B m' rL rH = side B m rL rH ∧ B.Keeps (upd G t g) m' rL rH rX := by
  have hf := hk.facts
  obtain ⟨ht, -⟩ := hf.w.live t (by show B.ph (G t) ≠ .gone; rw [hout]; decide)
  have hht : B.held (G t) = rnil := hf.idle t (by rw [hout]; rfl)
  have hhu : B.held (G u) = rnil := hf.idle u (by rw [huo]; rfl)
  have hjb := joinedB_join hu0 hj
  obtain ⟨rec, hr, -, hm⟩ := Proto.join_eq hj
  have hul : u < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
  have hsz : m'.threads.size = m.threads.size := by rw [hm]; simp
  have hblk : m'.blocks = m.blocks := by rw [hm]
  have he : B.heldOf (upd G t g) m' = B.heldOf G m := funext fun w => by
    unfold heldOf
    by_cases e : w = t
    · rw [e, upd_self, hgh, hht]; simp only [ite_self]
    · rw [upd_ne _ _ e]
      by_cases e' : w = u
      · rw [e', hhu]; simp only [ite_self]
      · rw [hjb, ite_eq_right e']
  have e1 : B.heldOf G m t = rnil := by unfold heldOf; rw [hht]; simp only [ite_self]
  have e2 : B.heldOf G m u = rnil := by unfold heldOf; rw [hhu]; simp only [ite_self]
  refine ⟨by unfold side; rw [wordR_congr (L := B) hblk],
    hf.join hut hu0 hout huo hj hgo hgh hRk, by rw [he, hsz]; exact hk.held, fun w hw => ?_,
    hk.hoff, hk.xdisj, hk.xoff⟩
  rw [he]
  by_cases e : w = t
  · have h1 := hk.owns t ht
    have h2 := hk.owns u hul
    rw [e1] at h1; rw [e2] at h2
    have h := h1.join h2 (by rw [hf.w.csize]; exact ht) hj fun l =>
      .inl (FAssn.Unshared.emp _ ⟨rfl, rfl, rfl⟩ l)
    rw [rsum_rnil] at h
    rw [e, e1]; exact h
  · exact (hk.owns w (hsz ▸ hw)).join_other e hj

end FLock

namespace FLock.Pair

variable {γ : Type} {A B : FLock γ} {G : ThreadId → γ} {m : Mem}
  {U : (ThreadId → γ) → Res → Mem → Prop} {rXA : Res}

/-- **The end of thread `t`, which is out of `B`'s code, keeps the product's rest**
(`Keeps.ghost`), when the protocol's own `U` is kept (`hcl`, with `B` kept before and after). -/
theorem U_ghost {t : ThreadId} {g : γ} (hU : Pair.U B U G rXA m) (hph : B.ph (G t) = .out)
    (hg : B.ph g = .out ∨ B.ph g = .gone ∨ B.ph g = .away) (hheld : B.held g = rnil)
    (hRk : ∀ r, B.R G r → B.R (upd G t g) r)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → B.Keeps (upd G t g) m rL rH rX → U G rX m → U (upd G t g) rX m) :
    Pair.U B U (upd G t g) rXA m := by
  obtain ⟨sB, rL, rH, rX, rfl, hs, hk, hu⟩ := hU
  have hk' := hk.ghost hph hg hheld hRk
  exact ⟨sB, rL, rH, rX, rfl, hs, hk', hcl sB rL rH rX rfl hs hk hk' hu⟩

/-- **A join of `u` by `t`, both out of `B`'s code, keeps the product's rest** (`Keeps.join`),
when the protocol's own `U` is kept (`hcl`, with `B` kept before and after). -/
theorem U_join {m' : Mem} {t u : ThreadId} {g : γ} (hU : Pair.U B U G rXA m) (hut : u ≠ t)
    (hu0 : u ≠ 0) (hout : B.ph (G t) = .out) (huo : B.ph (G u) = .gone)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hgo : B.ph g = .out) (hgh : B.held g = rnil) (hRk : ∀ r, B.R G r → B.R (upd G t g) r)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → B.Keeps (upd G t g) m' rL rH rX → U G rX m →
      U (upd G t g) rX m') :
    Pair.U B U (upd G t g) rXA m' := by
  obtain ⟨sB, rL, rH, rX, rfl, hs, hk, hu⟩ := hU
  obtain ⟨he, hk'⟩ := hk.join hut hu0 hout huo hj hgo hgh hRk
  exact ⟨sB, rL, rH, rX, rfl, by rw [he]; exact hs, hk', hcl sB rL rH rX rfl hs hk hk' hu⟩

/-- **The product over the end of thread `t`**, which is out of both locks' code
(`FLock.Inv.ghost` at `A`, `U_ghost`): at each lock it is `out`, `gone` or `away` after and holds
nothing, and it keeps its part; both locks' resources stay (`hRA`, `hRB`), and the protocol's own
`U` is kept (`hcl`). -/
theorem inv_ghost {t : ThreadId} {g : γ} (hi : A.Inv G rXA m) (hU : Pair.U B U G rXA m)
    (hA : A.ph (G t) = .out) (hgA : A.ph g = .out ∨ A.ph g = .gone ∨ A.ph g = .away)
    (hpart : A.part g = A.part (G t)) (hhA : A.held g = rnil)
    (hRA : ∀ r, A.R G r → A.R (upd G t g) r)
    (hB : B.ph (G t) = .out) (hgB : B.ph g = .out ∨ B.ph g = .gone ∨ B.ph g = .away)
    (hhB : B.held g = rnil) (hRB : ∀ r, B.R G r → B.R (upd G t g) r)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → B.Keeps (upd G t g) m rL rH rX → U G rX m → U (upd G t g) rX m) :
    A.Inv (upd G t g) rXA m ∧ Pair.U B U (upd G t g) rXA m :=
  ⟨hi.ghost hA hgA hpart hhA (fun _ => hi.ht (by rw [hA]; decide)) hRA,
    U_ghost hU hB hgB hhB hRB hcl⟩

/-- **The product over a join of `u` by `t`**, both out of both locks' code (`FLock.Inv.join` at
`A`, `U_join`): the joiner takes the ended thread's part and gathers no read share (`hgat`), both
locks' resources stay (`hRA`, `hRB`), and the protocol's own `U` is kept (`hcl`). -/
theorem inv_join {m' : Mem} {t u : ThreadId} {g : γ} (hi : A.Inv G rXA m)
    (hU : Pair.U B U G rXA m) (hut : u ≠ t) (hu0 : u ≠ 0)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hA : A.ph (G t) = .out) (huA : A.ph (G u) = .gone)
    (hpart : A.part g = rsum (A.part (G t)) (A.own G m u)) (hgA : A.ph g = .out)
    (hhA : A.held g = rnil) (hRA : ∀ r, A.R G r → A.R (upd G t g) r)
    (hB : B.ph (G t) = .out) (huB : B.ph (G u) = .gone) (hgB : B.ph g = .out)
    (hhB : B.held g = rnil) (hRB : ∀ r, B.R G r → B.R (upd G t g) r)
    (hgat : ∀ l, (A.own G m t).shared l = none ∨ (A.own G m u).shared l = none)
    (hcl : ∀ sB rL rH rX, rXA = rsum sB rX → Res.Sim sB (side B m rL rH) →
      B.Keeps G m rL rH rX → B.Keeps (upd G t g) m' rL rH rX → U G rX m →
      U (upd G t g) rX m') :
    A.Inv (upd G t g) rXA m' ∧ Pair.U B U (upd G t g) rXA m' :=
  ⟨hi.join hut hu0 hA huA hj hpart hgA hhA hRA hgat,
    U_join hU hut hu0 hB huB hj hgB hhB hRB hcl⟩

end FLock.Pair

end Full
end Zig
