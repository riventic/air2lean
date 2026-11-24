import ZigLean.Sep.Full.LockProd

/-!
# The end of two locks

(ledger #two-lock-product, item (5).) The dual of `FLock.Pair.start`
(`ZigLean/Sep/Full/LockProd.lean`): when no thread holds either lock of a two-lock product and one
thread `t` has a clock above every thread's, `t` takes both locks' words and resources back out of
the rest into its part, as `FLock.Inv.take` does for one lock. A program's end is then this lemma
and the end of the protocol's own rest, with no proof of its own.

- `FOwned.takeOwned`: thread `t` takes a resource `rA` of the rest that its clock owns
  (`Mem.OwnsRes`) without gathering a read share; its part is then `P ⋆ Q` for its old part's `P`
  and `rA`'s `Q` (`FOwned.take` with the assertion of the new part).
- `FLock.Facts.ownsFree`: the clock of a thread above every thread's owns the free lock's
  resource and the word's cells (the ownership half of `FLock.Inv.take`, from the lock's facts
  alone, so for either lock of a product).
- `FLock.Pair.stop`: the end of the pair. The protocol's own rest `rX` stays the rest: the locks'
  invariants do not record who accessed its bytes, so `t` takes a piece `rT` of it with
  `FOwned.takeOwned` once the protocol's own invariant gives `m.OwnsRes t rT` (for a shared word's
  cells the word's `Ok`; `FRw.Base.stop`, `ZigLean/Sep/Full/RwProdStop.lean`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- A sum has no shared byte where neither summand has one. -/
theorem Res.shared_rsum_none {a c : Res} {l : Zig.Loc} (ha : a.shared l = none)
    (hc : c.shared l = none) : (rsum a c).shared l = none :=
  Classical.byContradiction fun hn => by
    rcases (Res.owned_sep (r := rsum a c) rfl rfl).mp (Res.owned_of_shared hn) with h | h
    · exact Res.shared_sep (r := rsum a c) rfl rfl hn h ha
    · exact Res.shared_sep' (r := rsum a c) rfl rfl hn h hc

/-- Parts that are all `rnil` compose to `rnil`. -/
theorem sepN_eq_rnil {f : ThreadId → Res} : ∀ {n : Nat} {r : Res}, (∀ u < n, f u = rnil) →
    sepN n (partOf f) r → r = rnil
  | 0, r, _, ⟨h1, k1, g1⟩ => by rw [res_eta r, h1, k1, g1]
  | n + 1, _, hf, ⟨r₁, r₂, _, rfl, h1, h2⟩ => by
    obtain rfl : r₁ = f n := h1
    obtain rfl := sepN_eq_rnil (fun u hu => hf u (Nat.lt_succ_of_lt hu)) h2
    show rsum (f n) rnil = rnil
    rw [rsum_rnil]; exact hf n (Nat.lt_succ_self n)

namespace FOwned

variable {own : ThreadId → Res} {Y : Res} {m : Mem} {t : ThreadId}

/-- **Take a resource the thread's clock owns** (`FOwned.take` with the assertion of the new
part): thread `t`, whose part is `a` with `P`, takes the resource `rA` (with `Q`) of the rest
`rsum rA Y`. Its clock owns `rA` (`hown`), and `a` and `rA` share no byte partially (`hg`; engine
ledger #share-gather). Its new part is `rsum a rA`, with `P ⋆ Q`. -/
theorem takeOwned {P Q : FAssn} {a rA : Res} (ho : FOwned own (rsum rA Y) m)
    (ht : t < m.threads.size) (hat : own t = a) (hdA : FHeap.Disjoint rA.heap Y.heap)
    (hown : m.OwnsRes t rA) (hg : ∀ l, a.shared l = none ∨ rA.shared l = none) (hP : P a)
    (hQ : Q rA) : (P ⋆ Q) (rsum a rA) ∧ FOwned (upd own t (rsum a rA)) Y m := by
  subst hat
  refine ⟨⟨_, _, fun l => ?_, rfl, hP, hQ⟩, ho.take ht hdA ((ho.owns t ht).gather hown hg)⟩
  cases e : rA.heap l with
  | none => exact .inr rfl
  | some _ => exact .inl (ho.part_off ht (by
      show (rA.heap ∪ Y.heap) l ≠ none
      rw [FHeap.union_apply, e]; simp))

end FOwned

namespace FLock

variable {γ : Type} {L : FLock γ} {G : ThreadId → γ} {m : Mem} {rL : Res}

/-- **What the free lock has, the last thread owns** (the ownership half of `Inv.take`): no thread
holds the lock, and thread `t` (not `gone`) has a clock above every thread's. Then its clock owns
the free lock's resource `rL` and the word's cells: each access to them happened before a thread
that has not ended, before a thread (an atomic op at the word), or before the release clock of the
word's newest message, which happened before a thread. -/
theorem Facts.ownsFree {t : ThreadId} (hf : L.Facts G m rL) (hF : L.Free G)
    (ht : t < m.threads.size) (hg : L.ph (G t) ≠ .gone)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true) :
    m.OwnsRes t (rsum rL (L.wordR m)) := by
  obtain ⟨-, hLown⟩ := hf.free hF
  -- what the free lock owns (may read), `t` owns (may read): it is above every thread
  have hlk : ∀ (h : Heap) (w : Bool), L.toLockWord.Owns (L.pl G) m h w →
      LockWord.OwnsW w m (m.clocks[t]!) h := fun h w ho' e he hw htc => by
    rcases ho' e he hw htc with h | ⟨i, l, hl, hle⟩
    · exact h t ht hg
    · obtain ⟨⟨v, hv, hle'⟩, -⟩ := hf.w.rel i l hl
      exact VClock.le_trans hle (VClock.le_trans hle' (hall v hv))
  refine Mem.OwnsRes.gather ⟨LockWord.ownsW_false.mp (hlk _ _ hLown.1),
    LockWord.ownsW_true.mp (hlk _ _ hLown.2)⟩ (.of_owns ?_)
    fun l => .inr ((Res.excl_eq_erase).2 l)
  intro e he htc
  rcases htc with ⟨x, h1, h2, h3⟩ | hb
  · have hin : L.In (e.block, x) := Classical.byContradiction fun hn =>
      h3 (cellsAt_owned_none hn)
    obtain ⟨hb, hx1, hx2⟩ := hin
    rcases hf.w.wfp e he ⟨hb, x, h1, h2, hx1, hx2⟩ with ⟨-, v, hv, hle⟩ | h
    · exact VClock.le_trans hle (hall v hv)
    · exact h t ht hg
  · exact LockWord.ownsW_false.mp (hlk _ _ hLown.1) e he (.inr hb)

end FLock

namespace FLock.Pair

variable {γ : Type} {A B : FLock γ} {G : ThreadId → γ} {m : Mem}

/-- **The end of two locks** (`FLock.Inv.take` for a pair; the dual of `Pair.start`): `A`'s
invariant holds with `B`'s side in its rest (as `Pair.U` stores it) and `B` is kept, no thread
holds `A` or `B`, and thread `t` (out of both locks' code, not `gone`) has a clock above every
thread's. Then `t` takes both words' cells and both resources into its part: its new part `r` is
its old part, `A`'s resource (with `A.R`), `A`'s word's cells, `B`'s resource (with `B.R`) and
`B`'s word's cells, apart from each other.

No read share is gathered: `t`'s part shares no byte partially with `A`'s resource (`hgat`,
`FLock.NoGather`) or with `B`'s (`hgatB`), and the two resources share none with each other
(`hgAB`); a resource without partial shares gives each (`FAssn.Unshared`).

The protocol's own rest `rX` stays the rest. The two invariants order the accesses to the words
and to the locks' resources only, so they do not give `t`'s ownership of a byte of `rX`: `t` takes
a piece `rT` of it with `FOwned.takeOwned`, whose premise `m.OwnsRes t rT` (every access to `rT`'s
exclusive bytes and every write to its shared ones happened before `t`'s clock) comes from the
protocol's own invariant at `rX`. -/
theorem stop {sB rLB rHB rX : Res} {t : ThreadId}
    (hi : A.Inv G (rsum sB rX) m) (hs : Res.Sim sB (side B m rLB rHB))
    (hk : B.Keeps G m rLB rHB rX) (hFA : A.Free G) (hFB : B.Free G)
    (hgA : A.ph (G t) ≠ .gone) (hgB : B.ph (G t) ≠ .gone)
    (hall : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m.clocks[t]!) = true)
    (hgat : A.NoGather G m t)
    (hgatB : ∀ rB, B.R G rB → ∀ l, (A.own G m t).shared l = none ∨ rB.shared l = none)
    (hgAB : ∀ rA rB, A.R G rA → B.R G rB → ∀ l, rA.shared l = none ∨ rB.shared l = none) :
    ∃ r, ((fun r => r = A.own G m t) ⋆ (A.R G ⋆ ((fun r => r = A.wordR m) ⋆
        (B.R G ⋆ fun r => r = B.wordR m)))) r ∧
      FOwned (upd (A.own G m) t r) rX m := by
  -- `B`'s holders hold nothing
  have hH : rHB = rnil := sepN_eq_rnil (fun u _ => by
    unfold FLock.heldOf; split
    · rfl
    · exact hk.facts.idle u (hFB.held u)) hk.held
  subst hH
  have hiS := inv_side hi hs
  obtain ⟨ht, -⟩ := hiS.ht hgA
  obtain ⟨rLA, ⟨hoA, hLoffA, hLXA, -, -⟩, hfA⟩ := hiS.facts
  have hRA := (hfA.free hFA).1
  have hRB := (hk.facts.free hFB).1
  have nsh : ∀ (K : FLock γ) l, (K.wordR m).shared l = none := fun K l =>
    (Res.excl_eq_erase).2 l
  -- `A`'s resource and word
  have hWLA : FHeap.Disjoint (A.wordR m).heap rLA.heap := LockWord.off_disj hLoffA
  have hWXA : FHeap.Disjoint (A.wordR m).heap (rsum (side B m rLB rnil) rX).heap :=
    LockWord.off_disj hiS.xoff
  have e1 : rsum (A.wordR m) (rsum rLA (rsum (side B m rLB rnil) rX)) =
      rsum (rsum rLA (A.wordR m)) (rsum (side B m rLB rnil) rX) := by
    rw [← rsum_assoc, rsum_comm hWLA]
  rw [e1] at hoA
  obtain ⟨hs1, ho1⟩ := hoA.takeOwned (P := fun r => r = A.own G m t)
    (Q := A.R G ⋆ fun r => r = A.wordR m) ht rfl
    (FHeap.disjoint_union_left.mpr ⟨hLXA, hWXA⟩) (hfA.ownsFree hFA ht hgA hall)
    (fun l => (hgat rLA hRA l).imp id fun h => Res.shared_rsum_none h (nsh A l)) rfl
    ⟨rLA, _, hWLA.symm, rfl, hRA, rfl⟩
  -- `B`'s resource and word
  have hWLB : FHeap.Disjoint (B.wordR m).heap rLB.heap := LockWord.off_disj hk.facts.loff
  have e2 : rsum (side B m rLB rnil) rX = rsum (rsum rLB (B.wordR m)) rX := by
    show rsum (rsum (B.wordR m) (rsum rLB rnil)) rX = _
    rw [rsum_rnil, rsum_comm hWLB]
  rw [e2] at ho1
  have hg2 : ∀ l, (rsum (A.own G m t) (rsum rLA (A.wordR m))).shared l = none ∨
      (rsum rLB (B.wordR m)).shared l = none := fun l => by
    by_cases h : rLB.shared l = none
    · exact .inr (Res.shared_rsum_none h (nsh B l))
    · exact .inl (Res.shared_rsum_none ((hgatB rLB hRB l).resolve_right h)
        (Res.shared_rsum_none ((hgAB rLA rLB hRA hRB l).resolve_right h) (nsh A l)))
  obtain ⟨hs2, ho2⟩ := ho1.takeOwned (Q := B.R G ⋆ fun r => r = B.wordR m) ht (upd_self _ _ _)
    (FHeap.disjoint_union_left.mpr ⟨(FHeap.disjoint_union_left.mp hk.xdisj).1,
      LockWord.off_disj hk.xoff⟩)
    (hk.facts.ownsFree hFB ht hgB hall) hg2 hs1 ⟨rLB, _, hWLB.symm, rfl, hRB, rfl⟩
  rw [upd_upd] at ho2
  simp only [sep_assoc_eq] at hs2
  exact ⟨_, hs2, ho2⟩

end FLock.Pair

end Full
end Zig
