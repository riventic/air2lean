import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.AllocSpec.Ops

/-!
# Reclaiming what an allocator lent: shares regrouped, receipts revoked

An allocator with a reset (an arena's `reset`, `docs/sep-full-state.md` §Epoch-tagged shares)
takes back, at once, every extent share it lent: it bumps its ledger's epoch (`Upd.bump`), turns
every receipt of the old epoch back into a share tagged with the ledger's parent (`EUpd.revoke`),
and regroups the shares it then holds on each block into the shares it needs (for example one
share per node, at the node's end, to give each node back to its own allocator). The rules here
are general: lists of shares and receipts (`sharesL`, `rcptsL`), on any blocks and of any tag,
under any ledger, nested or not.

| rule | from | to | side condition |
|---|---|---|---|
| `EUpd.gather` | `sharesL t l` | `bshare b (Σ_b l) (max_b l) t ⋆ sharesL t (l without b)` | an entry on `b` |
| `EUpd.regroup` | `sharesL t src` | `sharesL t dst` | per block equal sums; every target's bound at most the block's highest source bound |
| `EUpd.revokeL` | `gauthP γ e' M p ⋆ rcptsL γ e l` | `gauthP γ e' M p ⋆ sharesL p l` | `e < e'` |
| `EUpd.bumpRevoke` | `gauthP γ e M p ⋆ rcptsL γ e l` | `(gauthP γ (e + 1) GMap.empty p ⋆ epTok γ (e + 1) 1) ⋆ sharesL p l` | |

`regroup` is `gather`, `bshare_split` and `EUpd.weaken`, one target at a time: the fractions on a
block are a sum that can be cut differently, and a joined share certifies the highest bound of its
parts (`EUpd.join`). Shares of different tags never mix.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-- An extent piece: a block, a fraction of its extent and a bound. -/
abbrev Piece := BlockId × Frac × Nat

/-- Shares tagged `t`, one per piece. -/
def sharesL (t : STag) : List Piece → FAssn
  | [] => emp
  | (b, q, k) :: l => bshare b q k t ⋆ sharesL t l

/-- Receipts of ledger `γ`'s epoch `e`, one per piece. -/
def rcptsL (γ e : Nat) : List Piece → FAssn
  | [] => emp
  | (b, q, k) :: l => brcpt b q k γ e ⋆ rcptsL γ e l

/-- The fractions of the pieces on block `b`. -/
def sumOn (b : BlockId) : List Piece → Rat
  | [] => 0
  | x :: l => (if x.1 = b then x.2.1.val else 0) + sumOn b l

/-- The highest bound of the pieces on block `b` (`0` if none). -/
def maxOn (b : BlockId) : List Piece → Nat
  | [] => 0
  | x :: l => if x.1 = b then Max.max x.2.2 (maxOn b l) else maxOn b l

theorem sumOn_nonneg (b : BlockId) : ∀ l : List Piece, 0 ≤ sumOn b l
  | [] => Rat.le_refl
  | x :: l => by
    have := sumOn_nonneg b l; have := x.2.1.nonneg
    simp only [sumOn]; split <;> grind

/-- The pieces on block `b` as one fraction. -/
def fracOn (b : BlockId) (l : List Piece) : Frac := ⟨sumOn b l, sumOn_nonneg b l⟩

theorem sumOn_filter (b : BlockId) (l : List Piece) (c : BlockId) :
    sumOn c (l.filter (·.1 ≠ b)) = if c = b then 0 else sumOn c l := by
  induction l with
  | nil => simp [sumOn]
  | cons x l ih =>
    by_cases hx : x.1 = b <;> by_cases hc : c = b <;> simp_all [sumOn] <;> grind

theorem maxOn_filter (b : BlockId) (l : List Piece) (c : BlockId) (hc : c ≠ b) :
    maxOn c (l.filter (·.1 ≠ b)) = maxOn c l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x.1 = b
    · have : ¬ x.1 = c := fun e => hc (e ▸ hx)
      simp_all [maxOn]
    · simp_all [maxOn]

/-- A list without pieces on `b` has none. -/
theorem sumOn_none {b : BlockId} {l : List Piece} (h : ∀ x ∈ l, x.1 ≠ b) : sumOn b l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp_all [sumOn, Rat.zero_add]

theorem maxOn_none {b : BlockId} {l : List Piece} (h : ∀ x ∈ l, x.1 ≠ b) : maxOn b l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp_all [maxOn]

/-- Positive pieces with no fraction on `b` lie elsewhere. -/
theorem not_on_of_sumOn {b : BlockId} : ∀ {l : List Piece}, (∀ x ∈ l, 0 < x.2.1.val) →
    sumOn b l = 0 → ∀ x ∈ l, x.1 ≠ b
  | [], _, _, _, h => absurd h List.not_mem_nil
  | y :: l, hp, hs, x, hx => by
    have hy := hp y (List.mem_cons_self ..)
    have hl := sumOn_nonneg b l
    have hpl : ∀ z ∈ l, 0 < z.2.1.val := fun z hz => hp z (List.mem_cons_of_mem _ hz)
    simp only [sumOn] at hs
    by_cases hyb : y.1 = b
    · rw [if_pos hyb] at hs; grind
    · rw [if_neg hyb] at hs
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hyb
      · exact not_on_of_sumOn hpl (by grind) x hx

/-- Positive pieces with a fraction on `b` have one there. -/
theorem exists_on_of_sumOn {b : BlockId} {l : List Piece} (h : 0 < sumOn b l) : ∃ x ∈ l, x.1 = b := by
  induction l with
  | nil => simp [sumOn] at h
  | cons y l ih =>
    by_cases hy : y.1 = b
    · exact ⟨y, List.mem_cons_self .., hy⟩
    · simp only [sumOn, if_neg hy] at h
      obtain ⟨x, hx, hxb⟩ := ih (by grind)
      exact ⟨x, List.mem_cons_of_mem _ hx, hxb⟩

theorem sharesL_pos {t : STag} : ∀ {l : List Piece} {r : Res}, sharesL t l r → ∀ x ∈ l, 0 < x.2.1.val
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (b, q, k) :: l, r, h, x, hx => by
    obtain ⟨r₁, r₂, -, -, h1, h2⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1.1
    · exact sharesL_pos h2 x hx

/-- **Gather the shares on one block** into one share of their sum, at their highest bound
(`EUpd.join`); the other pieces stay. -/
theorem EUpd.gather {t : STag} (b : BlockId) : ∀ (l : List Piece), (∃ x ∈ l, x.1 = b) →
    EUpd (sharesL t l) (bshare b (fracOn b l) (maxOn b l) t ⋆ sharesL t (l.filter (·.1 ≠ b)))
  | [], h => by obtain ⟨_, hx, _⟩ := h; cases hx
  | (c, q, k) :: l, h => by
    by_cases hon : ∃ x ∈ l, x.1 = b
    · have ih := EUpd.gather (t := t) b l hon
      by_cases hc : c = b
      · subst hc
        have ef : ((c, q, k) :: l).filter (·.1 ≠ c) = l.filter (·.1 ≠ c) := by simp
        rw [ef]
        refine EUpd.trans (EUpd.frameL (P := sharesL t l) ih) ?_
        refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc' h) ?_
        refine EUpd.trans (EUpd.frame EUpd.join) (EUpd.of_imp fun _ h => ?_)
        refine of_eq ?_ h
        congr 2
        · exact Frac.eq (by simp [fracOn, sumOn, Frac.add])
        · simp [maxOn]
      · have ef : ((c, q, k) :: l).filter (·.1 ≠ b) = (c, q, k) :: l.filter (·.1 ≠ b) := by
          simp [hc]
        rw [ef]
        refine EUpd.trans (EUpd.frameL (P := sharesL t l) ih) (EUpd.of_imp fun _ h => ?_)
        have e1 : fracOn b ((c, q, k) :: l) = fracOn b l := Frac.eq (by simp [fracOn, sumOn, hc, Rat.zero_add])
        have e2 : maxOn b ((c, q, k) :: l) = maxOn b l := by simp [maxOn, hc]
        rw [e1, e2]; simp only [sharesL] at h ⊢; exact of_eq (by ac_rfl) h
    · have hn : ∀ y ∈ l, y.1 ≠ b := fun y hy e => hon ⟨y, hy, e⟩
      have hc : c = b := by
        obtain ⟨x, hx, hxb⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hxb
        · exact absurd hxb (hn x hx)
      subst hc
      have hf : ((c, q, k) :: l).filter (·.1 ≠ c) = l := by
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte]
        exact List.filter_eq_self.mpr fun y hy => by simpa using hn y hy
      rw [hf]
      refine EUpd.of_imp fun _ h => of_eq ?_ h
      simp only [sharesL]
      congr 2
      · exact Frac.eq (by simp [fracOn, sumOn, sumOn_none hn, Rat.add_zero])
      · simp [maxOn, maxOn_none hn]

theorem sumOn_cons_same {b : BlockId} {q : Frac} {k : Nat} {l : List Piece} :
    sumOn b ((b, q, k) :: l) = q.val + sumOn b l := by simp [sumOn]

theorem sumOn_cons_ne {b c : BlockId} {q : Frac} {k : Nat} {l : List Piece} (h : c ≠ b) :
    sumOn c ((b, q, k) :: l) = sumOn c l := by simp [sumOn, Ne.symm h, Rat.zero_add]

theorem maxOn_cons_same {b : BlockId} {q : Frac} {k : Nat} {l : List Piece} :
    maxOn b ((b, q, k) :: l) = Max.max k (maxOn b l) := by simp [maxOn]

theorem maxOn_cons_ne {b c : BlockId} {q : Frac} {k : Nat} {l : List Piece} (h : c ≠ b) :
    maxOn c ((b, q, k) :: l) = maxOn c l := by simp [maxOn, Ne.symm h]

/-- **Regroup shares**: pieces of one tag become any pieces with the same sum on every block,
each at a bound up to the highest bound of the sources on its block. -/
theorem EUpd.regroup {t : STag} : ∀ (dst src : List Piece), (∀ d ∈ dst, 0 < d.2.1.val) →
    (∀ b, sumOn b src = sumOn b dst) → (∀ d ∈ dst, d.2.2 ≤ maxOn d.1 src) →
    EUpd (sharesL t src) (sharesL t dst)
  | [], src, _, hs, _ => fun m r rF hh hp hfs => by
    cases src with
    | nil => exact ⟨r, hh, hp⟩
    | cons x l =>
      have hx := sharesL_pos hp x (List.mem_cons_self ..)
      have h1 := hs x.1
      have := sumOn_nonneg x.1 l
      simp only [sumOn] at h1
      grind
  | (b, q, k) :: dst, src, hpos, hs, hk => fun m r rF hh hp hfs => by
    have hq : 0 < q.val := hpos _ (List.mem_cons_self ..)
    have hdst : ∀ d ∈ dst, 0 < d.2.1.val := fun d hd => hpos d (List.mem_cons_of_mem _ hd)
    have hsb : sumOn b src = q.val + sumOn b dst := by rw [hs b, sumOn_cons_same]
    have hex : ∃ x ∈ src, x.1 = b :=
      exists_on_of_sumOn (by rw [hsb]; have := sumOn_nonneg b dst; grind)
    have hkb : k ≤ maxOn b src := hk _ (List.mem_cons_self ..)
    obtain ⟨r₁, hh₁, hp₁⟩ := EUpd.gather (t := t) b src hex m r rF hh hp hfs
    have hrest : ∀ c, c ≠ b → sumOn c (src.filter (·.1 ≠ b)) = sumOn c dst := fun c hc => by
      rw [sumOn_filter, if_neg hc, hs c, sumOn_cons_ne hc]
    have hkd : ∀ d ∈ dst, d.2.2 ≤ maxOn d.1 src := fun d hd => hk d (List.mem_cons_of_mem _ hd)
    by_cases hz : sumOn b dst = 0
    · -- the whole sum on `b` is the first target's
      have e : fracOn b src = q := Frac.eq (by simp only [fracOn]; rw [hsb, hz]; grind)
      rw [e] at hp₁
      have hnb := not_on_of_sumOn hdst hz
      refine EUpd.trans (EUpd.frame (EUpd.weaken hkb))
        (EUpd.frameL (EUpd.regroup dst (src.filter (·.1 ≠ b)) hdst (fun c => ?_) fun d hd => ?_))
        m r₁ rF hh₁ hp₁ hfs
      · by_cases hc : c = b
        · subst hc; rw [sumOn_filter, if_pos rfl, hz]
        · exact hrest c hc
      · rw [maxOn_filter b src d.1 (hnb d hd)]; exact hkd d hd
    · -- split off the first target, keep the rest on `b` at the highest bound
      have hpos' : 0 < sumOn b dst := by have := sumOn_nonneg b dst; grind
      let q' : Frac := ⟨sumOn b dst, sumOn_nonneg b dst⟩
      have e : fracOn b src = q.add q' := Frac.eq (by simp only [fracOn, Frac.add, q']; exact hsb)
      rw [e] at hp₁
      have hp₂ := sep_mono_left (fun _ x => (bshare_split (k := maxOn b src) hq hpos').mp x) hp₁
      have hp₃ : (bshare b q (maxOn b src) t ⋆
          sharesL t ((b, q', maxOn b src) :: src.filter (·.1 ≠ b))) r₁ := by
        simp only [sharesL]; exact sep_assoc hp₂
      refine EUpd.trans (EUpd.frame (EUpd.weaken hkb))
        (EUpd.frameL (EUpd.regroup dst ((b, q', maxOn b src) :: src.filter (·.1 ≠ b)) hdst
          (fun c => ?_) fun d hd => ?_)) m r₁ rF hh₁ hp₃ hfs
      · by_cases hc : c = b
        · subst hc; rw [sumOn_cons_same, sumOn_filter, if_pos rfl, Rat.add_zero]
        · rw [sumOn_cons_ne hc, hrest c hc]
      · by_cases hdb : d.1 = b
        · rw [hdb, maxOn_cons_same]; have := hkd d hd; rw [hdb] at this; omega
        · rw [maxOn_cons_ne hdb, maxOn_filter b src d.1 hdb]; exact hkd d hd
termination_by dst => dst.length

theorem sharesL_append {t : STag} (l₁ l₂ : List Piece) :
    sharesL t (l₁ ++ l₂) = (sharesL t l₁ ⋆ sharesL t l₂) := by
  induction l₁ with
  | nil => simp only [List.nil_append, sharesL]; exact (emp_sep_eq _).symm
  | cons x l ih =>
    obtain ⟨b, q, k⟩ := x
    simp only [List.cons_append, sharesL, ih]; exact (sep_assoc_eq _ _ _).symm

theorem sumOn_append (b : BlockId) (l₁ l₂ : List Piece) :
    sumOn b (l₁ ++ l₂) = sumOn b l₁ + sumOn b l₂ := by
  induction l₁ with
  | nil => simp [sumOn, Rat.zero_add]
  | cons x l ih => simp only [List.cons_append, sumOn, ih]; grind

/-- A piece's bound is at most the highest bound on its block. -/
theorem le_maxOn {b : BlockId} {q : Frac} {k : Nat} : ∀ {l : List Piece}, (b, q, k) ∈ l → k ≤ maxOn b l
  | x :: l, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [maxOn, if_pos rfl]; exact Nat.le_max_left _ _
    · have := le_maxOn h; simp only [maxOn]; split <;> omega

/-- **Revoke a list of receipts** of a past epoch (`EUpd.revoke`, one at a time). -/
theorem EUpd.revokeL {γ e e' : Nat} {M : GMap} {p : STag} (he : e < e') :
    ∀ l : List Piece, EUpd (gauthP γ e' M p ⋆ rcptsL γ e l) (gauthP γ e' M p ⋆ sharesL p l)
  | [] => EUpd.of_imp fun _ h => h
  | (b, q, k) :: l => by
    simp only [rcptsL, sharesL]
    refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc' h) ?_
    refine EUpd.trans (EUpd.frame (EUpd.revoke he)) ?_
    refine EUpd.trans (EUpd.of_imp (P' := bshare b q k p ⋆ (gauthP γ e' M p ⋆ rcptsL γ e l))
      fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.frameL (EUpd.revokeL he l)) (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h)

/-- **Bump the epoch and revoke its receipts**: the ledger goes to the next epoch with no grant
(`Upd.bump`, which keeps the parent: a nested ledger revokes into its parent's tag), and every
receipt of the old epoch becomes a share tagged with the parent; the new epoch's whole token
comes with it. -/
theorem EUpd.bumpRevoke {γ e : Nat} {M : GMap} {p : STag} (l : List Piece) :
    EUpd (gauthP γ e M p ⋆ rcptsL γ e l)
      ((gauthP γ (e + 1) GMap.empty p ⋆ epTok γ (e + 1) Frac.one) ⋆ sharesL p l) :=
  EUpd.trans (EUpd.frame (EUpd.of_upd Upd.bump)) <|
    EUpd.trans (EUpd.of_imp (P' := epTok γ (e + 1) Frac.one ⋆ (gauthP γ (e + 1) GMap.empty p ⋆ rcptsL γ e l))
      fun _ h => of_eq (by ac_rfl) h) <|
    EUpd.trans (EUpd.frameL (EUpd.revokeL (Nat.lt_succ_self e) l)) (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h)


/-! ## Junk bytes as regions

An allocator keeps bytes it gave up (padding, frees that were not its last allocation) as junk
(`Junk`: some heap, never read again before a reset). One that must hand a whole block part back
(a reset that reuses a node's buffer, or gives the node to its own allocator) tracks *which*
bytes: `JunkAt h` is junk that is exactly the heap `h`, and a coverage fact (`Covers`, every byte
of a range is in `h`) says what it holds. `EUpd.junkRegion` turns covered junk bytes back into a
region with the labels of an owned byte of the same block (the cells of one block share its
address and its kind's normal form, `Holds.block`), which is what a region of the block needs. -/

/-- `P` owns byte `x` of block `b`, whose cell records address `A` and kind `K` (a cell's size
is a label: `docs/sep-full-state.md` §Block extents). -/
def Owns (b x : Nat) (A : Nat) (K : BlockKind) (P : FAssn) : Prop :=
  ∀ r, P r → ∃ fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A ∧ fc.cell.kind = K

/-- A byte owned by a part (`Within`) is owned. -/
theorem Owns.within {b x A K} {X P : FAssn} (h : Owns b x A K X) (hw : Within X P) : Owns b x A K P := by
  intro r hr
  obtain ⟨R, r₁, r₂, -, rfl, h1, -⟩ := hw r hr
  obtain ⟨fc, hx, e⟩ := h r₁ h1
  exact ⟨fc, by show (r₁.heap (b, x)).or _ = _; rw [hx]; rfl, e⟩

/-- Byte `i` of a `regionIn` is owned. -/
theorem Owns.region {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    (hb : p.block = some b) {i : Nat} (hi : i < bs.size) :
    Owns b (p.off.toNat + i) A K (up (regionIn p A S K a bs)) := by
  rintro r ⟨⟨-, -, b', hb', -, hl⟩, -⟩
  rw [hb] at hb'; cases hb'
  have := hl (b, p.off.toNat + i)
  simp only [FHeap.erase] at this
  rw [if_pos (by simp only [true_and]; omega)] at this
  cases e : r.heap (b, p.off.toNat + i) with
  | none => rw [e] at this; cases this
  | some fc =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨fc, rfl, by rw [this], by rw [this]⟩

/-- An owned byte is a live byte of a live block of the memory (at or above its first live
offset), at the cell's address, with the cell's kind up to `BlockKind.norm` (`Holds.block`). -/
theorem Owns.block {b x A K} {P : FAssn} (h : Owns b x A K P) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : P r) : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      x < blk.bytes.size ∧ blk.kind.mappedLo ≤ x ∧ blk.addr = A ∧ blk.kind.norm = K.norm := by
  obtain ⟨fc, hx, rfl, rfl⟩ := h r hp
  obtain ⟨blk, hb, hl, hx', hlo, ha, hk⟩ := hh.block hx
  exact ⟨blk, hb, hl, hx', hlo, ha.symm, hk.symm⟩

/-- Junk that is exactly the heap `h`. -/
def JunkAt (h : Heap) : FAssn := up (fun h' => h' = h)

theorem JunkAt.junk {h : Heap} {r : Res} (hj : JunkAt h r) : Junk r := ⟨h, hj⟩

theorem Junk.junkAt {r : Res} (hj : Junk r) : ∃ h, JunkAt h r := hj

/-- `h` without the bytes `[lo, hi)` of block `b`. -/
def _root_.Zig.Heap.cut (b : BlockId) (lo hi : Nat) (h : Heap) : Heap :=
  fun l => if l.1 = b ∧ lo ≤ l.2 ∧ l.2 < hi then none else h l

/-- **Absorb bytes into junk**: the junk grows by their heap. -/
theorem junkAt_absorb {X : Assn} {h : Heap} {r : Res} (hx : (up X ⋆ JunkAt h) r) :
    ∃ h₁, X h₁ ∧ Heap.Disjoint h₁ h ∧ JunkAt (h₁ ∪ h) r := by
  obtain ⟨r₁, r₂, hd, rfl, ⟨h1, k1, g1⟩, ⟨e2, k2, g2⟩⟩ := hx
  refine ⟨r₁.heap.erase, h1, ?_, ?_, by simp [k1, k2, Know.union_none], by simp [g1, g2]⟩
  · rw [← e2]; exact FHeap.erase_disjoint hd
  · show (FHeap.union r₁.heap r₂.heap).erase = _
    rw [← e2]; exact FHeap.erase_union _ _

/-- `junkAt_absorb` next to a frame `R`. -/
theorem junkAt_absorbR {X : Assn} {h : Heap} {R : FAssn} {r : Res} (hx : ((up X ⋆ JunkAt h) ⋆ R) r) :
    ∃ h₁, X h₁ ∧ (JunkAt (h₁ ∪ h) ⋆ R) r := by
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hx
  obtain ⟨h₁, hX, -, hj⟩ := junkAt_absorb h1
  exact ⟨h₁, hX, r₁, r₂, hd, rfl, hj, h2⟩

/-- A byte of `h₂` is a byte of `h₁ ∪ h₂`. -/
theorem _root_.Zig.Heap.union_ne_none_right {h₁ h₂ : Heap} {l : Loc} (h : h₂ l ≠ none) :
    (h₁ ∪ h₂) l ≠ none := by
  simp only [Heap.union_apply]; cases e : h₁ l <;> simp_all

theorem _root_.Zig.Covers.union_left {b : BlockId} {lo hi : Nat} {h₁ h₂ : Heap} (hc : Zig.Covers b lo hi h₁) :
    Zig.Covers b lo hi (h₁ ∪ h₂) := fun i h1 h2 => by
  have := hc i h1 h2; simp only [Heap.union_apply]; cases e : h₁ (b, i) <;> simp_all

theorem _root_.Zig.Covers.union_right {b : BlockId} {lo hi : Nat} {h₁ h₂ : Heap} (hd : Heap.Disjoint h₁ h₂)
    (hc : Zig.Covers b lo hi h₂) : Zig.Covers b lo hi (h₁ ∪ h₂) := fun i h1 h2 => by
  have := hc i h1 h2; simp only [Heap.union_apply]
  rcases hd (b, i) with e | e <;> simp_all

/-- A region's heap covers its bytes. -/
theorem _root_.Zig.Covers.region {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}
    {h : Heap} (hb : p.block = some b) (hr : regionIn p A S K a bs h) :
    Zig.Covers b p.off.toNat (p.off.toNat + bs.size) h := fun i h1 h2 => by
  obtain ⟨-, -, b', hb', -, hl⟩ := hr
  rw [hb] at hb'; cases hb'
  rw [hl]; simp only [true_and]; rw [if_pos ⟨h1, h2⟩]; simp

/-- A byte of a region is a byte of any heap its heap is joined into. -/
theorem _root_.Zig.Covers.region_union {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {a : Nat}
    {bs : Array Byte} {h h' : Heap} (hb : p.block = some b) (hr : regionIn p A S K a bs h) {x : Nat}
    (h1 : p.off.toNat ≤ x) (h2 : x < p.off.toNat + bs.size) : (h ∪ h') (b, x) ≠ none := by
  have := Zig.Covers.region hb hr x h1 h2
  simp only [Heap.union_apply]; cases e : h (b, x) <;> simp_all

/-- **Covered junk bytes are a region** with the labels `A`, `K` of an owned byte of their block
(any size label `S`): every cell of one block records the block's address and kind up to its
normal form (`Holds.block`), so the junk's cells there are relabelled (`FHeap.Sim`, as
`EUpd.relabel`). The rest stays junk. -/
theorem EUpd.junkRegion {hj : Heap} {R : FAssn} {p : Ptr} {b : BlockId} {n x A S : Nat}
    {K : BlockKind} (hpb : p.block = some b) (hp0 : 0 ≤ p.off) (hK : K ≠ .constGlobal)
    (ho : Owns b x A K R) (hcov : Zig.Covers b p.off.toNat (p.off.toNat + n) hj) :
    EUpd (JunkAt hj ⋆ R) (((FAssn.ex fun bs : Array Byte => ⟪bs.size = n⟫ ⋆
      up (regionIn p A S K 1 bs)) ⋆ JunkAt (hj.cut b p.off.toNat (p.off.toNat + n))) ⋆ R) := by
  intro m r rF hh hp _
  obtain ⟨r₁, r₂, hd, rfl, ⟨he1, k1, g1⟩, hR⟩ := hp
  obtain ⟨fc0, hx0, ha0, hk0⟩ := ho r₂ hR
  have hx0' : (r₁.heap ∪ r₂.heap) (b, x) = some fc0 := by
    rcases hd (b, x) with e | e
    · simp [e, hx0]
    · rw [e] at hx0; cases hx0
  obtain ⟨blk, hblk, -, -, -, hA, hKn⟩ := hh.block hx0'
  let o := p.off.toNat
  let inR : Loc → Prop := fun l => l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + n
  let f : FCell → FCell := fun fc => ⟨⟨fc.cell.byte, A, S, K⟩, fc.atom⟩
  let h₁ : FHeap := fun l => if inR l then (r₁.heap l).map f else r₁.heap l
  let bs : Array Byte := Array.ofFn (n := n) fun i => ((hj (b, o + i)).map (·.byte)).getD default
  have hj_eq : ∀ l, r₁.heap.erase l = hj l := fun l => congrFun he1 l
  -- the junk's cells of the range record the block's address and kind
  have hlab : ∀ l fc, inR l → r₁.heap l = some fc → fc.cell.addr = A ∧ fc.cell.kind.norm = K.norm := by
    intro l fc hl e
    obtain ⟨lb, lx⟩ := l
    obtain ⟨hlb, -, -⟩ := hl
    simp only at hlb; subst hlb
    have e' : (r₁.heap ∪ r₂.heap) (lb, lx) = some fc := by simp [e]
    obtain ⟨blk', hblk', -, -, -, hA', hK'⟩ := hh.block e'
    rw [hblk] at hblk'; cases hblk'
    rw [hk0] at hKn
    exact ⟨by rw [hA', ← hA, ha0], by rw [hK', ← hKn]⟩
  have hd₁ : FHeap.Disjoint h₁ r₂.heap := fun l => by
    rcases hd l with e | e
    · left; simp only [h₁]; split <;> simp [e]
    · right; exact e
  have hsim : FHeap.Sim (h₁ ∪ r₂.heap) (r₁.heap ∪ r₂.heap) := by
    intro l
    simp only [FHeap.union_apply, h₁]
    by_cases hl : inR l
    · rw [if_pos hl]
      cases e : r₁.heap l with
      | none => rfl
      | some fc =>
        obtain ⟨ha, hk⟩ := hlab l fc hl e
        simp only [Option.map_some, Option.some_or, f, Cell.norm, Option.some.injEq, Prod.mk.injEq,
          and_true]
        rw [ha, hk]
    · rw [if_neg hl]
  let rN : Res := ⟨h₁ ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩
  have hhN : Holds m rN rF := (Holds.congrF hh.swap (rF' := rN) hsim rfl rfl).swap
  refine ⟨rN, hhN, ⟨⟨h₁, r₁.know, r₁.gh⟩, r₂, hd₁, rfl, ?_, hR⟩⟩
  -- the relabelled junk: the region and the rest
  have hreg : ∀ l, (⟨h₁, r₁.know, r₁.gh⟩ : Res).heap.erase l =
      ((fun l : Loc => if inR l then some (⟨bs[l.2 - o]!, A, S, K⟩ : Cell) else none) ∪
        hj.cut b o (o + n)) l := by
    intro l
    simp only [FHeap.erase, h₁, Heap.union_apply, Heap.cut]
    by_cases hl : inR l
    · rw [if_pos hl, if_pos hl, if_pos hl]
      obtain ⟨lb, lx⟩ := l
      obtain ⟨rfl, h1, h2⟩ := hl
      have hc := hcov lx h1 h2
      have e := hj_eq (lb, lx)
      cases e1 : r₁.heap (lb, lx) with
      | none => simp only [FHeap.erase, e1, Option.map_none] at e; exact absurd e.symm hc
      | some fc =>
        simp only [FHeap.erase, e1, Option.map_some] at e
        have hi : lx - o < n := by omega
        simp only [Option.map_some, Option.some_or, Option.some.injEq, f, bs, getElem!_def,
          Array.getElem?_ofFn, hi, dite_true, Cell.mk.injEq, and_true]
        rw [show o + (lx - o) = lx by omega, ← e]; rfl
    · rw [if_neg hl, if_neg hl, if_neg hl]; simp only [Option.none_or]; exact hj_eq l
  have hdisj : Heap.Disjoint (fun l : Loc => if inR l then some (⟨bs[l.2 - o]!, A, S, K⟩ : Cell) else none)
      (hj.cut b o (o + n)) := fun l => by
    by_cases hl : inR l
    · right; simp only [Heap.cut]; rw [if_pos hl]
    · left; exact if_neg hl
  have hregion : regionIn p A S K 1 bs
      (fun l : Loc => if inR l then some (⟨bs[l.2 - o]!, A, S, K⟩ : Cell) else none) :=
    ⟨Nat.mod_one _, hK, b, hpb, hp0, fun l => by simp only [inR, bs, Array.size_ofFn]; rfl⟩
  have hup : up (regionIn p A S K 1 bs ∗ fun h' => h' = hj.cut b o (o + n))
      (⟨h₁, r₁.know, r₁.gh⟩ : Res) := ⟨⟨_, _, hdisj, funext hreg, hregion, rfl⟩, k1, g1⟩
  exact sep_mono_left (fun _ y => ⟨bs, sep_lift.mpr ⟨by simp [bs], y⟩⟩) (up_sep hup)

end Full
end Zig
