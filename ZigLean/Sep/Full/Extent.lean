import ZigLean.Sep.Full.Conc

/-!
# Extent updates (`docs/sep-full-state.md` §Block extents)

A block's extent claims (`bauth`, `bext`, `bshare`, `Res.lean`) change only by **frame-preserving
updates in a memory** (`EUpd P P'`): every resource of `P` that a memory holds with a frame can
be replaced by one of `P'` that the same memory holds with the same frame. Unlike `Upd`
(`Ghost.lean`), an `EUpd` may change extent claims, because it sees the memory that makes them
true. `FTriple.eupd` / `eupd_post` (and the `FTotalTriple`, `CTriple` versions) apply one to a
triple; `EUpd.frame` frames one.

The rules on one block's claims (all general; none is specific to an allocator):

| rule | from | to | side condition |
|---|---|---|---|
| `EUpd.lend` | `bauth b S K (q₁ + q₂)` | `bauth b S K q₁ ⋆ bshare b q₂ k` | `k ≤ S`, `0 < q₂` |
| `EUpd.unlend` | `bauth b S K q₁ ⋆ bshare b q₂ k` | `bauth b S K (q₁ + q₂)` | |
| `bshare_split` | `bshare b (q₁ + q₂) k` | `bshare b q₁ k ⋆ bshare b q₂ k` | `0 < q₁`, `0 < q₂` (an equivalence) |
| `EUpd.join` | `bshare b q₁ k₁ ⋆ bshare b q₂ k₂` | `bshare b (q₁ + q₂) (max k₁ k₂)` | |
| `EUpd.weaken` | `bshare b q k` | `bshare b q k'` | `k' ≤ k` |

Each is an instance of `EUpd.ext1` (`ECell.Step`): a change of the claims `c` on block `b` to `c'` that keeps
the authority claims, does not raise the fraction held below any bound beyond what `c` holds below
some bound (`ECell.total`), and whose every share is covered by a share of `c` at a bound at
least as high or by an authority claim of `c` of a size at least as high. `join` takes the higher
bound because the share at that bound already certifies it: this is what lets an allocator take a
grant's share back into its own share at the buffer's or node's bound.

Facts: `Holds.bshare` (a held share gives a live block of at least `k` bytes), `Holds.bauth` (the
authority gives the exact extent), and `EUpd.fact` (any fact of the memory, as an update).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Fractions -/

namespace Frac

/-- Half of a fraction. -/
def half (q : Frac) : Frac := ⟨q.val / 2, by have := q.nonneg; grind⟩

@[simp] theorem add_val (a b : Frac) : (a.add b).val = a.val + b.val := rfl

theorem half_add_half (q : Frac) : q.half.add q.half = q := eq (by simp only [add, half]; grind)

theorem half_pos {q : Frac} (h : 0 < q.val) : 0 < q.half.val := by simp only [half]; grind

end Frac

/-! ## The claims on one block -/

namespace ECell

/-- The claims `c` on block `b` are true in `m` (the clause of `ExtTrue` for `b`). -/
def TrueIn (m : Mem) (b : BlockId) (c : ECell) : Prop :=
  (∀ (S : Nat) (K : BlockKind), 0 < c.auth (S, K) → ∃ blk : Block, m.blocks[b]? = some blk ∧
      blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K ∧ K.mappedLo < S) ∧
    (∀ k : Nat, 0 < (c.sh k).val → ∃ blk : Block, m.blocks[b]? = some blk ∧ blk.live = true ∧
      k ≤ blk.bytes.size ∧ blk.kind.mappedLo < blk.bytes.size)

theorem total_mono (c : ECell) {n N : Nat} (h : n ≤ N) : c.total n ≤ c.total N := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]; exact Rat.le_refl
  | succ N ih =>
    rcases Nat.lt_or_ge n (N + 1) with hn | hn
    · have := ih (by omega); have := (c.sh N).nonneg; simp only [total]; grind
    · rw [show n = N + 1 by omega]; exact Rat.le_refl

theorem total_auth1 (S : Nat) (K : BlockKind) (q : Frac) :
    ∀ n, (auth1 S K q).total n = if n = 0 then 0 else q.val
  | 0 => rfl
  | n + 1 => by
    rw [total, total_auth1 S K q n]
    simp only [auth1, Frac.zero]
    by_cases hn : n = 0 <;> simp [hn] <;> grind

theorem total_share (q : Frac) (k : Nat) : ∀ n, (share q k).total n = if k < n then q.val else 0
  | 0 => by simp [total]
  | n + 1 => by
    rw [total, total_share q k n]
    simp only [share]
    by_cases h1 : k < n
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; simp only [Frac.zero]; grind
    · by_cases h2 : n = k
      · subst h2; rw [if_neg h1, if_pos rfl, if_pos (by omega)]; grind
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]; simp only [Frac.zero]; grind

/-- **A local step of one block's claims** (module doc): the authority claims stay, the fraction
below every bound is at most what `c` held below some bound, and every share of `c'` is covered by
a share of `c` at a bound at least as high or by an authority claim of `c`. -/
def Step (c c' : ECell) : Prop :=
  c'.auth = c.auth ∧ (∀ n, ∃ N, n ≤ N ∧ c'.total n ≤ c.total N) ∧
    ∀ j, 0 < (c'.sh j).val → (∃ j', j ≤ j' ∧ 0 < (c.sh j').val) ∨ ∃ S K, 0 < c.auth (S, K) ∧ j ≤ S

/-- A step keeps every frame `d` that `c` composed with, validly and truly in `m`. -/
theorem Step.ok {m : Mem} {b : BlockId} {c c' d : ECell} (hst : Step c c') (hv : (c.add d).Valid)
    (ht : (c.add d).TrueIn m b) : (c'.add d).Valid ∧ (c'.add d).TrueIn m b := by
  obtain ⟨hauth, htot, hsh⟩ := hst
  obtain ⟨h1, h2, h3⟩ := hv
  obtain ⟨ta, ts⟩ := ht
  have ea : (c'.add d).auth = (c.add d).auth := by simp only [add, hauth]
  refine ⟨⟨fun x => by rw [ea]; exact h1 x, fun x y hx hy => h2 x y (by rw [← ea]; exact hx)
    (by rw [← ea]; exact hy), fun n => ?_⟩, fun S K hp => ta S K (by rw [← ea]; exact hp),
    fun j hp => ?_⟩
  · obtain ⟨N, hnN, hle⟩ := htot n
    have := h3 N
    rw [total_add] at this ⊢
    have := d.total_mono hnN
    grind
  · simp only [add, Frac.add_val] at hp
    by_cases hd : 0 < (d.sh j).val
    · exact ts j (by simp only [add, Frac.add_val]; have := (c.sh j).nonneg; grind)
    · have hc : 0 < (c'.sh j).val := by have := (d.sh j).nonneg; grind
      rcases hsh j hc with ⟨j', hjj, hj'⟩ | ⟨S, K, hSK, hjS⟩
      · obtain ⟨blk, hb, hl, hs, hlo⟩ := ts j' (by
          simp only [add, Frac.add_val]; have := (d.sh j').nonneg; grind)
        exact ⟨blk, hb, hl, by omega, hlo⟩
      · obtain ⟨blk, hb, hl, hs, hk, hlo⟩ := ta S K (by simp only [add]; omega)
        exact ⟨blk, hb, hl, by omega, by rw [hk, hs]; exact hlo⟩

end ECell

theorem extTrue_iff {m : Mem} {e : BlockId → ECell} : ExtTrue m e ↔ ∀ b, (e b).TrueIn m b := Iff.rfl

/-- Replacing the claims on one block keeps a composition that the change keeps at that block. -/
theorem GOk.ext1 {m : Mem} {b : BlockId} {c c' : ECell} {gF : Ghost}
    (hok : GOk m (Ghost.atExt b c) gF)
    (h : (c.add (gF.extent b)).Valid → (c.add (gF.extent b)).TrueIn m b →
      (c'.add (gF.extent b)).Valid ∧ (c'.add (gF.extent b)).TrueIn m b) :
    GOk m (Ghost.atExt b c') gF := by
  obtain ⟨⟨⟨hv, hx⟩, N, hN⟩, ht⟩ := hok
  have hb := h (by simpa [Ghost.add, Ghost.atExt] using hx b)
    (by simpa [Ghost.add, Ghost.atExt, ECell.TrueIn] using ht b)
  refine ⟨⟨⟨fun γ => by simpa [Ghost.add, Ghost.atExt] using hv γ, fun x => ?_⟩, N,
    fun γ hγ => by simpa [Ghost.add, Ghost.atExt] using hN γ hγ⟩, fun x => ?_⟩
  · by_cases e : x = b
    · subst e; simpa [Ghost.add, Ghost.atExt] using hb.1
    · simpa [Ghost.add, Ghost.atExt, e] using hx x
  · by_cases e : x = b
    · subst e; simpa [Ghost.add, Ghost.atExt, ECell.TrueIn] using hb.2
    · simpa [Ghost.add, Ghost.atExt, e] using ht x

/-! ## Updates in a memory -/

/-- **A frame-preserving update in a memory**: every resource of `P` that `m` holds with a frame
can be replaced by one of `P'` that `m` holds with the same frame. -/
def EUpd (P P' : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq → ∃ r', Holds m r' rF ∧ P' r'

/-- `m` holds `r₁ ⋆ r₂` with frame `rF` if it holds `r₁` with frame `r₂ ⋆ rF` (`Holds.split`
backwards). -/
theorem Holds.join {m : Mem} {r₁ r₂ rF : Res} (hd : FHeap.Disjoint r₁.heap r₂.heap)
    (h2F : FHeap.Disjoint r₂.heap rF.heap)
    (hh : Holds m r₁ ⟨r₂.heap ∪ rF.heap, r₂.know.union rF.know, r₂.gh.add rF.gh⟩) :
    Holds m ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩ rF := by
  obtain ⟨hd', hh', hk', hkF', hg'⟩ := hh
  exact ⟨FHeap.disjoint_union_left.mpr ⟨(FHeap.disjoint_union_right.mp hd').2, h2F⟩,
    by rw [FHeap.union_assoc]; exact hh', hk'.union hkF'.left, hkF'.right, GOk.assoc.mpr hg'⟩

namespace EUpd

variable {P P' P'' R : FAssn}

theorem of_imp (h : ∀ r, P r → P' r) : EUpd P P' := fun _ r _ hh hp _ => ⟨r, hh, h r hp⟩

theorem trans (h₁ : EUpd P P') (h₂ : EUpd P' P'') : EUpd P P'' := fun m r rF hh hp hs => by
  obtain ⟨r₁, hh₁, hp₁⟩ := h₁ m r rF hh hp hs
  exact h₂ m r₁ rF hh₁ hp₁ hs

/-- A ghost update (`Upd`) is an update in every memory: it keeps the extent claims. -/
theorem of_upd (hu : Upd P P') : EUpd P P' := fun m r rF hh hp _ => by
  obtain ⟨r', hp', e, k, x, hg⟩ := hu r hp rF.gh hh.ghost.1
  exact ⟨r', ⟨by rw [e]; exact hh.disj, by rw [e]; exact hh.heap, by rw [k]; exact hh.know,
    hh.knowF, ⟨hg, by have := hh.ghost.2; simpa [Ghost.add, x] using this⟩⟩, hp'⟩

/-- Updates frame. -/
theorem frame (h : EUpd P P') : EUpd (P ⋆ R) (P' ⋆ R) := by
  rintro m _ rF hh ⟨r₁, r₂, hd, rfl, hp, hr⟩ hs
  have h2F := (FHeap.disjoint_union_left.mp hh.disj).2
  obtain ⟨r₁', hh', hp'⟩ := h m r₁ _ (Holds.split hd hh) hp hs
  have hd' := (FHeap.disjoint_union_right.mp hh'.disj).1
  exact ⟨_, Holds.join hd' h2F hh', ⟨r₁', r₂, hd', rfl, hp', hr⟩⟩

theorem frameL (h : EUpd P P') : EUpd (R ⋆ P) (R ⋆ P') :=
  trans (of_imp fun _ h => sep_comm h) (trans (frame h) (of_imp fun _ h => sep_comm h))

/-- A fact of every memory that holds `P`. -/
theorem fact {φ : Prop} (hφ : ∀ m r rF, Holds m r rF → P r → m.FSeq → φ) : EUpd P (⟪φ⟫ ⋆ P) :=
  fun m r rF hh hp hs => ⟨r, hh, sep_lift.mpr ⟨hφ m r rF hh hp hs, hp⟩⟩

/-- **A local update of one block's claims** (`ECell.Step`). -/
theorem ext1 {b : BlockId} {c c' : ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩ ∧
      P' ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩ ∧ ECell.Step c c') : EUpd P P' := by
  intro m r rF hh hr _
  obtain ⟨e, hp', hst⟩ := hp r hr
  subst e
  exact ⟨⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩,
    ⟨hh.disj, hh.heap, hh.know, hh.knowF, GOk.ext1 hh.ghost fun hv ht => hst.ok hv ht⟩, hp'⟩

end EUpd

/-! ## Rules on extent assertions -/

section Rules

variable {b : BlockId} {S k k' : Nat} {K : BlockKind} {q q₁ q₂ : Frac}

theorem bauth_eq {r : Res} (h : bauth b S K q r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.auth1 S K q)⟩ := by
  obtain ⟨h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

theorem bshare_eq {r : Res} (h : bshare b q k r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.share q k)⟩ := by
  obtain ⟨-, h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

/-- Two extent assertions on `b`, as one claim cell. -/
theorem ext_sep_eq {P Q : FAssn} {c c' : ECell} {r : Res}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩)
    (hq : ∀ r, Q r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩) (h : (P ⋆ Q) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (c.add c')⟩ := by
  obtain ⟨r₁, r₂, -, rfl, h1, h2⟩ := h
  rw [hp _ h1, hq _ h2]
  simp [FHeap.union_empty, Know.union_none, Ghost.atExt_add]

theorem ext_sep_intro {P Q : FAssn} {c c' : ECell}
    (hp : P ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩) (hq : Q ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩) :
    (P ⋆ Q) ⟨FHeap.empty, Know.none, Ghost.atExt b (c.add c')⟩ :=
  ⟨_, _, FHeap.disjoint_empty _, by simp [FHeap.union_empty, Know.union_none, Ghost.atExt_add], hp, hq⟩

/-- **Lend a share** off the authority, at a bound `k` up to the block's size. -/
theorem EUpd.lend (hk : k ≤ S) (hq : 0 < q₂.val) :
    EUpd (bauth b S K (q₁.add q₂)) (bauth b S K q₁ ⋆ bshare b q₂ k) := by
  refine EUpd.ext1 fun _ h => ⟨bauth_eq h, ext_sep_intro ⟨rfl, rfl, rfl⟩ ⟨hq, rfl, rfl, rfl⟩,
    by funext x; simp [ECell.add, ECell.auth1, ECell.share], fun n => ⟨n + 1, by omega, ?_⟩,
    fun j hj => .inr ⟨S, K, by simp [ECell.auth1], ?_⟩⟩
  · rw [ECell.total_add, ECell.total_auth1, ECell.total_auth1, ECell.total_share]
    have := q₁.nonneg; have := q₂.nonneg
    simp only [Frac.add_val]; split <;> split <;> grind
  · simp only [ECell.add, ECell.auth1, ECell.share, Frac.add_val, Frac.zero] at hj
    by_cases e : j = 0
    · omega
    · by_cases e' : j = k
      · omega
      · simp only [e, e', if_false] at hj; grind

/-- **Give a share back** to the authority (from any bound). -/
theorem EUpd.unlend : EUpd (bauth b S K q₁ ⋆ bshare b q₂ k) (bauth b S K (q₁.add q₂)) := by
  refine EUpd.ext1 fun _ h => ⟨ext_sep_eq (fun _ h => bauth_eq h) (fun _ h => bshare_eq h) h,
    ⟨rfl, rfl, rfl⟩, by funext x; simp [ECell.add, ECell.auth1, ECell.share],
    fun n => ⟨Max.max n (k + 1), by omega, ?_⟩, fun j hj => .inr ⟨S, K, by simp [ECell.add, ECell.auth1, ECell.share], ?_⟩⟩
  · rw [ECell.total_add, ECell.total_auth1, ECell.total_auth1, ECell.total_share]
    have := q₁.nonneg; have := q₂.nonneg
    simp only [Frac.add_val]
    by_cases hn : n = 0
    · subst hn; simp only [if_pos]; rw [if_neg (by omega), if_pos (by omega)]; grind
    · rw [if_neg hn, if_neg (by omega), if_pos (by omega)]; exact Rat.le_refl
  · simp only [ECell.auth1, Frac.zero] at hj
    by_cases e : j = 0
    · omega
    · simp [e] at hj

/-- **Split and join a share** at one bound. -/
theorem bshare_split {r : Res} (h₁ : 0 < q₁.val) (h₂ : 0 < q₂.val) :
    bshare b (q₁.add q₂) k r ↔ (bshare b q₁ k ⋆ bshare b q₂ k) r := by
  have e : ECell.share (q₁.add q₂) k = (ECell.share q₁ k).add (ECell.share q₂ k) := by
    ext x <;> simp only [ECell.share, ECell.add] <;> split <;> simp
  constructor
  · intro h
    rw [bshare_eq h, e]
    exact ext_sep_intro ⟨h₁, rfl, rfl, rfl⟩ ⟨h₂, rfl, rfl, rfl⟩
  · intro h
    rw [ext_sep_eq (fun _ h => bshare_eq h) (fun _ h => bshare_eq h) h, ← e]
    exact ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩

/-- **Join two shares** at the higher bound: the share there already certifies it. -/
theorem EUpd.join : EUpd (bshare b q₁ k ⋆ bshare b q₂ k') (bshare b (q₁.add q₂) (Max.max k k')) := by
  refine EUpd.ext1 (b := b) (c := (ECell.share q₁ k).add (ECell.share q₂ k'))
    (c' := ECell.share (q₁.add q₂) (Max.max k k')) fun r h => ?_
  have e := ext_sep_eq (fun _ h => bshare_eq h) (fun _ h => bshare_eq h) h
  obtain ⟨r₁, r₂, -, -, ⟨hp1, -⟩, ⟨hp2, -⟩⟩ := h
  have := q₁.nonneg; have := q₂.nonneg
  refine ⟨e, ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩,
    by funext x; simp [ECell.add, ECell.share], fun n => ⟨n, Nat.le_refl _, ?_⟩, fun j hj => ?_⟩
  · rw [ECell.total_add, ECell.total_share, ECell.total_share, ECell.total_share]
    simp only [Frac.add_val]
    by_cases h1 : Max.max k k' < n
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]; exact Rat.le_refl
    · rw [if_neg h1]; split <;> split <;> grind
  · simp only [ECell.share, Frac.zero] at hj
    split at hj
    · rename_i e; subst e
      left
      rcases Nat.le_total k k' with hkk | hkk
      · refine ⟨k', by omega, ?_⟩
        simp only [ECell.add, ECell.share, Frac.add_val, Frac.zero]
        split <;> grind
      · refine ⟨k, by omega, ?_⟩
        simp only [ECell.add, ECell.share, Frac.add_val, Frac.zero]
        split <;> grind
    · simp [Frac.zero] at hj

/-- **Weaken a share's bound.** -/
theorem EUpd.weaken (h : k' ≤ k) : EUpd (bshare b q k) (bshare b q k') := by
  refine EUpd.ext1 fun r hr => ⟨bshare_eq hr, ⟨hr.1, rfl, rfl, rfl⟩, rfl,
    fun n => ⟨Max.max n (k + 1), by omega, ?_⟩, fun j hj => .inl ⟨k, ?_, ?_⟩⟩
  · rw [ECell.total_share, ECell.total_share]
    have := q.nonneg
    split
    · rw [if_pos (by omega)]; exact Rat.le_refl
    · split <;> grind
  · simp only [ECell.share, Frac.zero] at hj; split at hj <;> simp_all [Frac.zero] <;> omega
  · simp only [ECell.share, if_pos]; exact hr.1

/-! ## Facts -/

/-- The claims of a held resource are true. -/
theorem Holds.extTrue {m : Mem} {r rF : Res} (hh : Holds m r rF) : ExtTrue m r.gh.extent :=
  ExtTrue.of_add hh.ghost.2

theorem Holds.claims {m : Mem} {r rF : Res} {P R : FAssn} (hh : Holds m r rF) (h : (P ⋆ R) r) :
    ∃ r₁, P r₁ ∧ ExtTrue m r₁.gh.extent := by
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := h
  exact ⟨r₁, h1, ExtTrue.of_add hh.extTrue⟩

/-- **A held share gives a live block** of at least `k` bytes. -/
theorem Holds.bshare {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF) (h : (bshare b q k ⋆ R) r) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ k ≤ blk.bytes.size ∧
      blk.kind.mappedLo < blk.bytes.size := by
  obtain ⟨r₁, h1, ht⟩ := hh.claims h
  have hq := h1.1
  rw [bshare_eq h1] at ht
  exact (ht b).2 k (by simpa [Ghost.atExt, ECell.share] using hq)

/-- **The authority gives the block's extent.** -/
theorem Holds.bauth {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF) (h : (bauth b S K q ⋆ R) r) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K ∧
      K.mappedLo < S := by
  obtain ⟨r₁, h1, ht⟩ := hh.claims h
  rw [bauth_eq h1] at ht
  exact (ht b).1 S K (by simp [Ghost.atExt, ECell.auth1])

end Rules

/-! ## Triple rules -/

namespace FTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

/-- An update of the precondition. -/
theorem eupd (hu : EUpd P P') (ht : FTriple P' c Q) : FTriple P c Q := fun m r rF hh hp hs => by
  obtain ⟨r', hh', hp'⟩ := hu m r rF hh hp hs
  exact ht m r' rF hh' hp' hs

/-- An update of the postcondition. -/
theorem eupd_post (ht : FTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTriple P c Q' := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hs'⟩ := this
    obtain ⟨r'', hh'', hq'⟩ := hu _ _ r' rF hh' hq hs'
    exact ⟨r'', hh'', hq', hs'⟩

end FTriple

namespace FTotalTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

theorem eupd (hu : EUpd P P') (ht : FTotalTriple P' c Q) : FTotalTriple P c Q :=
  ⟨FTriple.eupd hu ht.1, fun m r rF hh hp hs => by
    obtain ⟨r', hh', hp'⟩ := hu m r rF hh hp hs
    exact ht.2 m r' rF hh' hp' hs⟩

theorem eupd_post (ht : FTotalTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTotalTriple P c Q' :=
  ⟨FTriple.eupd_post ht.1 hu, ht.2⟩

end FTotalTriple

namespace CTriple

variable {Tgt α : Type} {P P' : FAssn} {x : ConcM Tgt α} {Q Q' : α → FAssn}

theorem eupd (hu : EUpd P P') (ht : CTriple P' x Q) : CTriple P x Q := fun n => FTriple.eupd hu (ht n)

theorem eupd_post (ht : CTriple P x Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : CTriple P x Q' :=
  fun n => FTriple.eupd_post (ht n) hu

end CTriple

end Full
end Zig
