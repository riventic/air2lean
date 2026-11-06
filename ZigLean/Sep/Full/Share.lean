import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.Ops

/-!
# Shared bytes: loads on a read share, and the whole share as the bytes

(`docs/sep-full-state.md` §Read shares, maintainer decision 2026-11-06 on #637, option A.)

A read share (`Ghost.share`, `SCell`) lets several resources read one byte at once. This module
gives the byte-level assertion and its rules:

* `sbytesAt p A S K bs tg q`: a fraction `q` of each cell that `abytesAt p A S K bs tg` owns
  (the bytes `bs` at `p`, block address `A`, size `S`, kind `K`, atomic tag `tg`); no cell, no
  knowledge, no other ghost state. `spts p a q v` is the typed form, with `0 < q`.
* **Reading**: a positive share reads the memory's cell (`Holds.cellS`, `SMatch.share_cell`),
  so the shared bytes are read in `m` (`Holds.sbytesRead`, `Mem.BytesRead`) and the load rules of
  owned bytes apply unchanged (`FTotalTriple.load_sbytesAt`, `@[fsym]` `FTotalTriple.sload`). A
  store or a free needs the byte exclusively, so no rule changes a byte a share reads.
* **Split and join** of one share's fraction are equalities (`sbytesAt_add`).
* **The whole share is the bytes**: `EUpd.share_whole` turns exclusive bytes into the whole share,
  `EUpd.unshare_whole` back (the same cells, split differently: `SMatch.of_full`).

These rules are sequential (`FTotalTriple`). Several threads that read one byte at once need the
race clocks of a partial share (slice F4).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-- The ghost state with the shares, at fraction `q`, of the cells that `abytesAt` owns at byte
`o` of block `b` (and nothing else). -/
noncomputable def Ghost.sharesAt (b : BlockId) (o A S : Nat) (K : BlockKind) (bs : Array Byte)
    (tg : Option (Nat × Nat)) (q : Frac) : Ghost :=
  { Ghost.unit with share := fun l =>
      if l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + bs.size then SCell.of ⟨⟨bs[l.2 - o]!, A, S, K⟩, tg⟩ q
      else SCell.zero }

/-- **Shared bytes** (module doc): a fraction `q` of each cell of `abytesAt p A S K bs tg`. -/
def sbytesAt (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (tg : Option (Nat × Nat))
    (q : Frac) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ ∃ b, p.block = some b ∧ 0 ≤ p.off ∧
    r.gh = Ghost.sharesAt b p.off.toNat A S K bs tg q

/-- **A shared typed value**: a positive fraction of bytes at `p`, readable with alignment `a`,
that decode to `v`. -/
def spts {T : Type} [Enc T] (p : Ptr) (a : Nat) (q : Frac) (v : T) : FAssn := fun r =>
  0 < q.val ∧ ∃ A S K bs tg, (A + p.off.toNat) % a = 0 ∧ bs.size = Enc.size T ∧
    Enc.decode bs = pure v ∧ sbytesAt p A S K bs tg q r

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)}
  {q : Frac}

/-! ## Reading -/

/-- **Shared bytes are read in `m`** (a positive fraction reads the memory's cell). -/
theorem Holds.sbytesRead {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : sbytesAt p A S K bs tg q r) (hq : 0 < q.val) : m.BytesRead p A S K bs := by
  obtain ⟨-, -, b, hpb, h0, hg⟩ := hp
  refine ⟨b, hpb, h0, fun j hj => ?_⟩
  have hin : (b, p.off.toNat + j).1 = b ∧ p.off.toNat ≤ (b, p.off.toNat + j).2 ∧
      (b, p.off.toNat + j).2 < p.off.toNat + bs.size := ⟨rfl, by simp, by simp; omega⟩
  have hs : r.gh.share (b, p.off.toNat + j) =
      SCell.of ⟨⟨bs[j]!, A, S, K⟩, tg⟩ q := by
    rw [hg]; simp only [Ghost.sharesAt, Nat.add_sub_cancel_left]
    exact if_pos ⟨trivial, hin.2⟩
  obtain ⟨c, hc, hn⟩ := hh.cellS (fc := ⟨⟨bs[j]!, A, S, K⟩, tg⟩)
    (by rw [hs, SCell.of_self]; exact hq)
  exact ⟨c, hc, hn⟩

namespace FTotalTriple

/-- **Load of a `T`** at byte `k` of shared bytes that decode to `v` there: the share stays. -/
theorem load_sbytesAt {T : Type} [Enc T] {v : T} {k al : Nat} (hq : 0 < q.val)
    (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % al = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    FTotalTriple (sbytesAt p A S K bs tg q) (Zig.load T al (p.add k))
      (fun x => ⟪x = v⟫ ⋆ sbytesAt p A S K bs tg q) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, -, -, hx⟩ := Mem.bytes_access (hh.sbytesRead hp hq) hn hk ha
    exact ⟨v, _, r, load_read hacc (by rw [hx]; exact hv)
      (noRace_of_singleThread hs.1.single _ _ _ _), hh.readAt _ _ _ _ _, sep_lift.mpr ⟨rfl, hp⟩,
      hs.readAt _ _ _ _ _⟩

/-- **Load of a shared typed value** (`spts`, `@[fsym]`): the share stays. -/
@[fsym] theorem sload {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (spts p a q v) (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ spts p a q v) :=
  of_cases fun _ ⟨hq, A, S, K, bs, tg, ha, hsz, hv, hb⟩ => by
    have t := load_sbytesAt (p := p) (k := 0) (al := a) (A := A) (S := S) (K := K) (bs := bs)
      (tg := tg) hq hn (by omega) (by simpa using ha)
      (by rw [Nat.zero_add, ← hsz, Array.extract_size]; exact hv)
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, hb, fun v' _ h => by
      obtain ⟨hφ, hb'⟩ := sep_lift.mp h
      exact sep_lift.mpr ⟨hφ, hq, A, S, K, bs, tg, ha, hsz, hv, hb'⟩⟩

end FTotalTriple

/-! ## Split and join -/

theorem Ghost.sharesAt_add (b : BlockId) (o A S : Nat) (K : BlockKind) (bs : Array Byte)
    (tg : Option (Nat × Nat)) (q₁ q₂ : Frac) :
    (Ghost.sharesAt b o A S K bs tg q₁).add (Ghost.sharesAt b o A S K bs tg q₂) =
      Ghost.sharesAt b o A S K bs tg (q₁.add q₂) := by
  ext1
  iterate 4 (· (try funext x) <;> (try funext y) <;> simp [Ghost.add, Ghost.sharesAt, Ghost.unit])
  · funext l
    simp only [Ghost.add_share, Ghost.sharesAt]
    split
    · exact SCell.of_add _ _ _
    · exact SCell.add_zero _

/-- **Split and join are equalities**: `q₁ + q₂` of the bytes is `q₁` of them next to `q₂`. -/
theorem sbytesAt_add {q₁ q₂ : Frac} {r : Res} :
    sbytesAt p A S K bs tg (q₁.add q₂) r ↔
      (sbytesAt p A S K bs tg q₁ ⋆ sbytesAt p A S K bs tg q₂) r := by
  constructor
  · rintro ⟨hh, hk, b, hpb, h0, hg⟩
    refine ⟨⟨FHeap.empty, Know.none, Ghost.sharesAt b p.off.toNat A S K bs tg q₁⟩,
      ⟨FHeap.empty, Know.none, Ghost.sharesAt b p.off.toNat A S K bs tg q₂⟩, fun _ => .inl rfl,
      ?_, ⟨rfl, rfl, b, hpb, h0, rfl⟩, ⟨rfl, rfl, b, hpb, h0, rfl⟩⟩
    obtain ⟨rh, rk, rg⟩ := r
    simp only at hh hk hg
    subst hh hk hg
    rw [FHeap.union_empty, Know.none_union, Ghost.sharesAt_add]
  · rintro ⟨r₁, r₂, -, rfl, ⟨h1, k1, b, hpb, h0, g1⟩, ⟨h2, k2, b', hpb', -, g2⟩⟩
    rw [hpb] at hpb'
    cases hpb'
    refine ⟨?_, ?_, b, hpb, h0, ?_⟩
    · show r₁.heap ∪ r₂.heap = _; rw [h1, h2, FHeap.union_empty]
    · show r₁.know.union r₂.know = _; rw [k1, k2, Know.none_union]
    · show r₁.gh.add r₂.gh = _; rw [g1, g2, Ghost.sharesAt_add]

/-! ## The whole share is the bytes -/

/-- The cells of `abytesAt`, as the share of the whole fraction reads them. -/
theorem sharesAt_one {b : BlockId} {o : Nat} {l : Loc} :
    (Ghost.sharesAt b o A S K bs tg Frac.one).share l =
      if l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + bs.size then SCell.of ⟨⟨bs[l.2 - o]!, A, S, K⟩, tg⟩ Frac.one
      else SCell.zero := rfl

/-- At a byte a resource holds as a cell, the frame holds no share (the cells and the shares are
apart, `SMatch.apart`). -/
theorem Holds.frame_share_zero {m : Mem} {r rF : Res} (hh : Holds m r rF) (hu : r.gh = Ghost.unit)
    {l : Loc} (hl : r.heap l ≠ none) : rF.gh.share l = SCell.zero := by
  have hn : ¬ ((r.gh.add rF.gh).share l).Pos := hh.not_pos_of_heap (by
    simp only [FHeap.union_apply]; intro e; exact hl (Option.or_eq_none_iff.mp e).1)
  rw [Ghost.add_share, hu, Ghost.unit_share, SCell.zero_add, SCell.not_pos_iff] at hn
  exact hn.eq

/-- **Exclusive bytes become the whole share**: the same cells, held as a share. -/
theorem EUpd.share_whole : EUpd (abytesAt p A S K bs tg) (sbytesAt p A S K bs tg Frac.one) := by
  intro m r rF hh hp _
  obtain ⟨hk, hg, b, hpb, h0, hH⟩ := hp
  let In : Loc → Prop := fun l => l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
  let fc : Loc → FCell := fun l => ⟨⟨bs[l.2 - p.off.toNat]!, A, S, K⟩, tg⟩
  have hin : ∀ l, In l → r.heap l = some (fc l) := fun l h => by rw [hH l, if_pos h]
  have hout : ∀ l, ¬ In l → r.heap l = none := fun l h => by rw [hH l, if_neg h]
  have hF0 : ∀ l, In l → rF.gh.share l = SCell.zero := fun l h =>
    hh.frame_share_zero hg (by rw [hin l h]; exact Option.some_ne_none _)
  have hFn : ∀ l, In l → rF.heap l = none := fun l h =>
    (hh.disj l).resolve_left (by rw [hin l h]; exact Option.some_ne_none _)
  have hsh : ∀ l, ((Ghost.sharesAt b p.off.toNat A S K bs tg Frac.one).add rF.gh).share l =
      if In l then SCell.of (fc l) Frac.one else (r.gh.add rF.gh).share l := fun l => by
    rw [Ghost.add_share, sharesAt_one, Ghost.add_share, hg, Ghost.unit_share]
    by_cases h : In l
    · rw [if_pos h, if_pos h, hF0 l h, SCell.add_zero]
    · rw [if_neg h, if_neg h]
  have hcell : ∀ l, In l → SCells (fun l => (SCell.of (fc l) Frac.one)) l = some (fc l) :=
    fun l _ => SCell.cell_eq_some (SCell.valid_of (by decide)) (by rw [SCell.of_self]; decide)
  refine ⟨⟨FHeap.empty, Know.none, Ghost.sharesAt b p.off.toNat A S K bs tg Frac.one⟩,
    ⟨fun _ => .inl rfl, hh.heap.of_full (fun l => ?_) (fun l => ?_) (fun l => ?_),
      Know.sub_none _, hh.knowF, by have hgo := hh.ghost; rw [hg] at hgo; exact hgo⟩, rfl, rfl, b,
      hpb, h0, rfl⟩
  · by_cases h : In l
    · have e : SCells ((Ghost.sharesAt b p.off.toNat A S K bs tg Frac.one).add rF.gh).share l =
          some (fc l) := by
        show (_ : SCell).cell = _; rw [hsh l, if_pos h]; exact hcell l h
      simp only [FHeap.union_apply, e, hin l h, FHeap.empty, Option.none_or, hFn l h,
        Option.some_or]
    · have e : SCells ((Ghost.sharesAt b p.off.toNat A S K bs tg Frac.one).add rF.gh).share l =
          SCells (r.gh.add rF.gh).share l := by
        show (_ : SCell).cell = (_ : SCell).cell; rw [hsh l, if_neg h]
      simp only [FHeap.union_apply, e, hout l h, FHeap.empty, Option.none_or]
  · by_cases h : In l
    · exact .inl (by simp only [FHeap.union_apply, FHeap.empty, Option.none_or, hFn l h])
    · have e : SCells ((Ghost.sharesAt b p.off.toNat A S K bs tg Frac.one).add rF.gh).share l =
          SCells (r.gh.add rF.gh).share l := by
        show (_ : SCell).cell = (_ : SCell).cell; rw [hsh l, if_neg h]
      rcases hh.heap.apart l with e' | e'
      · exact .inl (by
          simp only [FHeap.union_apply, FHeap.empty, Option.none_or] at e' ⊢
          rw [hout l h, Option.none_or] at e'; exact e')
      · exact .inr (by rw [e]; exact e')
  · rw [hsh l]
    by_cases h : In l
    · rw [if_pos h]; exact .inr ⟨fc l, rfl⟩
    · rw [if_neg h]; exact hh.heap.total l

/-- **The whole share becomes the bytes**: next to the whole fraction a valid frame holds none
(`SCell.Valid.whole`), so the cells are exclusive again. -/
theorem EUpd.unshare_whole : EUpd (sbytesAt p A S K bs tg Frac.one) (abytesAt p A S K bs tg) := by
  intro m r rF hh hp _
  obtain ⟨hH, hk, b, hpb, h0, hg⟩ := hp
  let In : Loc → Prop := fun l => l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
  let fc : Loc → FCell := fun l => ⟨⟨bs[l.2 - p.off.toNat]!, A, S, K⟩, tg⟩
  let cells : FHeap := fun l => if In l then some (fc l) else none
  have hs : ∀ l, (r.gh.add rF.gh).share l =
      (if In l then SCell.of (fc l) Frac.one else SCell.zero).add (rF.gh.share l) := fun l => by
    rw [Ghost.add_share, hg]; rfl
  have hF0 : ∀ l, In l → rF.gh.share l = SCell.zero := fun l h => by
    have hv := hh.heap.valid l
    rw [hs l, if_pos h] at hv
    exact (hv.whole (c := fc l) (by rw [SCell.of_self]; rfl)).eq
  have hS : ∀ l, In l → SCells (r.gh.add rF.gh).share l = some (fc l) := fun l h => by
    show (_ : SCell).cell = _
    rw [hs l, if_pos h, hF0 l h, SCell.add_zero]
    exact SCell.cell_eq_some (SCell.valid_of (by decide)) (by rw [SCell.of_self]; decide)
  have hFn : ∀ l, In l → rF.heap l = none := fun l h => by
    have := (hh.heap.apart l).resolve_right (by rw [hS l h]; exact Option.some_ne_none _)
    simp only [FHeap.union_apply, hH, FHeap.empty, Option.none_or] at this; exact this
  have hsh : ∀ l, (Ghost.unit.add rF.gh).share l =
      if In l then SCell.zero else (r.gh.add rF.gh).share l := fun l => by
    rw [Ghost.add_share, Ghost.unit_share, SCell.zero_add, hs l]
    by_cases h : In l
    · rw [if_pos h]; exact hF0 l h
    · rw [if_neg h, if_neg h, SCell.zero_add]
  refine ⟨⟨cells, Know.none, Ghost.unit⟩, ⟨fun l => ?_, hh.heap.of_full (fun l => ?_) (fun l => ?_)
      (fun l => ?_), Know.sub_none _, hh.knowF, by have hgo := hh.ghost; rw [hg] at hgo; exact hgo⟩,
    rfl, rfl, b, hpb, h0, fun l => rfl⟩
  · by_cases h : In l
    · exact .inr (hFn l h)
    · exact .inl (by simp only [cells, if_neg h])
  · by_cases h : In l
    · have e : SCells (Ghost.unit.add rF.gh).share l = none := by
        show (_ : SCell).cell = _; rw [hsh l, if_pos h]; exact SCell.cell_zero
      simp only [FHeap.union_apply, e, cells, if_pos h, hS l h, hH, FHeap.empty, Option.none_or,
        Option.some_or, hFn l h]
    · have e : SCells (Ghost.unit.add rF.gh).share l = SCells (r.gh.add rF.gh).share l := by
        show (_ : SCell).cell = (_ : SCell).cell; rw [hsh l, if_neg h]
      simp only [FHeap.union_apply, e, cells, if_neg h, hH, FHeap.empty, Option.none_or]
  · by_cases h : In l
    · have e : SCells (Ghost.unit.add rF.gh).share l = none := by
        show (_ : SCell).cell = _; rw [hsh l, if_pos h]; exact SCell.cell_zero
      exact .inr e
    · have e : SCells (Ghost.unit.add rF.gh).share l = SCells (r.gh.add rF.gh).share l := by
        show (_ : SCell).cell = (_ : SCell).cell; rw [hsh l, if_neg h]
      rcases hh.heap.apart l with e' | e'
      · exact .inl (by
          simp only [FHeap.union_apply, hH, FHeap.empty, Option.none_or] at e'
          simp only [FHeap.union_apply, cells, if_neg h, Option.none_or]; exact e')
      · exact .inr (by rw [e]; exact e')
  · rw [hsh l]
    by_cases h : In l
    · rw [if_pos h]; exact .inl rfl
    · rw [if_neg h]; exact hh.heap.total l

end Full
end Zig
