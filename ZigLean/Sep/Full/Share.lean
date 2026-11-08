import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.ThreadStep

/-!
# Shared resources: a fraction of an exclusive heap, loads on it, and the whole share

(`docs/sep-full-state.md` §Read shares, maintainer decision 2026-11-06 on #637, option A.)

A read share (`Ghost.share`, `SCell`) lets several resources read one byte at once. This module
states the share once, for every exclusive heap, and derives the byte and typed forms from it:

* `sheap H q`: the fraction `q` of each cell of the heap `H`, held as a share (no cell, no
  knowledge, no other ghost state). `shared P q`: `q` of a heap of the exclusive assertion `P`.
  `sbytesAt p A S K bs q := shared (up (bytesAt p A S K bs)) q` (each cell with its own tag) and
  `spts p a q v` (a positive `q` of `up (pts p a v)`) are instances.
* **The whole share is the heap**: `Holds.toShares` / `Holds.ofShares` move the cells of `H`
  between the exclusive heap and the whole share (the same cells, split differently:
  `SMatch.of_full`); `EUpd.share_whole` / `EUpd.unshare_whole` lift that to any `P` without
  knowledge or ghost state, so `up (pts p a v)` converts to `spts p a 1 v` and back.
* **Split and join**: `sheap_add` is an equality; `shared_split` splits any `P`, and
  `EUpd.shared_join` joins two positive shares of a `P` whose heaps have one domain
  (`FAssn.FixedDom`: then the two heaps agree, since shares of different cells of one byte do not
  compose).
* **Reading**: a positive share reads the memory's cell (`Holds.cellS`), so shared bytes are read
  in `m` (`Holds.sbytesRead`) and the generic load rule applies (`FTotalTriple.load_of_read`,
  `load_sbytesAt`, `@[fsym]` `sload`). A store or a free needs the byte exclusively, so no rule
  changes a byte a share reads.

These rules are sequential (`FTotalTriple`). In a thread a typed share load is local
(`ThreadLocal.sload`, slice F4: several threads may read one byte at once, `Mem.OwnsR`), so `fsym`
applies `sload` there too.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig
namespace Full

open FAssn

/-- The ghost state holding the fraction `q` of each cell of `H` as a share (and nothing else). -/
noncomputable def Ghost.sharesOf (H : FHeap) (q : Frac) : Ghost :=
  { Ghost.unit with share := fun l => (H l).elim SCell.zero (SCell.of · q) }

/-- **The share `q` of the heap `H`** (module doc). -/
def sheap (H : FHeap) (q : Frac) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.sharesOf H q

/-- The share `q` of the heap `H`, as a resource: the one resource of `sheap H q`. -/
noncomputable def shareRes (H : FHeap) (q : Frac) : Res :=
  ⟨FHeap.empty, Know.none, Ghost.sharesOf H q⟩

theorem shareRes_sheap (H : FHeap) (q : Frac) : sheap H q (shareRes H q) :=
  ⟨rfl, rfl, rfl⟩

/-- `shareRes H q` is the one resource of `sheap H q`. -/
theorem sheap_eq {H : FHeap} {q : Frac} {r : Res} (h : sheap H q r) : r = shareRes H q := by
  obtain ⟨rh, rk, rg⟩ := r
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- **The share `q` of an exclusive assertion** `P`: of a heap that `P` holds alone. -/
def shared (P : FAssn) (q : Frac) : FAssn := fun r =>
  ∃ H, P ⟨H, Know.none, Ghost.unit⟩ ∧ sheap H q r

/-- **Shared bytes**: a fraction `q` of the bytes `bs` at `p` (each cell with its own tag). -/
def sbytesAt (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (q : Frac) : FAssn :=
  shared (up (bytesAt p A S K bs)) q

/-- **A shared typed value**: a positive fraction of `p ↦ v` (`pts`, not of a `const` global). -/
def spts {T : Type} [Enc T] (p : Ptr) (a : Nat) (q : Frac) (v : T) : FAssn := fun r =>
  0 < q.val ∧ shared (up (pts p a v)) q r

/-- All the heaps an exclusive assertion holds alone cover the same locations. -/
def FAssn.FixedDom (P : FAssn) : Prop :=
  ∀ H₁ H₂, P ⟨H₁, Know.none, Ghost.unit⟩ → P ⟨H₂, Know.none, Ghost.unit⟩ →
    ∀ l, (H₁ l).isSome = (H₂ l).isSome

theorem Ghost.sharesOf_share (H : FHeap) (q : Frac) (l : Loc) :
    (Ghost.sharesOf H q).share l = (H l).elim SCell.zero (SCell.of · q) := rfl

theorem SCell.cell_of_one (c : FCell) : (SCell.of c Frac.one).cell = some c :=
  SCell.cell_eq_some (SCell.valid_of (by decide)) (by rw [SCell.of_self]; decide)

/-- A positive share of `H` owns `H`'s bytes. -/
theorem shareRes_owned {H : FHeap} {q : Frac} (hq : 0 < q.val) {l : Loc} :
    (shareRes H q).owned l ≠ none ↔ H l ≠ none := by
  rw [Res.owned_ne]
  constructor
  · rintro (h | ⟨c, hc⟩)
    · exact absurd rfl h
    · intro e
      have hc' : 0 < ((Ghost.sharesOf H q).share l c).val := hc
      rw [Ghost.sharesOf_share, e] at hc'
      exact absurd hc' Rat.lt_irrefl
  · intro h
    cases e : H l with
    | none => exact absurd e h
    | some c =>
      refine .inr ⟨c, ?_⟩
      show 0 < ((Ghost.sharesOf H q).share l c).val
      rw [Ghost.sharesOf_share, e, Option.elim_some, SCell.of_self]
      exact hq

/-- A share of `H` below the whole holds `H`'s bytes as shared bytes. -/
theorem shareRes_shared {H : FHeap} {q : Frac} (hq : 0 < q.val) (hq1 : q.val < 1) {l : Loc}
    (h : H l ≠ none) : (shareRes H q).shared l ≠ none := by
  cases e : H l with
  | none => exact absurd e h
  | some c =>
    have hs : (shareRes H q).gh.share l = SCell.of c q := by
      show (Ghost.sharesOf H q).share l = _
      rw [Ghost.sharesOf_share, e]; rfl
    refine Res.shared_ne.mpr ⟨rfl, fun ⟨c', hc'⟩ => ?_, c, by rw [hs, SCell.of_self]; exact hq⟩
    rw [hs] at hc'
    by_cases ec : c' = c
    · subst ec; rw [SCell.of_self] at hc'; grind
    · rw [SCell.of_ne q ec] at hc'; exact absurd hc' (by decide)

/-! ## The whole share is the heap -/

/-- Next to the whole share of `H`, a frame with no share on `H`'s cells: the composed share is
the cell where `H` has one and the frame's elsewhere. -/
theorem Ghost.sharesOf_one_add {H : FHeap} {g : Ghost}
    (hz : ∀ l c, H l = some c → g.share l = SCell.zero) (l : Loc) :
    ((Ghost.sharesOf H Frac.one).add g).share l = (H l).elim (g.share l) (SCell.of · Frac.one) := by
  rw [Ghost.add_share, Ghost.sharesOf_share]
  rcases e : H l with _ | c
  · exact SCell.zero_add _
  · rw [Option.elim_some, Option.elim_some, hz l c e, SCell.add_zero]

/-- **The exclusive cells of `H` become the whole share of `H`.** -/
theorem Holds.toShares {m : Mem} {H : FHeap} {rF : Res} (hh : Holds m ⟨H, Know.none, Ghost.unit⟩ rF) :
    Holds m ⟨FHeap.empty, Know.none, Ghost.sharesOf H Frac.one⟩ rF := by
  have hF : ∀ l c, H l = some c → rF.heap l = none ∧ rF.gh.share l = SCell.zero := fun l c e =>
    have hl : H l ≠ none := by rw [e]; exact Option.some_ne_none _
    ⟨(hh.disj l).resolve_left hl, hh.frame_share_zero rfl hl⟩
  have hm : SMatch m (H ∪ rF.heap) rF.gh.share := by
    have := hh.heap; rw [Ghost.unit_add] at this; exact this
  have hs := Ghost.sharesOf_one_add (H := H) (g := rF.gh) fun l c e => (hF l c e).2
  refine ⟨fun _ => .inl rfl, hm.of_full (fun l => ?_) (fun l => ?_) (fun l => ?_), Know.sub_none _,
    hh.knowF, hh.ghost⟩
  · simp only [FHeap.union_apply, SCells, hs l]
    rcases e : H l with _ | c
    · simp [FHeap.empty]
    · simp [FHeap.empty, (hF l c e).1, SCell.cell_of_one]
  · rcases e : H l with _ | c
    · rcases hm.apart l with e' | e'
      · exact .inl (by simpa [FHeap.union_apply, FHeap.empty, e] using e')
      · exact .inr (by show (_ : SCell).cell = none; rw [hs l, e, Option.elim_none]; exact e')
    · exact .inl (by simp [FHeap.union_apply, FHeap.empty, (hF l c e).1])
  · rw [hs l]
    rcases e : H l with _ | c
    · exact hm.total l
    · exact .inr ⟨c, rfl⟩

/-- **The whole share of `H` becomes the exclusive cells of `H`**: next to the whole fraction a
valid frame holds none (`SCell.Valid.whole`). -/
theorem Holds.ofShares {m : Mem} {H : FHeap} {rF : Res}
    (hh : Holds m ⟨FHeap.empty, Know.none, Ghost.sharesOf H Frac.one⟩ rF) :
    Holds m ⟨H, Know.none, Ghost.unit⟩ rF := by
  have hm : SMatch m (FHeap.empty ∪ rF.heap) ((Ghost.sharesOf H Frac.one).add rF.gh).share :=
    hh.heap
  have hz : ∀ l c, H l = some c → rF.gh.share l = SCell.zero := fun l c e => by
    have hv := hm.valid l
    rw [Ghost.add_share, Ghost.sharesOf_share, e, Option.elim_some] at hv
    exact (hv.whole (c := c) (by rw [SCell.of_self]; rfl)).eq
  have hs := Ghost.sharesOf_one_add hz
  have hFn : ∀ l c, H l = some c → rF.heap l = none := fun l c e => by
    have := (hm.apart l).resolve_right (by
      simp only [SCells, hs l, e, Option.elim_some, SCell.cell_of_one]; exact Option.some_ne_none _)
    simpa [FHeap.union_apply, FHeap.empty] using this
  refine ⟨fun l => ?_, ?_, Know.sub_none _, hh.knowF, hh.ghost⟩
  · rcases e : H l with _ | c
    · exact .inl e
    · exact .inr (hFn l c e)
  · show SMatch m (H ∪ rF.heap) (Ghost.unit.add rF.gh).share
    rw [Ghost.unit_add]
    refine hm.of_full (fun l => ?_) (fun l => ?_) (fun l => ?_)
    · simp only [FHeap.union_apply, SCells, hs l]
      rcases e : H l with _ | c
      · simp [FHeap.empty]
      · simp [FHeap.empty, hFn l c e, hz l c e, SCell.cell_zero, SCell.cell_of_one]
    · rcases e : H l with _ | c
      · rcases hm.apart l with e' | e'
        · exact .inl (by simpa [FHeap.union_apply, FHeap.empty, e] using e')
        · refine .inr ?_
          have h' : (((Ghost.sharesOf H Frac.one).add rF.gh).share l).cell = none := e'
          rwa [hs l, e, Option.elim_none] at h'
      · exact .inr (by simp [SCells, hz l c e, SCell.cell_zero])
    · rcases e : H l with _ | c
      · have := hm.total l; rwa [hs l, e, Option.elim_none] at this
      · rw [hz l c e]; exact .inl rfl

namespace EUpd

variable {P : FAssn}

/-- **An exclusive assertion becomes its whole share.** -/
theorem share_whole (hP : ∀ r, P r → r.know = Know.none ∧ r.gh = Ghost.unit) :
    EUpd P (shared P Frac.one) := by
  rintro m ⟨H, k, g⟩ rF hh hp _
  obtain ⟨hk, hg⟩ := hP _ hp
  subst hk hg
  exact ⟨_, hh.toShares, H, hp, rfl, rfl, rfl⟩

/-- **The whole share becomes the exclusive assertion.** -/
theorem unshare_whole : EUpd (shared P Frac.one) P := by
  rintro m ⟨h, k, g⟩ rF hh ⟨H, hp, hH, hk, hg⟩ _
  subst hH hk hg
  exact ⟨_, hh.ofShares, hp⟩

/-- **A heap becomes its whole share**, as resources (`share_whole`). -/
theorem shareRes_whole (H : FHeap) :
    EUpd (· = ⟨H, Know.none, Ghost.unit⟩) (· = shareRes H Frac.one) :=
  (share_whole fun _ h => by subst h; exact ⟨rfl, rfl⟩).trans
    (of_imp fun _ ⟨_, hH, hs⟩ => by cases hH; exact sheap_eq hs)

/-- **The whole share of a heap becomes the heap**, as resources (`unshare_whole`). -/
theorem shareRes_unwhole (H : FHeap) :
    EUpd (· = shareRes H Frac.one) (· = ⟨H, Know.none, Ghost.unit⟩) :=
  (of_imp fun _ h => ⟨H, rfl, by subst h; exact shareRes_sheap H _⟩).trans unshare_whole

end EUpd

/-! ## Split and join -/

theorem Ghost.sharesOf_add (H : FHeap) (q₁ q₂ : Frac) :
    (Ghost.sharesOf H q₁).add (Ghost.sharesOf H q₂) = Ghost.sharesOf H (q₁.add q₂) := by
  ext1
  · exact (congrArg Ghost.led (Ghost.add_unit Ghost.unit) :)
  · exact (congrArg Ghost.extent (Ghost.add_unit Ghost.unit) :)
  · exact (congrArg Ghost.cl (Ghost.add_unit Ghost.unit) :)
  · exact (congrArg Ghost.ac (Ghost.add_unit Ghost.unit) :)
  · funext l
    rw [Ghost.add_share, Ghost.sharesOf_share, Ghost.sharesOf_share, Ghost.sharesOf_share]
    rcases H l with _ | c
    · exact SCell.add_zero _
    · exact SCell.of_add _ _ _

/-- **Split and join of one heap's share are equalities.** -/
theorem sheap_add {H : FHeap} {q₁ q₂ : Frac} {r : Res} :
    sheap H (q₁.add q₂) r ↔ (sheap H q₁ ⋆ sheap H q₂) r := by
  constructor
  · rintro ⟨hh, hk, hg⟩
    refine ⟨⟨FHeap.empty, Know.none, Ghost.sharesOf H q₁⟩, ⟨FHeap.empty, Know.none,
      Ghost.sharesOf H q₂⟩, fun _ => .inl rfl, ?_, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨rh, rk, rg⟩ := r
    simp only at hh hk hg
    subst hh hk hg
    rw [FHeap.union_empty, Know.none_union, Ghost.sharesOf_add]
  · rintro ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · show r₁.heap ∪ r₂.heap = _; rw [h1, h2, FHeap.union_empty]
    · show r₁.know.union r₂.know = _; rw [k1, k2, Know.none_union]
    · show r₁.gh.add r₂.gh = _; rw [g1, g2, Ghost.sharesOf_add]

/-- **A share of `P` splits** into two shares of the same heap. -/
theorem shared_split {P : FAssn} {q₁ q₂ : Frac} {r : Res} (h : shared P (q₁.add q₂) r) :
    (shared P q₁ ⋆ shared P q₂) r := by
  obtain ⟨H, hp, hs⟩ := h
  obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := sheap_add.mp hs
  exact ⟨r₁, r₂, hd, e, ⟨H, hp, h1⟩, ⟨H, hp, h2⟩⟩

/-- **Two positive shares of `P` join** when `P`'s heaps have one domain: at each byte both read
a cell, and in a valid composition they read the same one, so the heaps are equal. -/
theorem EUpd.shared_join {P : FAssn} (hP : P.FixedDom) {q₁ q₂ : Frac} (hq₁ : 0 < q₁.val)
    (hq₂ : 0 < q₂.val) : EUpd (shared P q₁ ⋆ shared P q₂) (shared P (q₁.add q₂)) := by
  rintro m r rF hh ⟨r₁, r₂, hd, rfl, ⟨H₁, hp₁, hs₁⟩, ⟨H₂, hp₂, hs₂⟩⟩ _
  have e : H₁ = H₂ := funext fun l => by
    have hdom := hP H₁ H₂ hp₁ hp₂ l
    rcases e₁ : H₁ l with _ | c₁ <;> rcases e₂ : H₂ l with _ | c₂ <;>
      simp only [e₁, e₂, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
        Bool.true_eq_false] at hdom ⊢
    · have hv : (((r₁.gh.add r₂.gh).add rF.gh).share l).Valid := hh.heap.valid l
      have hg : (r₁.gh.add r₂.gh).share l = (SCell.of c₁ q₁).add (SCell.of c₂ q₂) := by
        rw [Ghost.add_share, hs₁.2.2, hs₂.2.2, Ghost.sharesOf_share, Ghost.sharesOf_share, e₁, e₂,
          Option.elim_some, Option.elim_some]
      rw [Ghost.add_share, hg] at hv
      exact congrArg some (hv.of_add.1 c₁ c₂ (SCell.pos_add _ (by rw [SCell.of_self]; exact hq₁))
        (SCell.pos_add' _ (by rw [SCell.of_self]; exact hq₂)))
  subst e
  exact ⟨_, hh, H₁, hp₁, sheap_add.mpr ⟨r₁, r₂, hd, rfl, hs₁, hs₂⟩⟩

/-! ## Instances: bytes and typed values -/

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {q : Frac}

/-- The bytes at `p` cover the `bs.size` bytes from `p`, whatever they hold. -/
theorem bytesAt_isSome {h : Heap} {b : BlockId} (hp : bytesAt p A S K bs h)
    (hb : p.block = some b) (l : Loc) :
    (h l).isSome = decide (l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size) := by
  obtain ⟨b', hb', -, hl⟩ := hp
  rw [hb] at hb'; cases hb'
  by_cases hc : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
  · rw [hl l, ite_eq_left hc, decide_eq_true hc]; rfl
  · rw [hl l, ite_eq_right hc, decide_eq_false hc]; rfl

theorem fixedDom_bytesAt : (up (bytesAt p A S K bs)).FixedDom := fun H₁ H₂ h₁ h₂ l => by
  obtain ⟨b, hb, -⟩ := h₁.1
  have e₁ := bytesAt_isSome h₁.1 hb l
  have e₂ := bytesAt_isSome h₂.1 hb l
  simp only [FHeap.erase, Option.isSome_map] at e₁ e₂
  rw [e₁, e₂]

theorem fixedDom_pts {T : Type} [Enc T] {a : Nat} {v : T} : (up (pts p a v)).FixedDom :=
  fun H₁ H₂ h₁ h₂ l => by
    obtain ⟨A₁, S₁, K₁, bs₁, -, hsz₁, -, hb₁, -⟩ := h₁.1
    obtain ⟨A₂, S₂, K₂, bs₂, -, hsz₂, -, hb₂, -⟩ := h₂.1
    have ⟨b, hb, _⟩ := hb₁
    have e₁ := bytesAt_isSome hb₁ hb l
    have e₂ := bytesAt_isSome hb₂ hb l
    simp only [FHeap.erase, Option.isSome_map, hsz₁, hsz₂] at e₁ e₂
    rw [e₁, e₂]

/-- **A positive share reads the memory's cell.** -/
theorem Holds.sharedCell {m : Mem} {r rF : Res} (hh : Holds m r rF) {H : FHeap}
    (hs : sheap H q r) (hq : 0 < q.val) {l : Loc} {c : FCell} (e : H l = some c) :
    ∃ c', m.heap l = some c' ∧ c'.norm = c.cell.norm :=
  hh.cellS (fc := c) (by rw [hs.2.2, Ghost.sharesOf_share, e, Option.elim_some, SCell.of_self]; exact hq)

/-- **Shared bytes are read in `m`.** -/
theorem Holds.sbytesRead {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hp : sbytesAt p A S K bs q r) (hq : 0 < q.val) : m.BytesRead p A S K bs := by
  obtain ⟨H, hb, hs⟩ := hp
  obtain ⟨b, hpb, h0, -⟩ := hb.1
  refine ⟨b, hpb, h0, fun j hj => ?_⟩
  obtain ⟨fc, hfc, hc⟩ := up_bytesAt_cell hb hpb hj
  rw [← hc]; exact hh.sharedCell hs hq hfc

namespace FTotalTriple

/-- **Load of a `T`** at byte `k` of shared bytes that decode to `v` there: the share stays. -/
theorem load_sbytesAt {T : Type} [Enc T] {v : T} {k al : Nat} (hq : 0 < q.val)
    (hn : 0 < Enc.size T) (hk : k + Enc.size T ≤ bs.size) (ha : (A + p.off.toNat + k) % al = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    FTotalTriple (sbytesAt p A S K bs q) (Zig.load T al (p.add k))
      (fun x => ⟪x = v⟫ ⋆ sbytesAt p A S K bs q) :=
  load_of_read (fun _ _ _ hh hp => hh.sbytesRead hp hq) hn hk ha hv

/-- **Load of a shared typed value** (`spts`, `@[fsym]`): the share stays. -/
@[fsym] theorem sload {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (spts p a q v) (Zig.load T a p) (fun x => ⟪x = v⟫ ⋆ spts p a q v) :=
  of_cases fun _ hp => by
    obtain ⟨hq, H, hP, hs⟩ := hp
    obtain ⟨A, S, K, bs, ha, hsz, hv, hb, -⟩ := hP.1
    have t := load_of_read (P := fun r => spts p a q v r ∧ sbytesAt p A S K bs q r) (q := p)
      (k := 0) (al := a) (fun _ _ _ hh hp => hh.sbytesRead hp.2 hq) hn (by omega)
      (by simpa using ha) (by rw [Nat.zero_add, ← hsz, Array.extract_size]; exact hv)
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, ⟨⟨hq, H, hP, hs⟩, H, ⟨hb, rfl, rfl⟩, hs⟩, fun v' _ h => by
      obtain ⟨hφ, hb'⟩ := sep_lift.mp h
      exact sep_lift.mpr ⟨hφ, hb'.1⟩⟩

end FTotalTriple

/-- A shared typed value holds a read share of each of its bytes (`Res.owned`). -/
theorem spts_owned {T : Type} [Enc T] {a : Nat} {v : T} {b : BlockId} (hpb : p.block = some b)
    {r : Res} (hp : spts p a q v r) {x : Nat} (h1 : p.off.toNat ≤ x)
    (h2 : x < p.off.toNat + Enc.size T) : r.owned (b, x) ≠ none := by
  obtain ⟨hq, H, hP, hs⟩ := hp
  obtain ⟨A, S, K, bs, -, hsz, -, hb, -⟩ := hP.1
  obtain ⟨fc, hfc, -⟩ := up_bytesAt_cell (r := ⟨H, Know.none, Ghost.unit⟩) ⟨hb, rfl, rfl⟩ hpb
    (j := x - p.off.toNat) (by omega)
  rw [show p.off.toNat + (x - p.off.toNat) = x by omega] at hfc
  change H (b, x) = some fc at hfc
  refine Res.owned_ne.mpr (.inr ⟨fc, ?_⟩)
  rw [hs.2.2, Ghost.sharesOf_share, hfc, Option.elim_some, SCell.of_self]
  exact hq

/-- **A load of a shared typed value is local to the thread** (`spts`, a locality provider,
§Read shares): the share orders every write before the load, and other holders of the share may
read the bytes meanwhile (`ThreadLocal.loadOwned`). So `fsym` applies the sequential `sload` in a
thread (`FTTotalTriple.ofSeq`, `Full/AutoThread.lean`), and the share stays. -/
@[fsym_provider] theorem ThreadLocal.sload {T : Type} [Enc T] {a : Nat} {v : T} :
    ThreadLocal (spts p a q v) (Zig.load T a p) :=
  ThreadLocal.loadOwned fun _ hpb _ hp _ h1 h2 => spts_owned hpb hp h1 h2

/-- **Shared bytes split** into two shares of the same bytes. -/
theorem sbytesAt_split {q₁ q₂ : Frac} {r : Res} (h : sbytesAt p A S K bs (q₁.add q₂) r) :
    (sbytesAt p A S K bs q₁ ⋆ sbytesAt p A S K bs q₂) r :=
  shared_split h

/-- **Two positive shares of the bytes join.** -/
theorem EUpd.sbytesAt_join {q₁ q₂ : Frac} (hq₁ : 0 < q₁.val) (hq₂ : 0 < q₂.val) :
    EUpd (sbytesAt p A S K bs q₁ ⋆ sbytesAt p A S K bs q₂) (sbytesAt p A S K bs (q₁.add q₂)) :=
  EUpd.shared_join fixedDom_bytesAt hq₁ hq₂

section Typed

variable {T : Type} [Enc T] {a : Nat} {v : T}

/-- **`p ↦ v` becomes its whole share.** -/
theorem EUpd.spts_whole : EUpd (up (pts p a v)) (spts p a Frac.one v) :=
  (EUpd.share_whole fun _ h => h.2).trans (EUpd.of_imp fun _ h => ⟨by decide, h⟩)

/-- **The whole share of `p ↦ v` becomes `p ↦ v`.** -/
theorem EUpd.spts_unwhole : EUpd (spts p a Frac.one v) (up (pts p a v)) :=
  (EUpd.of_imp fun _ h => h.2).trans EUpd.unshare_whole

/-- **A typed share splits** into two positive halves. -/
theorem spts_split {q₁ q₂ : Frac} (hq₁ : 0 < q₁.val) (hq₂ : 0 < q₂.val) {r : Res}
    (h : spts p a (q₁.add q₂) v r) : (spts p a q₁ v ⋆ spts p a q₂ v) r := by
  obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := shared_split h.2
  exact ⟨r₁, r₂, hd, e, ⟨hq₁, h1⟩, ⟨hq₂, h2⟩⟩

/-- **Two typed shares join.** -/
theorem EUpd.spts_join {q₁ q₂ : Frac} :
    EUpd (spts p a q₁ v ⋆ spts p a q₂ v) (spts p a (q₁.add q₂) v) := by
  intro m r rF hh hp hs
  obtain ⟨r₁, r₂, hd, e, h1, h2⟩ := hp
  obtain ⟨r', hh', hr'⟩ := EUpd.shared_join fixedDom_pts h1.1 h2.1 m r rF hh
    ⟨r₁, r₂, hd, e, h1.2, h2.2⟩ hs
  exact ⟨r', hh', by have := h1.1; have := h2.1; simp only [Frac.add]; grind, hr'⟩

end Typed

end Full
end Zig
