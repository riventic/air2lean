import ZigLean.Sep.Full.Ghost
import ZigLean.Sep.Full.Reclaim

/-!
# The reset ledger: grants, receipts and the epoch-token fee of an allocator with a bulk reset

An allocator that gives back all of its memory at once (`ArenaAllocator.reset`,
`FixedBufferAllocator.reset`) must know that no grant is outstanding: revoking ghost state does not
take back the bytes a client holds (`tests/roadmap/alloc-arena/ArenaObstruction.lean`,
`not_reset_own`). The evidence is the **epoch token** of the allocator's ledger
(`docs/sep-full-state.md` §Epoch tokens, §The fee of a grant). Each grant costs a nonzero part of
it, the fee (`epFee`), which the allocator keeps with the grant's receipt (`ledgerRcpt`) until the
grant comes back. The whole token next to the allocator's state therefore shows that the grant map
is empty (`ledgerOwn_epTok_empty`), and a client with an outstanding grant cannot hold the whole
token (`ResetLedger.granted_epTok_false`).

This module is the part that does not depend on the allocator:

* the fee `epFee`, the receipts `ledgerRcpt`/`LedgerRcpts` and their updates (pick, put, re-point,
  open);
* the ghost parts of the entries: a grant is issued (`ledger_issue`: half of a kept share lent
  against a receipt, the fee kept), goes back (`ledger_return`: the share against its receipt, the
  grant retired, the fee refunded), shrinks (`ledger_shrink`) or grows by re-lending its share
  (`ledger_regrow`);
* the reset: the whole token shows an empty map (`ledgerRcpts_epTok_empty`), the epoch is bumped
  with the token (`ledger_bump`), and the receipts of a past epoch are revoked
  (`ledgerRcpts_revoke`, `ledgerRcpts_list`);
* `ResetLedger I γ e`: an allocator invariant `I` whose state is a ledger next to the allocator's
  own resources (`LedgerOwn`), whose token names a grant of the ledger (`ledgerTok`) and whose fee
  is `epFee`. Its instances: the arena (`tests/roadmap/alloc-arena/AllocArena/Core.lean`) and the
  fixed buffer (`tests/roadmap/alloc-fba/AllocFba/Full.lean`).
-/

namespace Zig
namespace Full

open Zig.Region FAssn

/-! ## The fee and the receipts -/

/-- **The fee of a grant** (`FAllocInv.fee`): a nonzero part `φ` of the epoch token of epoch `e`
of the ledger `γ`. -/
def epFee (γ e : Nat) (φ : Frac) : FAssn := epTok γ e φ ⋆ ⟪0 < φ.val⟫

/-- A fee owns no bytes and no knowledge. -/
theorem epFee_ghost {γ e : Nat} {φ : Frac} {r : Res} (h : epFee γ e φ r) :
    r.heap = FHeap.empty ∧ r.know = Know.none := by
  obtain ⟨-, h⟩ := sep_lift.mp (sep_comm h); exact ⟨h.1, h.2.1⟩

/-- Fees split and join (`epTok_add`). -/
theorem epFee_add (γ e : Nat) {a b : Frac} (ha : 0 < a.val) (hb : 0 < b.val) :
    epFee γ e (a.add b) = (epFee γ e a ⋆ epFee γ e b) := by
  have hab : 0 < (a.add b).val := by simp only [Frac.add]; grind
  funext r; apply propext
  simp only [epFee, epTok_add]
  constructor
  · intro h
    obtain ⟨-, h⟩ := sep_lift.mp (sep_comm h)
    obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
    exact ⟨r₁, r₂, hd, rfl, sep_comm (sep_lift.mpr ⟨ha, h1⟩), sep_comm (sep_lift.mpr ⟨hb, h2⟩)⟩
  · rintro ⟨r₁, r₂, hd, rfl, h1, h2⟩
    obtain ⟨-, h1⟩ := sep_lift.mp (sep_comm h1)
    obtain ⟨-, h2⟩ := sep_lift.mp (sep_comm h2)
    exact sep_comm (sep_lift.mpr ⟨hab, ⟨r₁, r₂, hd, rfl, h1, h2⟩⟩)

/-- What the allocator keeps for a grant `(p, n, q, A, K, φ)` of epoch `e`: the receipt for its
share (`EUpd.lendT`: the fraction `q` of the extent of `p`'s block, at some bound; a share given
back against it is weakened to that bound first, `EUpd.returnTw`) and the fee `φ` the client paid
(a `free` gives it back). -/
def ledgerRcpt (γ e : Nat) : Option GRegion → FAssn
  | none => FAssn.emp
  | some (p, _, q, _, _, φ) =>
    (FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆ brcpt b q k γ e) ⋆ epFee γ e φ

/-- One receipt and fee per grant of the map `M`. -/
def LedgerRcpts (γ e : Nat) (M : GMap) : FAssn :=
  FAssn.ex fun N => ⟪∀ i, N ≤ i → M i = none⟫ ⋆ sepN N (fun i => ledgerRcpt γ e (M i))

theorem ledgerRcpts_pick {γ e i : Nat} {M : GMap} {g : GRegion} {r : Res} (hM : M i = some g)
    (h : LedgerRcpts γ e M r) : (ledgerRcpt γ e (some g) ⋆ LedgerRcpts γ e (M.set i none)) r := by
  obtain ⟨N, h⟩ := h
  obtain ⟨hN, h⟩ := sep_lift.mp h
  have hi : i < N := Nat.lt_of_not_le fun hle => by rw [hN i hle] at hM; cases hM
  rw [sepN_pick hi] at h
  simp only [hM] at h
  refine sep_mono_right (fun r h => ⟨N, sep_lift.mpr ⟨fun j hj => ?_, ?_⟩⟩) h
  · by_cases hji : j = i
    · subst hji; simp
    · rw [GMap.set_ne _ _ hji]; exact hN j hj
  · refine of_eq (sepN_congr fun j _ => ?_) h
    by_cases hji : j = i
    · subst hji; simp [ledgerRcpt]
    · simp [hji, GMap.set_ne _ _ hji]

theorem ledgerRcpts_put {γ e i : Nat} {M : GMap} {v : Option GRegion} {r : Res} (hM : M i = none)
    (h : (ledgerRcpt γ e v ⋆ LedgerRcpts γ e M) r) : LedgerRcpts γ e (M.set i v) r := by
  obtain ⟨N, h⟩ := sep_exR h
  obtain ⟨hN, h⟩ := sep_lift.mp (of_eq (sep_left_comm_eq _ _ _) h)
  refine ⟨N + i + 1, sep_lift.mpr ⟨fun j hj => ?_, ?_⟩⟩
  · rw [GMap.set_ne _ _ (by omega)]; exact hN j (by omega)
  · rw [sepN_pick (i := i) (by omega)]
    simp only [GMap.set_same]
    have e1 : (sepN (N + i + 1) fun j => if j = i then emp else ledgerRcpt γ e ((M.set i v) j)) =
        sepN (N + i + 1) fun j => ledgerRcpt γ e (M j) := sepN_congr fun j _ => by
      by_cases hji : j = i
      · subst hji; simp [hM, ledgerRcpt]
      · simp [hji, GMap.set_ne _ _ hji]
    have e2 : (sepN (N + i + 1) fun j => ledgerRcpt γ e (M j)) = sepN N fun j => ledgerRcpt γ e (M j) :=
      sepN_extend (by omega) fun j hj _ => by rw [hN j hj]; rfl
    rw [e1, e2]; exact h

/-- The receipts of the empty map own nothing. -/
theorem ledgerRcpts_empty {γ e : Nat} : LedgerRcpts γ e GMap.empty = emp := by
  funext r; apply propext; constructor
  · intro h
    obtain ⟨N, h⟩ := h
    obtain ⟨-, h⟩ := sep_lift.mp h
    rwa [sepN_extend (n := 0) (f := fun i => ledgerRcpt γ e (GMap.empty i)) (Nat.zero_le N)
      fun j _ _ => rfl] at h
  · intro h
    exact ⟨0, sep_lift.mpr ⟨fun _ _ => rfl, h⟩⟩

/-- The receipts after a grant is re-pointed with the same pointer, fraction and fee. -/
theorem ledgerRcpts_repoint {γ e i : Nat} {M : GMap} {p : Ptr} {n n' : Nat} {q φ : Frac} {A A' : Nat}
    {K K' : BlockKind} {r : Res} (hM : M i = some (p, n, q, A, K, φ)) (h : LedgerRcpts γ e M r) :
    LedgerRcpts γ e (M.set i (some (p, n', q, A', K', φ))) r := by
  have := ledgerRcpts_put (v := some (p, n', q, A', K', φ)) (GMap.set_same M i none)
    (sep_mono_left (P := ledgerRcpt γ e (some (p, n, q, A, K, φ)))
      (Q := ledgerRcpt γ e (some (p, n', q, A', K', φ))) (fun _ x => x) (ledgerRcpts_pick hM h))
  rwa [GMap.set_set] at this

/-- The receipt of a grant, opened: its block and bound, and the grant's fee. -/
theorem ledgerRcpts_open {γ e i : Nat} {M : GMap} {p : Ptr} {n : Nat} {q q' φ : Frac} {A : Nat}
    {K : BlockKind} {k₀ : Nat} {t : STag} {X : FAssn} {r : Res} (hM : M i = some (p, n, q, A, K, φ))
    (h : (pshare p q' k₀ t ⋆ (LedgerRcpts γ e M ⋆ X)) r) :
    ∃ b k, p.block = some b ∧
      (((bshare b q' k₀ t ⋆ brcpt b q k γ e) ⋆ (LedgerRcpts γ e (M.set i none) ⋆ X)) ⋆ epFee γ e φ) r := by
  have h1 := sep_mono_right (R := (ledgerRcpt γ e (some (p, n, q, A, K, φ)) ⋆
      LedgerRcpts γ e (M.set i none)) ⋆ X)
    (fun _ x => sep_mono_left (Q := ledgerRcpt γ e (some (p, n, q, A, K, φ)) ⋆
      LedgerRcpts γ e (M.set i none)) (fun _ y => ledgerRcpts_pick hM y) x) h
  have h2 := of_eq (Q := (pshare p q' k₀ t ⋆ ((FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
    brcpt b q k γ e) ⋆ (LedgerRcpts γ e (M.set i none) ⋆ X))) ⋆ epFee γ e φ)
    (by simp only [ledgerRcpt]; ac_rfl) h1
  obtain ⟨r₁, r₂, hd, rfl, h2, hf⟩ := h2
  obtain ⟨b, h3⟩ := sep_ex.mp h2
  obtain ⟨hb, h3⟩ := sep_lift.mp (sep_assoc h3)
  obtain ⟨b', h4⟩ := sep_ex.mp (of_eq (sep_left_comm_eq _ _ _) h3)
  obtain ⟨k, h4⟩ := sep_ex.mp h4
  obtain ⟨hb', h4⟩ := sep_lift.mp (sep_assoc h4)
  rw [hb] at hb'; cases hb'
  exact ⟨b, k, hb, ⟨r₁, r₂, hd, rfl, of_eq (by ac_rfl) h4, hf⟩⟩

/-- A grant's token names a grant of the map (`gfrag_mem`). -/
theorem ledger_grant_fact {γ e i : Nat} {M : GMap} {t : STag} {g : GRegion} {X : FAssn} :
    ∀ m r rF, Holds m r rF → (gauthP γ e M t ⋆ (gfrag γ e i g ⋆ X)) r → m.FSeq → M i = some g :=
  fun _ _ rF hh hp _ => by
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := sep_assoc' hp
    exact gfrag_mem h1 (Ghost.Ok.assoc.mp hh.ghost.1)

/-! ## The ghost parts of the entries -/

/-- **A grant is issued** (`alloc`'s ghost part): half of a share `qh` that the allocator keeps on
the grant's block (at the bound `kN`) is lent at the grant's end against a receipt
(`EUpd.lendT`), the grant is issued under the unused id `i` (`Upd.issue`), and its fee `φ` is kept
with the receipt. -/
theorem ledger_issue {γ e i : Nat} {M : GMap} {t : STag} {N : Ptr} {bN : BlockId} {qh : Frac}
    {kN : Nat} {p : Ptr} {n A : Nat} {K : BlockKind} {φ : Frac} (hi : M i = none) (hN : N.block = some bN)
    (hp : p.block = some bN) (hk : p.off.toNat + n ≤ kN) :
    EUpd (gauthP γ e M t ⋆ (pshare N qh kN t ⋆ (LedgerRcpts γ e M ⋆ epFee γ e φ)))
      (gauthP γ e (M.set i (some (p, n, qh.half, A, K, φ))) t ⋆ (gfrag γ e i (p, n, qh.half, A, K, φ) ⋆
        (pshare p qh.half (p.off.toNat + n) (some (γ, e)) ⋆
          (pshare N qh.half kN t ⋆ LedgerRcpts γ e (M.set i (some (p, n, qh.half, A, K, φ))))))) := by
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e M t ⋆ (bshare bN qh kN t ⋆ (LedgerRcpts γ e M ⋆ epFee γ e φ)))
    fun _ h => sep_mono_right (fun _ x => sep_mono_left (Q := bshare bN qh kN t)
      (fun _ y => (pshare_iff hN).mp y) x) h) ?_
  refine EUpd.withFact (φ := 0 < qh.val) (fun _ r _ _ h _ => ?_) fun hq => ?_
  · obtain ⟨_, _, -, -, -, _, _, -, -, h1, -⟩ := h
    exact h1.1
  have hh := Frac.half_pos hq
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ bshare bN qh.half kN t) ⋆
      (bshare bN qh.half kN t ⋆ (LedgerRcpts γ e M ⋆ epFee γ e φ))) fun r h => ?_) ?_
  · rw [← Frac.half_add_half qh] at h
    have h := sep_mono_right (R := (bshare bN qh.half kN t ⋆ bshare bN qh.half kN t) ⋆
      (LedgerRcpts γ e M ⋆ epFee γ e φ))
      (fun _ x => sep_mono_left (Q := bshare bN qh.half kN t ⋆ bshare bN qh.half kN t)
      (fun _ y => (bshare_split hh hh).mp y) x) h
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (EUpd.lendT hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e M t ⋆ ((bshare bN qh.half (p.off.toNat + n) (some (γ, e)) ⋆
      brcpt bN qh.half kN γ e) ⋆ (bshare bN qh.half kN t ⋆ (LedgerRcpts γ e M ⋆ epFee γ e φ))))
    fun _ h => sep_assoc h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.issue (p, n, qh.half, A, K, φ) hi))) ?_
  refine EUpd.of_imp fun r h => ?_
  have h := of_eq (Q := (brcpt bN qh.half kN γ e ⋆ epFee γ e φ) ⋆ (LedgerRcpts γ e M ⋆
      ((gauthP γ e (M.set i (some (p, n, qh.half, A, K, φ))) t ⋆ gfrag γ e i (p, n, qh.half, A, K, φ)) ⋆
        (bshare bN qh.half (p.off.toNat + n) (some (γ, e)) ⋆ bshare bN qh.half kN t)))) (by ac_rfl) h
  have h := sep_mono_left (Q := ledgerRcpt γ e (some (p, n, qh.half, A, K, φ)))
    (fun _ z => sep_mono_left (Q := FAssn.ex fun b' => FAssn.ex fun k' => ⟪p.block = some b'⟫ ⋆
      brcpt b' qh.half k' γ e) (fun _ y => ⟨bN, kN, sep_lift.mpr ⟨hp, y⟩⟩) z) h
  have h := sep_mono_left (Q := LedgerRcpts γ e (M.set i (some (p, n, qh.half, A, K, φ))))
    (fun _ z => ledgerRcpts_put hi z) (sep_assoc' h)
  have h := sep_mono_right (R := (gauthP γ e (M.set i (some (p, n, qh.half, A, K, φ))) t ⋆
      gfrag γ e i (p, n, qh.half, A, K, φ)) ⋆ (pshare p qh.half (p.off.toNat + n) (some (γ, e)) ⋆
        pshare N qh.half kN t))
    (fun _ x => sep_mono_right (R := pshare p qh.half (p.off.toNat + n) (some (γ, e)) ⋆
      pshare N qh.half kN t) (fun _ y => sep_mono (P' := pshare p qh.half (p.off.toNat + n) (some (γ, e)))
      (Q' := pshare N qh.half kN t) (fun _ z => (pshare_iff hp).mpr z) (fun _ z => (pshare_iff hN).mpr z) y) x) h
  exact of_eq (by ac_rfl) h

/-- **A grant goes back** (`free`'s ghost part): the share goes back against its receipt (at the
receipt's bound `k`, on the grant's block `b`), the grant is retired, and its fee comes back. -/
theorem ledger_return {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {n : Nat} {q φ : Frac} {A : Nat}
    {K : BlockKind} :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q, A, K, φ) ⋆ (pshare p q (p.off.toNat + n) (some (γ, e)) ⋆
      LedgerRcpts γ e M)))
      ((FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
        (gauthP γ e (M.set i none) t ⋆ (LedgerRcpts γ e (M.set i none) ⋆ bshare b q k t))) ⋆
          epFee γ e φ) := by
  refine EUpd.withFact ledger_grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := (FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
      ((gauthP γ e M t ⋆ (bshare b q (p.off.toNat + n) (some (γ, e)) ⋆ brcpt b q k γ e)) ⋆
        (gfrag γ e i (p, n, q, A, K, φ) ⋆ LedgerRcpts γ e (M.set i none)))) ⋆ epFee γ e φ)
      fun r h => ?_) (EUpd.frame (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hb => ?_))
  · obtain ⟨b, k, hb, h⟩ := ledgerRcpts_open (X := gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ)) hM
      (of_eq (Q := pshare p q (p.off.toNat + n) (some (γ, e)) ⋆ (LedgerRcpts γ e M ⋆
        (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ)))) (by ac_rfl) h)
    exact sep_mono_left (fun _ x => ⟨b, k, sep_lift.mpr ⟨hb, of_eq (by ac_rfl) x⟩⟩) h
  refine EUpd.trans (EUpd.frame EUpd.returnTw) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ)) ⋆
    (bshare b q k t ⋆ LedgerRcpts γ e (M.set i none))) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd Upd.retire)) ?_
  exact EUpd.of_imp fun _ h => ⟨b, k, sep_lift.mpr ⟨hb, of_eq (by ac_rfl) h⟩⟩

/-- **A grant shrinks**: the bound of the client's part `q'` of the share comes down to the new
end, the grant is re-pointed; its receipt does not change. -/
theorem ledger_shrink {γ e i : Nat} {M : GMap} {t : STag} {p : Ptr} {n n' : Nat} {q q' φ : Frac}
    {A : Nat} {K : BlockKind} (hn : n' ≤ n) :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q, A, K, φ) ⋆ (pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆
      LedgerRcpts γ e M)))
      (gauthP γ e (M.set i (some (p, n', q, A, K, φ))) t ⋆ (gfrag γ e i (p, n', q, A, K, φ) ⋆
        (pshare p q' (p.off.toNat + n') (some (γ, e)) ⋆
          LedgerRcpts γ e (M.set i (some (p, n', q, A, K, φ)))))) := by
  refine EUpd.withFact ledger_grant_fact fun hM => ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ)) ⋆
    (pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆ LedgerRcpts γ e (M.set i (some (p, n', q, A, K, φ)))))
    fun _ h => sep_assoc' (sep_mono_right (fun _ x => sep_mono_right (fun _ y => sep_mono_right
      (fun _ z => ledgerRcpts_repoint hM z) y) x) h)) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.reassign (p, n', q, A, K, φ)))) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.pweaken (p := p) (q := q') (k := p.off.toNat + n)
    (k' := p.off.toNat + n') (by omega)))) ?_
  exact EUpd.of_imp fun _ h => sep_assoc h

/-- **A growth's extent part** on a block `b` whose share `qh` at `kN` the allocator keeps
(`EUpd.returnTw`, `EUpd.join`, `EUpd.lendT`): the client's part `q'` of a grant's share goes back
against a receipt for it (at any bound), joins the kept share, and is lent again at the new end
`k'`, with a receipt at `kN`. -/
theorem ledger_regrow_core {γ e : Nat} {M : GMap} {t : STag} {b : BlockId} {q' qh : Frac}
    {k₀ k k' kN : Nat} (hk : k' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ ((bshare b q' k₀ (some (γ, e)) ⋆ brcpt b q' k γ e) ⋆ bshare b qh kN t))
      (gauthP γ e M t ⋆ ((bshare b q' k' (some (γ, e)) ⋆ brcpt b q' kN γ e) ⋆ bshare b qh kN t)) := by
  refine EUpd.withFact (φ := 0 < q'.val ∧ 0 < qh.val) (fun _ r _ _ h _ => ?_) fun ⟨hq, hqh⟩ => ?_
  · obtain ⟨_, _, -, -, -, _, _, -, -, ⟨_, _, -, -, h1, -⟩, h2⟩ := h
    exact ⟨h1.1, h2.1⟩
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ (bshare b q' k₀ (some (γ, e)) ⋆
    brcpt b q' k γ e)) ⋆ bshare b qh kN t) fun _ h => sep_assoc' h) ?_
  refine EUpd.trans (EUpd.frame EUpd.returnTw) ?_
  refine EUpd.trans (EUpd.of_imp (P' := gauthP γ e M t ⋆ (bshare b qh kN t ⋆ bshare b q' k t))
    fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frameL EUpd.join) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.weaken (k' := kN) (Nat.le_max_left _ _))) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ bshare b q' kN t) ⋆ bshare b qh kN t)
    fun _ h => of_eq (by ac_rfl) (sep_mono_right (R := bshare b qh kN t ⋆ bshare b q' kN t)
      (fun _ x => (bshare_split hqh hq).mp x) h)) ?_
  refine EUpd.trans (EUpd.frame (EUpd.lendT hk)) ?_
  exact EUpd.of_imp fun _ h => sep_assoc h

/-- **A growth's extent part, from a part of the share**: the client gives back the part `q'` of
the grant's share `q`; the grant's receipt splits (`brcpt_split`), the part `q'` is lent again at
the new end (`ledger_regrow_core`), and the two receipts join at the lower bound (`EUpd.rjoin`). -/
theorem ledger_regrow_rcpt {γ e : Nat} {M : GMap} {t : STag} {b : BlockId} {q q' qh : Frac}
    {k₀ k k' kN : Nat} (hq : q'.val ≤ q.val) (hk : k' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ ((bshare b q' k₀ (some (γ, e)) ⋆ brcpt b q k γ e) ⋆ bshare b qh kN t))
      (gauthP γ e M t ⋆ ((bshare b q' k' (some (γ, e)) ⋆ FAssn.ex fun k₁ => brcpt b q k₁ γ e) ⋆
        bshare b qh kN t)) := by
  by_cases hqq : q'.val = q.val
  · obtain rfl : q' = q := Frac.eq hqq
    exact EUpd.trans (ledger_regrow_core hk) (EUpd.of_imp fun _ h => sep_mono_right (fun _ x =>
      sep_mono_left (fun _ y => sep_mono_right (fun _ z => ⟨kN, z⟩) y) x) h)
  have hlt : q'.val < q.val := Rat.lt_of_le_of_ne hq hqq
  have hd := Frac.diff_pos hlt
  refine EUpd.withFact (φ := 0 < q'.val) (fun _ r _ _ h _ => ?_) fun hq' => ?_
  · obtain ⟨_, _, -, -, -, _, _, -, -, ⟨_, _, -, -, h1, -⟩, -⟩ := h
    exact h1.1
  have e1 : brcpt b q k γ e = brcpt b (q'.add (q.diff q' (Rat.le_of_lt hlt))) k γ e := by
    rw [Frac.add_diff]
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ ((bshare b q' k₀ (some (γ, e)) ⋆
      brcpt b q' k γ e) ⋆ bshare b qh kN t)) ⋆ brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)
    fun _ h => ?_) ?_
  · rw [e1] at h
    have h := sep_mono_right (R := (bshare b q' k₀ (some (γ, e)) ⋆ (brcpt b q' k γ e ⋆
      brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)) ⋆ bshare b qh kN t)
      (fun _ x => sep_mono_left (Q := bshare b q' k₀ (some (γ, e)) ⋆ (brcpt b q' k γ e ⋆
        brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)) (fun _ y => sep_mono_right
        (R := brcpt b q' k γ e ⋆ brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e)
        (fun _ z => (brcpt_split hq' hd).mp z) y) x) h
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (ledger_regrow_core hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (brcpt b q' kN γ e ⋆ brcpt b (q.diff q' (Rat.le_of_lt hlt)) k γ e) ⋆
    (gauthP γ e M t ⋆ (bshare b q' k' (some (γ, e)) ⋆ bshare b qh kN t))) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.rjoin) ?_
  refine EUpd.of_imp fun _ h => ?_
  rw [Frac.add_diff] at h
  have h := sep_mono_left (Q := FAssn.ex fun k₁ => brcpt b q k₁ γ e) (fun _ x => ⟨_, x⟩) h
  exact of_eq (by ac_rfl) h

/-- **A grant grows** within a block whose share `qh` at `kN` (at or past the new end) the
allocator keeps: the client's part `q'` of the share is re-lent at the new end
(`ledger_regrow_rcpt`), the grant is re-pointed at the new length (with the kind label `K'` of the
bytes it gets). -/
theorem ledger_regrow {γ e i : Nat} {M : GMap} {t : STag} {p N : Ptr} {n n' kN : Nat}
    {q q' qh φ : Frac} {A : Nat} {K K' : BlockKind} (hq : q'.val ≤ q.val) (hpN : p.block = N.block)
    (hk : p.off.toNat + n' ≤ kN) :
    EUpd (gauthP γ e M t ⋆ (gfrag γ e i (p, n, q, A, K, φ) ⋆ (pshare p q' (p.off.toNat + n) (some (γ, e)) ⋆
        (LedgerRcpts γ e M ⋆ pshare N qh kN t))))
      (gauthP γ e (M.set i (some (p, n', q, A, K', φ))) t ⋆ (gfrag γ e i (p, n', q, A, K', φ) ⋆
        (pshare p q' (p.off.toNat + n') (some (γ, e)) ⋆
          (LedgerRcpts γ e (M.set i (some (p, n', q, A, K', φ))) ⋆ pshare N qh kN t)))) := by
  refine EUpd.withFact ledger_grant_fact fun hM => ?_
  have hM' : (M.set i none) i = none := GMap.set_same M i none
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
      ((gauthP γ e M t ⋆ ((bshare b q' (p.off.toNat + n) (some (γ, e)) ⋆ brcpt b q k γ e) ⋆
        bshare b qh kN t)) ⋆ (gfrag γ e i (p, n, q, A, K, φ) ⋆
          (LedgerRcpts γ e (M.set i none) ⋆ epFee γ e φ))))
      fun r h => ?_) (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hb => ?_)
  · obtain ⟨b, k, hb, h⟩ := ledgerRcpts_open (X := gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ) ⋆
      pshare N qh kN t) hM (of_eq (by ac_rfl) h)
    have hbN : N.block = some b := hpN ▸ hb
    have h := of_eq (Q := pshare N qh kN t ⋆ ((bshare b q' (p.off.toNat + n) (some (γ, e)) ⋆
      brcpt b q k γ e) ⋆ (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ) ⋆
        (LedgerRcpts γ e (M.set i none) ⋆ epFee γ e φ))))
      (by ac_rfl) h
    exact ⟨b, k, sep_lift.mpr ⟨hb, of_eq (by ac_rfl) (sep_mono_left (Q := bshare b qh kN t)
      (fun _ x => (pshare_iff hbN).mp x) h)⟩⟩
  have hbN : N.block = some b := hpN ▸ hb
  refine EUpd.trans (EUpd.frame (ledger_regrow_rcpt (k' := p.off.toNat + n') hq hk)) ?_
  refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e M t ⋆ gfrag γ e i (p, n, q, A, K, φ)) ⋆
      (bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆ (ledgerRcpt γ e (some (p, n', q, A, K', φ)) ⋆
        (LedgerRcpts γ e (M.set i none) ⋆ bshare b qh kN t)))) fun _ h => ?_) ?_
  · have h := of_eq (Q := (FAssn.ex fun k₁ => brcpt b q k₁ γ e) ⋆ (epFee γ e φ ⋆ ((gauthP γ e M t ⋆
      gfrag γ e i (p, n, q, A, K, φ)) ⋆ (bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆
        (LedgerRcpts γ e (M.set i none) ⋆ bshare b qh kN t))))) (by ac_rfl) h
    obtain ⟨k₁, h⟩ := sep_ex.mp h
    have h := sep_mono_left (Q := ledgerRcpt γ e (some (p, n', q, A, K', φ)))
      (fun _ x => sep_mono_left (Q := FAssn.ex fun b' => FAssn.ex fun k' => ⟪p.block = some b'⟫ ⋆
        brcpt b' q k' γ e) (fun _ y => ⟨b, k₁, sep_lift.mpr ⟨hb, y⟩⟩) x) (sep_assoc' h)
    exact of_eq (by ac_rfl) h
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.reassign (p, n', q, A, K', φ)))) ?_
  refine EUpd.of_imp fun _ h => ?_
  have h := of_eq (Q := (ledgerRcpt γ e (some (p, n', q, A, K', φ)) ⋆ LedgerRcpts γ e (M.set i none)) ⋆
    ((gauthP γ e (M.set i (some (p, n', q, A, K', φ))) t ⋆ gfrag γ e i (p, n', q, A, K', φ)) ⋆
      bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆ bshare b qh kN t)) (by ac_rfl) h
  have h := sep_mono_left (Q := LedgerRcpts γ e ((M.set i none).set i (some (p, n', q, A, K', φ))))
    (fun _ x => ledgerRcpts_put hM' x) h
  rw [GMap.set_set] at h
  have h := of_eq (Q := bshare b q' (p.off.toNat + n') (some (γ, e)) ⋆ (bshare b qh kN t ⋆
    (LedgerRcpts γ e (M.set i (some (p, n', q, A, K', φ))) ⋆
      (gauthP γ e (M.set i (some (p, n', q, A, K', φ))) t ⋆ gfrag γ e i (p, n', q, A, K', φ))))) (by ac_rfl) h
  have h := sep_mono_left (Q := pshare p q' (p.off.toNat + n') (some (γ, e)))
    (fun _ x => (pshare_iff hb).mpr x) h
  have h := sep_mono_right (R := pshare N qh kN t ⋆ (LedgerRcpts γ e (M.set i (some (p, n', q, A, K', φ))) ⋆
    (gauthP γ e (M.set i (some (p, n', q, A, K', φ))) t ⋆ gfrag γ e i (p, n', q, A, K', φ))))
    (fun _ x => sep_mono_left (Q := pshare N qh kN t) (fun _ y => (pshare_iff hbN).mpr y) x) h
  exact of_eq (by ac_rfl) h

/-! ## The whole epoch token, and the bump of a reset -/

/-- **The whole epoch token shows that no grant is outstanding** (`gauth_epTok_whole`): the
allocator keeps each grant's fee, a nonzero part of the epoch token, with its receipt. -/
theorem ledgerRcpts_epTok_empty {γ e : Nat} {M : GMap} {t : STag} {X : FAssn} :
    ∀ m r rF, Holds m r rF → (((gauthP γ e M t ⋆ LedgerRcpts γ e M) ⋆ epTok γ e Frac.one) ⋆ X) r →
      m.FSeq → M = GMap.empty := by
  intro m r rF hh hp _
  funext i
  cases hM : M i with
  | none => rfl
  | some g =>
    exfalso
    obtain ⟨p, n, q, A, K, φ⟩ := g
    have h1 : (((gauthP γ e M t ⋆ (ledgerRcpt γ e (some (p, n, q, A, K, φ)) ⋆
        LedgerRcpts γ e (M.set i none))) ⋆ epTok γ e Frac.one) ⋆ X) r :=
      sep_mono_left (fun _ x => sep_mono_left (fun _ y => sep_mono_right
        (fun _ z => ledgerRcpts_pick hM z) y) x) hp
    have h2 := of_eq (Q := ⟪0 < φ.val⟫ ⋆ ((gauthP γ e M t ⋆ (epTok γ e Frac.one ⋆ epTok γ e φ)) ⋆
      (((FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆ brcpt b q k γ e) ⋆
        LedgerRcpts γ e (M.set i none)) ⋆ X))) (by simp only [ledgerRcpt, epFee]; ac_rfl) h1
    obtain ⟨hφ, h2⟩ := sep_lift.mp h2
    obtain ⟨r₁, r₂, -, rfl, h3, -⟩ := h2
    have h0 := gauth_epTok_whole h3 (Ghost.Ok.assoc.mp hh.ghost.1)
    rw [h0] at hφ
    simp at hφ

/-- **The bump of a reset** (`Upd.bump`): with no grant, the ledger moves to the next epoch and
the whole token of the old epoch becomes the whole token of the new one. -/
theorem ledger_bump {γ e : Nat} {t : STag} :
    EUpd ((gauthP γ e GMap.empty t ⋆ LedgerRcpts γ e GMap.empty) ⋆ epTok γ e Frac.one)
      ((gauthP γ (e + 1) GMap.empty t ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
        epTok γ (e + 1) Frac.one) := by
  rw [ledgerRcpts_empty, ledgerRcpts_empty, sep_emp_eq, sep_emp_eq]
  refine EUpd.trans EUpd.dropEp ?_
  exact EUpd.of_upd Upd.bump

/-! ## Revoking the receipts of a past epoch -/

/-- A grant's receipt, revoked: a share tagged `t` at the receipt's bound. -/
def ledgerRevoked (t : STag) : Option GRegion → FAssn
  | none => FAssn.emp
  | some (p, _, q, _, _, _) => FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆ bshare b q k t

/-- **Revoke every receipt** of a past epoch `e` under the ledger at epoch `e'` (`EUpd.revoke`);
the fees of the past epoch are dropped. -/
theorem ledgerRcpts_revoke {γ e e' : Nat} {M M' : GMap} {t : STag} (he : e < e') :
    ∀ N : Nat, EUpd (gauthP γ e' M' t ⋆ sepN N (fun i => ledgerRcpt γ e (M i)))
      (gauthP γ e' M' t ⋆ sepN N (fun i => ledgerRevoked t (M i)))
  | 0 => EUpd.of_imp fun _ h => h
  | N + 1 => by
    simp only [sepN]
    refine EUpd.trans (EUpd.of_imp (P' := (gauthP γ e' M' t ⋆ ledgerRcpt γ e (M N)) ⋆
      sepN N (fun i => ledgerRcpt γ e (M i))) fun _ h => sep_assoc' h) ?_
    refine EUpd.trans (EUpd.frame (P' := gauthP γ e' M' t ⋆ ledgerRevoked t (M N)) ?_) ?_
    · cases hM : M N with
      | none => exact EUpd.of_imp fun _ h => h
      | some g =>
        obtain ⟨p, n, q, A, K, φ⟩ := g
        simp only [ledgerRcpt, ledgerRevoked]
        refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc' h)
          (EUpd.trans (EUpd.drop fun _ h => epFee_ghost h) ?_)
        refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => FAssn.ex fun k => ⟪p.block = some b⟫ ⋆
          (gauthP γ e' M' t ⋆ brcpt b q k γ e)) fun _ h => ?_)
          (EUpd.exAll fun b => EUpd.exAll fun k => EUpd.lift fun hb => ?_)
        · obtain ⟨b, h⟩ := sep_exR h
          obtain ⟨k, h⟩ := sep_exR h
          exact ⟨b, k, of_eq (by ac_rfl) h⟩
        · refine EUpd.trans (EUpd.revoke he) (EUpd.of_imp fun _ h => ?_)
          exact sep_mono_right (fun _ x => ⟨b, k, sep_lift.mpr ⟨hb, x⟩⟩) h
    refine EUpd.trans (EUpd.of_imp (P' := ledgerRevoked t (M N) ⋆ (gauthP γ e' M' t ⋆
      sepN N (fun i => ledgerRcpt γ e (M i)))) fun _ h => of_eq (by ac_rfl) h) ?_
    refine EUpd.trans (EUpd.frameL (ledgerRcpts_revoke he N)) ?_
    exact EUpd.of_imp fun _ h => of_eq (by ac_rfl) h

/-- A grant's fraction on block `b`. -/
def grantOn (b : BlockId) : Option GRegion → Rat
  | some (p, _, q, _, _, _) => if p.block = some b then q.val else 0
  | none => 0

/-- The grants' fractions on block `b` (ids below `N`). -/
def grantsOn (b : BlockId) (M : GMap) (N : Nat) : Rat := esum (fun i => grantOn b (M i)) N

/-- Resources that own no bytes and no knowledge (the fees of `ledgerRcpts_list`'s grants). -/
def NoBytes : FAssn := fun r => r.heap = FHeap.empty ∧ r.know = Know.none

theorem noBytes_sep {r : Res} (h : (NoBytes ⋆ NoBytes) r) : NoBytes r := by
  obtain ⟨r1, r2, -, rfl, ⟨h1, k1⟩, ⟨h2, k2⟩⟩ := h
  show FHeap.union r1.heap r2.heap = FHeap.empty ∧ r1.know.union r2.know = Know.none
  rw [h1, h2, k1, k2]; exact ⟨FHeap.union_empty _, Know.union_none _⟩

/-- The receipts of a grant map as a list of pieces, with the grants' fractions per block, and
their fees. -/
theorem ledgerRcpts_list {γ e : Nat} {M : GMap} :
    ∀ N {r : Res}, sepN N (fun i => ledgerRcpt γ e (M i)) r →
      ∃ l, (∀ b, sumOn b l = esum (fun i => grantOn b (M i)) N) ∧ (rcptsL γ e l ⋆ NoBytes) r
  | 0, _, h => ⟨[], fun b => by simp [sumOn, esum],
    sep_mono_right (fun _ x => ⟨x.1, x.2.1⟩) (sep_emp.mpr h)⟩
  | N + 1, _, h => by
    obtain ⟨r1, r2, hd, rfl, h1, h2⟩ := h
    obtain ⟨l, hl, h2⟩ := ledgerRcpts_list N h2
    cases hM : M N with
    | none =>
      simp only [hM, ledgerRcpt] at h1
      exact ⟨l, fun b => by simp only [esum, hM, grantOn, hl b]; grind,
        of_eq (Full.emp_sep_eq _) ⟨r1, r2, hd, rfl, h1, h2⟩⟩
    | some g =>
      obtain ⟨p, n, q, A, K, φ⟩ := g
      simp only [hM, ledgerRcpt] at h1
      obtain ⟨b', h1⟩ := sep_ex.mp h1
      obtain ⟨k, h1⟩ := sep_ex.mp h1
      obtain ⟨hb', h1⟩ := sep_lift.mp (sep_assoc h1)
      have h3 : ((brcpt b' q k γ e ⋆ epFee γ e φ) ⋆ (rcptsL γ e l ⋆ NoBytes)) _ :=
        ⟨r1, r2, hd, rfl, h1, h2⟩
      have h3 := of_eq (Q := (brcpt b' q k γ e ⋆ rcptsL γ e l) ⋆ (epFee γ e φ ⋆ NoBytes))
        (by ac_rfl) h3
      refine ⟨(b', q, k) :: l, fun b => ?_,
        sep_mono_right (fun _ x => noBytes_sep (sep_mono_left (Q := NoBytes)
          (fun _ y => epFee_ghost y) x)) h3⟩
      simp only [sumOn, esum, hM, grantOn, hb', hl b, Option.some.injEq]
      grind

theorem esum_stable {f : Nat → Rat} {N : Nat} (h : ∀ j, N ≤ j → f j = 0) :
    ∀ d, esum f (N + d) = esum f N
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc]; simp only [esum]; rw [esum_stable h d, h _ (by omega)]; grind

/-- The grants' fractions do not depend on the bound past the map's support. -/
theorem grantsOn_bound {M : GMap} {N N' : Nat} (h : ∀ j, N ≤ j → M j = none)
    (h' : ∀ j, N' ≤ j → M j = none) (b : BlockId) :
    esum (fun i => grantOn b (M i)) N = grantsOn b M N' := by
  have e1 := esum_stable (f := fun i => grantOn b (M i)) (N := N)
    (fun j hj => by simp [h j hj, grantOn]) N'
  have e2 := esum_stable (f := fun i => grantOn b (M i)) (N := N')
    (fun j hj => by simp [h' j hj, grantOn]) N
  rw [grantsOn, ← e1, ← e2, Nat.add_comm]

/-! ## Allocators with a reset ledger -/

/-- The token of a grant of the ledger `γ` at epoch `e`: it names the grant with its fraction, its
cells' labels and its fee (`FAllocInv.tok`'s shape). -/
def ledgerTok (γ e : Nat) (p : Ptr) (n _k A _S : Nat) (K : BlockKind) (q φ : Frac) : FAssn :=
  FAssn.ex fun i => gfrag γ e i (p, n, q, A, K, φ)

/-- An allocator state that is a ledger next to the allocator's own resources: variables `w`
with their facts `F w`, the ledger's authority over the grant map `M w` with the receipts, and the
rest `B w`. -/
def LedgerOwn {W : Type} (γ e : Nat) (t : STag) (M : W → GMap) (F : W → Prop) (B : W → FAssn) :
    FAssn :=
  FAssn.ex fun w => ⟪F w⟫ ⋆ ((gauthP γ e (M w) t ⋆ LedgerRcpts γ e (M w)) ⋆ B w)

/-- **The state next to the whole epoch token has no grant** (`ledgerRcpts_epTok_empty`). -/
theorem ledgerOwn_epTok_empty {W : Type} {γ e : Nat} {t : STag} {M : W → GMap} {F : W → Prop}
    {B : W → FAssn} :
    EUpd (LedgerOwn γ e t M F B ⋆ epTok γ e Frac.one)
      ((FAssn.ex fun w => ⟪F w ∧ M w = GMap.empty⟫ ⋆
        ((gauthP γ e (M w) t ⋆ LedgerRcpts γ e (M w)) ⋆ B w)) ⋆ epTok γ e Frac.one) := by
  unfold LedgerOwn
  refine EUpd.ex fun w => EUpd.withFact (φ := M w = GMap.empty) (fun m r rF hh hp hs => ?_)
    fun hM => EUpd.of_imp fun r h => ?_
  · obtain ⟨-, hp⟩ := sep_lift.mp (sep_assoc hp)
    exact ledgerRcpts_epTok_empty (X := B w) m r rF hh (of_eq (by ac_rfl) hp) hs
  · obtain ⟨hf, h⟩ := sep_lift.mp (sep_assoc h)
    exact sep_mono_left (fun _ x => ⟨w, sep_lift.mpr ⟨⟨hf, hM⟩, x⟩⟩) h

/-- **A reset's ledger part**: the state next to the whole epoch token has no grant, and its ledger
moves to the next epoch with the whole token of that epoch (`ledgerOwn_epTok_empty`,
`ledger_bump`). The allocator's own resources `B w` stay as they were (of the past epoch); the
ledger at `e + 1` revokes what they lent (`EUpd.revoke`, `EUpd.prevokeC`). -/
theorem ledgerOwn_bump {W : Type} {γ e : Nat} {t : STag} {M : W → GMap} {F : W → Prop}
    {B : W → FAssn} :
    EUpd (LedgerOwn γ e t M F B ⋆ epTok γ e Frac.one)
      (FAssn.ex fun w => ⟪F w ∧ M w = GMap.empty⟫ ⋆
        (((gauthP γ (e + 1) GMap.empty t ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
          epTok γ (e + 1) Frac.one) ⋆ B w)) := by
  refine EUpd.trans ledgerOwn_epTok_empty ?_
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun w => (⟪F w ∧ M w = GMap.empty⟫ ⋆
      ((gauthP γ e (M w) t ⋆ LedgerRcpts γ e (M w)) ⋆ B w)) ⋆ epTok γ e Frac.one)
    fun _ h => sep_ex.mp h) (EUpd.exAll fun w => ?_)
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun ⟨hf, hM⟩ => ?_)
  rw [hM]
  refine EUpd.trans (EUpd.of_imp (P' := ((gauthP γ e GMap.empty t ⋆ LedgerRcpts γ e GMap.empty) ⋆
    epTok γ e Frac.one) ⋆ B w) fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame ledger_bump) ?_
  exact EUpd.of_imp fun _ h => ⟨w, sep_lift.mpr ⟨⟨hf, hM⟩, h⟩⟩

/-- **An allocator invariant with a reset ledger** (module doc): its state is `LedgerOwn` over its
variables, its token names a grant of the ledger (`ledgerTok`), its fee is a part of the epoch token
(`epFee`), and a grant can be given back without running code (`ret`: its bytes go back to the
allocator, the client gets the fee back). -/
structure ResetLedger (I : FAllocInv) (γ e : Nat) where
  /-- The allocator's variables. -/
  W : Type
  /-- Their grant map. -/
  M : W → GMap
  /-- Their facts. -/
  F : W → Prop
  /-- The allocator's resources besides the ledger's authority and receipts. -/
  B : W → FAssn
  /-- The ledger's parent tag. -/
  t : STag
  own_eq : I.own = LedgerOwn γ e t M F B
  tok_eq : I.tok = ledgerTok γ e
  fee_eq : I.fee = epFee γ e
  /-- Giving a grant back (`grant_return` of the arena). -/
  ret : ∀ (s : Slice) (k : Nat) (φ : Frac) (bs : Array Byte), s.len.toNat = bs.size → 0 < bs.size →
    EUpd (I.own ⋆ I.granted s.ptr k φ bs) (I.own ⋆ I.fee φ)

namespace ResetLedger

variable {I : FAllocInv} {γ e : Nat}

/-- **The state next to the whole epoch token has no grant.** -/
theorem own_epTok_empty (L : ResetLedger I γ e) :
    EUpd (I.own ⋆ epTok γ e Frac.one)
      ((FAssn.ex fun w => ⟪L.F w ∧ L.M w = GMap.empty⟫ ⋆
        ((gauthP γ e (L.M w) L.t ⋆ LedgerRcpts γ e (L.M w)) ⋆ L.B w)) ⋆ epTok γ e Frac.one) := by
  rw [L.own_eq]; exact ledgerOwn_epTok_empty

/-- **A client with an outstanding grant does not hold the whole epoch token**: the grant's token
names a grant of the map (`gfrag_mem`), which the whole token excludes (`own_epTok_empty`). -/
theorem granted_epTok_false (L : ResetLedger I γ e) {p : Ptr} {k : Nat} {φ : Frac} {bs : Array Byte} {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hs : m.FSeq)
    (h : ((I.own ⋆ epTok γ e Frac.one) ⋆ I.granted p k φ bs) r) : False := by
  obtain ⟨r', hh', h'⟩ := EUpd.frame L.own_epTok_empty m r rF hh h hs
  obtain ⟨r1, r2, hd, rfl, h1, h2⟩ := h'
  obtain ⟨w, h1⟩ := sep_ex.mp h1
  obtain ⟨⟨-, hM⟩, h1⟩ := sep_lift.mp (sep_assoc h1)
  obtain ⟨A, S, K, q, h2⟩ := h2
  rw [L.tok_eq] at h2
  obtain ⟨i, h2⟩ := sep_ex.mp (of_eq (sep_left_comm_eq _ _ _) h2)
  have h3 : ((((gauthP γ e (L.M w) L.t ⋆ LedgerRcpts γ e (L.M w)) ⋆ L.B w) ⋆ epTok γ e Frac.one) ⋆
      (gfrag γ e i (p, bs.size, q, A, K, φ) ⋆ (up (regionIn p A S K (2 ^ k) bs) ⋆
        (pshare p q (p.off.toNat + bs.size) I.tag ⋆
          pclaim p p.off.toNat (p.off.toNat + bs.size) I.tag)))) _ :=
    ⟨r1, r2, hd, rfl, h1, h2⟩
  have hi := ledger_grant_fact (M := L.M w) (t := L.t) (i := i) (g := (p, bs.size, q, A, K, φ))
    (X := ((LedgerRcpts γ e (L.M w) ⋆ L.B w) ⋆ epTok γ e Frac.one) ⋆
      (up (regionIn p A S K (2 ^ k) bs) ⋆ (pshare p q (p.off.toNat + bs.size) I.tag ⋆
        pclaim p p.off.toNat (p.off.toNat + bs.size) I.tag)))
    m _ rF hh' (of_eq (by ac_rfl) h3) hs
  rw [hM] at hi
  cases hi

/-- **A reset's ledger part** for the allocator's state (`ledgerOwn_bump`). -/
theorem own_bump (L : ResetLedger I γ e) :
    EUpd (I.own ⋆ epTok γ e Frac.one)
      (FAssn.ex fun w => ⟪L.F w ∧ L.M w = GMap.empty⟫ ⋆
        (((gauthP γ (e + 1) GMap.empty L.t ⋆ LedgerRcpts γ (e + 1) GMap.empty) ⋆
          epTok γ (e + 1) Frac.one) ⋆ L.B w)) := by
  rw [L.own_eq]; exact ledgerOwn_bump

end ResetLedger

end Full
end Zig
