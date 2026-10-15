import ZigLean.Sep.Full.Thread
import ZigLean.Conc.Call
import ZigLean.Conc.AtomicWord
import ZigLean.Conc.PtrAtomic
import ZigLean.Sep.AllocSpec.Norm

/-!
# Full-state triples for calls of concurrent functions

A concurrent function (`ConcM`, a tree of sync ops) runs in the calling thread. `CTriple P x Q`
(`docs/sep-threads.md` §Decision R2) is a thread triple over the run tree `x n m`, stop by stop
(`CTriple.Run`): from every memory in which the thread owns `P` (`Holds`, `Mem.FConc`,
`Mem.Owns`, as `FTTriple`), each segment up to the next stop or the result keeps the frame and
races with nothing (`FStepIn`); at a stop the thread holds some part, and it goes on in **every**
memory in which it still owns that part (other threads ran) with **every** answer that memory
allows (`Sched.soloAnswer`: every choice of a `pick`, as `Proto.Step`). A stop that one thread
does not answer itself (a spawn, a join, a futex wait or wake, a gate, an async choice) fails
closed: such functions need the protocol logic (`Proto.WP`).

- **One logic.** `CTriple.toSolo`: the old reading, the call read in the caller's thread
  (`Sched.soloRun fuel x`, each stop answered in the memory it stopped with, the oracle's choice
  `0`), is a sequential `FTriple`. `WP.call_fowned` (`ThreadCall.lean`) runs a `CTriple` inside a
  protocol (`Proto.WP`).
- **Rules** follow the generated code: `bind`, `liftMem` (an `FTTriple` of the `MemM` part),
  `pick_bind` (every choice of the oracle), `sync_bind`, and the structural rules.
- **Loops**: `CTriple.loop`, the invariant rule for `Zig.loop` (partial correctness: no
  measure), by induction on the depth and fixpoint induction on the root of the run tree
  (`Sched.admissible_root`). `CTriple P · Q` itself is not admissible (the parts at a stop of
  the elements of a chain need not have a common one), so there is no general rule for recursive
  groups yet. `admissible_solo` is the admissibility of the in-thread reading.

The `cnorm` simp set pushes `StateT.run` through the body monad `CM` of a generated concurrent
function (as `fsym_norm` does for `MM`).
-/

namespace Zig
namespace Sched

open Lean.Order

variable {Tgt α β γ : Type}

/-- The in-thread reading of a run (module doc): a stop at a non-solo op fails closed. -/
def soloTree : {n : Nat} → CoN Tgt (α × Mem) n → Out α
  | _, .leaf r => r
  | _, .sync op m k => match soloResp op with
    | some ρ => soloTree (k ρ m)
    | none => some (.error .illegal)

theorem soloTree_some {n : Nat} {op : SyncOp Tgt} {m : Mem} {k : op.Resp → Mem → CoN Tgt (α × Mem) n}
    {ρ : op.Resp} (h : soloResp op = some ρ) : soloTree (.sync op m k) = soloTree (k ρ m) := by
  simp only [soloTree, h]

theorem soloTree_none {n : Nat} {op : SyncOp Tgt} {m : Mem} {k : op.Resp → Mem → CoN Tgt (α × Mem) n}
    (h : soloResp op = none) : soloTree (.sync op m k) = some (.error .illegal) := by
  simp only [soloTree, h]

/-- A call of `x` read in the caller's thread, at depth `fuel`. -/
def soloRun (fuel : Nat) (x : ConcM Tgt α) : MemM α := fun m => ExceptT.mk (soloTree (x fuel m))

theorem soloTree_bind : ∀ {n : Nat} (t : CoN Tgt (γ × Mem) n)
    (G : γ × Mem → (k : Nat) → CoN Tgt (α × Mem) k),
    (soloTree t = none ∧ soloTree (t.bind G) = none) ∨
    (∃ e, soloTree t = some (.error e) ∧ soloTree (t.bind G) = some (.error e)) ∨
    (∃ b k, soloTree t = some (.ok b) ∧ soloTree (t.bind G) = soloTree (G b k))
  | _, .leaf none, _ => .inl ⟨rfl, rfl⟩
  | _, .leaf (some (.error e)), _ => .inr (.inl ⟨e, rfl, rfl⟩)
  | n, .leaf (some (.ok b)), _ => .inr (.inr ⟨b, n, rfl, rfl⟩)
  | _, .sync op m k, G => by
    cases h : soloResp op with
    | none => exact .inr (.inl ⟨.illegal, soloTree_none h, soloTree_none h⟩)
    | some ρ =>
      rw [soloTree_some h]
      exact (soloTree_some (k := fun r m => (k r m).bind G) h).symm ▸ soloTree_bind (k ρ m) G

/-- The in-thread reading of a chain's least upper bound is unknown (`none`) or the reading of an
element of the chain: at each sync op the reading follows one response, and the sup's rest there
is the sup of the elements' rests. -/
theorem soloTree_sup : ∀ {n : Nat} (s : CoN Tgt (α × Mem) n) {c : CoN Tgt (α × Mem) n → Prop},
    is_sup c s → soloTree s = none ∨ ∃ x, c x ∧ soloTree x = soloTree s
  | _, .leaf none, _, _ => .inl rfl
  | _, .leaf (some r), c, hs => by
    refine .inr (Classical.byContradiction fun hne => ?_)
    have hub : ∀ y, c y → y ⊑ CoN.leaf none := by
      intro y hy
      have hys : CoN.le y (.leaf (some r)) := (hs _).mp (PartialOrder.rel_refl) y hy
      cases hys with
      | bot => exact CoN.le.bot _
      | leaf => exact absurd ⟨_, hy, rfl⟩ hne
    have := (hs _).mpr hub
    cases this
  | _, .sync op m₀ k, c, hs => by
    classical
    have hup : ∀ y, c y → CoN.le y (.sync op m₀ k) := fun y hy => (hs _).mp PartialOrder.rel_refl y hy
    cases hρ : soloResp op with
    | none =>
      -- A non-solo stop fails closed; some element of the chain is a stop there too.
      refine .inr (Classical.byContradiction fun hne => ?_)
      have hub : ∀ y, c y → y ⊑ CoN.leaf none := by
        intro y hy
        rcases CoN.le_of_le_sync (hup y hy) with e | ⟨k', e, -⟩
        · subst e; exact CoN.le.bot _
        · subst e
          exact absurd ⟨_, hy, by rw [soloTree_none hρ, soloTree_none hρ]⟩ hne
      have := (hs _).mpr hub
      cases this
    | some ρ =>
      rw [soloTree_some hρ]
      let c' : CoN Tgt (α × Mem) _ → Prop := fun z => ∃ k', c (.sync op m₀ k') ∧ z = k' ρ m₀
      have hsup' : is_sup c' (k ρ m₀) := by
        intro u
        constructor
        · rintro hu _ ⟨k', hk', rfl⟩
          obtain ⟨k'', e, h⟩ := CoN.le_sync (hup _ hk')
          cases e
          exact PartialOrder.rel_trans (h ρ m₀) hu
        · intro hu
          let kz : op.Resp → Mem → CoN Tgt (α × Mem) _ := fun r m => if r = ρ ∧ m = m₀ then u else k r m
          have hz : ∀ y, c y → y ⊑ CoN.sync op m₀ kz := by
            intro y hy
            rcases CoN.le_of_le_sync (hup y hy) with e | ⟨k', e, h⟩
            · subst e; exact CoN.le.bot _
            · subst e
              refine CoN.le.sync op m₀ k' kz fun r m => ?_
              by_cases hrm : r = ρ ∧ m = m₀
              · obtain ⟨rfl, rfl⟩ := hrm
                simp only [kz, and_self, ↓reduceIte]
                exact hu _ ⟨k', hy, rfl⟩
              · simp only [kz, hrm, ↓reduceIte]; exact h r m
          obtain ⟨k₂, e, h⟩ := CoN.le_sync ((hs _).mpr hz)
          cases e
          have := h ρ m₀
          simp only [kz, and_self, ↓reduceIte] at this
          exact this
      rcases soloTree_sup (k ρ m₀) hsup' with h | ⟨_, ⟨k', hk', rfl⟩, h⟩
      · exact .inl h
      · exact .inr ⟨_, hk', by rw [soloTree_some hρ]; exact h⟩

/-- The responses with which a thread goes on at a solo stop, in the memory `m` it goes on in
(as `Proto.Step` answers them): `()` at a `yield`, every choice of a `choose n` or of a
`pick count` (`c < n`; `0` when there is none). Another op has none. -/
def soloAnswer : (op : SyncOp Tgt) → Mem → op.Resp → Prop
  | .yield, _, _ => True
  | .choose n, _, c => @LT.lt Nat _ c n ∨ n = 0 ∧ @Eq Nat c 0
  | .pick count, m, c => @LT.lt Nat _ c (count m) ∨ count m = 0 ∧ @Eq Nat c 0
  | _, _, _ => False

/-- A solo op has the in-thread answer, and it is one of its answers in every memory. -/
theorem soloResp_of_solo {op : SyncOp Tgt} (h : SyncOp.Solo op = true) :
    ∃ ρ, soloResp op = some ρ ∧ ∀ m, soloAnswer op m ρ := by
  cases op with
  | yield => exact ⟨(), rfl, fun _ => by simp only [soloAnswer]⟩
  | choose n => exact ⟨(0 : Nat), rfl, fun _ => show (0 : Nat) < n ∨ n = 0 ∧ (0 : Nat) = 0 by omega⟩
  | pick count => exact ⟨(0 : Nat), rfl, fun m =>
      show (0 : Nat) < count m ∨ count m = 0 ∧ (0 : Nat) = 0 by omega⟩
  | _ => cases h

/-- The tree is a stop (`leaf none` at its root, "no result") or not: the root of a chain's least
upper bound is not a `leaf none` only if the root of an element is not. So a property of the
runs whose trees are not `leaf none` is admissible (the loop rule, `CTriple.loop`). -/
theorem admissible_root (Ψ : Nat → Mem → Prop) :
    admissible (fun x : ConcM Tgt α => ∀ n m, x n m = .leaf none ∨ Ψ n m) := by
  intro c hc h n m
  have hsup : is_sup (fun t : CoN Tgt (α × Mem) n => ∃ x, c x ∧ x n m = t) (CCPO.csup hc n m) := by
    have h2 := CCPO.csup_spec (chain_apply (chain_apply hc n) m)
    have e1 : CCPO.csup hc n m = CCPO.csup (chain_apply (chain_apply hc n) m) := by
      have e := (fun_csup_eq (β := fun n => Mem → CoN Tgt (α × Mem) n) c hc).symm
      rw [show CCPO.csup hc = fun_csup (β := fun n => Mem → CoN Tgt (α × Mem) n) c hc from e]
      unfold fun_csup
      rw [← fun_csup_eq]
      rfl
    rw [e1]
    intro u
    rw [h2 u]
    constructor
    · rintro hu _ ⟨x, hx, rfl⟩; exact hu _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro hu _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact hu _ ⟨x, hx, rfl⟩
  by_cases hall : ∀ x, c x → x n m = .leaf none
  · refine .inl ?_
    have hle : CCPO.csup hc n m ⊑ CoN.leaf none := (hsup _).mpr fun _ ⟨x, hx, e⟩ => by
      subst e; rw [hall x hx]; exact PartialOrder.rel_refl
    revert hle
    generalize CCPO.csup hc n m = t
    intro hle
    cases hle; rfl
  · obtain ⟨x, hne⟩ := Classical.not_forall.mp hall
    obtain ⟨hx, hne⟩ := Classical.not_imp.mp hne
    exact .inr ((h x hx n m).resolve_left hne)

end Sched

namespace Full

open Sched FAssn Lean.Order

variable {Tgt α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {x : ConcM Tgt α}

/-- **Partial correctness of the in-thread reading is admissible**: a property of `x` that only
looks at `soloTree (x n m)` and holds when it is unknown is kept by least upper bounds. This is
what fixpoint induction (`partial_fixpoint`'s `fixpoint_induct`) needs. -/
theorem admissible_solo (Φ : Nat → Mem → Out α → Prop) (hΦ : ∀ n m, Φ n m none) :
    admissible (fun x : ConcM Tgt α => ∀ n m, Φ n m (soloTree (x n m))) := by
  intro c hc h n m
  have hsup : is_sup (fun t : CoN Tgt (α × Mem) n => ∃ x, c x ∧ x n m = t) (CCPO.csup hc n m) := by
    have h2 := CCPO.csup_spec (chain_apply (chain_apply hc n) m)
    have e1 : CCPO.csup hc n m = CCPO.csup (chain_apply (chain_apply hc n) m) := by
      have e := (fun_csup_eq (β := fun n => Mem → CoN Tgt (α × Mem) n) c hc).symm
      rw [show CCPO.csup hc = fun_csup (β := fun n => Mem → CoN Tgt (α × Mem) n) c hc from e]
      unfold fun_csup
      rw [← fun_csup_eq]
      rfl
    rw [e1]
    intro u
    rw [h2 u]
    constructor
    · rintro hu _ ⟨x, hx, rfl⟩; exact hu _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro hu _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact hu _ ⟨x, hx, rfl⟩
  rcases soloTree_sup _ hsup with e | ⟨_, ⟨x, hx, rfl⟩, e⟩
  · rw [e]; exact hΦ n m
  · rw [← e]; exact h x hx n m

namespace CTriple

/-- **The run of a call, stop by stop** (module doc): the run tree `t` of thread `m₀.current`,
from the start `m₀` of its current segment, with the frame `rF` of that segment. A result
holds `Q`, the frame's bytes stay and the thread owns its part (`FTTriple`'s post, over the
segment). At a stop the thread holds a part `r'` and the segment's post; it goes on, in every
memory `m₂` and with every frame `rF₂` in which it still owns `r'`, with every answer that
`m₂` allows (`Sched.soloAnswer`), as such a run again. A stop at an op that one thread does not
answer itself (a spawn, a join, a futex, a gate, an async choice) fails closed. -/
def Run (Q : α → FAssn) : {n : Nat} → Mem → Res → CoN Tgt (α × Mem) n → Prop
  | _, _, _, .leaf none => True
  | _, _, _, .leaf (some (.error e)) => e = .stackOverflow
  | _, m₀, rF, .leaf (some (.ok (v, m'))) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
      m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m₀ m'
  | _, m₀, rF, .sync op m₁ k => SyncOp.Solo op = true ∧ ∃ r', Holds m₁ r' rF ∧ m₁.FConc ∧
      m₁.Owns m₁.current r'.heap.erase ∧ FStepIn rF.heap.erase m₀ m₁ ∧
      ∀ m₂ rF₂, m₂.current = m₁.current → Holds m₂ r' rF₂ → m₂.FConc →
        m₂.Owns m₂.current r'.heap.erase → ∀ ρ, soloAnswer op m₂ ρ →
          (soloResp op = some ρ ∨ m₂.MsgCov) → Run Q m₂ rF₂ (k ρ m₂)

end CTriple

/-- **A full-state triple for a call of a concurrent function** (module doc): from every memory
in which the thread owns `P`, the run of `x` at every depth is a `CTriple.Run`. -/
def CTriple (P : FAssn) (x : ConcM Tgt α) (Q : α → FAssn) : Prop :=
  ∀ n m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
    CTriple.Run Q m rF (x n m)

namespace CTriple

/-! ### The run, stop by stop -/

section Run

variable {γ : Type}

theorem Run.ok_iff {Q : α → FAssn} {m₀ m' : Mem} {rF : Res} {v : α} {n : Nat} :
    Run (Tgt := Tgt) (n := n) Q m₀ rF (.leaf (some (.ok (v, m')))) ↔ ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
      m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m₀ m' := by
  simp only [Run]

theorem Run.sync_iff {Q : α → FAssn} {m₀ m₁ : Mem} {rF : Res} {n : Nat} {op : SyncOp Tgt}
    {k : op.Resp → Mem → CoN Tgt (α × Mem) n} :
    Run Q m₀ rF (.sync op m₁ k) ↔ SyncOp.Solo op = true ∧ ∃ r', Holds m₁ r' rF ∧ m₁.FConc ∧
      m₁.Owns m₁.current r'.heap.erase ∧ FStepIn rF.heap.erase m₀ m₁ ∧
      ∀ m₂ rF₂, m₂.current = m₁.current → Holds m₂ r' rF₂ → m₂.FConc →
        m₂.Owns m₂.current r'.heap.erase → ∀ ρ, soloAnswer op m₂ ρ →
          (soloResp op = some ρ ∨ m₂.MsgCov) → Run Q m₂ rF₂ (k ρ m₂) := by
  simp only [Run]

theorem Run.mono {Q' : α → FAssn} (hq : ∀ v r, Q v r → Q' v r) :
    ∀ {n} (t : CoN Tgt (α × Mem) n) {m₀ : Mem} {rF : Res}, Run Q m₀ rF t → Run Q' m₀ rF t
  | _, .leaf none, _, _, _ => trivial
  | _, .leaf (some (.error _)), _, _, h => h
  | _, .leaf (some (.ok (_, _))), _, _, h => by
    obtain ⟨r', hh, h, hc⟩ := Run.ok_iff.mp h
    exact Run.ok_iff.mpr ⟨r', hh, hq _ _ h, hc⟩
  | _, .sync _ _ k, _, _, h => by
    obtain ⟨hs, r', hh, hc, ho, hst, hk⟩ := Run.sync_iff.mp h
    exact Run.sync_iff.mpr ⟨hs, r', hh, hc, ho, hst, fun m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm =>
      Run.mono hq (k ρ m₂) (hk m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm)⟩

/-- A step before the segment: the segment starts earlier. -/
theorem Run.prefix {n : Nat} {t : CoN Tgt (α × Mem) n} {m₀ m₁ : Mem} {rF : Res}
    (hs : FStepIn rF.heap.erase m₀ m₁) (h : Run Q m₁ rF t) : Run Q m₀ rF t := by
  cases t with
  | leaf o =>
    rcases o with _ | _ | ⟨_, _⟩
    · trivial
    · exact h
    · obtain ⟨r', hh, hq, hc, ho, hst⟩ := Run.ok_iff.mp h
      exact Run.ok_iff.mpr ⟨r', hh, hq, hc, ho, hs.trans hst⟩
  | sync _ _ _ =>
    obtain ⟨hso, r', hh, hc, ho, hst, hk⟩ := Run.sync_iff.mp h
    exact Run.sync_iff.mpr ⟨hso, r', hh, hc, ho, hs.trans hst, hk⟩

/-- **Sequencing**: the rest `F` of each result runs with the depth that is left (at most the
tree's), from the memory and the part of the result. -/
theorem Run.bind {S : β → FAssn} {F : γ × Mem → (k : Nat) → CoN Tgt (β × Mem) k} {Q : γ → FAssn} :
    ∀ {n} (t : CoN Tgt (γ × Mem) n) {m₀ : Mem} {rF : Res}, Run Q m₀ rF t →
    (∀ v m' k, k ≤ n → ∀ r' rF', Holds m' r' rF' → Q v r' → m'.FConc →
      m'.Owns m'.current r'.heap.erase → Run S m' rF' (F (v, m') k)) →
    Run S m₀ rF (t.bind F)
  | _, .leaf none, _, _, _, _ => trivial
  | _, .leaf (some (.error _)), _, _, h, _ => h
  | _, .leaf (some (.ok (v, m'))), _, _, h, hf => by
    obtain ⟨r', hh, hq, hc, ho, hst⟩ := Run.ok_iff.mp h
    exact Run.prefix hst (hf v m' _ (Nat.le_refl _) r' _ hh hq hc ho)
  | _, .sync _ _ k, _, _, h, hf => by
    obtain ⟨hs, r', hh, hc, ho, hst, hk⟩ := Run.sync_iff.mp h
    exact Run.sync_iff.mpr ⟨hs, r', hh, hc, ho, hst, fun m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm =>
      Run.bind (k ρ m₂) (hk m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm) fun v m' k hk' =>
        hf v m' k (Nat.le_succ_of_le hk')⟩

/-- **The frame rule**, stop by stop: a part `rR` that holds `R` and that the thread owns stays
in the thread's part through every segment and every stop. -/
theorem Run.frame {R : FAssn} {rR : Res} (hR : R rR) :
    ∀ {n} (t : CoN Tgt (α × Mem) n) {m₀ : Mem} {rF : Res}, FHeap.Disjoint rR.heap rF.heap →
    m₀.Owns m₀.current rR.heap.erase →
    Run Q m₀ ⟨rR.heap ∪ rF.heap, rR.know.union rF.know, rR.gh.add rF.gh⟩ t →
    Run (fun v => Q v ⋆ R) m₀ rF t
  | _, .leaf none, _, _, _, _, _ => trivial
  | _, .leaf (some (.error _)), _, _, _, _, h => h
  | _, .leaf (some (.ok (_, _))), _, _, hRF, hoR, h => by
    obtain ⟨r', hh, hq, hc, ho, hst⟩ := Run.ok_iff.mp h
    have hQR := (FHeap.disjoint_union_right.mp hh.disj).1
    refine Run.ok_iff.mpr ⟨_, Holds.join hQR hRF hh, ⟨r', rR, hQR, rfl, hq, hR⟩, hc, ?_,
      hst.weaken fun l hl => ?_⟩
    · show Mem.OwnsC _ _ _
      rw [FHeap.erase_union]
      exact Mem.OwnsC.union ho (Mem.Owns.fstepSelf hst hoR fun l hl => by
        simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all)
    · simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all
  | _, .sync _ _ k, _, _, hRF, hoR, h => by
    obtain ⟨hs, r', hh, hc, ho, hst, hk⟩ := Run.sync_iff.mp h
    have hQR := (FHeap.disjoint_union_right.mp hh.disj).1
    refine Run.sync_iff.mpr ⟨hs, _, Holds.join hQR hRF hh, hc, ?_, hst.weaken fun l hl => ?_,
      fun m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm => ?_⟩
    · show Mem.OwnsC _ _ _
      rw [FHeap.erase_union]
      exact Mem.OwnsC.union ho (Mem.Owns.fstepSelf hst hoR fun l hl => by
        simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all)
    · simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all
    · have ho2 : m₂.Owns m₂.current (r'.heap.erase ∪ rR.heap.erase) := by
        simpa using ho₂
      exact Run.frame hR (k ρ m₂) (FHeap.disjoint_union_left.mp hh₂.disj).2 (Mem.OwnsC.right ho2)
        (hk m₂ _ e (Holds.split hQR hh₂) hc₂ (Mem.OwnsC.left ho2) ρ hρ hm)

/-- An update of each result (`EUpd`, read in `m.noFp`). -/
theorem Run.eupd_post {Q' : α → FAssn} (hu : ∀ v, EUpd (Q v) (Q' v)) :
    ∀ {n} (t : CoN Tgt (α × Mem) n) {m₀ : Mem} {rF : Res}, Run Q m₀ rF t → Run Q' m₀ rF t
  | _, .leaf none, _, _, _ => trivial
  | _, .leaf (some (.error _)), _, _, h => h
  | _, .leaf (some (.ok (_, _))), _, _, h => by
    obtain ⟨r', hh', hq, hc', ho', hst⟩ := Run.ok_iff.mp h
    obtain ⟨r'', hh'', hq'⟩ := hu _ _ r' _ hh'.toNoFp hq hc'.noFp
    exact Run.ok_iff.mpr ⟨r'', hh''.ofNoFp, hq', hc', ho'.sub (hh'.erase_sub_of hh''.ofNoFp), hst⟩
  | _, .sync _ _ k, _, _, h => by
    obtain ⟨hs, r', hh, hc, ho, hst, hk⟩ := Run.sync_iff.mp h
    exact Run.sync_iff.mpr ⟨hs, r', hh, hc, ho, hst, fun m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm =>
      Run.eupd_post hu (k ρ m₂) (hk m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm)⟩

/-- **The in-thread reading** of a run from a one-thread memory: at each stop the thread goes on
in the memory it stopped with, with the oracle's choice `0` (`soloTree`). -/
theorem Run.solo : ∀ {n} (t : CoN Tgt (α × Mem) n) {m₀ : Mem} {rF : Res}, m₀.SingleThread →
    Run Q m₀ rF t →
    (match soloTree t with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq)
  | _, .leaf none, _, _, _, _ => trivial
  | _, .leaf (some (.error _)), _, _, _, h => h
  | _, .leaf (some (.ok (_, _))), _, _, hst0, h => by
    obtain ⟨r', hh, hq, hc, -, hst⟩ := Run.ok_iff.mp h
    exact ⟨r', hh, hq, ⟨hst0.fstep hst⟩, hc.2⟩
  | _, .sync op m₁ k, _, rF, hst0, h => by
    obtain ⟨hs, r', hh, hc, ho, hst, hk⟩ := Run.sync_iff.mp h
    obtain ⟨ρ, hρ, hans⟩ := soloResp_of_solo hs
    rw [soloTree_some hρ]
    exact Run.solo (k ρ m₁) (hst0.fstep hst) (hk m₁ rF rfl hh hc ho ρ (hans m₁) (.inl hρ))

end Run

theorem run_eq (n : Nat) (m : Mem) : ((soloRun n x).run m).run = soloTree (x n m) := rfl

/-- **The old statement**: a call read in one thread (`soloRun`, each stop answered by the
thread itself in the memory it stopped with) is a sequential triple. -/
theorem toSolo (ht : CTriple P x Q) (n : Nat) : FTriple P (soloRun n x) Q := by
  intro m r rF hh hp hs
  rw [run_eq]
  exact Run.solo (x n m) hs.1.single (ht n m r rF hh hp hs.fconc (hs.1.single.owns _))

theorem bind {S : β → FAssn} {f : α → ConcM Tgt β} (hx : CTriple P x Q)
    (hf : ∀ a, CTriple (Q a) (f a) S) : CTriple P (x >>= f) S :=
  fun n m r rF hh hp hc ho => Run.bind (x n m) (hx n m r rF hh hp hc ho)
    fun a m' k _ r' rF' hh' hq hc' ho' => hf a k m' r' rF' hh' hq hc' ho'

/-- The run of a `MemM` step from one memory: the body of a thread triple there. -/
theorem Run.liftMem {c : MemM α} {m : Mem} {rF : Res} {n : Nat}
    (h1 : match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m') :
    Run Q m rF ((ConcM.liftMem c : ConcM Tgt α) n m) := by
  show Run Q m rF (.leaf (c.run m))
  match e : (c.run m).run, h1 with
  | none, _ => rw [show c.run m = ExceptT.mk none from e]; simp only [ExceptT.mk, Run]
  | some (.error er), h1 =>
    rw [show c.run m = ExceptT.mk (some (.error er)) from e]; simp only [ExceptT.mk, Run]
    exact h1
  | some (.ok (v, m')), h1 =>
    rw [show c.run m = ExceptT.mk (some (.ok (v, m'))) from e]; simp only [ExceptT.mk, Run]
    exact h1

/-- A `MemM` step: a thread triple of it. -/
theorem liftMem {c : MemM α} (h : FTTriple P c Q) : CTriple P (ConcM.liftMem c : ConcM Tgt α) Q :=
  fun _ m r rF hh hp hc ho => Run.liftMem (h m r rF hh hp hc ho)

theorem ret (v : α) : CTriple (Q v) (pure v : ConcM Tgt α) Q :=
  fun n m r _ hh hq hc ho => Run.ok_iff (n := n).mpr ⟨r, hh, hq, hc, ho, FStepIn.refl m _⟩

theorem ret' (v : α) (hq : ∀ r, P r → Q v r) : CTriple P (pure v : ConcM Tgt α) Q :=
  fun n m r rF hh hp hc ho => ret (Q := Q) v n m r rF hh (hq r hp) hc ho

/-- **A stop that the thread answers itself** (`yield`, a `choose`, a `pick`): the thread goes
on with every answer, in every memory in which it still owns its part. -/
theorem sync_bind {op : SyncOp Tgt} {f : op.Resp → ConcM Tgt α} (hs : SyncOp.Solo op = true)
    (h : ∀ ρ, CTriple P (f ρ) Q) : CTriple P ((ConcM.sync op : ConcM Tgt op.Resp) >>= f) Q := by
  intro n m r rF hh hp hc ho
  cases n with
  | zero => trivial
  | succ n =>
    show Run Q m rF (.sync op m fun ρ m' => f ρ n m')
    exact Run.sync_iff.mpr ⟨hs, r, hh, hc, ho, FStepIn.refl m _, fun m₂ rF₂ _ hh₂ hc₂ ho₂ ρ _ _ =>
      h ρ n m₂ r rF₂ hh₂ hp hc₂ ho₂⟩

/-- **An atomic op's choice of the oracle**: every choice, in every memory in which the thread
still owns its part. -/
theorem pick_bind {count : Mem → Nat} {f : Nat → ConcM Tgt α} (h : ∀ c, CTriple P (f c) Q) :
    CTriple P ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) Q :=
  sync_bind (op := .pick count) rfl h

/-- **An oracle choice among at most `k + 1` options** in every memory in which the thread owns
`P` and whose messages are covered (`Mem.MsgCov`, which the scheduler's resumption gives; the
in-thread reading answers `0`): the choice is at most `k`. With a count lemma of an atomic op on an
owned word (one option: the newest message) this is the choice `0` of its thread rule. -/
theorem pick_le {count : Mem → Nat} {k : Nat}
    (hle : ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase → m.MsgCov →
      count m ≤ k + 1) :
    CTriple P (ConcM.sync (.pick count) : ConcM Tgt Nat) (fun c : Nat => ⟪c ≤ k⟫ ⋆ P) := by
  intro n m r rF hh hp hc ho
  cases n with
  | zero => trivial
  | succ n =>
    have key : ∀ m₂ (c : Nat), (c < count m₂ ∨ count m₂ = 0 ∧ c = 0) →
        ((some 0 : Option Nat) = some c ∨ m₂.MsgCov) → (m₂.MsgCov → count m₂ ≤ k + 1) → c ≤ k := by
      intro m₂ c hρ hm hk
      rcases hm with hm | hm
      · cases hm; exact Nat.zero_le _
      · have := hk hm; omega
    show Run _ m rF (.sync (.pick count) m fun ρ m' => .leaf (some (.ok (ρ, m'))))
    exact Run.sync_iff.mpr ⟨rfl, r, hh, hc, ho, FStepIn.refl m _,
      fun m₂ rF₂ _ hh₂ hc₂ ho₂ ρ hρ hm => Run.ok_iff.mpr ⟨r, hh₂,
        sep_lift.mpr ⟨key m₂ ρ hρ hm (hle m₂ r rF₂ hh₂ hp hc₂ ho₂), hp⟩, hc₂, ho₂, FStepIn.refl m₂ _⟩⟩

/-- `pick_le` with one option: the choice `0`. -/
theorem pick_one {count : Mem → Nat}
    (hle : ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase → m.MsgCov →
      count m ≤ 1) :
    CTriple P (ConcM.sync (.pick count) : ConcM Tgt Nat) (fun c : Nat => ⟪c = 0⟫ ⋆ P) :=
  fun n m r rF hh hp hc ho => Run.mono (fun (c : Nat) _ h => by
    obtain ⟨h1, h2⟩ := sep_lift.mp h; exact sep_lift.mpr ⟨Nat.le_zero.mp h1, h2⟩) _
    (pick_le (k := 0) hle n m r rF hh hp hc ho)

theorem pre (ht : CTriple P x Q) (hp : ∀ r, P' r → P r) : CTriple P' x Q :=
  fun n m r rF hh h hc ho => ht n m r rF hh (hp r h) hc ho

theorem post (ht : CTriple P x Q) (hq : ∀ v r, Q v r → Q' v r) : CTriple P x Q' :=
  fun n m r rF hh hp hc ho => Run.mono hq _ (ht n m r rF hh hp hc ho)

theorem conseq (ht : CTriple P x Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    CTriple P' x Q' := (ht.pre hp).post hq

theorem frame (ht : CTriple P x Q) : CTriple (P ⋆ R) x (fun v => Q v ⋆ R) := by
  intro n m r rF hh hpr hc ho
  obtain ⟨rP, rR, hd, rfl, hp, hr⟩ := hpr
  have hRF := (FHeap.disjoint_union_left.mp hh.disj).2
  have ho2 : m.Owns m.current (rP.heap.erase ∪ rR.heap.erase) := by simpa using ho
  exact Run.frame hr (x n m) hRF (Mem.OwnsC.right ho2)
    (ht n m rP _ (Holds.split hd hh) hp hc (Mem.OwnsC.left ho2))

theorem frameL (ht : CTriple P x Q) : CTriple (R ⋆ P) x (fun v => R ⋆ Q v) :=
  conseq (frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ y, CTriple (P y) x Q) : CTriple (FAssn.ex P) x Q :=
  fun n m r rF hh ⟨y, hp⟩ hc ho => h y n m r rF hh hp hc ho

theorem lift {φ : Prop} (h : φ → CTriple P x Q) : CTriple (⟪φ⟫ ⋆ P) x Q := by
  intro n m r rF hh hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ n m r rF hh hp hc ho

/-- A fact that the precondition implies. -/
theorem of_pure {φ : Prop} (hφ : ∀ r, P r → φ) (h : φ → CTriple P x Q) : CTriple P x Q :=
  fun n m r rF hh hp hc ho => h (hφ r hp) n m r rF hh hp hc ho

/-- **An update of the precondition** (`EUpd`, read in `m.noFp`). -/
theorem eupd (hu : EUpd P P') (ht : CTriple P' x Q) : CTriple P x Q := by
  intro n m r rF hh hp hc ho
  obtain ⟨r', hh', hp'⟩ := hu m.noFp r rF hh.toNoFp hp hc.noFp
  exact ht n m r' rF hh'.ofNoFp hp' hc (ho.sub (hh.erase_sub_of hh'.ofNoFp))

/-- An update of the postcondition. -/
theorem eupd_post (ht : CTriple P x Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : CTriple P x Q' :=
  fun n m r rF hh hp hc ho => Run.eupd_post hu _ (ht n m r rF hh hp hc ho)

/-- A ghost update of the precondition. -/
theorem upd (hu : Upd P' P) (ht : CTriple P x Q) : CTriple P' x Q := eupd (EUpd.of_upd hu) ht

/-- **Knowledge from ownership** (`FTriple.know_intro`). -/
theorem know_intro {b : BlockId} {A : Nat}
    (hc : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A)
    (ht : CTriple (P ⋆ known b A) x Q) : CTriple P x Q := by
  intro n m r rF hh hp hcm ho
  obtain ⟨y, fc, hy, hA⟩ := hc r hp
  have hkn : m.kn (.addr b A) := by
    obtain ⟨blk, hblk, -, -, -, ha, -⟩ := hh.block hy
    exact ⟨blk, hblk, by rw [← hA, ha]⟩
  have hres : (P ⋆ known b A) ⟨r.heap, r.know.union (Know.single (.addr b A)), r.gh⟩ :=
    ⟨r, ⟨FHeap.empty, Know.single (.addr b A), Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, rfl⟩
  exact ht n m _ rF (hh.addKnow (Know.sub_single hkn)) hres hcm ho

/-- Knowledge and ghost state (anything that owns no bytes and no stack token) in the
precondition can be forgotten. -/
theorem forget {K : FAssn} (hK : ∀ r, K r → r.heap = FHeap.empty ∧ r.gh.Affine)
    (ht : CTriple P x Q) : CTriple (P ⋆ K) x Q := by
  intro n m r rF hh hp hc ho
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hp
  obtain ⟨e, ha⟩ := hK _ h2
  have hh₁ : Holds m r₁ rF := by
    obtain ⟨hd', hm, hk, hkF, hg⟩ := hh
    simp only [e, FHeap.union_empty] at hd' hm
    exact ⟨hd', hm, hk.left, hkF, GOk.mono hg ha⟩
  simp only [e, FHeap.union_empty] at ho
  exact ht n m r₁ rF hh₁ h1 hc ho

/-- A `MemM` step that returns `v` and leaves the memory as it is. -/
theorem pureStep {c : MemM α} {v : α} {f : α → ConcM Tgt β} {S : β → FAssn}
    (hc : ∀ m r rF, Holds m r rF → P r → m.FConc → c.run m = pure (v, m))
    (hf : CTriple P (f v) S) : CTriple P (ConcM.liftMem c >>= f) S := by
  refine bind (Q := fun w => ⟪w = v⟫ ⋆ P) (liftMem (FTTriple.of_run
    fun m r rF hh hp hcm ho => ⟨v, m, r, hc m r rF hh hp hcm, hh, sep_lift.mpr ⟨rfl, hp⟩, hcm, ho,
      FStepIn.refl m _⟩)) ?_
  intro w
  exact lift fun hw => hw ▸ hf

/-- Facts that hold of every memory that holds `P` (they mention no memory, so they stay true). -/
theorem facts {φ : Prop} (hφ : ∀ m r rF, Holds m r rF → P r → m.FConc → φ)
    (h : φ → CTriple P x Q) : CTriple P x Q :=
  fun n m r rF hh hp hc ho => h (hφ m r rF hh hp hc) n m r rF hh hp hc ho

/-- An entailment that may use the memory (`Holds`, `FConc`) and keeps the thread's bytes. -/
theorem preM (hp : ∀ m r rF, Holds m r rF → P' r → m.FConc → P r)
    (ht : CTriple P x Q) : CTriple P' x Q :=
  fun n m r rF hh h hc ho => ht n m r rF hh (hp m r rF hh h hc) hc ho

/-- An oracle pick on the part `X` of `P = X ⋆ R` whose choice is `0` (`pick_one`, an atomic op
at an owned word): the rest runs with the choice `0`. -/
theorem pickStep {X R : FAssn} {count : Mem → Nat} {f : Nat → ConcM Tgt β} {S : β → FAssn}
    (hpick : CTriple X (ConcM.sync (.pick count) : ConcM Tgt Nat) (fun c : Nat => ⟪c = 0⟫ ⋆ X))
    (hP : P = (X ⋆ R)) (hf : CTriple P (f 0) S) :
    CTriple P ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) S := by
  subst hP
  refine bind hpick.frame fun c => ?_
  exact pre (lift fun hc => hc ▸ hf) fun _ h => sep_assoc h

/-- A step on the part `X` of `P = X ⋆ R` that returns `v` and keeps `X`. -/
theorem readStep {X R : FAssn} {c : MemM α} {v : α} {f : α → ConcM Tgt β} {S : β → FAssn}
    (ht : FTTriple X c (fun w => ⟪w = v⟫ ⋆ X)) (hP : P = (X ⋆ R)) (hf : CTriple P (f v) S) :
    CTriple P (ConcM.liftMem c >>= f) S := by
  subst hP
  refine bind (liftMem ht.frame) fun w => ?_
  exact pre (lift fun hw => hw ▸ hf) fun _ h => sep_assoc h

/-- **A loop with an invariant** (`Zig.loop`, partial correctness): if one run of the body from the
invariant returns to it when it repeats and establishes `post` when it exits, the loop does. No
measure: a loop that never exits has no result, which partial correctness allows.

The proof is by induction on the depth and, at one depth, by fixpoint induction on the root of
the tree (`Sched.admissible_root`): a run whose tree is not "no result" at its root is
one iteration more than a run whose tree is not either (before its first stop), or stops
inside the body (and goes on at a smaller depth). (`CTriple P · Q` itself is not admissible:
the parts of the elements of a chain at a stop need not have a common one.) -/
theorem loop {σ ε : Type} {body : CM Tgt σ ε} {again : ε → Bool} (inv : σ → FAssn)
    (post : ε × σ → FAssn)
    (step : ∀ s, CTriple (inv s) (body.run s) (fun r => if again r.1 then inv r.2 else post r)) :
    ∀ s, CTriple (inv s) ((Zig.loop body again).run s) post := by
  intro s n
  induction n using Nat.strongRecOn generalizing s with
  | _ n ihn =>
  -- the rest of the body's run: the loop again, or the exit
  let G := fun (l : CM Tgt σ ε) (p : (ε × σ) × Mem) (k : Nat) =>
    (if again p.1.1 then l.run p.1.2 else (pure p.1 : ConcM Tgt (ε × σ))) k p.2
  have unfold : ∀ (l : CM Tgt σ ε) s n m,
      ((do let e ← body; if again e then l else pure e : CM Tgt σ ε).run s) n m =
        ((body.run s) n m).bind (G l) := by
    intro l s n m
    rw [StateT.run_bind]
    show ((body.run s) n m).bind _ = _
    congr 1
    funext ⟨⟨e, s'⟩, m'⟩ k
    simp only [G]
    split <;> rfl
  -- the rest after a stop of the body: a smaller depth
  have rest : ∀ {d} (t : CoN Tgt ((ε × σ) × Mem) d), d < n → ∀ {m₀ rF},
      Run (fun r => if again r.1 then inv r.2 else post r) m₀ rF t →
      Run post m₀ rF (t.bind (G (Zig.loop body again))) := by
    intro d t hd m₀ rF h
    refine Run.bind t h fun ⟨e, s'⟩ m' k hk r' rF' hh' hq hc' ho' => ?_
    simp only [G]
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hq ⊢
      exact Run.ok_iff.mpr ⟨r', hh', hq, hc', ho', FStepIn.refl m' _⟩
    · simp only [ha, ↓reduceIte] at hq ⊢
      exact ihn k (by omega) s' m' r' rF' hh' hq hc' ho'
  have key := Zig.loop.fixpoint_induct body again
    (fun l => ∀ s m, (l.run s) n m = .leaf none ∨ ∀ r rF, Holds m r rF → inv s r → m.FConc →
      m.Owns m.current r.heap.erase → Run post m rF (((Zig.loop body again).run s) n m))
    (admissible_pi_apply (β := fun _ => ConcM Tgt (ε × σ))
      (fun s x => ∀ m, x n m = .leaf none ∨ ∀ r rF, Holds m r rF → inv s r → m.FConc →
        m.Owns m.current r.heap.erase → Run post m rF (((Zig.loop body again).run s) n m))
      fun s => by
        have := Sched.admissible_root (Tgt := Tgt) (α := ε × σ) fun n' m => n' = n →
          ∀ r rF, Holds m r rF → inv s r → m.FConc → m.Owns m.current r.heap.erase →
            Run post m rF (((Zig.loop body again).run s) n m)
        intro c hc h m
        refine (this c hc (fun x hx n' m' => ?_) n m).imp id fun h' => h' rfl
        by_cases hn : n' = n
        · subst hn; exact (h x hx m').imp id fun h' _ => h'
        · exact .inr fun e => absurd e hn)
    (by
      intro l hl s m
      rw [unfold l s n m]
      by_cases hz : ((body.run s) n m).bind (G l) = .leaf none
      · exact .inl hz
      refine .inr fun r rF hh hp hc ho => ?_
      rw [Zig.loop.eq_1, unfold _ s n m]
      have hB := step s n m r rF hh hp hc ho
      revert hz hB
      generalize (body.run s) n m = B
      intro hz hB
      cases B with
      | leaf o =>
        rcases o with _ | _ | ⟨⟨e, s'⟩, m'⟩
        · exact absurd rfl hz
        · exact hB
        · obtain ⟨r', hh', hq, hc', ho', hst⟩ := Run.ok_iff.mp hB
          simp only [CoN.bind, G] at hz ⊢
          cases ha : again e
          · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hq ⊢
            exact Run.ok_iff.mpr ⟨r', hh', hq, hc', ho', hst⟩
          · simp only [ha, ↓reduceIte] at hq hz ⊢
            exact Run.prefix hst (((hl s' m').resolve_left hz) r' rF hh' hq hc' ho')
      | sync op m₁ k =>
        obtain ⟨hs, r', hh', hc', ho', hst, hk⟩ := Run.sync_iff.mp hB
        exact Run.sync_iff.mpr ⟨hs, r', hh', hc', ho', hst, fun m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm =>
          rest (k ρ m₂) (Nat.lt_succ_self _) (hk m₂ rF₂ e hh₂ hc₂ ho₂ ρ hρ hm)⟩)
  intro m r rF hh hp hc ho
  rcases key s m with e | h
  · rw [e]; trivial
  · exact h r rF hh hp hc ho

end CTriple

end Full

/-! ## Normalizing the body of a generated concurrent function -/

namespace CNorm

variable {Tgt σ α β : Type}

theorem run_callC (x : ConcM Tgt α) (s : σ) :
    (callC x : CM Tgt σ α).run s = x >>= fun a => pure (a, s) := rfl

theorem run_callMC (x : MemM α) (s : σ) :
    (callMC x : CM Tgt σ α).run s = ConcM.liftMem x >>= fun a => pure (a, s) := rfl

theorem run_callRC (x : Result α) (s : σ) :
    (callRC x : CM Tgt σ α).run s = ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s) := rfl

theorem run_liftR (x : Result α) (s : σ) :
    (liftM x : CM Tgt σ α).run s = ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s) := rfl

/-- A memory step of a concurrent body (`liftM` of a `MemM` step) in normal form, for a walk by
hand with the rules stated on `ConcM.liftMem` (`fsym_norm` reaches the same form through
`liftM`). -/
theorem run_liftM (x : MemM α) (s : σ) :
    (liftM x : CM Tgt σ α).run s = ConcM.liftMem x >>= fun a => pure (a, s) := rfl

theorem run_pickC (count : Mem → Nat) (s : σ) :
    (pickC count : CM Tgt σ Nat).run s =
      (ConcM.sync (.pick count) : ConcM Tgt Nat) >>= fun (a : Nat) => pure (a, s) := rfl

theorem run_ite {c : Prop} [Decidable c] (x y : CM Tgt σ α) (s : σ) :
    (if c then x else y).run s = if c then x.run s else y.run s := by split <;> rfl

theorem run_throw (e : Error) (s : σ) : (throw e : CM Tgt σ α).run s = throw e := rfl

theorem throw_bind (e : Error) (f : α → ConcM Tgt β) : (throw e : ConcM Tgt α) >>= f = throw e :=
  rfl

theorem run_get (s : σ) : (get : CM Tgt σ σ).run s = pure (s, s) := rfl

theorem run_modify (f : σ → σ) (s : σ) : (modify f : CM Tgt σ Unit).run s = pure ((), f s) := rfl

/-- `bind_assoc` at an oracle pick (whose result type `SyncOp.Resp (.pick _)` is `Nat` only up to
unfolding, so `bind_assoc` does not match it in `simp`). -/
theorem pick_assoc {γ : Type} (count : Mem → Nat) (f : Nat → ConcM Tgt β) (g : β → ConcM Tgt γ) :
    ((ConcM.sync (.pick count) : ConcM Tgt Nat) >>= f) >>= g =
      (ConcM.sync (.pick count) : ConcM Tgt Nat) >>= fun a => f a >>= g :=
  bind_assoc _ _ _

theorem liftMem_pure (v : α) : (ConcM.liftMem (pure v : MemM α) : ConcM Tgt α) = pure v := rfl

theorem liftMem_lift_pure (v : α) :
    (ConcM.liftMem (StateT.lift (pure v : Result α)) : ConcM Tgt α) = pure v := rfl

theorem liftMem_lift_throw (e : Error) :
    (ConcM.liftMem (StateT.lift (throw e : Result α)) : ConcM Tgt α) = throw e := rfl

end CNorm

/-- Normalize the body of a generated concurrent function to a `ConcM` program of `liftMem`
steps, oracle picks and `pure`/`if` (module doc). -/
macro "conc_norm" : tactic => `(tactic| (
  simp only [atomicLoadUnorderedEncC, cmpxchgPtrC, StateT.run'_eq, StateT.run_bind, StateT.run_pure, CNorm.run_callC,
    CNorm.run_callMC, CNorm.run_callRC, CNorm.run_liftR, CNorm.run_pickC, CNorm.run_ite,
    Norm.ite_bind, CNorm.run_throw, CNorm.throw_bind, CNorm.run_get, CNorm.run_modify,
    CNorm.pick_assoc, CNorm.liftMem_pure, CNorm.liftMem_lift_pure, CNorm.liftMem_lift_throw, Norm.sub_zero,
    Norm.elem_zero, Norm.add_zero_ptr, bind_assoc, pure_bind, map_pure, bind_map_left, map_bind,
    Norm.beq_true_iff, bind_pure_unit, Bool.not_false, Bool.not_true, ↓reduceIte,
    Bool.false_eq_true]))

end Zig
