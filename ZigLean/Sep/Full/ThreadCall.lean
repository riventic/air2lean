import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.ThreadOwned

/-!
# A call of a concurrent function inside a protocol (`WP.call_fowned`)

`CTriple P x Q` (`Conc.lean`) is a thread triple of the call `x`, stop by stop. This module runs
it inside the protocol logic (`Proto.WP`, `ZigLean/Conc/Logic.lean`): thread `t` of a protocol
whose invariant keeps each thread's part (`FOwned` of the parts `res (G u)` of the ghost values)
calls `x` on its part. So a contract proved once as a `CTriple` (an allocator entry, `CAllocSpec`;
an interface function, `FnSpec`) is usable in every thread (audit `structure-2026-10-13.md` #2).

The protocol supplies (`WP.call_fowned`):
- `hinv`: every memory of the invariant has thread `t` and the parts (`FOwned`, with some rest
  `rO` that the protocol owns);
- `hloc`: the invariant is local to the parts: after a segment of thread `t` that keeps the other
  parts and the rest (`FStepIn` of their bytes) and gives `t` the part `r'`, it holds with `t`'s
  ghost value `set (G t) r'` (what each protocol's `wp_liftMem` discharges, e.g.
  `Lock.Inv.wp_liftMem`);
- `hpost`: the same for the call's results, into the `WP` postcondition;
- `hcost`: the protocol counts no turns (`Proto.cost = none`; a call's stops are not charged).

At each stop the thread's ghost value becomes `set (G t) r'` with its part `r'`; when the
scheduler resumes it (in any memory of the invariant, with any answer that memory allows,
`Proto.Step`), the part `res (G₁ t) = r'` holds there again (`hinv`, `FOwned.part`), which is
exactly what `CTriple.Run` resumes with.
-/

namespace Zig
namespace Conc
namespace Proto

open Full Sched

variable {Tgt γ α : Type} {P : Proto Tgt γ} {t : ThreadId}

/-- A stop that the thread answers itself goes on with each of its answers in the memory the
scheduler resumes it in. -/
theorem Step.of_solo {op : SyncOp Tgt} {G : ThreadId → γ} {m : Mem}
    {K : op.Resp → (ThreadId → γ) → Mem → Prop} (hs : SyncOp.Solo op = true)
    (h : ∀ ρ, soloAnswer op { m with current := t } ρ → K ρ G { m with current := t }) :
    P.Step t op G m K := by
  cases op with
  | yield => exact h () (by simp only [soloAnswer])
  | choose n => exact fun c hc => h c hc
  | pick count => exact fun c hc => h c hc
  | _ => cases hs

section Call

variable {Qa : α → FAssn} {Q : α → (ThreadId → γ) → Mem → Nat → Prop}
  {res : γ → Res} {set : γ → Res → γ}

/-- **A call's run, stop by stop, keeps the protocol** (`WP.call_fowned`): from a memory of the
invariant switched to thread `t`, where the other parts and the rest are the run's frame. -/
theorem Run.safe (hcost : P.cost = none) (hres : ∀ g r, res (set g r) = r)
    (hinv : ∀ G m, P.inv G m → t < m.threads.size ∧ ∃ rO, FOwned (fun u => res (G u)) rO m)
    (hloc : ∀ G m m' rO rR r', P.inv G m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR →
      FOwned (upd (fun u => res (G u)) t r') rO m' →
      FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) { m with current := t } m' →
      P.inv (upd G t (set (G t) r')) m')
    (hpost : ∀ G m m' rO rR r' v d, P.inv G m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR →
      FOwned (upd (fun u => res (G u)) t r') rO m' →
      FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) { m with current := t } m' → Qa v r' →
      Q v G m' d) :
    ∀ {n} (tr : CoN Tgt (α × Mem) n) {G : ThreadId → γ} {m : Mem} {rO rR : Res},
      P.inv G m → t < m.threads.size → FOwned (fun u => res (G u)) rO m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR → FHeap.Disjoint rR.heap rO.heap →
      CTriple.Run Qa { m with current := t }
        ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, (rR.gh.add rO.gh).add (Ghost.cur t)⟩ tr →
      P.Safe t Q m.threads.size G tr
  | _, .leaf none, _, _, _, _, _, _, _, _, _, _ => by simp only [Safe]; exact .inl (.inr hcost)
  | _, .leaf (some (.error _)), _, _, _, _, _, _, _, _, _, h => by simp only [Safe]; exact .inr h
  | _, .leaf (some (.ok (v, m'))), G, m, rO, rR, hi, htl, ho, hR, hRO, h => by
    obtain ⟨r', hh', hq, hc', ho', hst⟩ := CTriple.Run.ok_iff.mp h
    -- the call ran with the running thread's token in its frame: its part holds none
    obtain ⟨hnc, hh'⟩ := Holds.dropCurF
      (rF := ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩) hh'
    have hs := (ho.current t).step rfl htl hR hRO hh' hc' ho' hst hnc
    simp only [Safe]
    exact ⟨by rw [hst.threads], hpost G m m' rO rR r' v _ hi hR hs hst hq⟩
  | _, .sync op m₁ k, G, m, rO, rR, hi, htl, ho, hR, hRO, h => by
    obtain ⟨hso, r', hh₁, hc₁, ho₁, hst, hk⟩ := CTriple.Run.sync_iff.mp h
    obtain ⟨hnc, hh₁⟩ := Holds.dropCurF
      (rF := ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩) hh₁
    have hs := (ho.current t).step rfl htl hR hRO hh₁ hc₁ ho₁ hst hnc
    refine (Safe.sync_none hcost).mpr ⟨by rw [hst.threads], set (G t) r',
      hloc G m m₁ rO rR r' hi hR hs hst, fun G₁ m₂ hg hi₂ => Step.of_solo hso fun ρ hρ => ?_⟩
    obtain ⟨htl₂, rO₂, ho₂⟩ := hinv G₁ m₂ hi₂
    obtain ⟨rR₂, hR₂, hRO₂, hh₂⟩ := (ho₂.current t).part htl₂
    have hh₂ := hh₂.addCurF (ho₂.part_noCur hR₂)
    have e : res (G₁ t) = r' := by rw [hg, hres]
    rw [e] at hh₂
    have hc₂ : ({ m₂ with current := t } : Mem).FConc :=
      ⟨by show t < m₂.clocks.size; rw [ho₂.csize]; exact htl₂, ho₂.conc.1, ho₂.conc.2.1⟩
    have hown : ({ m₂ with current := t } : Mem).Owns t r'.heap.erase := e ▸ ho₂.owns t htl₂
    exact Run.safe hcost hres hinv hloc hpost (k ρ { m₂ with current := t }) (m := m₂) hi₂ htl₂ ho₂
      hR₂ hRO₂
      (hk { m₂ with current := t } _ hst.current.symm hh₂ hc₂ hown ρ hρ (.inr ho₂.conc.2.2))

/-- **A call of a concurrent function by thread `t` of a protocol** (module doc): the call's
`CTriple` on the thread's part, with an invariant that keeps the parts (`hinv`) and is local to
them (`hloc`), gives its `WP`; each result holds `hpost`'s postcondition. -/
theorem WP.call_fowned {x : ConcM Tgt α} {Pa : FAssn} (hx : CTriple Pa x Qa)
    (hcost : P.cost = none) (hres : ∀ g r, res (set g r) = r)
    (hinv : ∀ G m, P.inv G m → t < m.threads.size ∧ ∃ rO, FOwned (fun u => res (G u)) rO m)
    (hloc : ∀ G m m' rO rR r', P.inv G m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR →
      FOwned (upd (fun u => res (G u)) t r') rO m' →
      FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) { m with current := t } m' →
      P.inv (upd G t (set (G t) r')) m')
    (hpost : ∀ G m m' rO rR r' v d, P.inv G m →
      sepN m.threads.size (partsBut (fun u => res (G u)) t) rR →
      FOwned (upd (fun u => res (G u)) t r') rO m' →
      FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) { m with current := t } m' → Qa v r' →
      Q v G m' d)
    {G : ThreadId → γ} {m : Mem} {n : Nat} (hi : P.inv G m) (hc : m.current = t)
    (hp : Pa (res (G t))) : P.WP t x Q G m n := by
  obtain ⟨htl, rO, ho⟩ := hinv G m hi
  have em : ({ m with current := t } : Mem) = m := by rw [← hc]
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part htl
  have hh' := hh.addCurF (ho.part_noCur hR)
  rw [hc] at hh'
  have hx' := hx n m _ _ hh' hp ⟨by rw [hc, ho.csize]; exact htl, ho.conc.1, ho.conc.2.1⟩
    (hc ▸ ho.owns t htl)
  exact Run.safe hcost hres hinv hloc hpost (x n m) hi htl ho hR hRO (by rw [em]; exact hx')

end Call

end Proto
end Conc
end Zig
