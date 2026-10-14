import ZigLean.Sep.Full.Thread
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Mmap
import ZigLean.Conc.Csl

/-!
# The threads' parts over full-state resources

`FOwned own rO m` (`docs/sep-threads.md` §The threads' parts): thread `u`'s part is the resource
`own u`; the parts compose (`sepN`) and hold in `m` next to the protocol's rest `rO` (resources no
thread holds: a free lock's resource, shared atomic words, ledgers the protocol keeps); each
thread's clock owns its part's bytes. It replaces the legacy `Owned` (`ZigLean/Conc/Csl.lean`)
for the full-state logic; a proof keeps it in its protocol invariant, as before.

- `FOwned.start`: no parts, the whole memory in `rO`, in a memory with no recorded access.
- `FOwned.step`, `WP.liftMem_fownedS` (and its forms `liftMem_fowned`, `liftM_fowned`,
  `callMC_fowned(S)`): a `MemM` step of thread `t` with a thread triple (`FTTriple`) on its part;
  the other parts and `rO` are the frame.
- `FOwned.keep` (a step that changes no block, location, thread, clock or access),
  `FOwned.recordAt` (a recorded access of a thread to its own bytes, e.g. a futex wait's read),
  `FOwned.cover` / `heap_empty` (every live byte belongs to a part or to `rO`).
- `FOwned.fork` (spawn), `FOwned.current` (a stop), `FOwned.setThread` (a detach): the clock
  reasoning is the legacy one (`Owned.fork`), applied to the parts' bytes with the memory's exact
  cells (`FOwned.legacy`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## Parts as an indexed separating conjunction -/

/-- Thread `u`'s part is exactly `own u`. -/
abbrev partOf (own : ThreadId → Res) (u : ThreadId) : FAssn := fun r => r = own u

/-- The parts other than `t`'s. -/
abbrev partsBut (own : ThreadId → Res) (t : ThreadId) (j : Nat) : FAssn :=
  if j = t then emp else partOf own j

/-- A conjunct of `sepN` owns a part of the bytes. -/
theorem sepN_mem {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {j : Nat}, sepN n f r → j < n →
    ∃ rj, f j rj ∧ ∀ l, rj.heap l ≠ none → r.heap l ≠ none
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, _, j, ⟨r₁, r₂, _, rfl, h1, h2⟩, hj => by
    by_cases hjn : j = n
    · subst hjn
      exact ⟨r₁, h1, fun l hl => by simp only [FHeap.union_apply]; cases e : r₁.heap l <;> simp_all⟩
    · obtain ⟨rj, hf, hs⟩ := sepN_mem (j := j) h2 (by omega)
      exact ⟨rj, hf, fun l hl => by
        have := hs l hl
        simp only [FHeap.union_apply]; cases e : r₁.heap l <;> simp_all⟩

/-- A byte of a `sepN` belongs to one of its conjuncts. -/
theorem sepN_cover {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {l : Loc}, sepN n f r →
    r.heap l ≠ none → ∃ j < n, ∃ rj, f j rj ∧ rj.heap l ≠ none
  | 0, _, _, ⟨he, _, _⟩, hl => absurd (by rw [he]; rfl) hl
  | n + 1, _, l, ⟨r₁, r₂, _, rfl, h1, h2⟩, hl => by
    by_cases e : r₁.heap l = none
    · obtain ⟨j, hj, rj, hf, hr⟩ := sepN_cover h2 (by simpa [FHeap.union_apply, e] using hl)
      exact ⟨j, by omega, rj, hf, hr⟩
    · exact ⟨n, by omega, r₁, h1, e⟩

/-- Pick thread `t`'s part out of the parts. -/
theorem parts_pick {own : ThreadId → Res} {n t : Nat} {rT : Res} (ht : t < n)
    (h : sepN n (partOf own) rT) :
    ∃ rR, sepN n (partsBut own t) rR ∧ FHeap.Disjoint (own t).heap rR.heap ∧
      rT = ⟨(own t).heap ∪ rR.heap, (own t).know.union rR.know, (own t).gh.add rR.gh⟩ := by
  rw [sepN_pick ht] at h
  obtain ⟨r₁, r₂, hd, rfl, rfl, h2⟩ := h
  exact ⟨r₂, h2, hd, rfl⟩

/-- Another thread's part is within the rest. -/
theorem partsBut_sub {own : ThreadId → Res} {n t u : Nat} {rR : Res}
    (h : sepN n (partsBut own t) rR) (hu : u < n) (hut : u ≠ t) (l : Loc)
    (hl : (own u).heap l ≠ none) : rR.heap l ≠ none := by
  obtain ⟨rj, hf, hs⟩ := sepN_mem h hu
  simp only [partsBut, hut, ↓reduceIte, partOf] at hf
  subst hf; exact hs l hl

/-- Put a new part `r` for `t` back. -/
theorem parts_put {own : ThreadId → Res} {n t : Nat} {rR r : Res} (ht : t < n)
    (h : sepN n (partsBut own t) rR) (hd : FHeap.Disjoint r.heap rR.heap) :
    sepN n (partOf (upd own t r)) ⟨r.heap ∪ rR.heap, r.know.union rR.know, r.gh.add rR.gh⟩ := by
  rw [sepN_pick ht]
  refine ⟨r, rR, hd, rfl, by simp [partOf], ?_⟩
  rw [sepN_congr (g := partsBut own t) fun j _ => ?_]
  · exact h
  · by_cases hj : j = t
    · simp [hj]
    · simp only [partsBut, hj, ↓reduceIte]; unfold partOf; rw [upd_ne _ _ hj]

theorem Exact.sub {m : Mem} {r : Res} (hx : Exact m r) : r.heap.erase.Sub m.heap := fun l c hc => by
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, rfl⟩ := hc
  exact hx l fc hfc

/-- The composition of two resources (the resource of `P ⋆ Q`). -/
abbrev rsum (a b : Res) : Res := ⟨a.heap ∪ b.heap, a.know.union b.know, a.gh.add b.gh⟩

theorem rsum_comm {a b : Res} (hd : FHeap.Disjoint a.heap b.heap) : rsum a b = rsum b a := by
  simp only [rsum, FHeap.union_comm hd, Know.union_comm, Ghost.add_comm]

theorem rsum_assoc {a b c : Res} : rsum (rsum a b) c = rsum a (rsum b c) := by
  simp only [rsum, FHeap.union_assoc, Know.union_assoc, Ghost.add_assoc]

/-- The empty resource: the part of a thread that owns nothing (a joined one). -/
abbrev rnil : Res := ⟨FHeap.empty, Know.none, Ghost.unit⟩

theorem rnil_rsum (r : Res) : rsum rnil r = r := by
  simp [rsum, Know.none_union]

theorem partOf_rnil : (fun r => r = rnil) = (emp : FAssn) := by
  funext r; apply propext
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩; rw [res_eta r, h1, h2, h3]

/-! ## The parts -/

/-- The threads' parts and the protocol's rest in `m` (module doc). -/
structure FOwned (own : ThreadId → Res) (rO : Res) (m : Mem) : Prop where
  holds : ∃ rT, sepN m.threads.size (partOf own) rT ∧ Holds m rT rO
  owns : ∀ u < m.threads.size, m.Owns u (own u).heap.erase
  outside : ∀ u, m.threads.size ≤ u → emp (own u)
  csize : m.clocks.size = m.threads.size
  conc : ShapesWF (shapes m) ∧ m.LiveLayout

namespace FOwned

variable {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t : ThreadId}

/-- Thread `t`'s part holds in `m`, with the other parts and `rO` as its frame. -/
theorem part (ho : FOwned own rO m) (ht : t < m.threads.size) :
    ∃ rR, sepN m.threads.size (partsBut own t) rR ∧ FHeap.Disjoint rR.heap rO.heap ∧
      Holds m (own t) ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩ := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  obtain ⟨rR, hR, hd, rfl⟩ := parts_pick ht hs
  exact ⟨rR, hR, (FHeap.disjoint_union_left.mp hh.disj).2, Holds.split hd hh⟩

/-- **The start**: no thread owns anything, the whole memory is the protocol's rest. No thread
has a stack budget (a budget demands its thread's stack token, `StackAuth`). -/
theorem start (hf : m.footprint = #[]) (hc : m.clocks.size = m.threads.size)
    (hw : ShapesWF (shapes m)) (hl : m.LiveLayout)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FOwned (fun _ => ⟨FHeap.empty, Know.none, Ghost.unit⟩) ⟨m.fheap, Know.none, Ghost.unit⟩ m where
  holds := by
    refine ⟨⟨FHeap.empty, Know.none, Ghost.unit⟩, ?_, ?_⟩
    · have : ∀ n, sepN n (partOf fun _ => (⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res))
          ⟨FHeap.empty, Know.none, Ghost.unit⟩ := by
        intro n; induction n with
        | zero => exact ⟨rfl, rfl, rfl⟩
        | succ n ih =>
          refine ⟨⟨FHeap.empty, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, Ghost.unit⟩,
            FHeap.disjoint_empty _, ?_, rfl, ih⟩
          simp [Know.union_none, Ghost.add_unit]
      exact this _
    · exact ⟨fun _ => .inl rfl, by simpa using FMatch.fheap m, Know.sub_none _, Know.sub_none _,
        by simpa [Ghost.add_unit] using GOk.unit hns⟩
  owns _ _ e he := by rw [hf] at he; simp at he
  outside _ _ := ⟨rfl, rfl, rfl⟩
  csize := hc
  conc := ⟨hw, hl⟩

/-- **A step of thread `t`** with a thread triple on its part (`FTTriple`'s post). -/
theorem step {rR r' : Res} (ho : FOwned own rO m) (hc : m.current = t) (ht : t < m.threads.size)
    (hR : sepN m.threads.size (partsBut own t) rR) (hRO : FHeap.Disjoint rR.heap rO.heap)
    (hh : Holds m' r' ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩)
    (hcm : m'.FConc) (how : m'.Owns m'.current r'.heap.erase)
    (hs : FStepIn (FHeap.erase (rR.heap ∪ rO.heap)) m m') :
    FOwned (upd own t r') rO m' where
  holds := by
    rw [hs.threads]
    exact ⟨_, parts_put ht hR (FHeap.disjoint_union_right.mp hh.disj).1,
      Holds.join (FHeap.disjoint_union_right.mp hh.disj).1 hRO hh⟩
  owns u hu := by
    rw [hs.threads] at hu
    by_cases hut : u = t
    · subst hut; rw [upd_self]; rw [hs.current, hc] at how; exact how
    · rw [upd_ne _ _ hut]
      exact Mem.Owns.fstep hs (hc ▸ hut) (ho.owns u hu) fun l hl => by
        have := partsBut_sub hR hu hut l (by simpa [FHeap.erase] using hl)
        simp only [FHeap.erase_union, Heap.union_apply]
        cases e : rR.heap l <;> simp_all [FHeap.erase]
  outside u hu := by
    rw [hs.threads] at hu
    rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hu))]; exact ho.outside u hu
  csize := by rw [hs.size, hs.threads]; exact ho.csize
  conc := hcm.2

/-- The parts' bytes with the memory's exact cells: the legacy parts (`Owned`), for the clock
reasoning of the legacy rules. -/
theorem legacy (ho : FOwned own rO m) : Owned (fun u => ((own u).heap.fix m).erase) m where
  sub u := by
    by_cases hu : u < m.threads.size
    · obtain ⟨_, -, -, hh⟩ := ho.part hu
      exact Exact.sub (r := (own u).fix m) hh.fix_exact
    · rw [(ho.outside u (Nat.le_of_not_lt hu)).1]; intro l c hc
      simp [FHeap.erase, FHeap.fix, FHeap.empty] at hc
  disj u v huv l := by
    simp only [FHeap.erase, FHeap.fix, Option.map_eq_none_iff]
    by_cases hu : u < m.threads.size
    · by_cases hv : v < m.threads.size
      · obtain ⟨rR, hR, -, hh⟩ := ho.part hu
        cases e : (own v).heap l with
        | none => exact .inr rfl
        | some fc =>
          have := partsBut_sub hR hv (Ne.symm huv) l (by simp [e])
          exact .inl ((FHeap.disjoint_union_right.mp hh.disj).1 l |>.resolve_right this)
      · exact .inr (by rw [(ho.outside v (Nat.le_of_not_lt hv)).1]; rfl)
    · exact .inl (by rw [(ho.outside u (Nat.le_of_not_lt hu)).1]; rfl)
  owns u hu := (ho.owns u hu).sub fun l h => FHeap.erase_fix_ne.mp h
  outside u hu := by
    funext l; simp [(ho.outside u hu).1, FHeap.erase, FHeap.fix, FHeap.empty, Heap.empty]
  csize := ho.csize

/-- A stop: only `current` changes. -/
theorem current (ho : FOwned own rO m) (t : ThreadId) : FOwned own rO { m with current := t } :=
  ⟨by obtain ⟨rT, h1, h2⟩ := ho.holds; exact ⟨rT, h1, Holds.congrMem (m := m) rfl rfl h2⟩,
    ho.owns, ho.outside, ho.csize, ho.conc⟩

/-- A change of a thread's record (a detach). -/
theorem setThread (ho : FOwned own rO m) (tid : ThreadId) (rec : ThreadRec) :
    FOwned own rO { m with threads := m.threads.set! tid rec } := by
  have hs : (m.threads.set! tid rec).size = m.threads.size := by simp [Array.set!_eq_setIfInBounds]
  exact ⟨by
      dsimp only; rw [hs]; obtain ⟨rT, h1, h2⟩ := ho.holds
      exact ⟨rT, h1, Holds.congrMem (m := m) rfl rfl h2⟩,
    fun u hu => ho.owns u (by rw [hs] at hu; exact hu), fun u hu => ho.outside u (by rw [hs] at hu; exact hu),
    by rw [hs]; exact ho.csize, ho.conc⟩

/-- **Spawn**: the parent `t` gives `r₂` of its part `r₁ ⋆ r₂` to the new thread. -/
theorem fork {r₁ r₂ : Res} {c : ThreadId} {gt : Bool} (ho : FOwned own rO m)
    (ht : t < m.threads.size)
    (hsplit : own t = ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩)
    (hd12 : FHeap.Disjoint r₁.heap r₂.heap)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t r₁) c r₂) rO m' := by
  have hleg := Owned.fork (h₁ := (r₁.heap.fix m).erase) (h₂ := (r₂.heap.fix m).erase)
    ((legacy ho).current t) ht (by simp [hsplit, FHeap.fix_union])
    (FHeap.erase_disjoint (FHeap.fix_disjoint hd12)) hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hd := FHeap.disjoint_union_right.mp hh.disj
  rw [hsplit] at hd
  have h1R : FHeap.Disjoint r₁.heap rR.heap := fun l => by
    rcases hd.1 l with e | e
    · simp only [FHeap.union_apply, Option.or_eq_none_iff] at e; exact .inl e.1
    · exact .inr e
  have h2R : FHeap.Disjoint r₂.heap rR.heap := fun l => by
    rcases hd.1 l with e | e
    · simp only [FHeap.union_apply, Option.or_eq_none_iff] at e; exact .inl e.2
    · exact .inr e
  refine ⟨?_, fun u hu => ?_, fun u hu => ?_, hleg.csize, ho.conc⟩
  · have h12R : FHeap.Disjoint (r₁.heap ∪ r₂.heap) rR.heap := hd.1
    have hput := parts_put (r := r₁) ht hR h1R
    rw [sepN_congr (g := partOf (upd (upd own t r₁) m.threads.size r₂)) fun j hj => by
      unfold partOf; rw [upd_ne _ _ (show j ≠ m.threads.size by omega)]] at hput
    rw [hsplit] at hh
    have hj : Holds m (rsum (rsum r₁ r₂) rR) rO := Holds.join h12R hRO hh
    rw [rsum_comm hd12, rsum_assoc] at hj
    refine ⟨rsum r₂ (rsum r₁ rR), ?_, Holds.congrMem (m := m) rfl rfl hj⟩
    dsimp only; rw [Array.size_push]
    exact ⟨r₂, rsum r₁ rR, FHeap.disjoint_union_right.mpr ⟨hd12.symm, h2R⟩, rfl,
      by simp [partOf], hput⟩
  · dsimp only at hu; simp only [Array.size_push] at hu
    have := hleg.owns u (by simpa using hu)
    refine this.sub fun l h => ?_
    by_cases huc : u = m.threads.size
    · subst huc; simp only [upd_self] at h ⊢; exact FHeap.erase_fix_ne.mpr h
    · rw [upd_ne _ _ huc] at h ⊢
      by_cases hut : u = t
      · subst hut; simp only [upd_self] at h ⊢; exact FHeap.erase_fix_ne.mpr h
      · rw [upd_ne _ _ hut] at h ⊢; exact FHeap.erase_fix_ne.mpr h
  · dsimp only at hu; simp only [Array.size_push] at hu
    have htu : t < u := Nat.lt_of_lt_of_le ht (Nat.le_of_succ_le hu)
    rw [upd_ne _ _ (Nat.ne_of_gt hu), upd_ne _ _ (Nat.ne_of_gt htu)]
    exact ho.outside u (Nat.le_of_succ_le hu)

/-- Two threads' parts are disjoint. -/
theorem disj (ho : FOwned own rO m) {u v : ThreadId} (hu : u < m.threads.size)
    (hv : v < m.threads.size) (huv : u ≠ v) : FHeap.Disjoint (own u).heap (own v).heap := fun l => by
  obtain ⟨rR, hR, -, hh⟩ := ho.part hu
  cases e : (own v).heap l with
  | none => exact .inr rfl
  | some fc =>
    have := partsBut_sub hR hv (Ne.symm huv) l (by simp [e])
    exact .inl ((FHeap.disjoint_union_right.mp hh.disj).1 l |>.resolve_right this)

/-- **Join**: the parent `t` takes the part of thread `u`, which has ended; `u` keeps nothing. -/
theorem join {u : ThreadId} (ho : FOwned own rO m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    FOwned (upd (upd own u rnil) t (rsum (own t) (own u))) rO m' := by
  have hleg := Owned.join (legacy ho) ht hut hj
  obtain ⟨rec, hr, -, rfl⟩ := Proto.join_eq hj
  have hul : u < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  -- `u`'s part out of the others'
  have hR' := hR
  rw [sepN_pick hul] at hR'
  obtain ⟨ru, rR', hdu, rfl, hru, hR'⟩ := hR'
  have hut' : ¬ @Eq Nat u t := hut
  simp only [partsBut, hut', ↓reduceIte] at hru
  subst hru
  have hR₁ : sepN m.threads.size (partsBut (upd own u rnil) t) rR' := by
    rw [sepN_congr (g := fun j => if j = u then emp else partsBut own t j) fun j _ => ?_]
    · exact hR'
    · by_cases hju : j = u
      · subst hju
        have hjt : ¬ @Eq Nat j t := hut
        simp only [partsBut, hjt, ↓reduceIte]; unfold partOf; rw [upd_self]; exact partOf_rnil
      · simp only [partsBut, hju, ↓reduceIte]; unfold partOf; rw [upd_ne _ _ hju]
  have hd := FHeap.disjoint_union_right.mp hh.disj
  have hdt := FHeap.disjoint_union_right.mp hd.1
  have hdtu : FHeap.Disjoint (rsum (own t) (own u)).heap rR'.heap :=
    FHeap.disjoint_union_left.mpr ⟨hdt.2, hdu⟩
  have hsz : (m.threads.set! u { rec with joined := true }).size = m.threads.size := by
    simp [Array.set!_eq_setIfInBounds]
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_, hleg.csize, ho.conc⟩
  · dsimp only; rw [hsz]
    refine ⟨_, parts_put ht hR₁ hdtu, Holds.congrMem (m := m) rfl rfl ?_⟩
    have := Holds.join hd.1 hRO hh
    show Holds m (rsum (rsum (own t) (own u)) rR') rO
    rw [rsum_assoc]
    exact this
  · refine (hleg.owns w hw).sub fun l h => ?_
    by_cases hwt : w = t
    · subst hwt
      rw [upd_self] at h; rw [upd_ne _ _ (Ne.symm hut), upd_self]
      simp only [FHeap.erase_union, Heap.union_apply] at h ⊢
      cases e : (own w).heap l <;> cases e' : (own u).heap l <;>
        simp_all [FHeap.erase, FHeap.fix]
    · rw [upd_ne _ _ hwt] at h
      by_cases hwu : w = u
      · subst hwu; rw [upd_self] at h; simp [FHeap.erase, FHeap.empty] at h
      · rw [upd_ne _ _ hwu] at h; rw [upd_ne _ _ hwu, upd_ne _ _ hwt]
        exact FHeap.erase_fix_ne.mpr h
  · dsimp only at hw; rw [hsz] at hw
    rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hw)),
      upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hul hw))]
    exact ho.outside w hw

/-- **A step that changes no block, atomic location, thread, clock or recorded access** (a stop,
a futex queue, a cancelation request, a group's table) keeps the parts. -/
theorem keep (ho : FOwned own rO m) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (ht : m'.threads = m.threads) (hc : m'.clocks = m.clocks) (hf : m'.footprint = m.footprint)
    (hx : m.Aux m' := by exact ⟨rfl, rfl, rfl⟩) :
    FOwned own rO m' := by
  have hsh : shapes m' = shapes m := by simp only [shapes, ha]
  refine ⟨?_, fun u hu e he htc => ?_, fun u hu => ho.outside u (ht ▸ hu), by rw [hc, ht]; exact ho.csize,
    ⟨hsh ▸ ho.conc.1, ?_⟩⟩
  · rw [ht]; obtain ⟨rT, h1, h2⟩ := ho.holds
    exact ⟨rT, h1, Holds.congrMem hb ha h2 (MemAuth.Keep.of_aux hb hx)⟩
  · rw [ht] at hu; rw [hf] at he; rw [hb] at htc
    show VClock.le e.clock (m'.clocks[u]!) = true
    rw [hc]; exact ho.owns u hu e he htc
  · obtain ⟨hd, hbd⟩ := ho.conc.2
    exact ⟨fun b b' blk blk' hne h1 h2 => hd b b' blk blk' hne (hb ▸ h1) (hb ▸ h2),
      fun b blk h1 => hbd b blk (hb ▸ h1)⟩

/-- **A recorded access of thread `t` to bytes of its part** (a futex wait's read of its word):
the parts stay. -/
theorem recordAt {b : BlockId} {off len : Nat} {kind : AccessKind} (ho : FOwned own rO m)
    (hc : m.current = t) (ht : t < m.threads.size)
    (hin : ∀ x, off ≤ x → x < off + len → (own t).heap (b, x) ≠ none) (hb : b < m.blocks.size)
    (hw : kind.isWrite = true → ¬ m.IsConst b := by intro h; exact absurd h (by decide)) :
    FOwned own rO (m.recordAt b off len kind) := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hcs : m.current < m.clocks.size := by rw [hc, ho.csize]; exact ht
  have := ho.step (m' := m.recordAt b off len kind) (r' := own t) hc ht hR hRO
    (Holds.congrMem (m := m) rfl rfl hh)
    ⟨by show m.current < (m.clocks.set! m.current _).size; simpa using hcs, ho.conc.1, ho.conc.2⟩
    (Mem.Owns.recordAt hcs (hc ▸ ho.owns t ht))
    (FStepIn.recordAt hcs (FHeap.erase_disjoint hh.disj)
      (fun x h1 h2 => by simpa [FHeap.erase] using hin x h1 h2) hb hw)
  rwa [upd_same] at this

/-- **Every live byte belongs to a thread's part or to the rest.** -/
theorem cover (ho : FOwned own rO m) {l : Loc} {c : Cell} (hl : m.heap l = some c) :
    (∃ u < m.threads.size, (own u).heap l ≠ none) ∨ rO.heap l ≠ none := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  have hu : (rT.heap ∪ rO.heap) l ≠ none := by
    have := hh.heap.1 l
    rw [hl] at this
    intro hn; rw [hn] at this; cases this
  by_cases e : rT.heap l = none
  · exact .inr (by simpa [FHeap.union_apply, e] using hu)
  · obtain ⟨j, hj, rj, hf, hr⟩ := sepN_cover hs e
    exact .inl ⟨j, hj, by rw [← hf]; exact hr⟩

/-- No part and not the rest owns a byte: no byte is live. -/
theorem heap_empty (ho : FOwned own rO m) (h0 : ∀ u < m.threads.size, (own u).heap = FHeap.empty)
    (hO : rO.heap = FHeap.empty) : m.heap = Heap.empty := by
  funext l
  cases hl : m.heap l with
  | none => rfl
  | some c =>
    rcases ho.cover hl with ⟨u, hu, hn⟩ | hn
    · rw [h0 u hu] at hn; exact absurd rfl hn
    · rw [hO] at hn; exact absurd rfl hn

end FOwned

/-- The start memory `{}` has no byte. -/
theorem fheap_empty_mem : ({} : Mem).fheap = FHeap.empty := by
  funext ⟨b, o⟩; simp [Mem.fheap, Mem.heap, FHeap.empty]

theorem FAssn.sep_ex_ex_lift {R : FAssn} {φ : Nat → BlockId → Prop} {P : Nat → BlockId → FAssn}
    {r : Res} (h : (R ⋆ FAssn.ex fun A => FAssn.ex fun b => ⟪φ A b⟫ ⋆ P A b) r) :
    ∃ A b, φ A b ∧ (R ⋆ P A b) r := by
  obtain ⟨r₁, r₂, hd, e, hr, A, b, hp⟩ := h
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact ⟨A, b, hφ, r₁, r₂, hd, e, hr, hp⟩

end Full

/-! ## In a thread -/

namespace Conc
namespace Proto

open Full

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Res} {rO : Res}

/-- **A `MemM` step of thread `t`** with a thread triple on its part `own t`: after it, `t`'s part
is the triple's post, the other parts and `rO` are unchanged, and the step is one of `t`'s
(`FStepIn`: the threads, the groups, the futex queue, … stay). A protocol that counts turns in
strict mode (`Proto.Partial` fails) needs the step to return (`FTTReturns`: the second half of an
`FTTotalTriple`). -/
theorem WP.liftMem_fownedS {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r' hF, (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn hF m m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part htl
  have hcs : m.FConc := ⟨by rw [hc, ho.csize]; exact htl, ho.conc⟩
  have hx := ht m (own t) _ hh hp hcs (hc ▸ ho.owns t htl)
  refine WP.liftMem' (fun e he => ?_) (fun a m' hr => ?_) fun hn => hret.resolve_right fun hr => ?_
  · rw [he] at hx; exact .inr hx
  · rw [hr] at hx
    obtain ⟨r', hh', hq, hc', ho', hs⟩ := hx
    exact ⟨by rw [hs.threads], h a m' r' _ hr (ho.step hc htl hR hRO hh' hc' ho' hs) hq hs⟩
  · obtain ⟨v, m', e⟩ := hr m (own t) _ hh hp hcs (hc ▸ ho.owns t htl)
    rw [e] at hn; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hn

/-- `WP.liftMem_fownedS` with the current thread and the threads of the step. -/
theorem WP.liftMem_fowned {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  WP.liftMem_fownedS ht ho hc htl hp (fun a m' r' _ hr ho' hq hs =>
    h a m' r' hr ho' hq (hs.current.trans hc) hs.threads) hret

/-- `WP.liftMem_fownedS` for a call of a `MemM` function (`callMC`). -/
theorem WP.callMC_fownedS {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r' hF, (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn hF m m' → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((Zig.callMC x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (WP.liftMem_fownedS ht ho hc htl hp (fun a m' r' hF hr ho' hq hs =>
    WP.pure' (h a m' r' hF hr ho' hq hs)) hret)

/-- `WP.liftMem_fowned` for a step of generated code (`liftM`). -/
theorem WP.liftM_fowned {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((_root_.liftM x : CM Tgt σ α).run s) Q G m n :=
  WP.callMC_fownedS ht ho hc htl hp (fun a m' r' _ hr ho' hq hs =>
    h a m' r' hr ho' hq (hs.current.trans hc) hs.threads) hret

/-- `WP.liftMem_fowned` for a call of a `MemM` function (`callMC`). -/
theorem WP.callMC_fowned {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((Zig.callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.liftM_fowned ht ho hc htl hp h hret

end Proto
end Conc

end Zig
