import Proofs.Sync.Lock
import ZigLean.Conc.Word

/-!
# `rwLockRead` over all schedules

WIP.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

set_option linter.unusedSectionVars false

attribute [local irreducible] Proto.WP

/-! ## A change of a thread's part, outside the lock's code -/

namespace Zig.Conc.Lock

variable {γ : Type} {L : Lock γ}

/-- Thread `t` gets the part `L.part g` (same place and resource), with the same memory: the
parts with it are `Owned` (`Owned.add`, `Owned.shrink`), and the free lock's resource does not
overlap it. -/
theorem Inv.repart {G : ThreadId → γ} {m : Mem} {t : ThreadId} {g : γ} (hi : L.Inv G m)
    (hjt : joinedB m t = false) (ho : Owned (upd (L.own G m) t (L.part g ∪ L.held g)) m)
    (hph : L.ph g = L.ph (G t)) (hheld : L.held g = L.held (G t))
    (hpd : Heap.Disjoint (L.part g) (L.held g)) (hoff : L.Off (L.part g))
    (hfr : L.Free G → ∀ hL, L.R G hL → Heap.Disjoint hL (L.part g))
    (hR : ∀ h, L.R (upd G t g) h ↔ L.R G h) : L.Inv (upd G t g) m := by
  have hown : L.own (upd G t g) m = upd (L.own G m) t (L.part g ∪ L.held g) := own_upd rfl hjt
  have hphu : ∀ u, L.ph (upd G t g u) = L.ph (G u) := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact hph
    · rfl
  have hfree : L.Free (upd G t g) ↔ L.Free G := by
    unfold Lock.Free; exact forall_congr' fun u => by rw [hphu]
  have hown_t : L.own G m t = L.part (G t) ∪ L.held (G t) := own_live hjt
  refine ⟨hown ▸ ho, fun u => ?_, fun u hu => ?_, fun u hu => hi.live u (by rw [← hphu]; exact hu),
    hi.blk, ?_, fun u v hu hv => hi.one u v (by rw [← hphu]; exact hu) (by rw [← hphu]; exact hv),
    ⟨hi.loc.only, hi.loc.ok⟩, fun u => ?_, hi.wfpW (fun u h => by rw [← hphu]; exact h),
    fun i l hl => ?_, fun hF => ?_, fun u hu => ?_,
    hi.fq.mono (fun w hw => hw) (fun w _ => hphu w.1), fun hp => ?_⟩
  · unfold upd; split
    · exact hpd
    · exact hi.pdisj u
  · by_cases e : u = t
    · subst e; rw [upd_self, hph] at hu; rw [upd_self, hheld]; exact hi.idle u hu
    · rw [upd_ne _ _ e] at hu ⊢; exact hi.idle u hu
  · obtain ⟨w, hw, hu, hz⟩ := hi.word; exact ⟨w, hw, hu, hz.trans hfree.symm⟩
  · rw [hown]; unfold upd; split
    · rename_i e; subst e
      refine off_union hoff (off_sub (hi.off u) fun l hl => ?_)
      rw [hown_t, hheld] at *; simp only [Heap.union_apply]
      cases e : L.part (G u) l <;> simp_all
    · exact hi.off u
  · obtain ⟨h1, h2⟩ := hi.rel i l hl
    exact ⟨h1, fun u hu => h2 u (by rw [← hphu]; exact hu)⟩
  · obtain ⟨hL, hRL, hs, hdj, hoffL, how⟩ := hi.free (hfree.mp hF)
    refine ⟨hL, (hR hL).mpr hRL, hs, fun u => ?_, hoffL,
      how.weaken fun u h => by rw [← hphu]; exact h⟩
    rw [hown]; unfold upd; split
    · rename_i e; subst e
      refine Heap.disjoint_union_right.mpr ⟨hfr (hfree.mp hF) hL hRL, ?_⟩
      have := hdj u; rw [hown_t] at this; rw [hheld]
      exact (Heap.disjoint_union_right.mp this).2
    · exact hdj u
  · rw [hR]
    by_cases e : u = t
    · subst e; rw [upd_self, hph] at hu; rw [upd_self, hheld]; exact hi.res u hu
    · rw [upd_ne _ _ e] at hu ⊢; exact hi.res u hu
  · obtain ⟨v, hv, hq, h1, h2⟩ := hi.wit hp
    exact ⟨v, hv, hq, by rw [hphu]; exact h1, fun hh => h2 (by rw [← hphu]; exact hh)⟩

end Zig.Conc.Lock

namespace Sync.RwLockRead

/-! ## The ops at a shared word, for every protocol -/

section WordOps

variable {Tgt γ σ : Type} {P : Proto Tgt γ} {n nb : Nat} {W : Word n nb} {s : σ} {t : ThreadId}
  {G : ThreadId → γ} {m : Mem} {d : Nat} {g : γ}

/-- The facts of the protocol at a stop of thread `t` (ghost value `g`) that an op at `W` needs. -/
def WAt (P : Proto Tgt γ) (W : Word n nb) (t : ThreadId) (g : γ) : Prop :=
  ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ →
    W.Ok m₁ ∧ t < m₁.threads.size ∧ m₁.clocks.size = m₁.threads.size

theorem ok_cur {m₁ : Mem} (hw : W.Ok m₁) (c : ThreadId) : W.Ok { m₁ with current := c } :=
  hw.keep (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _)

theorem op_cur {m₁ m' : Mem} (hop : W.Op t { m₁ with current := t } m') : W.Op t m₁ m' :=
  ⟨hop.current, hop.threads, hop.waiters, hop.woken, hop.groups, hop.csize, hop.others,
    hop.mine, hop.bsize, hop.cells, hop.fp, ⟨hop.locs.new, hop.locs.same⟩, hop.fpt⟩

theorem hist_cur (m₁ : Mem) (c : ThreadId) : W.hist { m₁ with current := c } = W.hist m₁ :=
  Word.hist_congr rfl rfl

/-- The newest write of a word. -/
abbrev last (h : Array Word.Entry) : Word.Entry := h[h.size - 1]!

/-- An atomic load at `W` by thread `t`: it reads write `j`, at least the floor. -/
theorem wp_load {ord : AtomicOrder} (hi : P.inv (upd G t g) m) (hW : WAt P W t g)
    {Q : BitVec n × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m' v j, G₁ t = g → P.inv G₁ m₁ →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → Q (v, s) G₁ m' k) :
    P.WP t ((atomicLoadC (n := n) ord nb W.ptr : CM Tgt σ (BitVec n)).run s) Q G m d := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨hw, htl, hcs⟩ := hW G₁ m₁ hg₁ hi₁
  have hwc := ok_cur hw t
  refine WP.callMC (fun e he => (hwc.load_noErr htl hcs hcr e he).elim) fun v m' hr => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hwc.load rfl htl hcs hr
  rw [hist_cur] at hj hv hfl hacq hh
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' v j hg₁ hi₁ hj hv hfl hacq hh hw' (op_cur hop)⟩

/-- An RMW at `W` by thread `t`: it reads the newest write `old`. -/
theorem wp_rmw {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec n}
    (hi : P.inv (upd G t g) m) (hW : WAt P W t g)
    {Q : BitVec n × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m' old, G₁ t = g → P.inv G₁ m₁ →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply signed old v)) →
      (ord.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → Q (old, s) G₁ m' k) :
    P.WP t ((atomicRmwC op signed ord nb W.ptr v : CM Tgt σ (BitVec n)).run s) Q G m d := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨hw, htl, hcs⟩ := hW G₁ m₁ hg₁ hi₁
  have hwc := ok_cur hw t
  refine WP.callMC (fun e he => (hwc.rmw_noErr htl hcs hcr e he).elim) fun old m' hr => ?_
  obtain ⟨hv, hw', hop, hU, hh, hacq⟩ := hwc.rmw rfl htl hcs hr
  rw [hist_cur] at hv hh hacq
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old hg₁ hi₁ hv hU hh hacq hw' (op_cur hop)⟩

/-- A `cmpxchg` at `W` by thread `t`: on success an RMW of the newest write, which holds `exp`;
on failure a read of write `j`. -/
theorem wp_cas {succ fail : AtomicOrder} {exp new : BitVec n}
    (hi : P.inv (upd G t g) m) (hW : WAt P W t g)
    {Q : Option (BitVec n) × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m', G₁ t = g → P.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      ((last (W.hist m₁)).Val exp → W.Holds m' new →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) new) →
        (succ.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j old, old ≠ exp → j < (W.hist m₁).size → (W.hist m₁)[j]!.Val old →
        Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some old, s) G₁ m' k)) :
    P.WP t ((cmpxchgC succ fail nb W.ptr exp new : CM Tgt σ (Option (BitVec n))).run s) Q G m d := by
  unfold cmpxchgC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨hw, htl, hcs⟩ := hW G₁ m₁ hg₁ hi₁
  have hwc := ok_cur hw t
  refine WP.callMC (fun e he => (hwc.cas_noErr (fail := fail) (new := new) htl hcs hcr e he).elim)
    fun r m' hr => ?_
  obtain ⟨hw', hop, ⟨rfl, hv, hU, hh, hacq⟩ | ⟨j, old, rfl, hne, hj, hv, hfl, hacq, hh⟩⟩ :=
    hwc.cas rfl htl hcs hr
  · rw [hist_cur] at hv hh hacq
    exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_cur hop)).1 hv hU hh hacq⟩
  · rw [hist_cur] at hj hv hfl hacq hh
    exact ⟨by rw [hop.threads],
      (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_cur hop)).2 j old hne hj hv hfl hacq hh⟩

/-- An RMW at a 32-bit word, with a decode (`atomicRmwAsC`), by thread `t`. -/
theorem wp_rmwAs {α : Type} [Packed α 32] {W : Word 32 4} {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hi : P.inv (upd G t g) m) (hW : WAt P W t g)
    (hdec : ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → ∀ b, (last (W.hist m₁)).Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m' old r, G₁ t = g → P.inv G₁ m₁ →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply false old (Packed.toBits v)) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply false old (Packed.toBits v))) →
      (ord.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → Q (r, s) G₁ m' k) :
    P.WP t ((atomicRmwAsC op ord 4 W.ptr v : CM Tgt σ α).run s) Q G m d := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨hw, htl, hcs⟩ := hW G₁ m₁ hg₁ hi₁
  have hwc := ok_cur hw t
  refine WP.callMC (fun e he => (atomicRmwAs_noErr (hwc.rmw_noErr htl hcs hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨hv, -⟩ := hwc.rmw rfl htl hcs hr
    rw [hist_cur] at hv
    exact hdec G₁ m₁ hg₁ hi₁ b hv
  obtain ⟨old, hb, hd⟩ := atomicRmwAs_ok hr
  obtain ⟨hv, hw', hop, hU, hh, hacq⟩ := hwc.rmw rfl htl hcs hb
  rw [hist_cur] at hv hh hacq
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old r hg₁ hi₁ hd hv hU hh hacq hw' (op_cur hop)⟩

/-- A `cmpxchg` at a 32-bit word, with a decode (`cmpxchgAsC`), by thread `t`. -/
theorem wp_casAs {α : Type} [Packed α 32] {W : Word 32 4} {succ fail : AtomicOrder} {exp new : α}
    (hi : P.inv (upd G t g) m) (hW : WAt P W t g)
    (hdec : ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m', G₁ t = g → P.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      ((last (W.hist m₁)).Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) (Packed.toBits new)) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, b ≠ Packed.toBits exp → (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → W.hist m' = W.hist m₁ →
        Q (some r, s) G₁ m' k)) :
    P.WP t ((cmpxchgAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m d := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  obtain ⟨hw, htl, hcs⟩ := hW G₁ m₁ hg₁ hi₁
  have hwc := ok_cur hw t
  refine WP.callMC (fun e he => (cmpxchgAs_noErr (hwc.cas_noErr (fail := fail)
    (new := Packed.toBits new) htl hcs hcr) (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, -, hj, hv, -⟩⟩ := hwc.cas rfl htl hcs hr
    · cases he
    · cases he
      rw [hist_cur] at hj hv
      exact hdec G₁ m₁ hg₁ hi₁ j hj _ hv
  rcases cmpxchgAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hU, hh, -⟩ | ⟨j, old, he, -⟩⟩ := hwc.cas rfl htl hcs ho
    · rw [hist_cur] at hv hh
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_cur hop)).1 hv hU hh⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hne, hj, hv, -, -, hh⟩⟩ := hwc.cas rfl htl hcs ho
    · cases he
    · cases he
      rw [hist_cur] at hj hv hh
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_cur hop)).2 j b v hne hd hj hv hh⟩

end WordOps

/-! ## Ghost values -/

/-- Where a thread is in the code of the `RwLock`'s mutex (`Io.Mutex`). -/
inductive MP where
  /-- At `lock`'s first `cmpxchg`. -/
  | cas
  /-- In `lock`'s loop, before its `xchg`. -/
  | spin
  /-- At a futex wait of `lock`. -/
  | wait
  /-- It holds the mutex. -/
  | holds
  /-- At `unlock`'s futex wake. -/
  | wake
  deriving DecidableEq

/-- Where a thread is, outside the semaphore's code. `main` (thread 0) reads; the writer
(thread 1) did `k` increments. -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` in `lockShared`'s loop (`cmpxchg` of `state + reader`). -/
  | ls (j : Bool)
  /-- `main` in `lockShared`'s slow path: in the mutex's `lock`, or it holds the mutex. -/
  | sl (j : Bool) (p : MP)
  /-- `main` did `state += reader` (it owns `n`) and holds the mutex, or is in its `unlock`. -/
  | sr (j : Bool) (p : MP)
  /-- `main` holds the shared lock: it owns `n`. -/
  | sh (j : Bool)
  /-- `main` was the last reader while the writer waits: it posts the semaphore (it owns `n`). -/
  | po
  /-- `main` gave `n` to the semaphore, in its `post`. -/
  | pd
  /-- `main` after `readShared`. -/
  | dn (j : Bool)
  /-- `main` at its join. -/
  | joins
  /-- The writer out of the lock. -/
  | wo (k : Nat)
  /-- The writer did `state += writer`; it is in the mutex's `lock`, or holds the mutex. -/
  | wa (k : Nat) (p : MP)
  /-- The writer saw a reader: it waits at the semaphore. -/
  | ws (k : Nat)
  /-- The writer owns `n`. -/
  | wn (k : Nat)
  /-- The writer did `state &= ~is_writing`; it holds the mutex, or is in its `unlock`. -/
  | wr (k : Nat) (p : MP)
  /-- The writer has ended. -/
  | wf
  deriving DecidableEq

namespace Ph

/-- The place in the mutex's code. -/
def mp : Ph → Option MP
  | sl _ p | sr _ p | wa _ p | wr _ p => some p
  | ws _ | wn _ => some .holds
  | _ => Option.none

/-- The same place, at `p` in the mutex's code. -/
def setM : Ph → MP → Ph
  | sl j _, p => sl j p
  | sr j _, p => sr j p
  | wa k _, p => wa k p
  | wr k _, p => wr k p
  | x, _ => x

/-- The writer's increments (`n`). -/
def cnt : Ph → Nat
  | wo k | wa k _ | ws k | wn k | wr k _ => k
  | wf => 2
  | _ => 0

/-- The three fields of the state word: `writer` (pending), `is_writing`, `reader`. -/
def wb : Ph → Nat
  | wa _ _ => 1
  | _ => 0

def ib : Ph → Nat
  | ws _ | wn _ => 1
  | _ => 0

def rb : Ph → Nat
  | sr _ _ | sh _ => 1
  | _ => 0

/-- The thread owns `n`. -/
def mustN : Ph → Bool
  | sr _ _ | sh _ | po | wn _ => true
  | _ => false

/-- The writer waits at the semaphore. -/
def isWs : Ph → Bool
  | ws _ => true
  | _ => false

/-- `main` gave `n` to the semaphore (or has no shared lock, after it). -/
def gave : Ph → Bool
  | pd | dn _ | joins => true
  | _ => false

/-- A thread that has started and not ended. -/
def live : Ph → Bool
  | none | wf => false
  | _ => true

/-- In the semaphore's code. -/
def inSem : Ph → Bool
  | po | pd | ws _ => true
  | _ => false

/-- `main`'s places after its spawn. -/
def isMain : Ph → Bool
  | ls _ | sl _ _ | sr _ _ | sh _ | po | pd | dn _ | joins => true
  | _ => false

/-- `main` after its join of the writer. -/
def jd : Ph → Bool
  | ls j | sl j _ | sr j _ | sh j | dn j => j
  | _ => false

/-- `main` while the writer waits at the semaphore: it holds the shared lock or posts. -/
def pw : Ph → Bool
  | sh _ | po | pd | sr _ .wake => true
  | _ => false

/-- The writer's places (`k ≤ 2` increments). -/
def isW : Ph → Bool
  | wo k | wn k => decide (k ≤ 2)
  | wa k _ | ws k => decide (k < 2)
  | wr k _ => decide (k ≤ 2)
  | wf => true
  | _ => false

end Ph

/-- A thread's ghost value: the semaphore's mutex's part, its ghost value in the semaphore's code
(`S`), and its place. -/
abbrev Gh (S : Type) := LG × (S × Ph)

/-- The `Shared` (block 0): `io` at 0, the `RwLock` at 16 (its state at 16, the semaphore at
24, the semaphore's mutex at 32, its condition at 36, its mutex at 48), `n` at 56. -/
def bPtr : Ptr := ⟨some 0, 0⟩

/-- `n`. -/
def nPtr : Ptr := bPtr.add 56

/-- The `RwLock`'s state. -/
def WS : Word 64 8 := { b := 0, o := 16 }

/-- The `RwLock`'s mutex. -/
def WM : Word 32 4 := { b := 0, o := 48 }

/-- The state word of `main` at `a` and the writer at `b`. -/
def sv (a b : Ph) : BitVec 64 := BitVec.ofNat 64 (2 * b.wb + b.ib + a.rb * 4294967296)

/-- The values of the state word: `writer` or `is_writing`, and `reader`. -/
def sVals : List (BitVec 64) := [0, 1, 2, 4294967296, 4294967297, 4294967298]

/-- The values of the mutex word: `unlocked`, `locked_once`, `contended`. -/
def mVals : List (BitVec 32) := [0, 1, 2]

/-- `n` holds `k`. -/
def NPts (k : Nat) : Assn := pts nPtr 4 (BitVec.ofNat 32 k)

/-- `main` at `a`, the writer at `b` (module doc). -/
structure Flags (a b : Ph) : Prop where
  /-- The writer waits at the semaphore only while `main` holds the shared lock, or after. -/
  ws : ∀ k, b = .ws k → a.pw ∨ a.gave
  /-- `main` posts only while the writer waits. -/
  po : a = .po → ∃ k, b = .ws k
  /-- At most one thread holds the mutex. -/
  one : ¬ (a.mp = some .holds ∧ b.mp = some .holds)
  /-- `main` at `sr` holds the mutex, or is at its `unlock`'s wake. -/
  sr : ∀ j p, a = .sr j p → p = .holds ∨ p = .wake
  /-- After its join, `main` knows the writer has ended. -/
  jd : a.jd → b = .wf

/-- The threads: `main` alone before its spawn; then `main` and the writer, which `main`
joins only after its end. -/
def Shape (Y : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ Y 0 = .pre ∧ ∀ u, 1 ≤ u → Y u = .none) ∨
   (m.threads.size = 2 ∧ (m.threads[1]? = some { spawner := 0, joined := false } ∨
      (m.threads[1]? = some { spawner := 0, joined := true } ∧ Y 1 = .wf)) ∧
    (Y 0).isMain ∧ (Y 1).isW ∧ ∀ u, 2 ≤ u → Y u = .none))

/-- Each access to the bytes of `io` (0..16) is a read, or happened before every thread. -/
def IoOk (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.off < 16 → e.kind = .read ∨ AllLe m e.clock

/-- Block 0 is the live `Shared`: 64 bytes on the stack, at an address that is a multiple of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 64 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- The semaphore has `n`: the writer waits, and `main` gave it. -/
def hasP (Y : ThreadId → Ph) : Bool := (Y 1).isWs && (Y 0).gave

/-- The semaphore's permit count (module doc). -/
def pv (Y : ThreadId → Ph) : BitVec 64 := if hasP Y then 1 else 0

/-- The resource of the semaphore's free permit: `n`. -/
def Res (Y : ThreadId → Ph) : Assn := if hasP Y then NPts (Y 1).cnt else emp

/-- `n` is in the state word: no thread owns it, and the semaphore does not have it. -/
def Car (a b : Ph) : Prop := a.mustN = false ∧ b.mustN = false ∧ (b.isWs && a.gave) = false

/-- No thread owns `n` (`hn`): each access to it happened before the release clock of the
state's newest write, or before every thread. -/
def CarOk (m : Mem) (hn : Heap) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches hn ∨ m.blocks.size ≤ e.block) →
    VClock.le e.clock (last (WS.hist m)).relClock = true ∨ AllLe m e.clock


/-- A thread asleep at the mutex: its place, and the other thread `o` holds the mutex (which is
`contended`) or wakes it. -/
def MQ (m : Mem) (x o : Ph) : Prop :=
  x.mp = some .wait ∧ ((o.mp = some .holds ∧ (last (WM.hist m)).Val (2 : BitVec 32)) ∨
    o.mp = some .wake)

/-! ## Facts of the places -/

namespace Ph

/-- A place with a place in the mutex's code (`setM` changes it). -/
def isMx : Ph → Bool
  | sl _ _ | sr _ _ | wa _ _ | wr _ _ => true
  | _ => false

theorem mp_setM {x : Ph} (h : x.isMx) (p : MP) : (x.setM p).mp = some p := by
  cases x <;> simp_all [isMx, setM, mp]

@[simp] theorem wb_setM (x : Ph) (p : MP) : (x.setM p).wb = x.wb := by cases x <;> rfl
@[simp] theorem ib_setM (x : Ph) (p : MP) : (x.setM p).ib = x.ib := by cases x <;> rfl
@[simp] theorem rb_setM (x : Ph) (p : MP) : (x.setM p).rb = x.rb := by cases x <;> rfl
@[simp] theorem isWs_setM (x : Ph) (p : MP) : (x.setM p).isWs = x.isWs := by cases x <;> rfl
@[simp] theorem gave_setM (x : Ph) (p : MP) : (x.setM p).gave = x.gave := by cases x <;> rfl
@[simp] theorem mustN_setM (x : Ph) (p : MP) : (x.setM p).mustN = x.mustN := by cases x <;> rfl
@[simp] theorem cnt_setM (x : Ph) (p : MP) : (x.setM p).cnt = x.cnt := by cases x <;> rfl
@[simp] theorem isMain_setM (x : Ph) (p : MP) : (x.setM p).isMain = x.isMain := by cases x <;> rfl
@[simp] theorem isW_setM (x : Ph) (p : MP) : (x.setM p).isW = x.isW := by cases x <;> rfl
@[simp] theorem inSem_setM (x : Ph) (p : MP) : (x.setM p).inSem = x.inSem := by cases x <;> rfl
@[simp] theorem isMx_setM (x : Ph) (p : MP) : (x.setM p).isMx = x.isMx := by cases x <;> rfl
@[simp] theorem jd_setM (x : Ph) (p : MP) : (x.setM p).jd = x.jd := by cases x <;> rfl

theorem mx_ne {x : Ph} (h : x.isMx) :
    x ≠ .po ∧ x.gave = false ∧ x ≠ .joins ∧ (∀ k, x ≠ .ws k) := by
  cases x <;> simp_all [isMx, gave]

theorem wb_ib (x : Ph) : x.wb + x.ib ≤ 1 := by cases x <;> simp [wb, ib]
theorem rb_le (x : Ph) : x.rb ≤ 1 := by cases x <;> simp [rb]

end Ph

/-! ## The state word's values -/

/-- A state: `writer` (`w`), `is_writing` (`i`), `reader` (`r`). -/
def sv3 (w i r : Nat) : BitVec 64 := BitVec.ofNat 64 (2 * w + i + r * 4294967296)

/-- The reader mask (bits 32..62). -/
abbrev RM : BitVec 64 := 9223372032559808512

theorem sv_eq (a b : Ph) : sv a b = sv3 b.wb b.ib a.rb := rfl

theorem cases3 {w i r : Nat} (hwi : w + i ≤ 1) (hr : r ≤ 1) :
    (w = 0 ∧ i = 0 ∨ w = 1 ∧ i = 0 ∨ w = 0 ∧ i = 1) ∧ (r = 0 ∨ r = 1) := by omega

theorem sv3_mem {w i r : Nat} (hwi : w + i ≤ 1) (hr : r ≤ 1) : sv3 w i r ∈ sVals := by
  obtain ⟨h1, h2⟩ := cases3 hwi hr
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with rfl | rfl <;> decide

theorem sv_mem (a b : Ph) : sv a b ∈ sVals := sv3_mem (Ph.wb_ib b) (Ph.rb_le a)

/-- The writer's `state += writer`. -/
theorem sv3_add2 {r : Nat} (hr : r ≤ 1) :
    RmwOp.add.apply false (sv3 0 0 r) (2 : BitVec 64) = sv3 1 0 r := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> decide

/-- The writer's `state += is_writing -% writer`: it reads `reader`. -/
theorem sv3_dec {r : Nat} (hr : r ≤ 1) :
    RmwOp.add.apply false (sv3 1 0 r) (18446744073709551615 : BitVec 64) = sv3 0 1 r ∧
      ((sv3 1 0 r &&& RM) != 0) = decide (r = 1) := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> decide

/-- The writer's `state &= ~is_writing`. -/
theorem sv3_and {r : Nat} (hr : r ≤ 1) :
    RmwOp.and.apply false (sv3 0 1 r) (18446744073709551614 : BitVec 64) = sv3 0 0 r := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> decide

/-- `main`'s `state += reader`. -/
theorem sv3_addR {w i : Nat} (hwi : w + i ≤ 1) :
    RmwOp.add.apply false (sv3 w i 0) (4294967296 : BitVec 64) = sv3 w i 1 := by
  rcases (by omega : w = 0 ∧ i = 0 ∨ w = 1 ∧ i = 0 ∨ w = 0 ∧ i = 1) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- `main`'s `state -= reader`: it reads `reader = 1` and `is_writing`. -/
theorem sv3_sub {w i : Nat} (hwi : w + i ≤ 1) :
    RmwOp.sub.apply false (sv3 w i 1) (4294967296 : BitVec 64) = sv3 w i 0 ∧
      ((sv3 w i 1 &&& RM) == 4294967296) = true ∧
      ((sv3 w i 1 &&& 1) != 0) = decide (i = 1) := by
  rcases (by omega : w = 0 ∧ i = 0 ∨ w = 1 ∧ i = 0 ∨ w = 0 ∧ i = 1) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- `lockShared`'s `cmpxchg` of `state + reader`. -/
theorem sv3_inc : sv3 0 0 0 + (4294967296 : BitVec 64) = sv3 0 0 1 := by decide

/-- A state with no `writer` and no `is_writing` (`lockShared`'s test) is `reader` or not. -/
theorem sVals_free {v : BitVec 64} (hv : v ∈ sVals) (h : (v &&& 4294967295) == 0) :
    v = sv3 0 0 0 ∨ v = sv3 0 0 1 := by
  simp only [sVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | (revert h; decide)

/-- `lockShared`'s `state + reader` does not overflow. -/
theorem sVals_addR {v : BitVec 64} (hv : v ∈ sVals) :
    (add false v (4294967296 : BitVec 64)).run = some (.ok (v + 4294967296)) := by
  simp only [sVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The state of the threads' places, as `sv3`: the fields. -/
theorem sv3_inj {w i r w' i' r' : Nat} (h1 : w + i ≤ 1) (h2 : r ≤ 1) (h1' : w' + i' ≤ 1)
    (h2' : r' ≤ 1) (h : sv3 w i r = sv3 w' i' r') : w = w' ∧ i = i' ∧ r = r' := by
  obtain ⟨a1, a2⟩ := cases3 h1 h2
  obtain ⟨b1, b2⟩ := cases3 h1' h2'
  rcases a1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases a2 with rfl | rfl <;>
    rcases b1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases b2 with rfl | rfl <;>
    first | exact ⟨rfl, rfl, rfl⟩ | (revert h; decide)

/-! ## The protocol, with the semaphore's part -/

/-- The semaphore's part of the protocol (module doc): the rest of its invariant. -/
structure Sem (S : Type) where
  inv : (ThreadId → Gh S) → Mem → Prop

variable {S : Type} (E : Sem S)

/-- The semaphore (24..48 of the `Shared`). -/
def semPtr : Ptr := ⟨some 0, 24⟩

/-- The resource of the semaphore's mutex: the permit count and the free permit's `n`. -/
def semR (Y : ThreadId → S × Ph) : Assn :=
  pts semPtr 8 (pv fun u => (Y u).2) ∗ Res fun u => (Y u).2

/-- The semaphore's mutex: a lock that owns `semR`. -/
abbrev L (S : Type) : Lock (Gh S) := Lock.prod 0 32 (semR (S := S))

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh S) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2.2) m
  flags : Flags (G 0).2.2 (G 1).2.2
  io : IoOk m
  blk : BlkOk m
  ws : WS.Ok m
  wm : WM.Ok m
  /-- Each write of the state word is a state. -/
  shist : ∀ j < (WS.hist m).size, ∃ v ∈ sVals, (WS.hist m)[j]!.Val v
  /-- The newest write: the state of the threads' places. -/
  slast : (last (WS.hist m)).Val (sv (G 0).2.2 (G 1).2.2)
  /-- Each write of the mutex word is `0`, `1` or `2`. -/
  mhist : ∀ j < (WM.hist m).size, ∃ v ∈ mVals, (WM.hist m)[j]!.Val v
  /-- The newest write is `0` if no thread holds the mutex. -/
  mlast : ∃ v ∈ mVals, (last (WM.hist m)).Val v ∧ (v = 0 ↔ ∀ u, (G u).2.2.mp ≠ some .holds)
  /-- A thread asleep at the mutex. -/
  mq : ∀ w ∈ m.waiters, w.2 = WM.ptr →
    (w.1 = 0 ∧ MQ m (G 0).2.2 (G 1).2.2) ∨ (w.1 = 1 ∧ MQ m (G 1).2.2 (G 0).2.2)
  /-- Out of the semaphore's code, a thread is out of its mutex's code. -/
  lph : ∀ u, (G u).2.2.inSem = false →
    (G u).1.ph = .out ∨ (G u).1.ph = .away ∨ ((G u).1.ph = .gone ∧ (G u).2.2.live = false)
  /-- A thread's part: `n` at a place that owns it, else nothing. -/
  parts : ∀ u, if (G u).2.2.mustN then NPts (G 1).2.2.cnt (G u).1.part else (G u).1.part = Heap.empty
  /-- `n` in the state word. -/
  car : Car (G 0).2.2 (G 1).2.2 → ∃ hn, NPts (G 1).2.2.cnt hn ∧ hn.Sub m.heap ∧ CarOk m hn

variable [Inhabited S]

/-- The protocol, in strict mode. -/
def proto : Proto Tgt (Gh S) where
  inv G m := (L S).Inv G m ∧ U G m ∧ E.inv G m
  init tgt g := match tgt with
    | .writer p => p = bPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, (default, .wo 0))
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.2 = .wf
  strict := true
  joins g := g.1.ph = .out ∧ g.2.2 = .joins

/-- A step that keeps the semaphore's bytes (24..48) and its futex queue (module doc). -/
structure Frame (m m' : Mem) : Prop where
  keep : ∀ W : Word 32 4, W.b = 0 → 24 ≤ W.o → W.o + 4 ≤ 48 → W.Keep m m'
  threads : m'.threads.size = m.threads.size
  waiters : ∀ w, w.2 ≠ WM.ptr → (w ∈ m'.waiters ↔ w ∈ m.waiters)
  clocks : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true

/-- The initial semaphore. -/
def sem0 : Io_Semaphore :=
  { mutex := { state := { raw := Io_Mutex_State.unlocked } }
    cond := { state := { raw := Packed.ofBits (0 : BitVec 32) }, epoch := { raw := 0 } }
    permits := 0 }

/-- What the proof of `rwLockRead` needs of the semaphore's ops (module doc). -/
structure Sem.Spec : Prop where
  /-- `wait` by the writer, who saw a reader: it takes `n` (`Res`). -/
  wait : ∀ (k : Nat) (G : ThreadId → Gh S) (m : Mem) (d : Nat) (io : Io),
    (proto E).inv (upd G 1 (⟨.out, Heap.empty, Heap.empty⟩, (default, .ws k))) m → m.current = 1 →
    (proto E).WP 1 (Io_Semaphore_waitUncancelable semPtr io)
      (fun _ G' m' d' => d' ≤ d ∧ m'.current = 1 ∧ ∃ h, NPts k h ∧
        (proto E).inv (upd G' 1 (⟨.out, h, Heap.empty⟩, (default, .wn k))) m') G m d
  /-- `post` by `main`, the last reader: it gives `n` to the semaphore. -/
  post : ∀ (h : Heap) (G : ThreadId → Gh S) (m : Mem) (d : Nat) (io : Io),
    (proto E).inv (upd G 0 (⟨.out, h, Heap.empty⟩, (default, .po))) m → m.current = 0 →
    (proto E).WP 0 (Io_Semaphore_post semPtr io)
      (fun _ G' m' d' => d' ≤ d ∧ m'.current = 0 ∧
        (proto E).inv (upd G' 0 (⟨.out, Heap.empty, Heap.empty⟩, (default, .pd))) m') G m d
  /-- A thread asleep at a futex of the semaphore's condition is the writer, while `main` has
  not ended its `post`. -/
  live : ∀ G m, (proto E).inv G m → ∀ w ∈ m.waiters, w.2 ≠ (L S).ptr → w.2 ≠ WM.ptr →
    w.1 = 1 ∧ (∃ k, (G 1).2.2 = .ws k) ∧
      (G 0).2.2.pw
  /-- A step out of the semaphore's code keeps its invariant. -/
  frame : ∀ G G' m m', E.inv G m → Frame m m' →
    (∀ u, (G' u).2.1 = (G u).2.1 ∧ (G' u).1.held = (G u).1.held ∧
      (∀ x, 24 ≤ x → x < 48 → (G' u).1.part (0, x) = none) ∧
      ((G' u).1.ph = (G u).1.ph ∨ ((G u).1.ph ≠ .holds ∧ (G' u).1.ph ≠ .holds))) →
    E.inv G' m'
  /-- The start, after the spawn: the semaphore's bytes hold `sem0`, no atomic op was done, no
  thread waits, and each access happened before every thread. -/
  start : ∀ G m, (∀ u, (G u).2.1 = default) →
    (∀ u, (G u).1.ph = .out ∨ (G u).1.ph = .gone) → BlkOk m →
    curBytes m 0 24 24 = Enc.encode sem0 → m.atomics = #[] → m.waiters = #[] →
    (∀ e ∈ m.footprint, AllLe m e.clock) → E.inv G m

/-! ## Basic facts -/

variable {E}

/-- A thread out of the semaphore's mutex, at `x`, with the part `h`. -/
def gA (x : Ph) (h : Heap) (s : S) : Gh S := (⟨.out, h, Heap.empty⟩, (s, x))

theorem upd1_0 (G : ThreadId → Gh S) (g : Gh S) : upd G 1 g 0 = G 0 := upd_ne _ _ (by decide)
theorem upd0_1 (G : ThreadId → Gh S) (g : Gh S) : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)

/-- A change of a running thread's place keeps the threads. -/
theorem shape_upd {Y : ThreadId → Ph} {m : Mem} {t : ThreadId} {y : Ph} (h : Shape Y m)
    (hY : (Y t).isMain ∨ ((Y t).isW ∧ Y t ≠ .wf)) (hm : (Y t).isMain → y.isMain)
    (hw : (Y t).isW → y.isW) : Shape (upd Y t y) m := by
  obtain ⟨h0, ⟨-, hp, hn⟩ | ⟨hs, hj, hM, hW, hn⟩⟩ := h
  · exfalso
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [hp] at hY; simp [Ph.isMain, Ph.isW] at hY
    · rw [hn t ht] at hY; simp [Ph.isMain, Ph.isW] at hY
  rcases Nat.lt_or_ge t 2 with ht | ht
  · rcases (by unfold ThreadId at *; omega : t = 0 ∨ t = 1) with rfl | rfl
    · have hm' : (Y 0).isW = false := by revert hM; cases Y 0 <;> simp [Ph.isMain, Ph.isW]
      refine ⟨h0, .inr ⟨hs, ?_, by rw [upd_self]; exact hm hM, by rw [upd_ne _ _ (by decide)]; exact hW,
        fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn u hu⟩⟩
      rcases hj with hj | ⟨hj, hf⟩
      · exact .inl hj
      · exact .inr ⟨hj, by rw [upd_ne _ _ (by decide)]; exact hf⟩
    · refine ⟨h0, .inr ⟨hs, ?_, by rw [upd_ne _ _ (by decide)]; exact hM, by rw [upd_self]; exact hw hW,
        fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn u hu⟩⟩
      rcases hj with hj | ⟨hj, hf⟩
      · exact .inl hj
      · rw [hf] at hY; simp [Ph.isMain, Ph.isW] at hY
  · rw [hn t ht] at hY; simp [Ph.isMain, Ph.isW] at hY

theorem ph_upd (G : ThreadId → Gh S) (t : ThreadId) (g : Gh S) :
    (fun u => (upd G t g u).2.2) = upd (fun u => (G u).2.2) t g.2.2 := by
  funext u; unfold upd; split <;> rfl

/-- `n`'s cells. -/
theorem npts_at {k : Nat} {h : Heap} (hp : NPts k h) (l : Zig.Loc) :
    h l ≠ none ↔ l.1 = 0 ∧ 56 ≤ l.2 ∧ l.2 < 60 := by
  obtain ⟨A, S, K, bs, -, hs, -, ⟨b, hb, -, hl⟩, -⟩ := hp
  cases hb
  rw [hl]
  have : Enc.size (BitVec 32) = 4 := rfl
  obtain ⟨b, o⟩ := l
  simp only [nPtr, bPtr, Ptr.add, hs, this]
  split <;> simp_all <;> omega

theorem npts_none {k : Nat} {h : Heap} (hp : NPts k h) {l : Zig.Loc}
    (hl : ¬ (l.1 = 0 ∧ 56 ≤ l.2 ∧ l.2 < 60)) : h l = none := by
  cases e : h l with
  | none => rfl
  | some c => exact absurd ((npts_at hp l).mp (by rw [e]; simp)) hl

/-- Two heaps of `n` overlap. -/
theorem npts_meet {k k' : Nat} {h h' : Heap} (hp : NPts k h) (hp' : NPts k' h')
    (hd : Heap.Disjoint h h') : False := by
  rcases hd (0, 56) with e | e
  · exact (npts_at hp _).mpr ⟨rfl, by decide, by decide⟩ e
  · exact (npts_at hp' _).mpr ⟨rfl, by decide, by decide⟩ e

/-- The cell of byte `x < 64` of the `Shared`. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 64) : m.heap (0, x) ≠ none := by
  obtain ⟨blk, hblk, hl, hs, -⟩ := hb
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

/-- The same first cell: the same block 0. -/
theorem blk_keep {m m' : Mem} (hb : BlkOk m) (h : m'.heap (0, 0) = m.heap (0, 0)) : BlkOk m' := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (0, 0) = some ⟨blk.bytes[0]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  exact ⟨blk', hblk', by simpa using hl', by rw [← hS, hs], by rw [← hA, ha], by rw [← hK, hk]⟩

/-- The access `e` does not touch `n`. -/
def NOff (e : FootprintEntry) : Prop := e.block ≠ 0 ∨ e.off + e.len ≤ 56 ∧ e.off < 56 ∨ 60 ≤ e.off

theorem NOff.not {e : FootprintEntry} (he : NOff e) {k : Nat} {hn : Heap} (hp : NPts k hn) :
    ¬ e.Touches hn := fun ⟨x, h1, h2, h3⟩ => by
  obtain ⟨hb, hx1, hx2⟩ := (npts_at hp _).mp h3
  dsimp only at hb hx1 hx2
  rcases he with he | ⟨he1, he2⟩ | he
  · exact he hb
  · rcases h2 with h2 | h2 <;> omega
  · omega

/-- `n` stays in the state word, if its cells and the release clock of the state's newest write
stay, and each new access does not touch it. -/
theorem car_keep {m m' : Mem} {k : Nat} {hn : Heap} (hp : NPts k hn) (hs : hn.Sub m.heap)
    (hc : CarOk m hn)
    (hrel : VClock.le (last (WS.hist m)).relClock (last (WS.hist m')).relClock = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (NOff e ∧ e.block < m'.blocks.size))
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hcells : ∀ x, 56 ≤ x → x < 60 → m'.heap (0, x) = m.heap (0, x))
    (hall : ∀ c, AllLe m c → AllLe m' c) : hn.Sub m'.heap ∧ CarOk m' hn := by
  refine ⟨fun l c hl => ?_, fun e he htc => ?_⟩
  · obtain ⟨hb, h1, h2⟩ := (npts_at hp l).mp (by rw [hl]; simp)
    obtain ⟨b, x⟩ := l; dsimp only at hb h1 h2; subst hb
    rw [hcells x h1 h2]; exact hs _ c hl
  · rcases hfp e he with he' | ⟨hno, hb⟩
    · rcases hc e he' (htc.imp id fun h => Nat.le_trans hbs h) with h | h
      · exact .inl (VClock.le_trans h hrel)
      · exact .inr (hall _ h)
    · rcases htc with h | h
      · exact absurd h (hno.not hp)
      · exact absurd hb (Nat.not_lt.mpr h)

/-- A step that keeps the two words, the threads, the threads at the mutex, `n` and the order of
the clocks: `U` with the same ghost values. -/
theorem U_keep {G : ThreadId → Gh S} {m m' : Mem} (hu : U G m) (hkS : WS.Keep m m')
    (hkM : WM.Keep m m') (ht : m'.threads = m.threads)
    (hq : ∀ w ∈ m'.waiters, w.2 = WM.ptr → w ∈ m.waiters) (hio : IoOk m') (hblk : BlkOk m')
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (NOff e ∧ e.block < m'.blocks.size))
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hcells : ∀ x, 56 ≤ x → x < 60 → m'.heap (0, x) = m.heap (0, x))
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) : U G m' := by
  have hhS := Word.hist_keep hu.ws hkS
  have hhM := Word.hist_keep hu.wm hkM
  have hall : ∀ c, AllLe m c → AllLe m' c := fun c h u hu' =>
    VClock.le_trans (h u (ht ▸ hu')) (hcl u)
  refine ⟨by unfold Shape at *; rw [ht]; exact hu.shape, hu.flags, hio, hblk, hu.ws.keep hkS,
    hu.wm.keep hkM, by rw [hhS]; exact hu.shist, by rw [hhS]; exact hu.slast,
    by rw [hhM]; exact hu.mhist, by rw [hhM]; exact hu.mlast, fun w hw hp => ?_, hu.lph, hu.parts,
    fun hc => ?_⟩
  · unfold MQ; rw [hhM]; exact hu.mq w (hq w hw hp) hp
  · obtain ⟨hn', hp, hs, hok⟩ := hu.car hc
    exact ⟨hn', hp, car_keep hp hs hok (by rw [hhS]; exact VClock.le_refl _) hfp hbs hcells hall⟩

/-- A change of the ghost values with the same memory: `U` from the facts that depend on
them; the state word and the mutex's places stay. -/
theorem U_ghost {G G' : ThreadId → Gh S} {m : Mem} (hu : U G m)
    (hsh : Shape (fun u => (G' u).2.2) m) (hfl : Flags (G' 0).2.2 (G' 1).2.2)
    (hsv : sv (G' 0).2.2 (G' 1).2.2 = sv (G 0).2.2 (G 1).2.2)
    (hmp : ∀ u, (G' u).2.2.mp = (G u).2.2.mp)
    (hlph : ∀ u, (G' u).2.2.inSem = false →
      (G' u).1.ph = .out ∨ (G' u).1.ph = .away ∨ ((G' u).1.ph = .gone ∧ (G' u).2.2.live = false))
    (hparts : ∀ u, if (G' u).2.2.mustN then NPts (G' 1).2.2.cnt (G' u).1.part
      else (G' u).1.part = Heap.empty)
    (hcar : Car (G' 0).2.2 (G' 1).2.2 → ∃ hn, NPts (G' 1).2.2.cnt hn ∧ hn.Sub m.heap ∧ CarOk m hn) :
    U G' m := by
  refine ⟨hsh, hfl, hu.io, hu.blk, hu.ws, hu.wm, hu.shist, by rw [hsv]; exact hu.slast,
    hu.mhist, ?_, fun w hw hp => ?_, hlph, hparts, hcar⟩
  · obtain ⟨v, hv, hl, hz⟩ := hu.mlast
    exact ⟨v, hv, hl, hz.trans (forall_congr' fun u => by rw [hmp])⟩
  · unfold MQ; rw [hmp, hmp]; exact hu.mq w hw hp

/-! ## The heap of the parts and of the resource -/

/-- Bytes that no part and no resource has: below the semaphore, and between its end and `n`. -/
def Free8 (x : Nat) : Prop := x < 24 ∨ (48 ≤ x ∧ x < 56)

/-- The cells of the permit count. -/
theorem pts_sem {v : BitVec 64} {h : Heap} (hp : pts semPtr 8 v h) (l : Zig.Loc) (hl : h l ≠ none) :
    l.1 = 0 ∧ 24 ≤ l.2 ∧ l.2 < 32 := by
  obtain ⟨A, S, K, bs, -, hs, -, ⟨b, hb, -, hown⟩, -⟩ := hp
  cases hb
  rw [hown] at hl
  have : Enc.size (BitVec 64) = 8 := rfl
  obtain ⟨b, o⟩ := l
  simp only [semPtr, hs, this] at hl ⊢
  split at hl
  · simp_all
  · exact absurd rfl hl

/-- The resource's cells: the permit count, and `n` while the semaphore has it. -/
theorem semR_at {Y : ThreadId → S × Ph} {h : Heap} (hR : semR Y h) (l : Zig.Loc) (hl : h l ≠ none) :
    l.1 = 0 ∧ ((24 ≤ l.2 ∧ l.2 < 32) ∨ (hasP (fun u => (Y u).2) ∧ 56 ≤ l.2 ∧ l.2 < 60)) := by
  obtain ⟨h1, h2, -, rfl, hp, hr⟩ := hR
  simp only [Heap.union_apply] at hl
  cases e : h1 l with
  | some c => obtain ⟨a, b, c⟩ := pts_sem hp l (by rw [e]; simp); exact ⟨a, .inl ⟨b, c⟩⟩
  | none =>
    rw [e] at hl; simp only [Option.none_or] at hl
    unfold Res at hr; split at hr
    · rename_i hh; obtain ⟨a, b, c⟩ := (npts_at hr l).mp hl; exact ⟨a, .inr ⟨hh, b, c⟩⟩
    · rw [hr] at hl; exact absurd rfl hl

/-- The resource with other places that keep `hasP` and, while it holds, the writer's count. -/
theorem semR_congr {Y Y' : ThreadId → S × Ph}
    (h1 : hasP (fun u => (Y' u).2) = hasP (fun u => (Y u).2))
    (h2 : hasP (fun u => (Y u).2) = true → (Y' 1).2.cnt = (Y 1).2.cnt) (h : Heap) :
    semR Y' h ↔ semR Y h := by
  unfold semR pv Res; rw [h1]
  split
  · rename_i hh; simp only [h2 hh]
  · exact Iff.rfl

/-- A change of thread `t`'s place that keeps `isWs`, `gave` and `cnt` keeps the resource. -/
theorem R_upd {G : ThreadId → Gh S} {t : ThreadId} {g' : Gh S}
    (hw : g'.2.2.isWs = (G t).2.2.isWs) (hg : g'.2.2.gave = (G t).2.2.gave)
    (hc : g'.2.2.cnt = (G t).2.2.cnt) (h : Heap) : (L S).R (upd G t g') h ↔ (L S).R G h := by
  have e : ∀ (f : Ph → Bool), f g'.2.2 = f (G t).2.2 → ∀ u, f (upd G t g' u).2.2 = f (G u).2.2 :=
    fun f hf u => by
      unfold upd; split
      · rename_i e; subst e; exact hf
      · rfl
  refine semR_congr (by unfold hasP; rw [e _ hw, e _ hg]) (fun _ => ?_) h
  unfold upd; split
  · rename_i e; subst e; exact hc
  · rfl

/-- Ghost values with the same places: the same resource. -/
theorem R_two {G G' : ThreadId → Gh S} (h2 : ∀ u, (G' u).2.2 = (G u).2.2) (h : Heap) :
    (L S).R G' h ↔ (L S).R G h :=
  semR_congr (by unfold hasP; simp only [h2]) (fun _ => by simp only [h2]) h

theorem R_none {Y : ThreadId → S × Ph} {h : Heap} (hR : semR Y h) {x : Nat}
    (hx : Free8 x) : h (0, x) = none := by
  cases e : h (0, x) with
  | none => rfl
  | some c =>
    obtain ⟨-, h1 | ⟨-, h1⟩⟩ := semR_at hR (0, x) (by rw [e]; simp) <;>
      (dsimp only at h1; unfold Free8 at hx; omega)

theorem part_none {G : ThreadId → Gh S} {m : Mem} (hu : U G m) (u : ThreadId) {x : Nat}
    (hx : x < 56 ∨ 60 ≤ x) : (G u).1.part (0, x) = none := by
  have := hu.parts u; split at this
  · exact npts_none this (by omega)
  · rw [this]; rfl

theorem own_none {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (u : ThreadId) {x : Nat} (hx : Free8 x) : (L S).own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    have hp := part_none hi.2.1 u (x := x) (by unfold Free8 at hx; omega)
    simp only [Heap.union_apply, hp, Option.none_or]
    by_cases hh : (L S).ph (G u) = .holds
    · exact R_none (hi.1.res u hh) hx
    · rw [show (G u).1.held = (L S).held (G u) from rfl, hi.1.idle u hh]; rfl

/-- A word in the free bytes has no byte of a part or of the resource. -/
theorem off_own {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    {n nb : Nat} {W : Word n nb} (hb : W.b = 0) (ho : ∀ x, W.o ≤ x → x < W.o + nb → Free8 x)
    (u : ThreadId) : W.Off ((L S).own G m u) := fun x h1 h2 => by
  rw [hb]; exact own_none hi u (ho x h1 h2)

theorem off_R {n nb : Nat} {W : Word n nb} (hb : W.b = 0)
    (ho : ∀ x, W.o ≤ x → x < W.o + nb → Free8 x) :
    ∀ G hL, (L S).R G hL → W.Off hL := fun _ _ hR x h1 h2 => by
  rw [hb]; exact R_none hR (ho x h1 h2)

theorem ws_free : ∀ x, WS.o ≤ x → x < WS.o + 8 → Free8 x := fun x _ h => .inl (by
  simp only [WS] at h; omega)
theorem wm_free : ∀ x, WM.o ≤ x → x < WM.o + 4 → Free8 x := fun x h1 h2 => .inr (by
  simp only [WM] at h1 h2; omega)

theorem apS : Word.Apart (L S) WS := .inr (.inr (by simp [WS, L, Lock.prod]))
theorem apM : Word.Apart (L S) WM := .inr (.inl (by simp [WM, L, Lock.prod]))

/-- An op at a word out of the semaphore's bytes keeps them. -/
theorem frame_op {n nb : Nat} {W : Word n nb} {t : ThreadId} {m m' : Mem} (hop : W.Op t m m')
    (hap : W.b ≠ 0 ∨ W.o + nb ≤ 24 ∨ 48 ≤ W.o) : Frame m m' :=
  ⟨fun W' hb h1 h2 => Word.keep_op hop (by
      rcases hap with h | h | h
      · exact .inl (by rw [hb]; exact h)
      · exact .inr (.inl (by omega))
      · exact .inr (.inr (by omega))),
    by rw [hop.threads], fun w _ => by rw [hop.waiters], hop.clocks⟩

/-- A thread in the mutex's code is `main` or the writer. -/
theorem mp_lt {G : ThreadId → Gh S} {m : Mem} (hu : U G m) {u : ThreadId}
    (h : (G u).2.2.mp ≠ Option.none) : u = 0 ∨ u = 1 := by
  obtain ⟨-, ⟨-, hp0, hn⟩ | ⟨-, -, -, -, hn⟩⟩ := hu.shape
  · rcases Nat.eq_zero_or_pos u with e | e
    · exact .inl e
    · have := hn u e; change (G u).2.2 = _ at this; rw [this] at h; exact absurd rfl h
  · rcases Nat.lt_or_ge u 2 with e | e
    · unfold ThreadId at *; omega
    · have := hn u e; change (G u).2.2 = _ at this; rw [this] at h; exact absurd rfl h

/-! ## The mutex's code -/

/-- A place `y` with the same fields of the state word, the same rights to `n`, of the same
thread, out of the semaphore's code. -/
structure Ph.Same (x y : Ph) : Prop where
  wb : y.wb = x.wb
  ib : y.ib = x.ib
  rb : y.rb = x.rb
  gave : y.gave = x.gave
  isWs : y.isWs = x.isWs
  mustN : y.mustN = x.mustN
  cnt : y.cnt = x.cnt
  isMain : y.isMain = x.isMain
  isW : y.isW = x.isW
  inSem : y.inSem = x.inSem
  live : y.live = x.live
  nwf : y ≠ .wf

theorem Ph.same_setM {x : Ph} (h : x.isMx) (p : MP) : x.Same (x.setM p) := by
  cases x <;> simp_all [isMx] <;> constructor <;> simp [setM, wb, ib, rb, gave, isWs, mustN, cnt, isMain, isW, inSem, live]

/-- Thread `t`, running and out of the semaphore's code, goes to a place `y` of the same kind
(`g'`). -/
def MSet (G : ThreadId → Gh S) (t : ThreadId) (y : Ph) (g' : Gh S) : Prop :=
  (G t).2.2.live ∧ (G t).2.2.inSem = false ∧ (G t).2.2 ≠ .pre ∧ (G t).2.2.Same y ∧
    g'.2.2 = y ∧ g'.2.1 = (G t).2.1 ∧ g'.1.part = (G t).1.part ∧ g'.1.held = (G t).1.held

theorem MSet.ph {G : ThreadId → Gh S} {t : ThreadId} {y : Ph} {g' : Gh S} (h : MSet G t y g')
    (u : ThreadId) : (upd G t g' u).2.2 = if u = t then y else (G u).2.2 := by
  unfold upd; split
  · exact h.2.2.2.2.1
  · rfl

theorem flags_setM0 {a b : Ph} {p : MP} (hf : Flags a b) (hx : a.isMx)
    (hnw : a.mp = some .cas ∨ a.mp = some .spin ∨ a.mp = some .wait ∨ p = .wake)
    (hone : ¬ ((a.setM p).mp = some .holds ∧ b.mp = some .holds)) : Flags (a.setM p) b := by
  obtain ⟨f1, f2, -, f4, f5⟩ := hf
  cases a with
  | sr j p₀ =>
    cases p₀ <;> cases p <;>
      exact ⟨fun k hk => by simp_all [Ph.setM, Ph.pw, Ph.gave, Ph.mp], fun h => by simp_all [Ph.setM],
        hone, fun j q h => by simp_all [Ph.setM, Ph.mp], fun h => by simp_all [Ph.setM, Ph.jd]⟩
  | _ =>
    simp only [Ph.isMx, Bool.false_eq_true] at hx <;> cases p <;>
      exact ⟨fun k hk => by simp_all [Ph.setM, Ph.pw, Ph.gave, Ph.mp], fun h => by simp_all [Ph.setM],
        hone, fun j q h => by simp_all [Ph.setM, Ph.mp], fun h => by simp_all [Ph.setM, Ph.jd]⟩

theorem flags_setM1 {a b : Ph} {p : MP} (hf : Flags a b) (hx : b.isMx)
    (hone : ¬ (a.mp = some .holds ∧ (b.setM p).mp = some .holds)) : Flags a (b.setM p) := by
  obtain ⟨f1, f2, -, f4, f5⟩ := hf
  cases b <;> simp only [Ph.isMx, Bool.false_eq_true] at hx <;>
    exact ⟨fun k hk => by simp_all [Ph.setM], fun h => by obtain ⟨k, hk⟩ := f2 h; simp_all [Ph.setM],
      hone, f4, fun h => by have := f5 h; simp_all [Ph.setM]⟩

/-- The flags after a change of the place in the mutex's code. -/
theorem flags_setM {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {p : MP} {g' : Gh S}
    (hu : U G m) (hx : (G t).2.2.isMx) (hph : g'.2.2 = (G t).2.2.setM p)
    (hnw : (G t).2.2.mp = some .cas ∨ (G t).2.2.mp = some .spin ∨ (G t).2.2.mp = some .wait ∨
      p = .wake)
    (hone : ¬ ((upd G t g' 0).2.2.mp = some .holds ∧ (upd G t g' 1).2.2.mp = some .holds)) :
    Flags (upd G t g' 0).2.2 (upd G t g' 1).2.2 := by
  rcases mp_lt hu (by cases e : (G t).2.2 <;> simp_all [Ph.isMx, Ph.mp]) with rfl | rfl
  · simp only [upd_self, upd0_1, hph] at hone ⊢
    exact flags_setM0 hu.flags hx hnw hone
  · simp only [upd_self, upd1_0, hph] at hone ⊢
    exact flags_setM1 hu.flags hx hone

theorem MSet.setM {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {p : MP} {g' : Gh S}
    (hu : U G m) (hx : (G t).2.2.isMx) (hph : g'.2.2 = (G t).2.2.setM p)
    (hs : g'.2.1 = (G t).2.1) (hpart : g'.1.part = (G t).1.part) (hh : g'.1.held = (G t).1.held) :
    MSet G t ((G t).2.2.setM p) g' := by
  refine ⟨?_, ?_, ?_, Ph.same_setM hx p, hph, hs, hpart, hh⟩ <;>
    cases e : (G t).2.2 <;> simp_all [Ph.isMx, Ph.live, Ph.inSem]

/-- A change of a thread's place to one of the same kind, with a step that keeps the state word,
`n`, the threads, `io` and the order of the clocks: `U` from the mutex word's facts. -/
theorem U_mx {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {y : Ph} {g' : Gh S}
    (hu : U G m) (hg : MSet G t y g')
    (hlph : (G t).1.ph = .out ∨ (G t).1.ph = .away → g'.1.ph = .out ∨ g'.1.ph = .away)
    (hkS : WS.Keep m m') (ht : m'.threads = m.threads) (hio : IoOk m') (hblk : BlkOk m')
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (NOff e ∧ e.block < m'.blocks.size))
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hcells : ∀ x, 56 ≤ x → x < 60 → m'.heap (0, x) = m.heap (0, x))
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hw' : WM.Ok m') (hmh : ∀ j < (WM.hist m').size, ∃ v ∈ mVals, (WM.hist m')[j]!.Val v)
    (hml : ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds))
    (hmq : ∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t g' 0).2.2 (upd G t g' 1).2.2) ∨
      (w.1 = 1 ∧ MQ m' (upd G t g' 1).2.2 (upd G t g' 0).2.2))
    (hfl : Flags (upd G t g' 0).2.2 (upd G t g' 1).2.2) :
    U (upd G t g') m' := by
  have hP := hg.ph
  obtain ⟨hlv, hns, hnp, ⟨hwb, hib, hrb, hgv, hiw, hmust, hcn, hM, hW, hS, hL, hwf⟩, hph, hs, hpart, -⟩ := hg
  have hhS := Word.hist_keep hu.ws hkS
  have hall : ∀ c, AllLe m c → AllLe m' c := fun c h u hu' =>
    VClock.le_trans (h u (ht ▸ hu')) (hcl u)
  have hf : ∀ {β : Type} (f : Ph → β), f y = f (G t).2.2 →
      ∀ u, f (upd G t g' u).2.2 = f (G u).2.2 := fun f hfx u => by
    rw [hP]; split
    · rename_i e; subst e; exact hfx
    · rfl
  have hcnt : (upd G t g' 1).2.2.cnt = (G 1).2.2.cnt := hf Ph.cnt hcn 1
  have hsv' : sv (upd G t g' 0).2.2 (upd G t g' 1).2.2 = sv (G 0).2.2 (G 1).2.2 := by
    rw [sv_eq, sv_eq, hf Ph.wb hwb, hf Ph.ib hib, hf Ph.rb hrb]
  -- `t`'s place is `main`'s or the writer's (not at its end)
  have hY : (G t).2.2.isMain ∨ ((G t).2.2.isW ∧ (G t).2.2 ≠ .wf) := by
    obtain ⟨-, ⟨-, hp0, hn⟩ | ⟨-, -, hM0, hW0, hn⟩⟩ := hu.shape
    · exfalso
      rcases Nat.eq_zero_or_pos t with rfl | h
      · exact hnp hp0
      · have := hn t h; change (G t).2.2 = _ at this; rw [this] at hlv; cases hlv
    · rcases Nat.lt_or_ge t 2 with h | h
      · rcases (by unfold ThreadId at *; omega : t = 0 ∨ t = 1) with rfl | rfl
        · exact .inl hM0
        · exact .inr ⟨hW0, fun e => by rw [e] at hlv; cases hlv⟩
      · have := hn t h; change (G t).2.2 = _ at this; rw [this] at hlv; cases hlv
  refine ⟨?_, hfl, hio, hblk, hu.ws.keep hkS, hw', by rw [hhS]; exact hu.shist,
    by rw [hhS, hsv']; exact hu.slast, hmh, hml, hmq, fun u hu' => ?_, fun u => ?_, fun hc => ?_⟩
  · rw [ph_upd]; have := shape_upd hu.shape hY (y := g'.2.2) (by rw [hph, hM]; exact id)
      (by rw [hph, hW]; exact id)
    unfold Shape at this ⊢; rw [ht]; exact this
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢
      have hl : (G u).1.ph = .out ∨ (G u).1.ph = .away := by
        rcases hu.lph u hns with h | h | ⟨-, h⟩
        · exact .inl h
        · exact .inr h
        · rw [hlv] at h; cases h
      rcases hlph hl with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · rw [upd_ne _ _ e] at hu' ⊢; exact hu.lph u hu'
  · rw [hcnt]
    by_cases e : u = t
    · subst e; rw [upd_self, hpart, hph, hmust]; exact hu.parts u
    · rw [upd_ne _ _ e]; exact hu.parts u
  · have hc' : Car (G 0).2.2 (G 1).2.2 := by
      unfold Car at hc ⊢
      rwa [hf Ph.mustN hmust 0, hf Ph.mustN hmust 1, hf Ph.isWs hiw 1, hf Ph.gave hgv 0] at hc
    obtain ⟨hn, hp, hsb, hok⟩ := hu.car hc'
    rw [hcnt]
    exact ⟨hn, hp, car_keep hp hsb hok (by rw [hhS]; exact VClock.le_refl _) hfp hbs hcells hall⟩

/-! ## Steps that keep the protocol -/

/-- The ghost values of the semaphore's part stay (`Sem.Spec.frame`). -/
theorem econd {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {g' : Gh S} (hu : U G m)
    (hs : g'.2.1 = (G t).2.1) (hh : g'.1.held = (G t).1.held)
    (hpt : ∀ x, 24 ≤ x → x < 48 → g'.1.part (0, x) = none)
    (hp : g'.1.ph = (G t).1.ph ∨ ((G t).1.ph ≠ .holds ∧ g'.1.ph ≠ .holds)) :
    ∀ u, (upd G t g' u).2.1 = (G u).2.1 ∧ (upd G t g' u).1.held = (G u).1.held ∧
      (∀ x, 24 ≤ x → x < 48 → (upd G t g' u).1.part (0, x) = none) ∧
      ((upd G t g' u).1.ph = (G u).1.ph ∨ ((G u).1.ph ≠ .holds ∧ (upd G t g' u).1.ph ≠ .holds)) :=
    fun u => by
  unfold upd; split
  · rename_i e; subst e; exact ⟨hs, hh, hpt, hp⟩
  · exact ⟨rfl, rfl, fun x _ h2 => part_none hu u (by omega), .inl rfl⟩

theorem econd0 {G : ThreadId → Gh S} {m : Mem} (hu : U G m) :
    ∀ u, (G u).2.1 = (G u).2.1 ∧ (G u).1.held = (G u).1.held ∧
      (∀ x, 24 ≤ x → x < 48 → (G u).1.part (0, x) = none) ∧
      ((G u).1.ph = (G u).1.ph ∨ ((G u).1.ph ≠ .holds ∧ (G u).1.ph ≠ .holds)) :=
  fun u => ⟨rfl, rfl, fun x _ h2 => part_none hu u (by omega), .inl rfl⟩

/-- A part that stays has no byte of the semaphore. -/
theorem pnone {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {g' : Gh S} (hu : U G m)
    (hp : g'.1.part = (G t).1.part) : ∀ x, 24 ≤ x → x < 48 → g'.1.part (0, x) = none :=
  fun x _ h2 => by rw [hp]; exact part_none hu t (by omega)

/-- An op at a word below `n` and out of `io`: the new access does not touch them. -/
theorem op_fp {n nb : Nat} {W : Word n nb} {t : ThreadId} {m m' : Mem} (hop : W.Op t m m')
    (hw : W.Ok m) (ho : 16 ≤ W.o) (ho' : W.o + nb ≤ 56) :
    (∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (NOff e ∧ e.block < m'.blocks.size)) ∧
      (IoOk m → IoOk m') := by
  have hWb : W.b < m'.blocks.size := by
    obtain ⟨blk, h, -⟩ := hw.blk; rw [hop.bsize]; exact (Array.getElem?_eq_some_iff.mp h).1
  refine ⟨fun e he => ?_, fun hio e he hb' ho16 => ?_⟩
  · rcases hop.fp e he with h | ⟨h1, h2, h3, -⟩
    · exact .inl h
    · refine .inr ⟨.inr (.inl ⟨by rw [h2, h3]; exact ho', by rw [h2]; have := W.sz_pos; omega⟩),
        by rw [h1]; exact hWb⟩
  · rcases hop.fp e he with h | ⟨-, h2, -⟩
    · rcases hio e h hb' ho16 with h' | h'
      · exact .inl h'
      · exact .inr (hop.allLe h')
    · omega

/-- An op at the mutex word by a thread in its code: the protocol, from the mutex word's facts. -/
theorem inv_mop (hE : E.Spec) {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {y : Ph}
    {g' : Gh S} (hi : (proto E).inv G m) (hg : MSet G t y g') (hg1 : g'.1.ph = (G t).1.ph)
    (hop : WM.Op t m m') (hw' : WM.Ok m')
    (hmh : ∀ j < (WM.hist m').size, ∃ v ∈ mVals, (WM.hist m')[j]!.Val v)
    (hml : ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds))
    (hmq : ∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t g' 0).2.2 (upd G t g' 1).2.2) ∨
      (w.1 = 1 ∧ MQ m' (upd G t g' 1).2.2 (upd G t g' 0).2.2))
    (hfl : Flags (upd G t g' 0).2.2 (upd G t g' 1).2.2) :
    (proto E).inv (upd G t g') m' := by
  have hu := hi.2.1
  have hl := hi.1.wordOp hu.wm hop apM (off_own hi rfl wm_free) (off_R rfl wm_free G)
  obtain ⟨hfp, hio⟩ := op_fp hop hu.wm (by decide) (by decide)
  have hph1 : ∀ u, (L S).ph (upd G t g' u) = (L S).ph (G u) := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact hg1
    · rfl
  refine ⟨hl.congr hph1 (fun u => by
      unfold upd; split
      · rename_i e; subst e; exact hg.2.2.2.2.2.2.1
      · rfl) (fun u => by
      unfold upd; split
      · rename_i e; subst e; exact hg.2.2.2.2.2.2.2
      · rfl) (R_upd (by rw [hg.2.2.2.2.1]; exact hg.2.2.2.1.isWs)
        (by rw [hg.2.2.2.2.1]; exact hg.2.2.2.1.gave) (by rw [hg.2.2.2.2.1]; exact hg.2.2.2.1.cnt)),
    U_mx hu hg (fun h => by rw [hg1]; exact h) (Word.keep_op hop (.inr (.inr (by decide))))
      hop.threads (hio hu.io) (blk_keep hu.blk (hop.cells _ (by simp [WM])))
      hfp (Nat.le_of_eq hop.bsize.symm) (fun x h1 _ => hop.cells _ (by simp [WM]; omega))
      hop.clocks hw' hmh hml hmq hfl,
    hE.frame G _ m m' hi.2.2 (frame_op hop (.inr (.inr (by decide))))
      (econd hu hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.2 (pnone hu hg.2.2.2.2.2.2.1) (.inl hg1))⟩

theorem Frame.refl (m : Mem) : Frame m m :=
  ⟨fun _ _ _ _ => Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _, rfl, fun _ _ => Iff.rfl,
    fun _ => VClock.le_refl _⟩

/-- A change of a place in the mutex's code that neither holds the mutex nor wakes it keeps the
mutex word's facts. -/
theorem calm {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {g' : Gh S} (hu : U G m)
    (hmpt : (G t).2.2.mp ≠ some .holds ∧ (G t).2.2.mp ≠ some .wake)
    (hmp' : g'.2.2.mp ≠ some .holds ∧ g'.2.2.mp ≠ some .wake) (hh : WM.hist m' = WM.hist m)
    (hq : ∀ w ∈ m'.waiters, w.2 = WM.ptr → w ∈ m.waiters ∧ w.1 ≠ t) :
    (∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds)) ∧
    (∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t g' 0).2.2 (upd G t g' 1).2.2) ∨
      (w.1 = 1 ∧ MQ m' (upd G t g' 1).2.2 (upd G t g' 0).2.2)) ∧
    ¬ ((upd G t g' 0).2.2.mp = some .holds ∧ (upd G t g' 1).2.2.mp = some .holds) := by
  have hH : ∀ u, (upd G t g' u).2.2.mp = some .holds ↔ (G u).2.2.mp = some .holds := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact ⟨fun h => absurd h hmp'.1, fun h => absurd h hmpt.1⟩
    · exact Iff.rfl
  have hO : ∀ u, ((G u).2.2.mp = some .holds ∨ (G u).2.2.mp = some .wake) → upd G t g' u = G u :=
    fun u h => upd_ne _ _ fun e => by subst e; rcases h with h | h; exact hmpt.1 h; exact hmpt.2 h
  refine ⟨?_, fun w hw hp => ?_, fun ⟨h0, h1⟩ => hu.flags.one ⟨(hH 0).mp h0, (hH 1).mp h1⟩⟩
  · obtain ⟨v, hv, hl, hz⟩ := hu.mlast
    exact ⟨v, hv, by rw [hh]; exact hl, hz.trans (forall_congr' fun u => not_congr (hH u).symm)⟩
  · obtain ⟨hw', hwt⟩ := hq w hw hp
    have hMQ : ∀ {a b : ThreadId}, a ≠ t → MQ m (G a).2.2 (G b).2.2 →
        MQ m' (upd G t g' a).2.2 (upd G t g' b).2.2 := fun ha ⟨h1, h2⟩ => by
      unfold MQ; rw [hh, upd_ne _ _ ha, hO _ (h2.imp And.left id)]; exact ⟨h1, h2⟩
    rcases hu.mq w hw' hp with ⟨h0, hq'⟩ | ⟨h1, hq'⟩
    · exact .inl ⟨h0, hMQ (h0 ▸ hwt) hq'⟩
    · exact .inr ⟨h1, hMQ (h1 ▸ hwt) hq'⟩

theorem get_push_lt {h : Array Word.Entry} {x : Word.Entry} {k : Nat} (hk : k < h.size) :
    (h.push x)[k]! = h[k]! := by
  have h1 : k < (h.push x).size := by simp; omega
  rw [getElem!_pos (h.push x) k h1, getElem!_pos h k hk, Array.getElem_push_lt hk]

theorem last_push (h : Array Word.Entry) (x : Word.Entry) : last (h.push x) = x := by
  show (h.push x)[(h.push x).size - 1]! = x
  rw [getElem!_pos _ _ (by simp)]; simp

theorem rmwEnt_val {n nb : Nat} (W : Word n nb) {M : Mem} {t : ThreadId} {ord : AtomicOrder}
    {l : Word.Entry} {new : BitVec n} : (Word.rmwEnt M t ord l new).Val new := W.enc_val new

/-- Each write of `h.push x` has a value of `V`, if each write of `h` has and `x` has. -/
theorem vals_push {n : Nat} {V : List (BitVec n)} {h : Array Word.Entry} {x : Word.Entry}
    {v : BitVec n} (hh : ∀ j < h.size, ∃ v ∈ V, h[j]!.Val v) (hv : v ∈ V) (hx : x.Val v) :
    ∀ j < (h.push x).size, ∃ v ∈ V, (h.push x)[j]!.Val v := by
  intro j hj
  simp only [Array.size_push] at hj
  rcases Nat.lt_or_ge j h.size with h1 | h1
  · rw [get_push_lt h1]; exact hh j h1
  · have : j = h.size := by omega
    subst this
    rw [getElem!_pos _ _ (by simp)]; simp only [Array.getElem_push_eq]; exact ⟨v, hv, hx⟩

/-- A word has a write. -/
theorem hist_pos {n nb : Nat} {W : Word n nb} {m : Mem} (hw : W.Ok m) :
    (W.hist m).size - 1 < (W.hist m).size := by
  unfold Word.hist
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => simp
  | some i =>
    have hl := Word.loc_of_find hf
    obtain ⟨-, h0, -⟩ := hw.loc i _ hl
    simp only [Array.size_mapIdx]; omega

theorem val_eq {n : Nat} {x : Word.Entry} {a b : BitVec n} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

/-- Other places in the semaphore's mutex (`out` or `away`), with the same places and parts. -/
theorem U_lph {G G' : ThreadId → Gh S} {m : Mem} (hu : U G m) (h2 : ∀ u, (G' u).2 = (G u).2)
    (hp : ∀ u, (G' u).1.part = (G u).1.part)
    (hlph : ∀ u, (G' u).2.2.inSem = false →
      (G' u).1.ph = .out ∨ (G' u).1.ph = .away ∨ ((G' u).1.ph = .gone ∧ (G' u).2.2.live = false)) :
    U G' m := by
  have e : (fun u => (G' u).2) = fun u => (G u).2 := funext h2
  have e' : (fun u => (G' u).2.2) = fun u => (G u).2.2 := by funext u; rw [h2]
  have e's : (fun u => (G' u).2.1) = fun u => (G u).2.1 := by funext u; rw [h2]
  obtain ⟨hsh, hfl, hio, hblk, hws, hwm, hsh', hsl, hmh, hml, hmq, -, hpa, hcar⟩ := hu
  refine ⟨by rw [e']; exact hsh, by rw [h2, h2]; exact hfl, hio, hblk, hws, hwm, hsh',
    by rw [h2, h2]; exact hsl, hmh, ?_, fun w hw hq => by rw [h2, h2]; exact hmq w hw hq, hlph,
    fun u => by rw [hp, h2, h2]; exact hpa u, fun hc => by rw [h2, h2] at hc; rw [h2]; exact hcar hc⟩
  obtain ⟨v, hv, hl, hz⟩ := hml
  exact ⟨v, hv, hl, hz.trans (forall_congr' fun u => by rw [h2])⟩

/-! ## No deadlock -/

/-- A thread asleep at the mutex is in its `lock`. -/
theorem mq_wait {G : ThreadId → Gh S} {m : Mem} (hu : U G m) {w : ThreadId × Ptr}
    (hw : w ∈ m.waiters) (hp : w.2 = WM.ptr) : (G w.1).2.2.mp = some .wait := by
  rcases hu.mq w hw hp with ⟨h0, h, -⟩ | ⟨h1, h, -⟩
  · rw [h0]; exact h
  · rw [h1]; exact h

/-- A thread that sleeps at a futex is not the last one. -/
theorem live_all (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (t : ThreadId) : (proto E).Live t G m := by
  intro hw hall
  -- no thread waits at the semaphore's mutex: its witness goes on
  have hnoL : ¬ (L S).Waits m.waiters := fun hp => by
    obtain ⟨v, hv, hq, hb, -⟩ := hi.1.wit hp
    rcases hall v hv with h | h | h
    · rw [show (L S).ph (G v) = (G v).1.ph from rfl, h.1] at hb; cases hb
    · rw [hq] at h; cases h
    · rw [show (L S).ph (G v) = (G v).1.ph from rfl, h.1] at hb; cases hb
  have hnot : ∀ w ∈ m.waiters, w.2 ≠ (L S).ptr := fun w hw' e =>
    hnoL (Array.any_eq_true.mpr (by
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hw'
      exact ⟨j, hj, by simp [e]⟩))
  -- a waiter's thread
  have hwait : ∀ u, m.waiters.any (·.1 == u) = true → ∃ w ∈ m.waiters, w.1 = u := fun u h => by
    obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp h
    exact ⟨_, Array.getElem_mem hi', by simpa using he⟩
  have hu := hi.2.1
  have hmpf : ∀ x : Ph, x.mp = some .wait → x.pw = false :=
    fun x h => by
    cases x <;> simp_all [Ph.mp, Ph.pw]
  have hmpf' : ∀ x : Ph, (x.mp = some .holds ∨ x.mp = some .wake) → x ≠ .wf ∧ x ≠ .joins ∧
      x.mp ≠ some .wait := fun x h => by
    cases x <;> rcases h with h | h <;> simp_all [Ph.mp]
  have h2 : m.threads.size = 2 := by
    obtain ⟨w, hwm, rfl⟩ := hwait t hw
    obtain ⟨-, ⟨-, hp0, hn⟩ | ⟨hs, -⟩⟩ := hu.shape
    · exfalso
      have hn1 : (G 1).2.2 = .none := hn 1 (Nat.le_refl _)
      change (G 0).2.2 = _ at hp0
      by_cases hl : w.2 = WM.ptr
      · rcases hu.mq w hwm hl with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · rw [hp0] at h; cases h
        · rw [hn1] at h; cases h
      · obtain ⟨-, ⟨k, hk⟩, -⟩ := hE.live G m hi w hwm (hnot w hwm) hl
        rw [hn1] at hk; cases hk
    · exact hs
  -- thread `u` goes on
  have hgo : ∀ u, u < 2 → (G u).2.2.mp ≠ some .wait → (G u).2.2 ≠ .wf →
      (G u).2.2 ≠ .joins → (u = 1 → (G 0).2.2.pw = false) → False := by
    intro u hu2 hmp hwf hj hm
    rcases hall u (by rw [h2]; exact hu2) with h | h | h
    · exact hwf h.2
    · obtain ⟨w', hw', rfl⟩ := hwait _ h
      by_cases hl : w'.2 = WM.ptr
      · exact hmp (mq_wait hu hw' hl)
      · obtain ⟨h1, -, h0⟩ := hE.live G m hi w' hw' (hnot w' hw') hl
        rw [hm h1] at h0; cases h0
    · exact hj h.2
  obtain ⟨w, hwm, rfl⟩ := hwait t hw
  by_cases hl : w.2 = WM.ptr
  · rcases hu.mq w hwm hl with ⟨h0, hx, ho⟩ | ⟨h1, hx, ho⟩
    · have := hmpf' _ (ho.imp_left And.left)
      exact hgo 1 (by decide) this.2.2 this.1 this.2.1 fun _ => hmpf _ hx
    · have := hmpf' _ (ho.imp_left And.left)
      exact hgo 0 (by decide) this.2.2 this.1 this.2.1 fun h => absurd h (by decide)
  · obtain ⟨-, -, h0⟩ := hE.live G m hi w hwm (hnot w hwm) hl
    have hx : (G 0).2.2.mp ≠ some .wait ∧ (G 0).2.2 ≠ .wf ∧ (G 0).2.2 ≠ .joins := by
      revert h0; cases (G 0).2.2 <;> simp [Ph.pw, Ph.mp]
      rename_i p; cases p <;> simp
    exact hgo 0 (by decide) hx.1 hx.2.1 hx.2.2 fun h => absurd h (by decide)

/-! ## The futex of the mutex -/

/-- A change of the futex queue: `U` from the facts of the threads asleep at the mutex. -/
theorem U_q {G : ThreadId → Gh S} {m m' : Mem} {c : ThreadId} {ws : Array (ThreadId × Ptr)}
    {wk : Array ThreadId} (hu : U G m)
    (hm : m' = { m with current := c, waiters := ws, woken := wk })
    (hmq : ∀ w ∈ ws, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m (G 0).2.2 (G 1).2.2) ∨ (w.1 = 1 ∧ MQ m (G 1).2.2 (G 0).2.2)) :
    U G m' := by
  subst hm
  have hk : ∀ {n nb : Nat} (W : Word n nb), W.Keep m { m with current := c, waiters := ws, woken := wk } :=
    fun W => Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _
  have hhS := Word.hist_keep hu.ws (hk WS)
  have hhM := Word.hist_keep hu.wm (hk WM)
  refine ⟨hu.shape, hu.flags, hu.io, hu.blk, hu.ws.keep (hk WS), hu.wm.keep (hk WM),
    by rw [hhS]; exact hu.shist, by rw [hhS]; exact hu.slast, by rw [hhM]; exact hu.mhist,
    by rw [hhM]; exact hu.mlast, fun w hw hp => ?_, hu.lph, hu.parts, fun h => ?_⟩
  · unfold MQ; rw [hhM]; exact hmq w hw hp
  · obtain ⟨hn, hp, hs, hc⟩ := hu.car h
    exact ⟨hn, hp, hs, fun e he ht => by rw [hhS]; exact hc e he ht⟩


theorem wmL : WM.ptr ≠ (L S).ptr := by simp [WM, Word.ptr, Lock.ptr, L, Lock.prod]

/-- A thread at `x` goes to `away` before a futex wait of the mutex. -/
theorem inv_away (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {x : Ph} {sx : S}
    (hi : (proto E).inv (upd G t (gA x Heap.empty sx)) m) (hx : x.inSem = false) :
    (proto E).inv (upd G t (⟨.away, Heap.empty, Heap.empty⟩, (sx, x))) m := by
  have hl := hi.1.ghost (t := t) (g := (⟨.away, Heap.empty, Heap.empty⟩, (sx, x)))
    (by rw [upd_self]; rfl) (.inr (.inr rfl)) (by rw [upd_self]; rfl) rfl
    (fun _ => hi.1.live t (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun hL hR => (R_two (fun u => by unfold upd; split <;> rfl) hL).mpr hR)
  rw [upd_upd] at hl
  refine ⟨hl, U_lph hi.2.1 (fun u => by unfold upd; split <;> rfl)
    (fun u => by unfold upd; split <;> rfl) fun u hu => ?_, ?_⟩
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact .inr (.inl rfl)
    · rw [upd_ne _ _ e] at hu ⊢; have := hi.2.1.lph u; rw [upd_ne _ _ e] at this; exact this hu
  · have hc := econd (G := upd G t (gA x Heap.empty sx)) (t := t)
      (g' := (⟨.away, Heap.empty, Heap.empty⟩, (sx, x))) hi.2.1 (by rw [upd_self]; rfl)
      (by rw [upd_self]; rfl) (fun _ _ _ => rfl)
      (.inr ⟨by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.holds),
        (by decide : LPh.away ≠ LPh.holds)⟩)
    rw [upd_upd] at hc
    exact hE.frame _ _ m m hi.2.2 (Frame.refl m) hc

theorem bits_contended : (Packed.toBits Io_Mutex_State.contended).setWidth 32 = (2 : BitVec 32) := by
  decide

/-- `lock`'s futex wait for `contended` by thread `t` at `x` (`wait`): it can sleep while the
word is `2`, so the other thread holds the mutex. It goes on at `x.setM .spin`. -/
theorem wp_mwait (hE : E.Spec) {σ : Type} {s₀ : σ} {G : ThreadId → Gh S} {m : Mem} {d : Nat}
    {t : ThreadId} {x : Ph} {sx : S} {io : Io} (hx : x.isMx) (hxw : x.mp = some .wait)
    (hi : (proto E).inv (upd G t (gA x Heap.empty sx)) m)
    {Q : Unit × σ → (ThreadId → Gh S) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m', m'.current = t →
      (proto E).inv (upd G₁ t (gA (x.setM .spin) Heap.empty sx)) m' → Q ((), s₀) G₁ m' k) :
    (proto E).WP t ((futexWaitC io WM.ptr Io_Mutex_State.contended : CM Tgt σ Unit).run s₀) Q G m d := by
  have hxs : x.inSem = false := by cases x <;> simp_all [Ph.isMx, Ph.inSem]
  refine WP.futexWaitC fun k hk => ⟨_, inv_away hE hi hxs, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have hu₁ := hi₁.2.1
  have hw := hu₁.wm
  have hph : (L S).ph (G₁ t) = .away := by rw [hg₁]; rfl
  have hg1 : (G₁ t).2 = (sx, x) := by rw [hg₁]
  have ht01 : t = 0 ∨ t = 1 := mp_lt hu₁ (by rw [hg1, hxw]; simp)
  refine ⟨fun _ => live_all hE hi₁ t, fun hq0 => ⟨fun _ => ?_, fun b m' hr => ?_⟩⟩
  · by_cases hwk : ({ m₁ with current := t } : Mem).woken.contains
      ({ m₁ with current := t } : Mem).current = true
    · exact ⟨_, _, futexWait_run_woken hwk⟩
    · obtain ⟨blk, hb, -, -, ha, -⟩ := hw.access
      obtain ⟨v, hv⟩ := hw.val
      rw [Word.holds_bytes hb] at hv
      exact ⟨_, _, futexWait_run_go (by simpa using hwk) ha hv⟩
  have hl := hi₁.1.waitOff hph wmL hq0 hr
  -- the new ghost value after a wait that goes on
  let g' : Gh S := gA (x.setM .spin) Heap.empty sx
  have hgo : ∀ m', m'.current = t → m'.blocks = m₁.blocks → m'.atomics = m₁.atomics →
      m'.footprint = m₁.footprint → m'.threads = m₁.threads → m'.clocks = m₁.clocks →
      m'.waiters = m₁.waiters →
      (L S).Inv (upd G₁ t ((L S).set (G₁ t) .out Heap.empty)) m' →
      (proto E).inv (upd G₁ t g') m' := by
    intro m' hc hb ha hf ht hcl hq hL
    have hkW : ∀ {n nb : Nat} (W : Word n nb), W.Keep m₁ m' := fun W =>
      Word.keep_of hb ha hf ht fun u => by rw [hcl]; exact VClock.le_refl _
    have hMS : MSet G₁ t (x.setM .spin) g' := by
      have := MSet.setM (p := .spin) (g' := g') hu₁ (by rw [hg1]; exact hx) (by rw [hg1]; rfl)
        (by rw [hg1]; rfl) (by rw [hg₁]; rfl) (by rw [hg₁]; rfl)
      rwa [hg1] at this
    obtain ⟨hml, hmq, hone⟩ := calm (g' := g') hu₁ (by rw [hg1, hxw]; simp) (by
        show (x.setM .spin).mp ≠ _ ∧ (x.setM .spin).mp ≠ _; rw [Ph.mp_setM hx]; simp)
      (Word.hist_keep hw (hkW WM)) (fun w hw' _ => by
        rw [hq] at hw'; exact ⟨hw', Lock.ne_of_notQ hq0 hw'⟩)
    refine ⟨?_, U_mx hu₁ hMS (fun _ => .inl rfl) (hkW WS) ht ?_ ?_
      (fun e he => .inl (hf ▸ he)) (by rw [hb]; exact Nat.le_refl _)
      (fun x _ _ => by simp only [Mem.heap, hb])
      (fun u => by rw [hcl]; exact VClock.le_refl _) (hw.keep (hkW WM))
      (by rw [Word.hist_keep hw (hkW WM)]; exact hu₁.mhist) hml hmq
      (flags_setM hu₁ (by rw [hg1]; exact hx) (by rw [hg1]; rfl) (.inr (.inr (.inl (by rw [hg1, hxw])))) hone), ?_⟩
    · have : (L S).set (G₁ t) .out Heap.empty = gA x Heap.empty sx := by rw [hg₁]; rfl
      rw [this] at hL
      refine hL.congr (fun u => ?_) (fun u => ?_) (fun u => ?_) fun h => ?_
      · unfold upd; split <;> rfl
      · unfold upd; split <;> rfl
      · unfold upd; split <;> rfl
      · have hx2 : (G₁ t).2.2 = x := by rw [hg1]
        exact (R_upd (by simp [g', gA, hx2]) (by simp [g', gA, hx2]) (by simp [g', gA, hx2]) h).trans
          (R_upd (by simp [gA, hx2]) (by simp [gA, hx2]) (by simp [gA, hx2]) h).symm
    · intro e he hb' ho; rw [hf] at he
      rcases hu₁.io e he hb' ho with h' | h'
      · exact .inl h'
      · exact .inr fun u hu => by rw [ht] at hu; rw [hcl]; exact h' u hu
    · unfold BlkOk; rw [hb]; exact hu₁.blk
    · exact hE.frame _ _ m₁ m' hi₁.2.2 ⟨fun W _ _ _ => hkW W, by rw [ht],
        fun w _ => by rw [hq], fun u => by rw [hcl]; exact VClock.le_refl _⟩
        (econd hu₁ (by rw [hg₁]; rfl) (by rw [hg₁]; rfl) (fun _ _ _ => rfl)
          (.inr ⟨by rw [hg₁]; exact (by decide : LPh.away ≠ LPh.holds),
            (by decide : LPh.out ≠ LPh.holds)⟩))
  rcases futexWait_ok hr with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, hv, ⟨hve, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    exact h k hk G₁ _ rfl (hgo _ rfl rfl rfl rfl rfl rfl rfl hl.2)
  · -- it sleeps: the word is `2`, so the other thread holds the mutex
    simp only [↓reduceIte] at hl ⊢
    obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hw.access
    have : ({ m₁ with current := t } : Mem).access WM.ptr 4 4 = m₁.access WM.ptr 4 4 := rfl
    rw [this, ha₀] at ha
    cases ha
    have h2 : (last (WM.hist m₁)).Val (2 : BitVec 32) := by
      rw [← hw.holds_last, Word.holds_bytes hb₀, ← bits_contended, ← hve]; exact hv
    obtain ⟨v₀, -, hl₀, hz⟩ := hu₁.mlast
    have hv₀ : v₀ = 2 := val_eq hl₀ h2
    obtain ⟨u, hu⟩ : ∃ u, (G₁ u).2.2.mp = some .holds := Classical.byContradiction fun hc =>
      absurd (hz.mpr fun u hu => hc ⟨u, hu⟩) (by rw [hv₀]; decide)
    have hut : u ≠ t := fun e => by subst e; rw [hg1] at hu; simp only at hu; rw [hxw] at hu; cases hu
    have hu01 := mp_lt hu₁ (u := u) (by rw [hu]; simp)
    have hMQ : MQ m₁ (G₁ t).2.2 (G₁ u).2.2 := ⟨by rw [hg1]; exact hxw, .inl ⟨hu, h2⟩⟩
    refine ⟨hl, U_q hu₁ rfl fun w hw' hp => ?_,
      hE.frame _ _ m₁ _ hi₁.2.2 ⟨fun W _ _ _ => Word.keep_of rfl rfl rfl rfl
        fun _ => VClock.le_refl _, rfl, fun w hw => ?_, fun _ => VClock.le_refl _⟩
        (econd0 hu₁)⟩
    · rcases Array.mem_push.mp hw' with hw' | rfl
      · exact hu₁.mq w hw' hp
      · rcases ht01 with rfl | rfl <;> rcases hu01 with rfl | rfl
        all_goals first | exact absurd rfl hut | exact .inl ⟨rfl, hMQ⟩ | exact .inr ⟨rfl, hMQ⟩
    · simp only [Array.mem_push]
      exact ⟨fun h => h.resolve_right fun e => hw (by rw [e]), .inl⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    exact h k hk G₁ _ rfl (hgo _ rfl rfl rfl rfl rfl rfl rfl hl.2)

/-! ## `lock` and `unlock` of the mutex -/

/-- The facts of the protocol at a stop of a running thread that an op at a word needs. -/
theorem wat {n nb : Nat} {W : Word n nb} (hW : ∀ G m, (proto E).inv G m → W.Ok m) {t : ThreadId}
    {g : Gh S} (hg : g.1.ph ≠ .gone) : WAt (proto E) W t g := fun G₁ m₁ hg₁ hi₁ =>
  ⟨hW G₁ m₁ hi₁, (hi₁.1.live t (by rw [hg₁]; exact hg)).1, hi₁.1.own.csize⟩

/-- No thread sleeps at the mutex while a running thread neither holds it nor wakes it. -/
theorem noWM {G : ThreadId → Gh S} {m : Mem} (hu : U G m) {t : ThreadId} (ht01 : t = 0 ∨ t = 1)
    (ht : (G t).2.2.mp ≠ some .holds ∧ (G t).2.2.mp ≠ some .wake ∧ (G t).2.2.mp ≠ some .wait) :
    ∀ w ∈ m.waiters, w.2 ≠ WM.ptr := fun w hw hp => by
  have hw1 := mq_wait hu hw hp
  have hwt : w.1 ≠ t := fun e => ht.2.2 (by rw [← e]; exact hw1)
  rcases hu.mq w hw hp with ⟨h0, -, ho⟩ | ⟨h1, -, ho⟩
  · have : t = 1 := by rw [h0] at hwt; unfold ThreadId at *; omega
    subst this
    rcases ho with ⟨h, -⟩ | h
    · exact ht.1 h
    · exact ht.2.1 h
  · have : t = 0 := by rw [h1] at hwt; unfold ThreadId at *; omega
    subst this
    rcases ho with ⟨h, -⟩ | h
    · exact ht.1 h
    · exact ht.2.1 h

/-- The mutex word's values decode. -/
theorem mdec {G₀ : ThreadId → Gh S} {m : Mem} (hu : U G₀ m) {j : Nat} (hj : j < (WM.hist m).size) {b : BitVec 32}
    (hb : (WM.hist m)[j]!.Val b) :
    ∃ r, (Packed.ofBits? (α := Io_Mutex_State) b).run = some (.ok r) ∧ Packed.toBits r = b := by
  obtain ⟨v, hv, hv'⟩ := hu.mhist j hj
  rw [val_eq hb hv']
  simp only [mVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨.unlocked, rfl, rfl⟩
  · exact ⟨.locked_once, rfl, rfl⟩
  · exact ⟨.contended, rfl, rfl⟩

theorem setM_setM (x : Ph) (p q : MP) : (x.setM p).setM q = x.setM q := by cases x <;> rfl

/-- After an RMW of the mutex word with `w` by thread `t` (new place `g'`): its writes. -/
theorem mpush {G : ThreadId → Gh S} {m₁ m' : Mem} {t : ThreadId} {g' : Gh S} {w : BitVec 32}
    {e : Word.Entry} (hu : U G m₁) (hh : WM.hist m' = (WM.hist m₁).push e) (he : e.Val w)
    (hw : w ∈ mVals) (hz : w = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds) :
    (∀ j < (WM.hist m').size, ∃ v ∈ mVals, (WM.hist m')[j]!.Val v) ∧
    ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧ (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds) :=
  ⟨by rw [hh]; exact vals_push hu.mhist hw he, w, hw, by rw [hh, last_push]; exact he, hz⟩

/-- The newest write of the mutex word is not `0`: a thread holds it. -/
theorem holder_of {G : ThreadId → Gh S} {m : Mem} (hu : U G m) {v : BitVec 32}
    (hv : (last (WM.hist m)).Val v) (h0 : v ≠ 0) : ∃ u, (G u).2.2.mp = some .holds := by
  obtain ⟨v₀, -, hl₀, hz⟩ := hu.mlast
  rw [val_eq hv hl₀] at h0
  exact Classical.byContradiction fun hc => h0 (hz.mpr fun u hu => hc ⟨u, hu⟩)

/-- An op at the mutex word by thread `t` at `y`, which goes to `y.setM p`. -/
theorem inv_mstep (hE : E.Spec) {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {y : Ph}
    {p : MP} {sx : S} {h : Heap} (hi : (proto E).inv G m) (hg : G t = gA y h sx) (hy : y.isMx)
    (hnw : y.mp = some .cas ∨ y.mp = some .spin ∨ y.mp = some .wait ∨ p = .wake)
    (hop : WM.Op t m m') (hw' : WM.Ok m')
    (hmh : ∀ j < (WM.hist m').size, ∃ v ∈ mVals, (WM.hist m')[j]!.Val v)
    (hml : ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t (gA (y.setM p) h sx) u).2.2.mp ≠ some .holds))
    (hmq : ∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t (gA (y.setM p) h sx) 0).2.2
        (upd G t (gA (y.setM p) h sx) 1).2.2) ∨
      (w.1 = 1 ∧ MQ m' (upd G t (gA (y.setM p) h sx) 1).2.2
        (upd G t (gA (y.setM p) h sx) 0).2.2))
    (hone : ¬ ((upd G t (gA (y.setM p) h sx) 0).2.2.mp = some .holds ∧
      (upd G t (gA (y.setM p) h sx) 1).2.2.mp = some .holds)) :
    (proto E).inv (upd G t (gA (y.setM p) h sx)) m' := by
  have hy' : (G t).2.2.isMx := by rw [hg]; exact hy
  have hM := MSet.setM (p := p) (g' := gA (y.setM p) h sx) hi.2.1 hy' (by rw [hg]; rfl)
    (by rw [hg]; rfl) (by rw [hg]; rfl) (by rw [hg]; rfl)
  rw [hg] at hM
  exact inv_mop hE hi hM (by rw [hg]; rfl) hop hw' hmh hml hmq
    (flags_setM hi.2.1 hy' (by rw [hg]; rfl) (by rw [hg]; exact hnw) hone)

/-- An op at the mutex word that writes nothing (a failed `cmpxchg`), by thread `t` at `y`,
which goes to `y.setM p`; neither place holds or wakes the mutex. -/
theorem inv_mcalm (hE : E.Spec) {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {y : Ph}
    {p : MP} {sx : S} (hi : (proto E).inv G m) (hg : G t = gA y Heap.empty sx) (hy : y.isMx)
    (hyp : y.mp ≠ some .holds ∧ y.mp ≠ some .wake ∧ y.mp ≠ some .wait)
    (hp : p ≠ .holds ∧ p ≠ .wake) (hop : WM.Op t m m') (hw' : WM.Ok m')
    (hh : WM.hist m' = WM.hist m) : (proto E).inv (upd G t (gA (y.setM p) Heap.empty sx)) m' := by
  have hu := hi.2.1
  have ht01 : t = 0 ∨ t = 1 := mp_lt hu (by rw [hg]; show y.mp ≠ _; cases y <;> simp_all [Ph.isMx, Ph.mp])
  have hnw := noWM hu ht01 (by rw [hg]; exact hyp)
  have hq : ∀ w ∈ m'.waiters, w.2 = WM.ptr → w ∈ m.waiters ∧ w.1 ≠ t := fun w hw hpw => by
    rw [hop.waiters] at hw; exact absurd hpw (hnw w hw)
  obtain ⟨hml, hmq, hone⟩ := calm (g' := gA (y.setM p) Heap.empty sx) hu
    (by rw [hg]; exact ⟨hyp.1, hyp.2.1⟩)
    (by show (y.setM p).mp ≠ _ ∧ (y.setM p).mp ≠ _; rw [Ph.mp_setM hy]; simp [hp.1, hp.2]) hh hq
  exact inv_mstep hE hi hg hy (by
    cases y <;> simp_all [Ph.isMx, Ph.mp] <;> rename_i q <;> cases q <;> simp_all) hop hw' (by rw [hh]; exact hu.mhist) hml hmq hone

theorem bits_unlocked : Packed.toBits Io_Mutex_State.unlocked = (0 : BitVec 32) := rfl
theorem bits_once : Packed.toBits Io_Mutex_State.locked_once = (1 : BitVec 32) := rfl
theorem bits_cont : Packed.toBits Io_Mutex_State.contended = (2 : BitVec 32) := rfl

/-- `lock`'s loop invariant: thread `t` at `x.setM spin`. -/
def lockInv (E : Sem S) (t : ThreadId) (x : Ph) (sx : S) (D : Nat) (_ : Io_Mutex_lockUncancelableLocals)
    (G : ThreadId → Gh S) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = t ∧ (proto E).inv (upd G t (gA (x.setM .spin) Heap.empty sx)) m

/-- `lock`'s loop ends when thread `t` holds the mutex. -/
def lockPost (E : Sem S) (t : ThreadId) (x : Ph) (sx : S) (D : Nat)
    (r : Io_Mutex_lockUncancelableExit × Io_Mutex_lockUncancelableLocals) (G : ThreadId → Gh S)
    (m : Mem) (d : Nat) : Prop :=
  r.1 = .br22 ∧ d < D ∧ m.current = t ∧ (proto E).inv (upd G t (gA (x.setM .holds) Heap.empty sx)) m

/-- One repeat of `lock`'s loop: `xchg(contended)`; the thread holds the mutex, or it waits at the
futex. -/
theorem mloop_body (hE : E.Spec) {t : ThreadId} {x : Ph} (hx : x.isMx) {sx : S} (D : Nat) (io : Io)
    (s : Io_Mutex_lockUncancelableLocals) (G : ThreadId → Gh S) (m : Mem) (d : Nat)
    (h : lockInv E t x sx D s G m d) :
    (proto E).WP t ((Io_Mutex_lockUncancelable.loop23 WM.ptr io).run s) (fun r G' m' d' =>
      if Io_Mutex_lockUncancelable.again23 r.1 then lockInv E t x sx D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Mutex_lockUncancelableLocals) => 0) s)
      else lockPost E t x sx D r G' m' d') G m d := by
  obtain ⟨hD, -, hi⟩ := h
  have hxs : (x.setM .spin).isMx := by simpa using hx
  unfold Io_Mutex_lockUncancelable.loop23
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [show (WM.ptr.add 0).add 0 = WM.ptr from rfl]
  refine WP.bind (wp_rmwAs (W := WM) hi (wat (fun _ _ h => h.2.1.wm) (by simp [gA]))
    (fun G₁ m₁ _ hi₁ b hb => (mdec hi₁.2.1 (hist_pos hi₁.2.1.wm) hb).imp fun _ h => h.1)
    fun k hk G₁ m₁ m' old r hg₁ hi₁ hd hv hU hh hacq hw' hop => ?_)
  have hu₁ := hi₁.2.1
  have hgt : (G₁ t).2.2 = x.setM .spin := by rw [hg₁]; rfl
  have ht01 : t = 0 ∨ t = 1 := mp_lt hu₁ (by rw [hgt, Ph.mp_setM hx]; simp)
  have hnw := noWM hu₁ ht01 (by rw [hgt, Ph.mp_setM hx]; simp)
  have hmq : ∀ (P : Prop), ∀ w ∈ m'.waiters, w.2 = WM.ptr → P := fun _ w hw hp =>
    absurd hp (hnw w (hop.waiters ▸ hw))
  obtain ⟨r', hr', hrb⟩ := mdec hu₁ (hist_pos hu₁.wm) hv
  rw [hr'] at hd; cases hd
  have hp2 : ∀ p : MP, ((x.setM .spin).setM p).isMx := fun p => by simpa using hx
  have hval : (Word.rmwEnt m' t AtomicOrder.acquire (last (WM.hist m₁))
      (RmwOp.xchg.apply false old (Packed.toBits Io_Mutex_State.contended))).Val (2 : BitVec 32) :=
    rmwEnt_val WM
  cases r
  · -- `unlocked`: `t` holds the mutex
    rw [bits_unlocked] at hrb; subst hrb
    obtain ⟨v₀, -, hl₀, hz⟩ := hu₁.mlast
    have hno := hz.mp (val_eq hv hl₀).symm
    simp only [show (Io_Mutex_State.unlocked != Io_Mutex_State.unlocked) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, Bool.false_eq_true, ↓reduceIte]
    have hth : ∀ u, (upd G₁ t (gA ((x.setM .spin).setM .holds) Heap.empty sx) u).2.2.mp =
        some .holds ↔ u = t := fun u => by
      unfold upd; split
      · rename_i e; subst e; simp [gA, Ph.mp_setM hxs]
      · rename_i e; simp only [e, iff_false]; exact hno u
    obtain ⟨hmh, hml⟩ := mpush (t := t) (g' := gA ((x.setM .spin).setM .holds) Heap.empty sx) hu₁ hh
      hval (by decide) (iff_of_false (by decide) fun h => h t ((hth t).mpr rfl))
    have := inv_mstep hE hi₁ hg₁ hxs (.inr (.inl (Ph.mp_setM hx _))) hop hw' hmh hml (fun w hw hp => hmq _ w hw hp) (fun ⟨h0, h1⟩ => by
      rcases ht01 with rfl | rfl
      · exact absurd ((hth 1).mp h1) (by decide)
      · exact absurd ((hth 0).mp h0) (by decide))
    rw [setM_setM] at this
    exact ⟨rfl, by omega, hop.current, this⟩
  all_goals
    -- the other thread holds the mutex: `t` waits
    have hne : old ≠ 0 := by rw [← hrb]; decide
    obtain ⟨u, hu⟩ := holder_of hu₁ hv hne
    have hut : u ≠ t := fun e => by subst e; rw [hgt, Ph.mp_setM hx] at hu; cases hu
    simp only [show ∀ y : Io_Mutex_State, y ≠ .unlocked → (y != Io_Mutex_State.unlocked) = true from
      fun y h => by cases y <;> simp_all, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte,
      StateT.run_bind, bind_assoc]
    have hw2 : ∀ u', (upd G₁ t (gA ((x.setM .spin).setM .wait) Heap.empty sx) u').2.2.mp =
        some .holds → u' ≠ t := fun u' h e => by
      subst e; simp [gA, Ph.mp_setM hxs] at h
    obtain ⟨hmh, hml⟩ := mpush (t := t) (g' := gA ((x.setM .spin).setM .wait) Heap.empty sx) hu₁ hh
      hval (by decide) (iff_of_false (by decide) fun h => h u (by rw [upd_ne _ _ hut]; exact hu))
    have hiw := inv_mstep hE hi₁ hg₁ hxs (.inr (.inl (Ph.mp_setM hx _))) hop hw' hmh hml (fun w hw hp => hmq _ w hw hp) (fun ⟨h0, h1⟩ => by
      rcases ht01 with rfl | rfl
      · exact hw2 0 h0 rfl
      · exact hw2 1 h1 rfl)
    refine WP.bind (wp_mwait hE (hp2 .wait) (Ph.mp_setM hxs _) hiw
      fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Mutex_lockUncancelable.again23, ↓reduceIte]
    rw [setM_setM, setM_setM] at hi₂
    exact ⟨⟨by omega, hc₂, hi₂⟩, .inl (by omega)⟩

/-- `lock` of the mutex by thread `t` at `x` (`cas`): it holds the mutex. -/
theorem mlock_spec (hE : E.Spec) {t : ThreadId} {x : Ph} (hx : x.isMx) (hxc : x.mp = some .cas)
    {sx : S} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat}
    (hi : (proto E).inv (upd G t (gA x Heap.empty sx)) m) :
    (proto E).WP t (Io_Mutex_lockUncancelable WM.ptr io) (fun _ G' m' d' => d' < d ∧
      m'.current = t ∧ (proto E).inv (upd G' t (gA (x.setM .holds) Heap.empty sx)) m') G m d := by
  unfold Io_Mutex_lockUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  -- the loop, from `spin`
  have hloop : ∀ G₃ m₃ d₃, lockInv E t x sx d default G₃ m₃ d₃ →
      (proto E).WP t ((do
          let __do_lift ← loop (Io_Mutex_lockUncancelable.loop23 WM.ptr io)
            Io_Mutex_lockUncancelable.again23
          match __do_lift with
          | Io_Mutex_lockUncancelableExit.br22 => pure Io_Mutex_lockUncancelableExit.ret
          | e => pure e : CM Tgt Io_Mutex_lockUncancelableLocals Io_Mutex_lockUncancelableExit).run
          default)
        (fun a G₄ m₄ d₄ => (proto E).WP t (match a.1 with
          | Io_Mutex_lockUncancelableExit.ret => pure ()
          | _ => throw Error.panic)
          (fun _ G' m' d' => d' < d ∧ m'.current = t ∧
            (proto E).inv (upd G' t (gA (x.setM .holds) Heap.empty sx)) m') G₄ m₄ d₄)
        G₃ m₃ d₃ := by
    intro G₃ m₃ d₃ h₃
    simp only [StateT.run_bind]
    refine WP.bind (WP.mono ?_ (WP.loop _ _ (lockInv E t x sx d) (fun _ => 0) (lockPost E t x sx d)
      (mloop_body hE hx d io) default G₃ m₃ d₃ h₃))
    rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hd', hc', hi'⟩
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    exact WP.pure' ⟨hd', hc', hi'⟩
  rw [show (WM.ptr.add 0).add 0 = WM.ptr from rfl]
  refine WP.bind (wp_casAs (W := WM) hi (wat (fun _ _ h => h.2.1.wm) (by simp [gA]))
    (fun G₁ m₁ _ hi₁ j hj b hb => (mdec hi₁.2.1 hj hb).imp fun _ h => h.1)
    fun k₁ hk₁ G₁ m₁ m' hg₁ hi₁ hw' hop => ⟨fun hv hU hh => ?_, fun j b r hne hd hj hv hh => ?_⟩)
  all_goals
    have hu₁ := hi₁.2.1
    have hgt : (G₁ t).2.2 = x := by rw [hg₁]; rfl
    have ht01 : t = 0 ∨ t = 1 := mp_lt hu₁ (by rw [hgt, hxc]; simp)
    have hxn : x.mp ≠ some .holds ∧ x.mp ≠ some .wake ∧ x.mp ≠ some .wait := by rw [hxc]; simp
    have hnw := noWM hu₁ ht01 (by rw [hgt]; exact hxn)
  · -- `unlocked` → `locked_once`: `t` holds the mutex
    rw [bits_unlocked] at hv
    obtain ⟨v₀, -, hl₀, hz⟩ := hu₁.mlast
    have hno := hz.mp (val_eq hv hl₀).symm
    have hth : ∀ u, (upd G₁ t (gA (x.setM .holds) Heap.empty sx) u).2.2.mp =
        some .holds ↔ u = t := fun u => by
      unfold upd; split
      · rename_i e; subst e; simp [gA, Ph.mp_setM hx]
      · rename_i e; simp only [e, iff_false]; exact hno u
    obtain ⟨hmh, hml⟩ := mpush (t := t) (g' := gA (x.setM .holds) Heap.empty sx) hu₁ hh
      (rmwEnt_val WM) (by decide) (iff_of_false (by decide) fun h => h t ((hth t).mpr rfl))
    have := inv_mstep hE hi₁ hg₁ hx (.inl hxc) hop hw' hmh hml
      (fun w hw hp => absurd hp (hnw w (hop.waiters ▸ hw))) (fun ⟨h0, h1⟩ => by
      rcases ht01 with rfl | rfl
      · exact absurd ((hth 1).mp h1) (by decide)
      · exact absurd ((hth 0).mp h0) (by decide))
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hop.current, this⟩
  · simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callRC (fun e he => by cases he) fun a ha => ?_)
    cases ha
    simp only [StateT.run_pure, pure_bind]
    obtain ⟨r', hr', hrb⟩ := mdec hu₁ hj hv
    rw [hr'] at hd; cases hd
    cases r
    · exact absurd hrb.symm hne
    · -- `locked_once`: the loop
      simp only [show (Io_Mutex_State.locked_once == Io_Mutex_State.contended) = false from rfl,
        Bool.false_eq_true, ↓reduceIte, pure_bind]
      exact hloop G₁ m' k₁ ⟨by omega, hop.current,
        inv_mcalm hE hi₁ hg₁ hx hxn (by decide) hop hw' hh⟩
    · -- `contended`: the futex wait, then the loop
      simp only [show (Io_Mutex_State.contended == Io_Mutex_State.contended) = true from rfl,
        ↓reduceIte, StateT.run_bind, bind_assoc]
      have hiw := inv_mcalm (p := .wait) hE hi₁ hg₁ hx hxn (by decide) hop hw' hh
      refine WP.bind (wp_mwait hE (by simpa using hx) (Ph.mp_setM hx _) hiw
        fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
      simp only [StateT.run_pure, pure_bind]
      rw [setM_setM] at hi₂
      exact hloop G₂ m₂ k₂ ⟨by omega, hc₂, hi₂⟩

/-- The place after the mutex's `unlock`. -/
def Ph.unl : Ph → Ph
  | sr j _ => sh j
  | wr k _ => wo k
  | x => x

/-- A thread that unlocks the mutex: `main` after its `+ reader`, or the writer. -/
def Ph.isUnl : Ph → Bool
  | sr _ _ | wr _ _ => true
  | _ => false

theorem Ph.same_unl {x : Ph} (h : x.isUnl) : x.Same x.unl := by
  cases x <;> simp_all [isUnl] <;> constructor <;> simp [unl, wb, ib, rb, gave, isWs, mustN, cnt, isMain, isW, inSem, live]

theorem Ph.isMx_of_unl {x : Ph} (h : x.isUnl) : x.isMx := by cases x <;> simp_all [isUnl, isMx]

/-- A thread that unlocks the mutex: `main` at `sr`, the writer at `wr`. -/
def UnlAt (G : ThreadId → Gh S) (t : ThreadId) : Prop :=
  (t = 0 ∧ ∃ j p, (G 0).2.2 = .sr j p) ∨ (t = 1 ∧ ∃ k p, (G 1).2.2 = .wr k p)

theorem UnlAt.isUnl {G : ThreadId → Gh S} {t : ThreadId} (h : UnlAt G t) : (G t).2.2.isUnl := by
  rcases h with ⟨rfl, j, p, hp⟩ | ⟨rfl, k, p, hp⟩ <;> rw [hp] <;> rfl

/-- The flags after an `unlock`. -/
theorem flags_unl {G : ThreadId → Gh S} {t : ThreadId} {g' : Gh S} (hf : Flags (G 0).2.2 (G 1).2.2)
    (hx : UnlAt G t) (hph : g'.2.2 = (G t).2.2.unl) :
    Flags (upd G t g' 0).2.2 (upd G t g' 1).2.2 := by
  obtain ⟨-, f2, -, f4, f5⟩ := hf
  rcases hx with ⟨rfl, j, p, hp⟩ | ⟨rfl, k, p, hp⟩
  · simp only [upd_self, upd0_1, hph, hp, Ph.unl]
    rw [hp] at f5
    exact ⟨fun _ _ => .inl rfl, (fun h => by cases h), (fun hh => by cases hh.1), (fun _ _ h => by cases h),
      f5⟩
  · simp only [upd_self, upd1_0, hph, hp, Ph.unl]
    refine ⟨(fun _ h => by cases h), (fun ha => ?_), (fun hh => by cases hh.2), f4,
      fun h => by have := f5 h; rw [hp] at this; cases this⟩
    obtain ⟨k', hk⟩ := f2 ha; rw [hp] at hk; cases hk

/-- A change of a thread's place to one of the same kind, with the same memory and the same place
in the semaphore's mutex. -/
theorem inv_mghost (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {y : Ph}
    {g' : Gh S} (hi : (proto E).inv G m) (hg : MSet G t y g') (hg1 : g'.1.ph = (G t).1.ph)
    (hml : ∃ v ∈ mVals, (last (WM.hist m)).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds))
    (hmq : ∀ w ∈ m.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m (upd G t g' 0).2.2 (upd G t g' 1).2.2) ∨
      (w.1 = 1 ∧ MQ m (upd G t g' 1).2.2 (upd G t g' 0).2.2))
    (hfl : Flags (upd G t g' 0).2.2 (upd G t g' 1).2.2) : (proto E).inv (upd G t g') m := by
  have hu := hi.2.1
  refine ⟨hi.1.congr (fun u => ?_) (fun u => ?_) (fun u => ?_)
      (R_upd (by rw [hg.2.2.2.2.1]; exact hg.2.2.2.1.isWs)
        (by rw [hg.2.2.2.2.1]; exact hg.2.2.2.1.gave) (by rw [hg.2.2.2.2.1]; exact hg.2.2.2.1.cnt)),
    U_mx hu hg (fun h => by rw [hg1]; exact h) (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _)
      rfl hu.io hu.blk (fun e he => .inl he) (Nat.le_refl _) (fun _ _ _ => rfl)
      (fun _ => VClock.le_refl _) hu.wm hu.mhist hml hmq hfl,
    hE.frame G _ m m hi.2.2 (Frame.refl m)
      (econd hu hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.2 (pnone hu hg.2.2.2.2.2.2.1) (.inl hg1))⟩
  all_goals unfold upd; split
  all_goals first | rfl | (rename_i e; subst e)
  · exact hg1
  · exact hg.2.2.2.2.2.2.1
  · exact hg.2.2.2.2.2.2.2

/-- A thread asleep at the mutex is asleep nowhere else. -/
theorem wm_only (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    {w w' : ThreadId × Ptr} (hw : w ∈ m.waiters) (hp : w.2 = WM.ptr) (hw' : w' ∈ m.waiters)
    (he : w'.1 = w.1) : w'.2 = WM.ptr := by
  have hmp := mq_wait hi.2.1 hw hp
  have hns : (G w.1).2.2.inSem = false := by
    cases e : (G w.1).2.2 <;> rw [e] at hmp <;> simp_all [Ph.mp, Ph.inSem]
  refine Classical.byContradiction fun hne => ?_
  by_cases hl : w'.2 = (L S).ptr
  · rcases hi.1.fq w' hw' with ⟨-, h⟩ | ⟨h, -⟩
    · rw [he] at h
      rcases hi.2.1.lph w.1 hns with h' | h' | ⟨h', -⟩ <;>
        (change (G w.1).1.ph = _ at h; rw [h'] at h; cases h)
    · exact h hl
  · obtain ⟨-, ⟨k, hk⟩, -⟩ := hE.live G m hi w' hw' hl hne
    have h1 := (hE.live G m hi w' hw' hl hne).1
    rw [he] at h1; rw [h1, hk] at hmp; cases hmp

/-- `unlock`'s futex wake by thread `t` (at `wake`): the other thread, if it sleeps at the mutex,
goes on; `t` goes to the place after `unlock`. -/
theorem wp_mwake (hE : E.Spec) {σ : Type} {s₀ : σ} {G : ThreadId → Gh S} {m : Mem} {d : Nat}
    {t : ThreadId} {x : Ph} {h : Heap} {sx : S} {io : Io}
    (hx : UnlAt (upd G t (gA x h sx)) t) (hxw : x.mp = some .wake)
    (hi : (proto E).inv (upd G t (gA x h sx)) m)
    {Q : Unit × σ → (ThreadId → Gh S) → Mem → Nat → Prop}
    (hq : ∀ k, d = k + 1 → ∀ G₁ m', m'.current = t →
      (proto E).inv (upd G₁ t (gA x.unl h sx)) m' → Q ((), s₀) G₁ m' k) :
    (proto E).WP t ((futexWakeC io WM.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s₀) Q G m d := by
  refine WP.futexWakeC fun k hk => ⟨_, hi, fun G₁ m₁ hg₁ hi₁ m' hw => ?_⟩
  have hu₁ := hi₁.2.1
  have hgt : (G₁ t).2.2 = x := by rw [hg₁]; rfl
  have hux : UnlAt G₁ t := by
    rcases hx with ⟨rfl, j, p, hp⟩ | ⟨rfl, k', p, hp⟩
    · exact .inl ⟨rfl, j, p, by rw [hg₁]; rw [upd_self] at hp; exact hp⟩
    · exact .inr ⟨rfl, k', p, by rw [hg₁]; rw [upd_self] at hp; exact hp⟩
  have ht01 : t = 0 ∨ t = 1 := by rcases hux with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hm' := Proto.modify_ok hw
  generalize hwk : ((m₁.waiters.filter (·.2 == WM.ptr)).extract 0 (1 : BitVec 32).toNat).map (·.1) =
    woke at hm'
  -- every thread at the mutex was woken: it is the other thread
  have hno : ∀ w ∈ m'.waiters, w.2 ≠ WM.ptr := by
    intro w hw' hp
    rw [hm'] at hw'
    have hw'' := Array.mem_filter.mp hw'
    have hpos : 0 < (m₁.waiters.filter (·.2 == WM.ptr)).size :=
      Array.size_pos_of_mem (Array.mem_filter.mpr ⟨hw''.1, by simp [hp]⟩)
    have hw0 := Array.getElem_mem (xs := m₁.waiters.filter (·.2 == WM.ptr)) hpos
    have hw0m := Array.mem_filter.mp hw0
    have hin : (m₁.waiters.filter (·.2 == WM.ptr))[0].1 ∈ woke := by
      rw [← hwk]
      exact Array.mem_map.mpr ⟨_, Array.mem_extract_iff_getElem.mpr ⟨0, by simp; omega, rfl⟩, rfl⟩
    -- both waiters at the mutex are the thread other than `t`
    have hother : ∀ v ∈ m₁.waiters, v.2 = WM.ptr → v.1 ≠ t := fun v hv hvp e => by
      have := mq_wait hu₁ hv hvp; rw [e, hgt, hxw] at this; cases this
    have h1 := hother w hw''.1 hp
    have h2 := hother _ hw0m.1 (by simpa using hw0m.2)
    have heq : w.1 = (m₁.waiters.filter (·.2 == WM.ptr))[0].1 := by
      have a := mp_lt hu₁ (u := w.1) (by rw [mq_wait hu₁ hw''.1 hp]; simp)
      have b := mp_lt hu₁ (u := (m₁.waiters.filter (·.2 == WM.ptr))[0].1)
        (by rw [mq_wait hu₁ hw0m.1 (by simpa using hw0m.2)]; simp)
      unfold ThreadId at *; omega
    have := hw''.2
    simp only [Bool.not_eq_true'] at this
    rw [heq, Array.contains_iff_mem.mpr hin] at this
    cases this
  have hl := hi₁.1.wakeOff wmL hw
  have hU := U_q (c := t) hu₁ hm' fun w hw' hp => absurd hp (hno w (by rw [hm']; exact hw'))
  have hEi := hE.frame G₁ G₁ m₁ m' hi₁.2.2 ⟨fun W _ _ _ => by
      rw [hm']; exact Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _, by rw [hm'],
      fun w hw2 => by
        rw [hm']; simp only [Array.mem_filter]
        constructor
        · exact fun h => h.1
        · intro hwm; refine ⟨hwm, ?_⟩
          simp only [Bool.not_eq_true']
          apply Bool.eq_false_iff.mpr; intro hc
          rw [← hwk] at hc
          obtain ⟨v, hv, hve⟩ := Array.mem_map.mp (Array.contains_iff_mem.mp hc)
          have hv' : v ∈ m₁.waiters.filter (·.2 == WM.ptr) := by
            obtain ⟨j, -, rfl⟩ := Array.mem_extract_iff_getElem.mp hv; exact Array.getElem_mem _
          have hv'' := Array.mem_filter.mp hv'
          exact hw2 (wm_only hE hi₁ hv''.1 (by simpa using hv''.2) hwm hve.symm),
      fun _ => by rw [hm']; exact VClock.le_refl _⟩
      (econd0 hu₁)
  have hxu : x.isUnl := by rw [← hgt]; exact hux.isUnl
  have hxk : x.live ∧ x.inSem = false ∧ x ≠ .pre ∧ x.unl.mp = Option.none := by
    revert hxu; cases x <;> simp [Ph.isUnl, Ph.live, Ph.inSem, Ph.unl, Ph.mp]
  have hMS : MSet G₁ t x.unl (gA x.unl h sx) := by
    refine ⟨?_, ?_, ?_, by rw [hgt]; exact Ph.same_unl hxu, rfl, by rw [hg₁]; rfl,
      by rw [hg₁]; rfl, by rw [hg₁]; rfl⟩ <;> rw [hgt]
    · exact hxk.1
    · exact hxk.2.1
    · exact hxk.2.2.1
  have hml : ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G₁ t (gA x.unl h sx) u).2.2.mp ≠ some .holds) := by
    obtain ⟨v, hv, hl', hz⟩ := hU.mlast
    refine ⟨v, hv, hl', hz.trans (forall_congr' fun u => ?_)⟩
    unfold upd; split
    · rename_i e; subst e; rw [hgt, hxw]; show _ ↔ x.unl.mp ≠ _; rw [hxk.2.2.2]; simp
    · exact Iff.rfl
  exact hq k hk G₁ m' (by rw [hm']) (inv_mghost hE ⟨hl, hU, hEi⟩ hMS (by rw [hg₁]; rfl) hml
    (fun w hw' hp => absurd hp (hno w hw'))
    (flags_unl hU.flags hux (by rw [hgt]; rfl)))

/-- `unlock` of the mutex by its holder `t` at `x` (`main` at `sr`, the writer at `wr`): it goes
to the place after `unlock`. -/
theorem munlock_spec (hE : E.Spec) {t : ThreadId} {x : Ph} {h : Heap} {sx : S} {io : Io}
    {G : ThreadId → Gh S} {m : Mem} {d : Nat} (hx : UnlAt (upd G t (gA x h sx)) t)
    (hxh : x.mp = some .holds) (hi : (proto E).inv (upd G t (gA x h sx)) m) :
    (proto E).WP t (Io_Mutex_unlock WM.ptr io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = t ∧ (proto E).inv (upd G' t (gA x.unl h sx)) m') G m d := by
  unfold Io_Mutex_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [show (WM.ptr.add 0).add 0 = WM.ptr from rfl]
  refine WP.bind (wp_rmwAs (W := WM) hi (wat (fun _ _ h => h.2.1.wm) (by simp [gA]))
    (fun G₁ m₁ _ hi₁ b hb => (mdec hi₁.2.1 (hist_pos hi₁.2.1.wm) hb).imp fun _ h => h.1)
    fun k hk G₁ m₁ m' old r hg₁ hi₁ hd hv hU hh hacq hw' hop => ?_)
  have hu₁ := hi₁.2.1
  have hgt : (G₁ t).2.2 = x := by rw [hg₁]; rfl
  have hux : UnlAt G₁ t := by
    rcases hx with ⟨rfl, j, p, hp⟩ | ⟨rfl, k', p, hp⟩
    · exact .inl ⟨rfl, j, p, by rw [hg₁]; rw [upd_self] at hp; exact hp⟩
    · exact .inr ⟨rfl, k', p, by rw [hg₁]; rw [upd_self] at hp; exact hp⟩
  have ht01 : t = 0 ∨ t = 1 := by rcases hux with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hxu : x.isUnl := by rw [← hgt]; exact hux.isUnl
  have hx' : x.isMx := Ph.isMx_of_unl hxu
  obtain ⟨r', hr', hrb⟩ := mdec hu₁ (hist_pos hu₁.wm) hv
  rw [hr'] at hd; cases hd
  -- the other thread does not hold the mutex
  have hoth : ∀ u, u ≠ t → (G₁ u).2.2.mp ≠ some .holds := fun u hut hu => by
    have h1 := hu₁.flags.one
    have hu01 := mp_lt hu₁ (u := u) (by rw [hu]; simp)
    rcases ht01 with rfl | rfl <;> rcases hu01 with rfl | rfl
    all_goals first | exact hut rfl | exact h1 ⟨by rw [hgt, hxh], hu⟩ | exact h1 ⟨hu, by rw [hgt, hxh]⟩
  have hval : (Word.rmwEnt m' t AtomicOrder.release (last (WM.hist m₁))
      (RmwOp.xchg.apply false old (Packed.toBits Io_Mutex_State.unlocked))).Val (0 : BitVec 32) :=
    rmwEnt_val WM
  have hfree : ∀ (y : Ph), y.mp ≠ some .holds →
      ∀ u, (upd G₁ t (gA y h sx) u).2.2.mp ≠ some .holds := fun y hy u => by
    unfold upd; split
    · exact hy
    · rename_i e; exact hoth u e
  cases r
  · -- `unlocked`: the holder reads a word that is not `0`
    exfalso
    rw [bits_unlocked] at hrb; subst hrb
    obtain ⟨v₀, -, hl₀, hz⟩ := hu₁.mlast
    exact (hz.mp (val_eq hv hl₀).symm) t (by rw [hgt, hxh])
  · -- `locked_once`: no thread waits
    rw [bits_once] at hrb; subst hrb
    have hnw : ∀ w ∈ m₁.waiters, w.2 ≠ WM.ptr := fun w hw hp => by
      have hw1 := mq_wait hu₁ hw hp
      have hwt : w.1 ≠ t := fun e => by rw [e, hgt, hxh] at hw1; cases hw1
      rcases hu₁.mq w hw hp with ⟨h0, -, ho⟩ | ⟨h1, -, ho⟩
      all_goals
        have hot : (if w.1 = 0 then (1 : ThreadId) else 0) = t := by
          rcases ht01 with rfl | rfl <;> simp_all
        rcases ho with ⟨-, h2⟩ | h2
        · exact absurd (val_eq hv h2) (by decide)
        · first
            | (rw [show (1 : ThreadId) = t by simp_all] at h2; rw [hgt, hxh] at h2; cases h2)
            | (rw [show (0 : ThreadId) = t by simp_all] at h2; rw [hgt, hxh] at h2; cases h2)
    have hxk : x.unl.mp = Option.none ∧ x.unl.isMx = false := by
      revert hxu; cases x <;> simp [Ph.isUnl, Ph.unl, Ph.mp, Ph.isMx]
    have hMS : MSet G₁ t x.unl (gA x.unl h sx) := by
      refine ⟨?_, ?_, ?_, by rw [hgt]; exact Ph.same_unl hxu, rfl, by rw [hg₁]; rfl,
        by rw [hg₁]; rfl, by rw [hg₁]; rfl⟩ <;> rw [hgt] <;> revert hxu <;> cases x <;>
        simp [Ph.isUnl, Ph.live, Ph.inSem]
    obtain ⟨hmh, hml⟩ := mpush (t := t) (g' := gA x.unl h sx) hu₁ hh hval (by decide)
      (iff_of_true rfl (hfree _ (by rw [hxk.1]; simp)))
    have := inv_mop hE hi₁ hMS (by rw [hg₁]; rfl) hop hw' hmh hml
      (fun w hw hp => absurd hp (hnw w (hop.waiters ▸ hw))) (flags_unl hu₁.flags hux (by rw [hgt]; rfl))
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hop.current, this⟩
  · -- `contended`: `t` wakes the other thread
    rw [bits_cont] at hrb; subst hrb
    obtain ⟨hmh, hml⟩ := mpush (t := t) (g' := gA (x.setM .wake) h sx) hu₁ hh hval (by decide)
      (iff_of_true rfl (hfree _ (by rw [Ph.mp_setM hx']; simp)))
    have hiw := inv_mstep (p := .wake) hE hi₁ hg₁ hx' (.inr (.inr (.inr rfl))) hop hw' hmh hml (fun w hw hp => by
        rw [hop.waiters] at hw
        have hw1 := mq_wait hu₁ hw hp
        have hwt : w.1 ≠ t := fun e => by rw [e, hgt, hxh] at hw1; cases hw1
        have hup : ∀ u, u ≠ t → upd G₁ t (gA (x.setM .wake) h sx) u = G₁ u := fun u e => upd_ne _ _ e
        rcases ht01 with rfl | rfl
        · have : w.1 = 1 := by have := mp_lt hu₁ (u := w.1) (by rw [hw1]; simp); unfold ThreadId at *; omega
          refine .inr ⟨this, by rw [hup 1 (by decide), ← this]; exact hw1, .inr ?_⟩
          rw [upd_self]; exact Ph.mp_setM hx' _
        · have : w.1 = 0 := by have := mp_lt hu₁ (u := w.1) (by rw [hw1]; simp); unfold ThreadId at *; omega
          refine .inl ⟨this, by rw [hup 0 (by decide), ← this]; exact hw1, .inr ?_⟩
          rw [upd_self]; exact Ph.mp_setM hx' _)
      (fun ⟨h0, h1⟩ => by
        rcases ht01 with rfl | rfl
        · rw [upd_self] at h0; change (x.setM .wake).mp = _ at h0; rw [Ph.mp_setM hx'] at h0; cases h0
        · rw [upd_self] at h1; change (x.setM .wake).mp = _ at h1; rw [Ph.mp_setM hx'] at h1; cases h1)
    simp only [StateT.run_bind, bind_assoc]
    refine WP.bind (wp_mwake hE (x := x.setM .wake) (by
        rcases hux with ⟨rfl, j, p, hp⟩ | ⟨rfl, k', p, hp⟩
        · exact .inl ⟨rfl, j, .wake, by rw [upd_self]; show (x.setM .wake) = _; rw [← hgt, hp]; rfl⟩
        · exact .inr ⟨rfl, k', .wake, by rw [upd_self]; show (x.setM .wake) = _; rw [← hgt, hp]; rfl⟩)
      (Ph.mp_setM hx' _) hiw fun k₂ hk₂ G₂ m₂ hc₂ hi₂ => ?_)
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    have : (x.setM .wake).unl = x.unl := by revert hxu; cases x <;> simp [Ph.isUnl, Ph.setM, Ph.unl]
    rw [this] at hi₂
    exact WP.pure' ⟨by omega, hc₂, hi₂⟩

/-! ## The state word -/

/-- After an RMW of the state word (release): `n` stays in it. -/
theorem car_rmw {m m' : Mem} {t : ThreadId} {hn : Heap} {k : Nat} {v : BitVec 64}
    (hp : NPts k hn) (hs : hn.Sub m.heap) (hc : CarOk m hn) (hw : WS.Ok m) (hop : WS.Op t m m')
    (hh : WS.hist m' = (WS.hist m).push (Word.rmwEnt m' t .seqCst (last (WS.hist m)) v)) :
    hn.Sub m'.heap ∧ CarOk m' hn := by
  obtain ⟨hfp, -⟩ := op_fp hop hw (by decide) (by decide)
  exact car_keep hp hs hc (by rw [hh, last_push]; exact VClock.le_merge_left _ _) hfp
    (Nat.le_of_eq hop.bsize.symm) (fun x _ _ => hop.cells _ (by simp [WS]; omega))
    (fun _ h => hop.allLe h)

/-- An acquire RMW of the state word takes `n` from it. -/
theorem own_rmw {m m' : Mem} {t : ThreadId} {hn : Heap} {k : Nat} (hp : NPts k hn)
    (hc : CarOk m hn) (hw : WS.Ok m) (hop : WS.Op t m m') (ht : t < m.threads.size)
    (hacq : VClock.le (last (WS.hist m)).relClock (m'.clocks[t]!) = true) :
    m'.OwnsC (m'.clocks[t]!) hn := fun e he htc => by
  obtain ⟨hfp, -⟩ := op_fp hop hw (by decide) (by decide)
  rcases hfp e he with he' | ⟨hno, hb⟩
  · rcases hc e he' (htc.imp id fun h => by rw [← hop.bsize]; exact h) with h | h
    · exact VClock.le_trans h hacq
    · exact VClock.le_trans (h t ht) (hop.clocks t)
  · rcases htc with h | h
    · exact absurd h (hno.not hp)
    · exact absurd hb (Nat.not_lt.mpr h)

/-- Thread `t` takes `n` (`hn`) from the state word: no thread owns anything. -/
theorem linv_gain {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {g' : Gh S}
    {hn : Heap} {k : Nat} (hl : (L S).Inv G m) (ht : t < m.threads.size)
    (hjt : joinedB m t = false) (hdj : ∀ u, Heap.Disjoint hn ((L S).own G m u)) (hp : NPts k hn)
    (hs : hn.Sub m.heap) (hc : m.OwnsC (m.clocks[t]!) hn)
    (hnh : hasP (fun u => (G u).2.2) = false) (hown0 : (L S).own G m t = Heap.empty)
    (hheld : (G t).1.held = Heap.empty)
    (hg' : g'.1 = ⟨(G t).1.ph, hn, Heap.empty⟩)
    (hR : ∀ h, (L S).R (upd G t g') h ↔ (L S).R G h) :
    (L S).Inv (upd G t g') m := by
  have ho := hl.own.add ht hs hdj hc
  rw [hown0, Heap.empty_union] at ho
  refine hl.repart hjt ?_ (by show g'.1.ph = _; rw [hg']; rfl)
    (by show g'.1.held = _; rw [hg', show (L S).held (G t) = (G t).1.held from rfl, hheld])
    (by show Heap.Disjoint g'.1.part g'.1.held; rw [hg']; exact Heap.disjoint_empty _)
    (fun x h1 h2 => by
      show g'.1.part _ = none; rw [hg']
      exact npts_none hp (by simp only [L, Lock.prod] at h1 h2 ⊢; omega))
    (fun _ hL hR => ?_) hR
  · show Owned (upd ((L S).own G m) t (g'.1.part ∪ g'.1.held)) m
    rw [hg']; simpa using ho
  · show Heap.Disjoint hL g'.1.part
    rw [hg']; intro l
    cases e : hL l with
    | none => exact .inl rfl
    | some c =>
      right
      obtain ⟨hb, h1 | ⟨hh, -⟩⟩ := semR_at hR l (by rw [e]; simp)
      · exact npts_none hp (by omega)
      · rw [hnh] at hh; cases hh

/-- Thread `t` gives its part to the state word (or to the semaphore). -/
theorem linv_lose {G : ThreadId → Gh S} {m : Mem} {t : ThreadId} {g' : Gh S} (hl : (L S).Inv G m)
    (hjt : joinedB m t = false) (hheld : (G t).1.held = Heap.empty)
    (hg' : g'.1 = ⟨(G t).1.ph, Heap.empty, Heap.empty⟩)
    (hR : ∀ h, (L S).R (upd G t g') h ↔ (L S).R G h) : (L S).Inv (upd G t g') m := by
  have ho := hl.own.shrink (t := t) (h := Heap.empty) fun _ _ h => by cases h
  refine hl.repart hjt ?_ (by show g'.1.ph = _; rw [hg']; rfl)
    (by show g'.1.held = _; rw [hg', show (L S).held (G t) = (G t).1.held from rfl, hheld])
    (by show Heap.Disjoint g'.1.part g'.1.held; rw [hg']; exact Heap.disjoint_empty _)
    (fun x _ _ => by show g'.1.part _ = none; rw [hg']; rfl)
    (fun _ hL _ => by show Heap.Disjoint hL g'.1.part; rw [hg']; exact Heap.disjoint_empty _) hR
  show Owned (upd ((L S).own G m) t (g'.1.part ∪ g'.1.held)) m
  rw [hg']; simpa using ho

/-- The mutex word's facts after a step at another word, when `t`'s place in the mutex's code
stays, or neither place holds or wakes the mutex. -/
theorem mfacts {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {g' : Gh S} (hu : U G m)
    (hk : WM.Keep m m') (hq : m'.waiters = m.waiters)
    (hmp : g'.2.2.mp = (G t).2.2.mp ∨ ((G t).2.2.mp ≠ some .holds ∧ (G t).2.2.mp ≠ some .wake ∧
      (G t).2.2.mp ≠ some .wait ∧ g'.2.2.mp ≠ some .holds ∧ g'.2.2.mp ≠ some .wake)) :
    (∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds)) ∧
    (∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t g' 0).2.2 (upd G t g' 1).2.2) ∨
      (w.1 = 1 ∧ MQ m' (upd G t g' 1).2.2 (upd G t g' 0).2.2)) := by
  have hh := Word.hist_keep hu.wm hk
  rcases hmp with hmp | ⟨h1, h2, h3, h4, h5⟩
  · have hm : ∀ u, (upd G t g' u).2.2.mp = (G u).2.2.mp := fun u => by
      unfold upd; split
      · rename_i e; subst e; exact hmp
      · rfl
    obtain ⟨v, hv, hl, hz⟩ := hu.mlast
    refine ⟨⟨v, hv, by rw [hh]; exact hl, hz.trans (forall_congr' fun u => by rw [hm])⟩,
      fun w hw hp => ?_⟩
    unfold MQ; rw [hh, hm, hm]; exact hu.mq w (hq ▸ hw) hp
  · obtain ⟨a, b, -⟩ := calm (g' := g') hu ⟨h1, h2⟩ ⟨h4, h5⟩ hh (fun w hw hp => by
      rw [hq] at hw
      exact ⟨hw, fun e => h3 (by rw [← e]; exact mq_wait hu hw hp)⟩)
    exact ⟨a, b⟩

/-- An RMW of the state word by thread `t` (running, out of the semaphore's code), which goes to
`g'` (the same place in the semaphore's mutex, the same `S`): `U` from the new facts. -/
theorem U_sop {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {g' : Gh S} {e : Word.Entry}
    (hu : U G m) (hop : WS.Op t m m') (hw' : WS.Ok m')
    (hh : WS.hist m' = (WS.hist m).push e)
    (he : e.Val (sv (upd G t g' 0).2.2 (upd G t g' 1).2.2)) (hs : g'.2.1 = (G t).2.1)
    (hl : g'.1.ph = (G t).1.ph) (hlv : (G t).2.2.live) (hns : (G t).2.2.inSem = false)
    (hml : ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.2.mp ≠ some .holds))
    (hmq : ∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t g' 0).2.2 (upd G t g' 1).2.2) ∨
      (w.1 = 1 ∧ MQ m' (upd G t g' 1).2.2 (upd G t g' 0).2.2))
    (hsh : Shape (fun u => (upd G t g' u).2.2) m) (hfl : Flags (upd G t g' 0).2.2 (upd G t g' 1).2.2)
    (hparts : ∀ u, if (upd G t g' u).2.2.mustN then
      NPts (upd G t g' 1).2.2.cnt (upd G t g' u).1.part else (upd G t g' u).1.part = Heap.empty)
    (hcar : Car (upd G t g' 0).2.2 (upd G t g' 1).2.2 →
      ∃ hn, NPts (upd G t g' 1).2.2.cnt hn ∧ hn.Sub m'.heap ∧ CarOk m' hn) :
    U (upd G t g') m' := by
  obtain ⟨-, hio⟩ := op_fp hop hu.ws (by decide) (by decide)
  have hkM := Word.keep_op hop (W' := WM) (.inr (.inl (by decide)))
  refine ⟨by unfold Shape at *; rw [hop.threads]; exact hsh, hfl, hio hu.io,
    blk_keep hu.blk (hop.cells _ (by simp [WS])), hw', hu.wm.keep hkM,
    by rw [hh]; exact vals_push hu.shist (sv_mem _ _) he, by rw [hh, last_push]; exact he,
    by rw [Word.hist_keep hu.wm hkM]; exact hu.mhist, hml, hmq, fun u hu' => ?_, hparts, hcar⟩
  by_cases e : u = t
  · subst e; rw [upd_self] at hu' ⊢; rw [hl]
    rcases hu.lph u hns with h | h | ⟨-, h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · rw [hlv] at h; cases h
  · rw [upd_ne _ _ e] at hu' ⊢; exact hu.lph u hu'

/-- The resource when the semaphore has no `n` before and after. -/
theorem R_nohas {G G' : ThreadId → Gh S} (h1 : hasP (fun u => (G' u).2.2) = false)
    (h2 : hasP (fun u => (G u).2.2) = false) (h : Heap) : (L S).R G' h ↔ (L S).R G h :=
  semR_congr (by rw [h1, h2]) (fun hh => by rw [h2] at hh; cases hh) h

/-- An RMW of the state word by thread `t` at `x` (part `hx`), which goes to `y` (part `hy`):
the protocol, from the lock's invariant and the new facts. -/
theorem inv_sstep (hE : E.Spec) {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {x y : Ph}
    {hx hy : Heap} {sx : S} {e : Word.Entry} (hi : (proto E).inv G m)
    (hg : G t = gA x hx sx) (hop : WS.Op t m m') (hw' : WS.Ok m')
    (hh : WS.hist m' = (WS.hist m).push e)
    (he : e.Val (sv (upd G t (gA y hy sx) 0).2.2 (upd G t (gA y hy sx) 1).2.2))
    (hlv : x.live) (hns : x.inSem = false) (hnp : x ≠ .pre) (hM : y.isMain = x.isMain)
    (hW : y.isW = x.isW) (hcnt : y.cnt = x.cnt)
    (hmp : y.mp = x.mp ∨ (x.mp ≠ some .holds ∧ x.mp ≠ some .wake ∧ x.mp ≠ some .wait ∧
      y.mp ≠ some .holds ∧ y.mp ≠ some .wake))
    (hfl : Flags (upd G t (gA y hy sx) 0).2.2 (upd G t (gA y hy sx) 1).2.2)
    (hpy : if y.mustN then NPts (upd G t (gA y hy sx) 1).2.2.cnt hy else hy = Heap.empty)
    (hcar : Car (upd G t (gA y hy sx) 0).2.2 (upd G t (gA y hy sx) 1).2.2 →
      ∃ hn, NPts (upd G t (gA y hy sx) 1).2.2.cnt hn ∧ hn.Sub m'.heap ∧ CarOk m' hn)
    (hL : (L S).Inv (upd G t (gA y hy sx)) m') :
    (proto E).inv (upd G t (gA y hy sx)) m' := by
  have hu := hi.2.1
  have hgt : (G t).2.2 = x := by rw [hg]; rfl
  have hY : (G t).2.2.isMain ∨ ((G t).2.2.isW ∧ (G t).2.2 ≠ .wf) := by
    rw [hgt]
    obtain ⟨-, ⟨-, hp0, hn⟩ | ⟨-, -, hM0, hW0, hn⟩⟩ := hu.shape
    · exfalso
      rcases Nat.eq_zero_or_pos t with rfl | h
      · change (G 0).2.2 = _ at hp0; rw [hgt] at hp0; exact hnp hp0
      · have := hn t h; change (G t).2.2 = _ at this; rw [hgt] at this; subst this; cases hlv
    · rcases Nat.lt_or_ge t 2 with h | h
      · rcases (by unfold ThreadId at *; omega : t = 0 ∨ t = 1) with rfl | rfl
        · exact .inl (by rw [← hgt]; exact hM0)
        · exact .inr ⟨by rw [← hgt]; exact hW0, fun e => by subst e; cases hlv⟩
      · have := hn t h; change (G t).2.2 = _ at this; rw [hgt] at this; subst this; cases hlv
  obtain ⟨hml, hmq⟩ := mfacts (g' := gA y hy sx) hu (Word.keep_op hop (W' := WM) (.inr (.inl (by decide))))
    hop.waiters (by rw [hgt]; exact hmp)
  have hpt : ∀ x', 24 ≤ x' → x' < 48 → hy (0, x') = none := fun x' _ h2 => by
    split at hpy
    · exact npts_none hpy (by omega)
    · rw [hpy]; rfl
  refine ⟨hL, U_sop hu hop hw' hh he (by rw [hg]; rfl) (by rw [hg]; rfl) (by rw [hgt]; exact hlv)
    (by rw [hgt]; exact hns) hml hmq (by
      rw [ph_upd]; exact shape_upd hu.shape hY (by rw [hgt]; simp [gA, hM]) (by rw [hgt]; simp [gA, hW]))
    hfl (fun u => ?_) hcar,
    hE.frame G _ m m' hi.2.2 (frame_op hop (.inr (.inl (by decide))))
      (econd hu (by rw [hg]; rfl) (by rw [hg]; rfl) hpt (.inl (by rw [hg]; rfl)))⟩
  have h1 : (upd G t (gA y hy sx) 1).2.2.cnt = (G 1).2.2.cnt := by
    unfold upd; split
    · rename_i e1; subst e1; rw [hgt]; exact hcnt
    · rfl
  by_cases e' : u = t
  · subst e'; rw [upd_self]; exact hpy
  · rw [upd_ne _ _ e', h1]; exact hu.parts u

/-- A release RMW of the state word by `t`, which owns `hn`: `n` goes to the state word. -/
theorem car_lose {m m' : Mem} {t : ThreadId} {hn : Heap} {v : BitVec 64} (hw : WS.Ok m)
    (ho : m.OwnsC (m.clocks[t]!) hn) (hs : hn.Sub m.heap) {k : Nat} (hp : NPts k hn)
    (hop : WS.Op t m m')
    (hh : WS.hist m' = (WS.hist m).push (Word.rmwEnt m' t .seqCst (last (WS.hist m)) v)) :
    hn.Sub m'.heap ∧ CarOk m' hn := by
  obtain ⟨hfp, -⟩ := op_fp hop hw (by decide) (by decide)
  refine ⟨fun l c hl => ?_, fun e he htc => ?_⟩
  · obtain ⟨hb, h1, h2⟩ := (npts_at hp l).mp (by rw [hl]; simp)
    rw [hop.cells l (by simp [WS]; omega)]; exact hs l c hl
  · rcases hfp e he with he' | ⟨hno, hb⟩
    · refine .inl (VClock.le_trans (ho e he' (htc.imp id fun h => by rw [← hop.bsize]; exact h))
        (VClock.le_trans hop.mine ?_))
      rw [hh, last_push]; exact VClock.le_merge_right _ _
    · rcases htc with h | h
      · exact absurd h (hno.not hp)
      · exact absurd hb (Nat.not_lt.mpr h)

/-- The parts and the resource have no byte of `n` while the semaphore does not have it and no
place owns it. -/
theorem own_nN {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (hc : Car (G 0).2.2 (G 1).2.2) {k : Nat} {hn : Heap} (hp : NPts k hn) (u : ThreadId) :
    Heap.Disjoint hn ((L S).own G m u) := fun l => by
  by_cases hl : hn l = none
  · exact .inl hl
  right
  obtain ⟨b, o⟩ := l
  obtain ⟨rfl, h1, h2⟩ := (npts_at hp _).mp hl
  unfold Lock.own; split
  · rfl
  show ((G u).1.part ∪ (G u).1.held) (0, o) = none
  have hpart : (G u).1.part = Heap.empty := by
    have := hi.2.1.parts u
    split at this
    · rename_i hm
      exfalso
      have hu01 : u = 0 ∨ u = 1 := by
        rcases Nat.lt_or_ge u 2 with h | h
        · unfold ThreadId at *; omega
        · obtain ⟨-, ⟨-, -, hn⟩ | ⟨-, -, -, -, hn⟩⟩ := hi.2.1.shape
          · have := hn u (by unfold ThreadId at *; omega); change (G u).2.2 = _ at this
            rw [this] at hm; cases hm
          · have := hn u h; change (G u).2.2 = _ at this; rw [this] at hm; cases hm
      rcases hu01 with rfl | rfl
      · rw [hc.1] at hm; cases hm
      · rw [hc.2.1] at hm; cases hm
    · exact this
  rw [hpart, Heap.empty_union]
  by_cases hh : (L S).ph (G u) = .holds
  · cases e : (G u).1.held (0, o) with
    | none => rfl
    | some c =>
      obtain ⟨-, h3 | ⟨hh', -⟩⟩ := semR_at (hi.1.res u hh) (0, o) (by
        show (L S).held (G u) (0, o) ≠ none; rw [show (L S).held (G u) = (G u).1.held from rfl, e]
        simp)
      · dsimp only at h3; omega
      · rw [show hasP (fun u => (G u).2.2) = ((G 1).2.2.isWs && (G 0).2.2.gave) from rfl,
          hc.2.2] at hh'
        cases hh'
  · rw [show (G u).1.held = (L S).held (G u) from rfl, hi.1.idle u hh]; rfl

/-- The lock's invariant after an op at the state word by `t`, with the same part. -/
theorem lws_keep {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {x y : Ph} {hx : Heap} {sx : S}
    (hi : (proto E).inv G m) (hop : WS.Op t m m') (hg : G t = gA x hx sx)
    (h1 : hasP (fun u => (upd G t (gA y hx sx) u).2.2) = false)
    (h2 : hasP (fun u => (G u).2.2) = false) : (L S).Inv (upd G t (gA y hx sx)) m' := by
  have hf : ∀ u, (upd G t (gA y hx sx) u).1 = (G u).1 := fun u => by
    unfold upd; split
    · rename_i e; subst e; rw [hg]; rfl
    · rfl
  exact (hi.1.wordOp hi.2.1.ws hop apS (off_own hi rfl ws_free) (off_R rfl ws_free G)).congr
    (fun u => by show (upd G t _ u).1.ph = _; rw [hf]; rfl)
    (fun u => by show (upd G t _ u).1.part = _; rw [hf]; rfl)
    (fun u => by show (upd G t _ u).1.held = _; rw [hf]; rfl) (R_nohas h1 h2)

/-- The lock's invariant after an acquire RMW of the state word by `t`, which takes `n` (`hn`). -/
theorem lws_gain {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {x y : Ph} {sx : S} {hn : Heap}
    {k : Nat} (hi : (proto E).inv G m) (hop : WS.Op t m m') (hg : G t = gA x Heap.empty sx)
    (hc : Car (G 0).2.2 (G 1).2.2) (hp : NPts k hn) (hs : hn.Sub m'.heap)
    (ho : m'.OwnsC (m'.clocks[t]!) hn)
    (h1 : hasP (fun u => (upd G t (gA y hn sx) u).2.2) = false) :
    (L S).Inv (upd G t (gA y hn sx)) m' := by
  have hl := hi.1.wordOp hi.2.1.ws hop apS (off_own hi rfl ws_free) (off_R rfl ws_free G)
  have hjt : joinedB m t = false := (hi.1.live t (by rw [hg]; exact (by decide : LPh.out ≠ LPh.gone))).2
  have hjb : joinedB m' = joinedB m := Lock.joinedB_congr hop.threads
  have hown : (L S).own G m' = (L S).own G m := by funext u; unfold Lock.own; rw [hjb]
  refine linv_gain hl (by rw [hop.threads]; exact (hi.1.live t (by rw [hg]; exact (by decide :
      LPh.out ≠ LPh.gone))).1) (by rw [hjb]; exact hjt) (fun u => by rw [hown]; exact own_nN hi hc hp u)
    hp hs ho hc.2.2 (by rw [hown, Lock.own_live hjt, hg]; simp [L, Lock.prod, gA]) (by rw [hg]; rfl)
    (by rw [hg]; rfl) (R_nohas h1 hc.2.2)

/-- The lock's invariant after a release RMW of the state word by `t`, which gives its part. -/
theorem lws_lose {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {x y : Ph} {sx : S} {hx : Heap}
    (hi : (proto E).inv G m) (hop : WS.Op t m m') (hg : G t = gA x hx sx)
    (h1 : hasP (fun u => (upd G t (gA y Heap.empty sx) u).2.2) = false)
    (h2 : hasP (fun u => (G u).2.2) = false) : (L S).Inv (upd G t (gA y Heap.empty sx)) m' := by
  have hl := hi.1.wordOp hi.2.1.ws hop apS (off_own hi rfl ws_free) (off_R rfl ws_free G)
  have hjt : joinedB m t = false := (hi.1.live t (by rw [hg]; exact (by decide : LPh.out ≠ LPh.gone))).2
  exact linv_lose hl (by rw [Lock.joinedB_congr hop.threads]; exact hjt) (by rw [hg]; rfl)
    (by rw [hg]; rfl) (R_nohas h1 h2)

/-! ## The `RwLock`'s ops -/

/-- The old value of an RMW of the state word: the state of the places. -/
theorem sold {G : ThreadId → Gh S} {m : Mem} (hu : U G m) {old : BitVec 64}
    (hv : (last (WS.hist m)).Val old) : old = sv3 (G 1).2.2.wb (G 1).2.2.ib (G 0).2.2.rb :=
  val_eq hv hu.slast

theorem wsptr : (bPtr.add 16).add 0 = WS.ptr := rfl
theorem wmptr : (bPtr.add 16).add 32 = WM.ptr := rfl
theorem semptr : (bPtr.add 16).add 8 = semPtr := rfl

/-- `lock` of the `RwLock` by the writer at `wo k`: it owns `n`. -/
theorem wlock_spec (hE : E.Spec) {k : Nat} (hk : k < 2) {io : Io} {G : ThreadId → Gh S}
    {m : Mem} {d : Nat} (hi : (proto E).inv (upd G 1 (gA (.wo k) Heap.empty default)) m) :
    (proto E).WP 1 (Io_RwLock_lockUncancelable (bPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = 1 ∧ ∃ h, NPts k h ∧ (proto E).inv (upd G' 1 (gA (.wn k) h default)) m') G m d := by
  unfold Io_RwLock_lockUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [wsptr, wmptr]
  refine WP.bind (wp_rmw (W := WS) hi (wat (fun _ _ h => h.2.1.ws) (by simp [gA]))
    fun k₁ hk₁ G₁ m₁ m' old hg₁ hi₁ hv hU hh hacq hw' hop => ?_)
  have hu₁ := hi₁.2.1
  have hg1 : (G₁ 1).2.2 = .wo k := by rw [hg₁]; rfl
  have hold := sold hu₁ hv
  rw [hg1] at hold; simp only [Ph.wb, Ph.ib] at hold
  have hr := Ph.rb_le (G₁ 0).2.2
  -- `state += writer`
  have hi₂ : (proto E).inv (upd G₁ 1 (gA (.wa k .cas) Heap.empty default)) m' := by
    have hnp : (G₁ 0).2.2 ≠ .po := fun h => by obtain ⟨k', hk'⟩ := hu₁.flags.po h; rw [hg1] at hk'; cases hk'
    have hval : RmwOp.add.apply false old (2 : BitVec 64) = sv (G₁ 0).2.2 (.wa k .cas) := by
      rw [hold, sv3_add2 hr, sv_eq]; rfl
    refine inv_sstep hE hi₁ hg₁ hop hw' hh (by
        rw [upd1_0, upd_self]; show Word.Entry.Val _ (sv (G₁ 0).2.2 (.wa k .cas)); rw [← hval]
        exact rmwEnt_val WS) rfl rfl (fun h => by cases h)
      (by rfl) (by simp [Ph.isW]; omega) rfl (.inr (by simp [Ph.mp])) ?_ (by rfl) (fun hc => ?_)
      (lws_keep hi₁ hop hg₁ (by simp only [hasP, upd_self]; rfl) (by simp [hasP, hg1, Ph.isWs]))
    · rw [upd1_0, upd_self]
      exact ⟨(fun _ h => by cases h), (fun h => absurd h hnp), (fun h => by cases h.2), hu₁.flags.sr,
        fun h => by have := hu₁.flags.jd h; rw [hg1] at this; cases this⟩
    · simp only [upd1_0, upd_self] at hc ⊢
      obtain ⟨hn, hp, hs, hok⟩ := hu₁.car (by rw [hg1]; exact ⟨hc.1, rfl, by simpa [Ph.isWs] using hc.2.2⟩)
      rw [hg1] at hp
      exact ⟨hn, hp, car_rmw hp hs hok hu₁.ws hop hh⟩
  -- the mutex
  refine WP.bind (WP.callC (WP.mono ?_ (mlock_spec hE (t := 1) (x := .wa k .cas) rfl rfl hi₂)))
  rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hi₃⟩
  -- `state += is_writing -% writer`
  refine WP.bind (wp_rmw (W := WS) hi₃ (wat (fun _ _ h => h.2.1.ws) (by simp [gA]))
    fun k₃ hk₃ G₃ m₃ m₄ old' hg₃ hi₄ hv' hU' hh' hacq' hw₄ hop₄ => ?_)
  have hu₄ := hi₄.2.1
  have hg3 : (G₃ 1).2.2 = .wa k .holds := by rw [hg₃]; rfl
  have hold' := sold hu₄ hv'
  rw [hg3] at hold'; simp only [Ph.wb, Ph.ib] at hold'
  have hr' := Ph.rb_le (G₃ 0).2.2
  obtain ⟨hdec, htest⟩ := sv3_dec hr'
  obtain ⟨-, f2, f3, f4, f5⟩ := hu₄.flags
  rw [hg3] at f3 f2 f5
  have hm0 : (G₃ 0).2.2.mp ≠ some .holds := fun h => f3 ⟨h, rfl⟩
  have hnp : (G₃ 0).2.2 ≠ .po := fun h => by obtain ⟨k', hk'⟩ := f2 h; cases hk'
  have he : ∀ y : Ph, y.wb = 0 → y.ib = 1 →
      (Word.rmwEnt m₄ 1 .seqCst (last (WS.hist m₃)) (RmwOp.add.apply false old' 18446744073709551615)).Val
        (sv (upd G₃ 1 (gA y Heap.empty default) 0).2.2 (upd G₃ 1 (gA y Heap.empty default) 1).2.2) := by
    intro y h1 h2
    rw [upd1_0, upd_self]
    show Word.Entry.Val _ (sv (G₃ 0).2.2 y)
    rw [sv_eq, h1, h2, ← hdec, ← hold']; exact rmwEnt_val WS
  rcases (by omega : (G₃ 0).2.2.rb = 0 ∨ (G₃ 0).2.2.rb = 1) with hr0 | hr1
  · -- no reader: the writer takes `n` from the state word
    have hM : (G₃ 0).2.2.isMain := by
      obtain ⟨-, ⟨-, -, hn1⟩ | ⟨-, -, hM, -, -⟩⟩ := hu₄.shape
      · exfalso; have := hn1 1 (Nat.le_refl _); change (G₃ 1).2.2 = _ at this; rw [hg3] at this
        cases this
      · exact hM
    have hm0' : (G₃ 0).2.2.mustN = false := by
      cases e : (G₃ 0).2.2 <;> rw [e] at hr0 hnp hM <;> simp_all [Ph.rb, Ph.mustN, Ph.isMain]
    have hc : Car (G₃ 0).2.2 (G₃ 1).2.2 := ⟨hm0', by rw [hg3]; rfl, by rw [hg3]; rfl⟩
    obtain ⟨hn, hpn, hsn, hokn⟩ := hu₄.car hc
    rw [hg3] at hpn
    have htl : 1 < m₃.threads.size := (hi₄.1.live 1 (by rw [hg₃]; exact (by decide : LPh.out ≠ LPh.gone))).1
    have ho := own_rmw hpn hokn hu₄.ws hop₄ htl (hacq' rfl)
    have hsn' := (car_rmw hpn hsn hokn hu₄.ws hop₄ hh').1
    have hi₅ : (proto E).inv (upd G₃ 1 (gA (.wn k) hn default)) m₄ :=
      inv_sstep hE hi₄ hg₃ hop₄ hw₄ hh' (by
          rw [upd1_0, upd_self]
          show Word.Entry.Val _ (sv (G₃ 0).2.2 (.wn k))
          rw [sv_eq]; show Word.Entry.Val _ (sv3 0 1 _); rw [← hdec, ← hold']; exact rmwEnt_val WS)
        rfl rfl (fun h => by cases h) rfl (by simp [Ph.isW, Ph.setM]; omega) rfl (.inl rfl)
        (by
          rw [upd1_0, upd_self]
          exact ⟨(fun _ h => by cases h), (fun h => absurd h hnp), (fun h => hm0 h.1), f4,
            fun h => by have := f5 h; cases this⟩)
        (by rw [upd_self]; exact hpn)
        (fun hc' => absurd hc'.2.1 (by rw [upd_self]; simp [gA, Ph.mustN]))
        (lws_gain hi₄ hop₄ hg₃ hc hpn hsn' ho (by simp [hasP, upd_self, upd1_0, gA, Ph.isWs]))
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [hold', htest]
    simp only [hr0, show ((0 : Nat) = 1) = False from by decide, decide_false, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure]
    exact WP.pure' (WP.pure' ⟨by omega, hop₄.current, hn, hpn, hi₅⟩)
  · -- a reader: the writer waits at the semaphore
    have hms : (G₃ 0).2.2.pw ∧ (G₃ 0).2.2.mustN ∧ (G₃ 0).2.2.gave = false := by
      cases e : (G₃ 0).2.2 <;> rw [e] at hr1 <;> simp [Ph.rb] at hr1 <;>
        simp [Ph.pw, Ph.mustN, Ph.gave]
      rename_i j p
      rcases f4 j p e with rfl | rfl <;> simp_all [Ph.mp]
    have hi₅ : (proto E).inv (upd G₃ 1 (gA (.ws k) Heap.empty default)) m₄ :=
      inv_sstep hE hi₄ hg₃ hop₄ hw₄ hh' (he (.ws k) rfl rfl) rfl rfl (fun h => by cases h) rfl rfl rfl
        (.inl rfl) (by
          rw [upd1_0, upd_self]
          exact ⟨fun _ _ => .inl hms.1, fun h => absurd h hnp, fun h => hm0 h.1, f4,
            fun h => by have := f5 h; cases this⟩) (by rfl)
        (fun hc => absurd hc.1 (by rw [upd1_0]; simp [hms.2.1]))
        (lws_keep hi₄ hop₄ hg₃
          (by simp only [hasP, upd_self, upd1_0]; simp [hms.2.2])
          (by simp [hasP, hg3, Ph.isWs]))
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [hold', htest]
    simp only [hr1, decide_true, ↓reduceIte, StateT.run_bind]
    rw [semptr]
    refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (hE.wait k G₃ m₄ k₃ io hi₅ hop₄.current))))
    rintro _ G₄ m₅ d₄ ⟨hd₄, hc₅, h, hnk, hi₆⟩
    simp only [StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' (WP.pure' ⟨by omega, hc₅, h, hnk, hi₆⟩))

/-- Only one thread owns `n`. -/
theorem not_both {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (h0 : (G 0).2.2.mustN) (h1 : (G 1).2.2.mustN) : False := by
  have hu := hi.2.1
  have hj : ∀ u, (G u).2.2.mustN → (G u).2.2.inSem = false → joinedB m u = false := fun u hm hns => by
    have hlv : (G u).2.2.live := by cases e : (G u).2.2 <;> simp_all [Ph.mustN, Ph.live]
    refine (hi.1.live u ?_).2
    rcases hu.lph u hns with h | h | ⟨-, h⟩
    · show (G u).1.ph ≠ _; rw [h]; decide
    · show (G u).1.ph ≠ _; rw [h]; decide
    · rw [hlv] at h; cases h
  have hW : (G 1).2.2.isW := by
    obtain ⟨-, ⟨-, -, hn⟩ | ⟨-, -, -, hW, -⟩⟩ := hu.shape
    · have := hn 1 (Nat.le_refl _); change (G 1).2.2 = _ at this; rw [this] at h1; cases h1
    · exact hW
  have hn0 : (G 0).2.2.inSem = false := by
    cases e : (G 0).2.2 <;> simp_all [Ph.mustN, Ph.inSem]
    obtain ⟨k, hk⟩ := hu.flags.po e; rw [hk] at h1; cases h1
  have hn1 : (G 1).2.2.inSem = false := by cases e : (G 1).2.2 <;> simp_all [Ph.mustN, Ph.inSem, Ph.isW]
  have a := hu.parts 0; simp only [h0, ↓reduceIte] at a
  have b := hu.parts 1; simp only [h1, ↓reduceIte] at b
  have hd := hi.1.own.disj 0 1 (by decide)
  rw [Lock.own_live (hj 0 h0 hn0), Lock.own_live (hj 1 h1 hn1)] at hd
  exact npts_meet a b (Heap.disjoint_union_right.mp (Heap.disjoint_union_left.mp hd).1).1

/-- `unlock` of the `RwLock` by the writer at `wn k`, which owns `n` (`hn`): it gives `n` to the
state word. -/
theorem wunlock_spec (hE : E.Spec) {k : Nat} {hn : Heap} (hp : NPts k hn) {io : Io}
    {G : ThreadId → Gh S} {m : Mem} {d : Nat} (hi : (proto E).inv (upd G 1 (gA (.wn k) hn default)) m) :
    (proto E).WP 1 (Io_RwLock_unlock (bPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = 1 ∧ (proto E).inv (upd G' 1 (gA (.wo k) Heap.empty default)) m') G m d := by
  unfold Io_RwLock_unlock
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [wsptr, wmptr]
  refine WP.bind (wp_rmw (W := WS) hi (wat (fun _ _ h => h.2.1.ws) (by simp [gA]))
    fun k₁ hk₁ G₁ m₁ m' old hg₁ hi₁ hv hU hh hacq hw' hop => ?_)
  have hu₁ := hi₁.2.1
  have hg1 : (G₁ 1).2.2 = .wn k := by rw [hg₁]; rfl
  have hold := sold hu₁ hv
  rw [hg1] at hold; simp only [Ph.wb, Ph.ib] at hold
  have hr := Ph.rb_le (G₁ 0).2.2
  have hm0 : (G₁ 0).2.2.mustN = false :=
    Bool.eq_false_iff.mpr fun h => not_both hi₁ h (by rw [hg1]; rfl)
  obtain ⟨-, f2, f3, f4, f5⟩ := hu₁.flags
  rw [hg1] at f3 f2 f5
  have hnp : (G₁ 0).2.2 ≠ .po := fun h => by obtain ⟨k', hk'⟩ := f2 h; cases hk'
  -- `n` from the writer's part
  have htl : 1 < m₁.threads.size := (hi₁.1.live 1 (by rw [hg₁]; exact (by decide : LPh.out ≠ LPh.gone))).1
  have hj1 : joinedB m₁ 1 = false := (hi₁.1.live 1 (by rw [hg₁]; exact (by decide : LPh.out ≠ LPh.gone))).2
  have hown := hi₁.1.own.owns 1 htl
  have hsub := hi₁.1.own.sub 1
  rw [Lock.own_live hj1, hg₁] at hown hsub
  have hcl := car_lose hu₁.ws hown.left (fun l c h => hsub l c (Heap.sub_union_left l c h)) hp hop hh
  have hi₂ : (proto E).inv (upd G₁ 1 (gA (.wr k .holds) Heap.empty default)) m' :=
    inv_sstep hE hi₁ hg₁ hop hw' hh (by
        rw [upd1_0, upd_self]
        show Word.Entry.Val _ (sv (G₁ 0).2.2 (.wr k .holds))
        rw [sv_eq]; show Word.Entry.Val _ (sv3 0 0 _); rw [← sv3_and hr, ← hold]; exact rmwEnt_val WS)
      rfl rfl (fun h => by cases h) rfl rfl rfl (.inl rfl)
      (by
        rw [upd1_0, upd_self]
        exact ⟨(fun _ h => by cases h), (fun h => absurd h hnp), (fun h => f3 ⟨h.1, rfl⟩), f4,
          fun h => by have := f5 h; cases this⟩)
      (by rfl) (fun _ => ⟨hn, by rw [upd_self]; exact hp, hcl⟩)
      (lws_lose hi₁ hop hg₁ (by simp [hasP, upd_self, gA, Ph.isWs]) (by simp [hasP, hg1, Ph.isWs]))
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (munlock_spec hE (t := 1) (x := .wr k .holds)
    (.inr ⟨rfl, k, .holds, by rw [upd_self]; rfl⟩) rfl hi₂)))
  rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hi₃⟩
  exact WP.pure' (WP.pure' ⟨by omega, hc₂, hi₃⟩)

/-! ## Plain accesses: `io`, and `n` by its owner -/

theorem noRace_io {m : Mem} (hio : IoOk m) (ht : m.current < m.threads.size) :
    NoRace m 0 0 16 .read :=
  noRace_of fun e he hb _ h2 => by
    rcases hio e he hb (by omega) with h | h
    · exact .inr (by rw [h]; rfl)
    · exact .inl (h _ ht)

/-- A read of `io` (bytes 0..16): no race, and the invariant holds after it. -/
theorem step_io (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (ht : m.current < m.threads.size) :
    (load Io 8 bPtr).run m = pure (⟨⟩, m.recordAt 0 0 16 .read) ∧
      (proto E).inv G (m.recordAt 0 0 16 .read) := by
  obtain ⟨hl, hu, he⟩ := hi
  obtain ⟨blk, hblk, hlv, hsz, ha, hk⟩ := hu.blk
  have hb0 := (Array.getElem?_eq_some_iff.mp hblk).1
  have hacc : m.access bPtr (Enc.size Io) 8 = pure (0, blk, 0) :=
    access_of (p := bPtr) rfl hblk hlv (by decide)
      (by rw [show Enc.size Io = 16 from rfl]; simp [bPtr, hsz]) (by simpa [bPtr] using ha)
  have hk' : ∀ {n nb : Nat} (W : Word n nb), 16 ≤ W.o → W.Keep m (m.recordAt 0 0 16 .read) :=
    fun _ h => Word.keep_read m (by decide) (.inr (.inl h))
  have hcl := recordAt_le m 0 0 16 .read
  refine ⟨load_run hacc rfl (noRace_io hu.io ht), hl.read (b := 0) (o := 0) (n := 16) hb0 (by decide)
      (fun u x _ hx => own_none ⟨hl, hu, he⟩ u (.inl (by omega)))
      (fun hL hR x _ hx => R_none hR (.inl (by omega))) (.inr (.inl (by simp [L, Lock.prod]))),
    U_keep hu (hk' WS (by decide)) (hk' WM (by decide)) rfl (fun w hw _ => hw) (fun e he' hb ho => ?_)
      (blk_keep hu.blk rfl) (fun e he' => ?_) (by simp [Mem.recordAt]) (fun _ _ _ => rfl) hcl,
    hE.frame G G m _ he ⟨fun W _ h1 _ => hk' W (by omega), rfl, fun _ _ => Iff.rfl, hcl⟩ (econd0 hu)⟩
  · simp only [Mem.recordAt, Array.mem_push] at he'
    rcases he' with he' | rfl
    · rcases hu.io e he' hb ho with h | h
      · exact .inl h
      · exact .inr fun u hu => VClock.le_trans (h u hu) (hcl u)
    · exact .inl rfl
  · simp only [Mem.recordAt, Array.mem_push] at he'
    rcases he' with he' | rfl
    · exact .inl he'
    · exact .inr ⟨.inr (.inl ⟨by simp, by simp⟩), hb0⟩

/-- A read of `io` by thread `t` in generated code. -/
theorem wp_io (hE : E.Spec) {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh S} {m : Mem}
    {d : Nat} {g : Gh S} (hi : (proto E).inv (upd G t g) m) (hc : m.current = t)
    (ht : t < m.threads.size) {Q : Io × σ → (ThreadId → Gh S) → Mem → Nat → Prop}
    (h : ∀ m', m'.current = t → m'.threads = m.threads → (proto E).inv (upd G t g) m' →
      Q (⟨⟩, s) G m' d) :
    (proto E).WP t ((liftM (load Io 8 bPtr) : CM Tgt σ Io).run s) Q G m d := by
  obtain ⟨hrun, hi'⟩ := step_io hE hi (hc ▸ ht)
  refine WP.liftM (fun e he => (MemM.noErr_of_run hrun e he).elim) fun v m' hr => ?_
  rw [hrun] at hr
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  cases v
  exact ⟨rfl, h _ hc rfl hi'⟩

/-- The bytes of block 0 out of `n` are in the heap out of `n`'s part. -/
theorem diff_n {m : Mem} {h : Heap} {k : Nat} (hb : BlkOk m) (hp : NPts k h) {x : Nat}
    (hx : x < 56 ∨ (60 ≤ x ∧ x < 64)) : m.heap.diff h (0, x) ≠ none := by
  have : h (0, x) = none := npts_none hp (by simp only; omega)
  simp only [Heap.diff, this, ↓reduceIte]; exact blk_heap hb (by omega)

/-- `main` or the writer owns `n`. -/
theorem mustN_lt {G : ThreadId → Gh S} {m : Mem} (hu : U G m) {u : ThreadId}
    (h : (G u).2.2.mustN) : u = 0 ∨ u = 1 := by
  obtain ⟨-, ⟨-, -, hn⟩ | ⟨-, -, -, -, hn⟩⟩ := hu.shape
  · rcases Nat.eq_zero_or_pos u with e | e
    · exact .inl e
    · have := hn u e; change (G u).2.2 = _ at this; rw [this] at h; cases h
  · rcases Nat.lt_or_ge u 2 with e | e
    · unfold ThreadId at *; omega
    · have := hn u e; change (G u).2.2 = _ at this; rw [this] at h; cases h

/-- The thread other than the owner of `n` does not own it. -/
theorem other_nN {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m) {t u : ThreadId}
    (ht : (G t).2.2.mustN) (hut : u ≠ t) : (G u).2.2.mustN = false := by
  refine Bool.eq_false_iff.mpr fun hu => ?_
  rcases mustN_lt hi.2.1 ht with rfl | rfl <;> rcases mustN_lt hi.2.1 hu with rfl | rfl
  · exact hut rfl
  · exact not_both hi ht hu
  · exact not_both hi hu ht
  · exact hut rfl

theorem mustN_noP {x : Ph} (h : x.mustN) : x.isWs = false ∧ x.gave = false := by
  cases x <;> simp_all [Ph.mustN, Ph.isWs, Ph.gave]

/-- The load or the store of `n` by thread `t` at `x`, which owns it (`h`); after it, `t` is at
`y`: the same place, or the writer after its increment. -/
theorem wp_n (hE : E.Spec) {σ β : Type} {c : MemM β} {s : σ} {t : ThreadId} {G : ThreadId → Gh S}
    {m : Mem} {d : Nat} {x y : Ph} {h : Heap} {sx : S} {r₀ : β}
    {Q : β × σ → (ThreadId → Gh S) → Mem → Nat → Prop}
    (hi : (proto E).inv (upd G t (gA x h sx)) m) (hc : m.current = t) (hxm : x.mustN)
    (hy : y = x ∨ ∃ k, x = .wn k ∧ y = .wn (k + 1) ∧ k + 1 ≤ 2)
    (ht : TTriple (NPts (upd G t (gA x h sx) 1).2.2.cnt) c
      (fun r => ⌜r = r₀⌝ ∗ NPts (upd G t (gA y h sx) 1).2.2.cnt))
    (hq : ∀ m' h', m'.current = t → m'.threads = m.threads →
      (proto E).inv (upd G t (gA y h' sx)) m' → Q (r₀, s) G m' d) :
    (proto E).WP t ((liftM c : CM Tgt σ β).run s) Q G m d := by
  obtain ⟨hl, hu, hE₀⟩ := hi
  have hi : (proto E).inv (upd G t (gA x h sx)) m := ⟨hl, hu, hE₀⟩
  have hgt : (upd G t (gA x h sx) t).2.2 = x := by rw [upd_self]; rfl
  have hxm' : (upd G t (gA x h sx) t).2.2.mustN := by rw [hgt]; exact hxm
  have ht01 := mustN_lt hu hxm'
  obtain ⟨htl, hjt⟩ := hl.live t (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))
  have hown : (L S).own (upd G t (gA x h sx)) m t = h := by
    rw [Lock.own_live hjt, upd_self]; exact Heap.union_empty h
  have hpart : NPts (upd G t (gA x h sx) 1).2.2.cnt h := by
    have := hu.parts t; rw [upd_self] at this; simp only [gA, hxm, ↓reduceIte] at this; exact this
  -- the facts of `y`
  have hyx : y.wb = x.wb ∧ y.ib = x.ib ∧ y.rb = x.rb ∧ y.isWs = x.isWs ∧ y.gave = x.gave ∧
      y.mustN = x.mustN ∧ y.isMain = x.isMain ∧ y.inSem = x.inSem ∧ y.live = x.live ∧
      y.mp = x.mp ∧ (x.isW → y.isW) := by
    rcases hy with rfl | ⟨k, rfl, rfl, hk⟩
    · simp
    · simp [Ph.wb, Ph.ib, Ph.rb, Ph.isWs, Ph.gave, Ph.mustN, Ph.isMain, Ph.inSem, Ph.live, Ph.mp,
        Ph.isW]; omega
  obtain ⟨hwb, hib, hrb, hiw, hgv, hmu, hM, hns, hlv, hmp, hW⟩ := hyx
  refine WP.liftM_owned ht hl.own hc htl (by rw [hown]; exact hpart)
    fun a m' hQ _ ho' hq' hst hm' hd => ?_
  obtain ⟨rfl, hpQ⟩ := sep_lift.mp hq'
  rw [hown] at hst hm' hd
  let G₀ := upd G t (gA x h sx)
  let g' : Gh S := gA y hQ sx
  have hG : upd G₀ t g' = upd G t g' := upd_upd _ _ _ _
  have hcnt : (upd G t (gA y h sx) 1).2.2.cnt = (upd G₀ t g' 1).2.2.cnt := by
    rw [hG]; unfold upd; split <;> rfl
  rw [hcnt] at hpQ
  have hf : ∀ {β : Type} (f : Ph → β), f y = f x → ∀ u, f (upd G₀ t g' u).2.2 = f (G₀ u).2.2 :=
    fun f hfx u => by
      unfold upd; split
      · rename_i e; subst e; show f y = f (upd G _ (gA x h sx) _).2.2; rw [upd_self]; exact hfx
      · rfl
  have hnoP : ∀ (G' : ThreadId → Gh S) (z : Ph) (hz : Heap), z.mustN →
      hasP (fun u => (upd G' t (gA z hz sx) u).2.2) = false := fun G' z hz h => by
    have := mustN_noP h
    rcases ht01 with rfl | rfl <;> simp [hasP, upd_self, upd1_0, upd0_1, gA, this]
  have hl' := hl.stepIn (g := g') hc hjt
    (by show Owned (upd _ t (hQ ∪ Heap.empty)) m'; rw [Heap.union_empty]; exact ho')
    (by rw [hown]; exact hst)
    (by rw [hown]; show m'.heap = (hQ ∪ Heap.empty) ∪ _; rw [Heap.union_empty]; exact hm')
    (by rw [hown]; show Heap.Disjoint (hQ ∪ Heap.empty) _; rw [Heap.union_empty]; exact hd)
    (by rw [upd_self]; rfl) (Heap.disjoint_empty _) (fun _ => rfl)
    (fun _ hL hR => (R_nohas (hnoP G₀ y hQ (by rw [hmu]; exact hxm)) (hnoP G x h hxm) hL).mpr hR)
    (fun h₀ => by cases h₀)
  have hkW : ∀ {n nb : Nat} (W : Word n nb), W.b = 0 → W.o + nb ≤ 56 → W.Keep m m' :=
    fun W hb ho => Word.keep_stepIn_of (fun x h1 h2 => by
      rw [hb]; exact diff_n hu.blk hpart (.inl (by omega))) hst hm' hd
  have hkS := hkW WS rfl (by decide)
  have hkM := hkW WM rfl (by decide)
  have hnone : ∀ x, ¬ (56 ≤ x ∧ x < 60) → x < 64 → m'.heap (0, x) = m.heap (0, x) := fun x hx _ => by
    rw [hm', Heap.union_apply, npts_none hpQ (by simp only; omega), Option.none_or]
    simp [Heap.diff, npts_none hpart (show ¬ ((0, x).1 = 0 ∧ 56 ≤ (0, x).2 ∧ (0, x).2 < 60) by
      simp only; omega)]
  obtain ⟨hml, hmq⟩ := mfacts (g' := g') hu hkM hst.waiters (.inl (by rw [upd_self]; exact hmp))
  have hY : (G₀ t).2.2.isMain ∨ ((G₀ t).2.2.isW ∧ (G₀ t).2.2 ≠ .wf) := by
    obtain ⟨-, ⟨-, hp, hn⟩ | ⟨-, -, hM0, hW0, -⟩⟩ := hu.shape
    · exfalso; rcases ht01 with e | e <;> subst e
      · change (G₀ 0).2.2 = _ at hp; rw [hgt] at hp; subst hp; cases hxm
      · have := hn 1 (Nat.le_refl _); change (G₀ 1).2.2 = _ at this; rw [this] at hxm'; cases hxm'
    · rcases ht01 with e | e <;> subst e
      · exact .inl hM0
      · exact .inr ⟨hW0, fun e => by rw [e] at hxm'; cases hxm'⟩
  have hU : U (upd G t g') m' := by
    rw [← hG]
    refine ⟨?_, ?_, fun e he hb ho => ?_, blk_keep hu.blk (hnone 0 (by omega) (by omega)),
      hu.ws.keep hkS, hu.wm.keep hkM, by rw [Word.hist_keep hu.ws hkS]; exact hu.shist,
      (by rw [Word.hist_keep hu.ws hkS, sv_eq, hf Ph.wb hwb, hf Ph.ib hib, hf Ph.rb hrb, ← sv_eq]; exact hu.slast),
      by rw [Word.hist_keep hu.wm hkM]; exact hu.mhist, hml, hmq, fun u hu' => ?_, fun u => ?_,
      fun hc' => ?_⟩
    · rw [ph_upd]
      have := shape_upd hu.shape hY (y := g'.2.2) (by rw [hgt]; show _ → y.isMain; rw [hM]; exact id)
        (by rw [hgt]; exact hW)
      unfold Shape at this ⊢; rw [hst.threads]; exact this
    · rcases hy with rfl | ⟨k, rfl, rfl, -⟩
      · have e : ∀ u, (upd G₀ t g' u).2.2 = (G₀ u).2.2 := fun u => by
          unfold upd; split
          · rename_i e; subst e; show _ = (upd G _ _ _).2.2; rw [upd_self]; rfl
          · rfl
        rw [e, e]; exact hu.flags
      · obtain ⟨-, f2, f3, f4, f5⟩ := hu.flags
        rcases ht01 with e | e <;> subst e
        · exfalso; obtain ⟨-, ⟨-, hp, -⟩ | ⟨-, -, hM0, -, -⟩⟩ := hu.shape
          · change (G₀ 0).2.2 = _ at hp; rw [hgt] at hp; cases hp
          · change (G₀ 0).2.2.isMain at hM0; rw [hgt] at hM0; cases hM0
        · rw [upd1_0, upd_self]
          change Flags (G₀ 0).2.2 (.wn (k + 1))
          rw [hgt] at f2 f3 f5
          exact ⟨(fun _ h => by cases h), (fun h => by obtain ⟨_, h'⟩ := f2 h; cases h'),
            (fun h => f3 ⟨h.1, rfl⟩), f4, fun h => by have := f5 h; cases this⟩
    · rcases hst.fp e he with h' | ⟨-, hnt, -⟩
      · rcases hu.io e h' hb ho with h'' | h''
        · exact .inl h''
        · exact .inr (allLe_stepIn hst h'')
      · exact absurd ⟨e.off, Nat.le_refl _, .inr rfl, by
          rw [hb]; exact diff_n hu.blk hpart (.inl (by omega))⟩ hnt
    · by_cases e : u = t
      · subst e; rw [upd_self]; exact .inl rfl
      · rw [upd_ne _ _ e] at hu' ⊢; exact hu.lph u hu'
    · by_cases e : u = t
      · subst e; rw [upd_self]; simp only [g', gA, hmu, hxm, ↓reduceIte]; exact hpQ
      · rw [upd_ne _ _ e]
        have h₁ := other_nN hi hxm' e
        have := hu.parts u; rw [h₁] at this ⊢; exact this
    · exfalso
      rcases ht01 with e | e <;> subst e
      · have := hc'.1; rw [upd_self] at this; simp [g', gA, hmu, hxm] at this
      · have := hc'.2.1; rw [upd_self] at this; simp [g', gA, hmu, hxm] at this
  have hE' : E.inv (upd G t g') m' := by
    rw [← hG]
    exact hE.frame G₀ _ m m' hE₀ ⟨fun W hb h1 h2 => hkW W hb (by omega), by rw [hst.threads],
      fun _ _ => by rw [hst.waiters], hst.clock⟩
      (econd hu (by show _ = (upd G t (gA x h sx) t).2.1; rw [upd_self]; rfl)
        (by show _ = (upd G t (gA x h sx) t).1.held; rw [upd_self]; rfl)
        (fun x _ h2 => npts_none hpQ (by simp only; omega))
        (.inl (by show _ = (upd G t (gA x h sx) t).1.ph; rw [upd_self]; rfl)))
  rw [upd_upd] at hl'
  exact hq m' hQ (hst.current.trans hc) hst.threads ⟨hl', hU, hE'⟩

/-- The invariant with another running thread. -/
theorem inv_cur (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (c : ThreadId) : (proto E).inv G { m with current := c } :=
  ⟨hi.1.current c, U_q hi.2.1 rfl fun w hw hp => hi.2.1.mq w hw hp,
    hE.frame G G m _ hi.2.2 ⟨fun _ _ _ _ => Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _,
      rfl, fun _ _ => Iff.rfl, fun _ => VClock.le_refl _⟩ (econd0 hi.2.1)⟩

/-! ## The writer -/

/-- The writer's loop invariant: it did `local1` increments, out of the lock. -/
def wInv (s : writerLocals) (G : ThreadId → Gh S) (m : Mem) (_ : Nat) : Prop :=
  m.current = 1 ∧ s.local1.toNat ≤ 2 ∧
    (proto E).inv (upd G 1 (gA (.wo s.local1.toNat) Heap.empty default)) m

/-- The writer's loop: 2 increments. -/
def wPost (r : writerExit × writerLocals) (G : ThreadId → Gh S) (m : Mem) (_ : Nat) : Prop :=
  r.1 = .br3 ∧ m.current = 1 ∧ (proto E).inv (upd G 1 (gA (.wo 2) Heap.empty default)) m

theorem wloop_body (hE : E.Spec) (s : writerLocals) (G : ThreadId → Gh S) (m : Mem) (d : Nat)
    (h : wInv (E := E) s G m d) :
    (proto E).WP 1 ((writer.loop4 bPtr).run s) (fun r G' m' d' =>
      if writer.again4 r.1 then wInv (E := E) r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : writerLocals) => 0) s)
      else wPost (E := E) r G' m' d') G m d := by
  obtain ⟨hc, hle, hi⟩ := h
  unfold writer.loop4
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have htl : 1 < m.threads.size :=
    (hi.1.live 1 (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))).1
  split
  · rename_i hlt
    have hlt' : s.local1.toNat < 2 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc]
    rw [show bPtr.add 0 = bPtr from rfl]
    -- `io`, the lock
    refine WP.bind (wp_io hE hi hc htl fun m₁ hc₁ ht₁ hi₁ => ?_)
    refine WP.bind (WP.callC (WP.mono ?_ (wlock_spec hE hlt' hi₁)))
    rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, h, -, hi₂⟩
    rw [show bPtr.add 56 = nPtr from rfl]
    -- the load of `n`
    have hk2 : ∀ h' : Heap, (upd G₂ 1 (gA (.wn s.local1.toNat) h' default) 1).2.2.cnt =
        s.local1.toNat := fun _ => by rw [upd_self]; rfl
    refine WP.bind (wp_n hE (y := .wn _) hi₂ hc₂ rfl (.inl rfl) (TTriple.load (by decide))
      fun m₃ h₃ hc₃ ht₃ hi₃ => ?_)
    rw [hk2]
    have hS32 : (BitVec.ofNat 32 s.local1.toNat).toNat = s.local1.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    -- the add, the store
    refine WP.bind (WP.callRC (fun e he => (add_one_noErr (by rw [hS32]; omega) e he).elim)
      fun v₃ hadd => ?_)
    have hv₃ := add_one_ok hadd (by rw [hS32]; omega)
    rw [hS32] at hv₃
    have hv : v₃ = BitVec.ofNat 32 (upd G₂ 1 (gA (.wn (s.local1.toNat + 1)) h₃ default) 1).2.2.cnt := by
      rw [upd_self]; apply BitVec.eq_of_toNat_eq
      show v₃.toNat = (BitVec.ofNat 32 (s.local1.toNat + 1)).toNat
      rw [hv₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine WP.bind (wp_n hE (r₀ := ()) (y := .wn (s.local1.toNat + 1)) hi₃ hc₃ rfl
      (.inr ⟨_, rfl, rfl, by omega⟩) (TTriple.conseq (TTriple.store (by decide) v₃) (fun _ h => h)
        fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, by rw [hv] at hq; exact hq⟩) fun m₄ h₄ hc₄ ht₄ hi₄ => ?_)
    have hp₄ : NPts (s.local1.toNat + 1) h₄ := by
      have := hi₄.2.1.parts 1; rw [upd_self] at this; simpa [gA, Ph.mustN, Ph.cnt] using this
    -- `io`, the unlock
    have htl₄ : 1 < m₄.threads.size :=
      (hi₄.1.live 1 (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))).1
    refine WP.bind (wp_io hE hi₄ hc₄ htl₄ fun m₅ hc₅ ht₅ hi₅ => ?_)
    refine WP.bind (WP.callC (WP.mono ?_ (wunlock_spec hE hp₄ hi₅)))
    rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
    simp only [StateT.run_pure, pure_bind, StateT.run_bind]
    -- the next repeat
    refine WP.bind (WP.callRC (fun e he =>
      (add_one_noErr (a := s.local1) (by have := s.local1.isLt; omega) e he).elim) fun i24 hadd' => ?_)
    have h24 := add_one_ok (a := s.local1) hadd' (by have := s.local1.isLt; omega)
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [writer.again4, ↓reduceIte]
    exact ⟨⟨hc₆, by simp only; omega, by simp only; rw [h24]; exact hi₆⟩, .inl (by omega)⟩
  · rename_i hge
    have heq : s.local1.toNat = 2 := by
      have : ¬ s.local1.toNat < 2 := by simpa [lt, BitVec.ult] using hge
      omega
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [writer.again4, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc, heq ▸ hi⟩

theorem writer_spec (hE : E.Spec) (G : ThreadId → Gh S) (m : Mem) (d : Nat)
    (hi : (proto E).inv (upd G 1 (gA (.wo 0) Heap.empty default)) m) (hc : m.current = 1) :
    (proto E).WP 1 (writer bPtr) (fun _ G' m' _ => m'.current = 1 ∧
      (proto E).inv (upd G' 1 (gA (.wo 2) Heap.empty default)) m') G m d := by
  unfold writer
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (wInv (E := E)) (fun _ => 0) (wPost (E := E))
    (wloop_body hE) _ G m d ⟨hc, by decide, by simpa using hi⟩))
  rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hc', hi'⟩
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  exact WP.pure' ⟨hc', hi'⟩

/-- The writer's end: `gone`, at `wf`. -/
theorem inv_wend (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem}
    (hi : (proto E).inv (upd G 1 (gA (.wo 2) Heap.empty default)) m) :
    (proto E).inv (upd G 1 (⟨.gone, Heap.empty, Heap.empty⟩, (default, .wf))) m := by
  obtain ⟨hl, hu, he⟩ := hi
  let g : Gh S := (⟨.gone, Heap.empty, Heap.empty⟩, (default, .wf))
  have hR := R_upd (G := upd G 1 (gA (.wo 2) Heap.empty default)) (t := 1) (g' := g)
    (by rw [upd_self]; rfl) (by rw [upd_self]; rfl) (by rw [upd_self]; rfl)
  have hl' := hl.ghost (t := 1) (g := g) (by rw [upd_self]; rfl) (.inr (.inl rfl))
    (by rw [upd_self]; rfl) rfl (fun h => absurd rfl h) (fun hL h => (hR hL).mpr h)
  rw [upd_upd] at hl'
  have hY : (fun u => (upd G 1 g u).2.2) =
      upd (fun u => (upd G 1 (gA (.wo 2) Heap.empty default) u).2.2) 1 .wf := by
    funext u
    by_cases e : u = 1
    · subst e; rw [upd_self, upd_self]
    · rw [upd_ne _ _ e, upd_ne _ _ e]; show _ = (upd G 1 _ u).2.2; rw [upd_ne _ _ e]
  have hf := hu.flags
  rw [upd1_0, upd_self] at hf
  have hU : U (upd G 1 g) m := by
    have := U_ghost (G' := upd G 1 g) hu (by
        rw [hY]
        exact shape_upd hu.shape (.inr ⟨by rw [upd_self]; rfl, by rw [upd_self]; simp [gA]⟩)
          (by rw [upd_self]; simp [gA, Ph.isMain]) (fun _ => rfl))
      (by
        rw [upd1_0, upd_self]
        exact ⟨(fun _ h => by cases h), (fun h => by obtain ⟨k, hk⟩ := hf.po h; cases hk),
          (fun h => by cases h.2), hf.sr, fun _ => rfl⟩)
      (by rw [upd1_0, upd1_0, upd_self, upd_self]; rfl)
      (fun u => by unfold upd; split <;> rfl)
      (fun u hu' => by
        by_cases e : u = 1
        · subst e; rw [upd_self]; exact .inr (.inr ⟨rfl, rfl⟩)
        · rw [upd_ne _ _ e] at hu' ⊢; have := hu.lph u; rw [upd_ne _ _ e] at this; exact this hu')
      (fun u => by
        by_cases e : u = 1
        · subst e; rw [upd_self]; rfl
        · rw [upd_ne _ _ e, upd_self]
          have := hu.parts u; rw [upd_ne _ _ e, upd_self] at this; exact this)
      (fun hc => by
        rw [upd1_0, upd_self] at hc; rw [upd_self]
        obtain ⟨hn, hp, hs, hok⟩ := hu.car (by rw [upd1_0, upd_self]; exact ⟨hc.1, rfl, rfl⟩)
        rw [upd_self] at hp
        exact ⟨hn, hp, hs, hok⟩)
    exact this
  have he' := hE.frame _ _ m m he (Frame.refl m) (econd hu (g' := g) (t := 1) (by rw [upd_self]; rfl)
    (by rw [upd_self]; rfl) (fun _ _ _ => rfl)
    (.inr ⟨by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.holds), (by decide : LPh.gone ≠ LPh.holds)⟩))
  rw [upd_upd] at he'
  exact ⟨hl', hU, he'⟩

/-- The writer spawned no thread. -/
theorem joinedAll_w {G : ThreadId → Gh S} {m : Mem} (hu : U G m) : joinedAll 1 m := by
  intro r hr hs
  obtain ⟨h0, h⟩ := hu.shape
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have h0' : ∀ h : 0 < m.threads.size, (m.threads[0]'h).spawner = 0 := by
    intro h; rw [Array.getElem?_eq_getElem h] at h0; rw [Option.some.inj h0]
  rcases h with ⟨h1, -, -⟩ | ⟨h2, h1, -⟩
  · have : i = 0 := by omega
    subst this
    rw [h0' hi'] at hs; exact absurd hs (by decide)
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0' hi'] at hs; exact absurd hs (by decide)
    · rcases h1 with h1 | ⟨h1, -⟩ <;>
        (rw [Array.getElem?_eq_getElem hi'] at h1; rw [Option.some.inj h1] at hs; exact absurd hs (by decide))

/-- The writer: its loop, then its end. -/
theorem dispatch_spec (hE : E.Spec) (tgt : Tgt) (g : Gh S) (hg : (proto E).init tgt g) (u : ThreadId)
    (G : ThreadId → Gh S) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : (proto E).inv G m) :
    (proto E).WP u (dispatch tgt) ((proto E).QKid u) G { m with current := u } d := by
  cases tgt with
  | writer p =>
    obtain ⟨rfl, rfl⟩ := hg
    have hu1 : u = 1 := by
      have hlv := (hi.1.live u (by rw [hgu]; exact (by decide : LPh.out ≠ LPh.gone))).1
      obtain ⟨-, ⟨h1, -, -⟩ | ⟨h2, -⟩⟩ := hi.2.1.shape <;> unfold ThreadId at * <;> omega
    subst hu1
    show (proto E).WP 1 ((fun _ => ()) <$> writer bPtr) _ G _ d
    refine WP.map (WP.mono ?_ (writer_spec hE G _ d
      (by rw [show gA (.wo 0) Heap.empty default = G 1 from hgu.symm, upd_same]
          exact inv_cur hE hi 1) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    exact ⟨_, inv_wend hE hi', ⟨rfl, rfl⟩, fun _ => joinedAll_w hi'.2.1⟩
  | producer p => cases hg
  | work p => cases hg
  | semWork p => cases hg

/-! ## `lockShared` -/

/-- A load or a failed `cmpxchg` of the state word: the same ghost values. -/
theorem inv_sread (hE : E.Spec) {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId}
    (hi : (proto E).inv G m) (hop : WS.Op t m m') (hw' : WS.Ok m') (hh : WS.hist m' = WS.hist m) :
    (proto E).inv G m' := by
  have hu := hi.2.1
  obtain ⟨hfp, hio⟩ := op_fp hop hu.ws (by decide) (by decide)
  have hkM := Word.keep_op hop (W' := WM) (.inr (.inl (by decide)))
  have hhM := Word.hist_keep hu.wm hkM
  refine ⟨hi.1.wordOp hu.ws hop apS (off_own hi rfl ws_free) (off_R rfl ws_free G),
    ⟨by unfold Shape at *; rw [hop.threads]; exact hu.shape, hu.flags, hio hu.io,
      blk_keep hu.blk (hop.cells _ (by simp [WS])), hw', hu.wm.keep hkM, by rw [hh]; exact hu.shist,
      by rw [hh]; exact hu.slast, by rw [hhM]; exact hu.mhist, by rw [hhM]; exact hu.mlast,
      fun w hw hp => ?_, hu.lph, hu.parts, fun hc => ?_⟩,
    hE.frame G G m m' hi.2.2 (frame_op hop (.inr (.inl (by decide)))) (econd0 hu)⟩
  · rw [hop.waiters] at hw; unfold MQ; rw [hhM]; exact hu.mq w hw hp
  · obtain ⟨hn, hp, hs, hok⟩ := hu.car hc
    exact ⟨hn, hp, car_keep hp hs hok (by rw [hh]; exact VClock.le_refl _) hfp
      (Nat.le_of_eq hop.bsize.symm) (fun x _ _ => hop.cells _ (by simp [WS]; omega))
      (fun _ h => hop.allLe h)⟩

/-- The writer's place, after `main`'s spawn. -/
theorem w_isW {G : ThreadId → Gh S} {m : Mem} (hu : U G m) (hm : (G 0).2.2 ≠ .pre) :
    (G 1).2.2.isW := by
  obtain ⟨-, ⟨-, hp, -⟩ | ⟨-, -, -, hW, -⟩⟩ := hu.shape
  · exact absurd hp hm
  · exact hW

/-- A writer without `is_writing`, or without the mutex, does not own `n` and does not wait. -/
theorem w_free {x : Ph} (hW : x.isW) (h : x.ib = 0 ∨ x.mp ≠ some .holds) :
    x.mustN = false ∧ x.isWs = false := by
  cases x <;> simp_all [Ph.isW, Ph.ib, Ph.mp, Ph.mustN, Ph.isWs]

/-- `main` goes to `lockShared`'s slow path: the mutex's first `cmpxchg`. -/
theorem inv_lsl (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} {j : Bool}
    (hi : (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m) :
    (proto E).inv (upd G 0 (gA (.sl j .cas) Heap.empty default)) m := by
  have hu := hi.2.1
  have hMS : MSet (upd G 0 (gA (.ls j) Heap.empty default)) 0 (.sl j .cas)
      (gA (.sl j .cas) Heap.empty default) := by
    refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩ <;> rw [upd_self]
    · rfl
    · rfl
    · simp [gA]
    · constructor <;> first | rfl | simp
    · rfl
    · rfl
    · rfl
  obtain ⟨hml, hmq⟩ := mfacts (g' := gA (.sl j .cas) Heap.empty default) hu
    (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _) rfl
    (.inr (by rw [upd_self]; simp [gA, Ph.mp]))
  have hf : Flags (.ls j) (G 1).2.2 := by have := hu.flags; rw [upd_self, upd0_1] at this; exact this
  have := inv_mghost hE hi hMS (by rw [upd_self]; rfl) hml hmq (by
    rw [upd_self, upd0_1]
    show Flags (.sl j .cas) (G 1).2.2
    exact ⟨(fun k hk => by have := hf.ws k hk; simp [Ph.pw, Ph.gave] at this),
      (fun h => by cases h), (fun h => by simp [Ph.mp] at h), (fun _ _ h => by cases h), hf.jd⟩)
  rwa [upd_upd] at this

variable (E) in
/-- `lockShared`'s loop invariant: `main` at `ls j`, with a value of the state word. -/
def lsInv (j : Bool) (D : Nat) (s : Io_RwLock_lockSharedUncancelableLocals) (G : ThreadId → Gh S)
    (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ m.current = 0 ∧ s.state ∈ sVals ∧
    (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m

variable (E) in
/-- `lockShared`'s loop ends: `main` holds the shared lock, or goes to the slow path. -/
def lsPost (j : Bool) (D : Nat)
    (r : Io_RwLock_lockSharedUncancelableExit × Io_RwLock_lockSharedUncancelableLocals)
    (G : ThreadId → Gh S) (m : Mem) (d : Nat) : Prop :=
  d ≤ D ∧ m.current = 0 ∧
    ((r.1 = .ret ∧ ∃ h, (proto E).inv (upd G 0 (gA (.sh j) h default)) m) ∨
      (r.1 = .br7 ∧ (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m))

theorem ls_body (hE : E.Spec) (j : Bool) (D : Nat) (s : Io_RwLock_lockSharedUncancelableLocals)
    (G : ThreadId → Gh S) (m : Mem) (d : Nat) (h : lsInv E j D s G m d) :
    (proto E).WP 0 ((Io_RwLock_lockSharedUncancelable.loop8 (bPtr.add 16)).run s) (fun r G' m' d' =>
      if Io_RwLock_lockSharedUncancelable.again8 r.1 then lsInv E j D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_RwLock_lockSharedUncancelableLocals) => 0) s)
      else lsPost E j D r G' m' d') G m d := by
  obtain ⟨hD, hc, hvS, hi⟩ := h
  unfold Io_RwLock_lockSharedUncancelable.loop8
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases htest : (s.state &&& 4294967295 == 0)
  rotate_left
  · simp only [↓reduceIte]
    have hfree : s.state = sv3 0 0 0 ∨ s.state = sv3 0 0 1 := by
      have := hvS
      simp only [sVals, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h | h | h <;> rw [h] at htest ⊢ <;>
        first | decide | (revert htest; decide)
    refine WP.bind ?_
    rw [StateT.run_bind]
    refine WP.bind ?_
    rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_bind]
    refine WP.bind (WP.callRC_ok (sVals_addR hvS) ?_)
    rw [StateT.run_bind]
    rw [wsptr]
    refine WP.bind (wp_cas (W := WS) hi (wat (fun _ _ h => h.2.1.ws) (by simp [gA]))
      fun k₁ hk₁ G₁ m₁ m' hg₁ hi₁ hw' hop => ⟨fun hv hU hh hacq => ?_, fun jx old hne hj hv hfl hacq hh => ?_⟩)
    · -- the `cmpxchg` succeeds: `main` takes `n` from the state word
      have hu₁ := hi₁.2.1
      have hg0 : (G₁ 0).2.2 = .ls j := by rw [hg₁]; rfl
      have hold := sold hu₁ hv
      rw [hg0] at hold; simp only [Ph.rb] at hold
      have hW1 := w_isW hu₁ (by rw [hg0]; simp)
      have hwi := Ph.wb_ib (G₁ 1).2.2
      have hz : (G₁ 1).2.2.wb = 0 ∧ (G₁ 1).2.2.ib = 0 ∧ s.state = sv3 0 0 0 := by
        rcases hfree with h | h <;> rw [h] at hold ⊢
        · obtain ⟨a, b, -⟩ := sv3_inj (by omega) (by omega) hwi (by omega) hold
          exact ⟨a.symm, b.symm, rfl⟩
        · obtain ⟨-, -, c⟩ := sv3_inj (by omega) (by omega) hwi (by omega) hold
          omega
      obtain ⟨hw0, hi0, hs0⟩ := hz
      obtain ⟨hm1, hws1⟩ := w_free hW1 (.inl hi0)
      have hc : Car (G₁ 0).2.2 (G₁ 1).2.2 := ⟨by rw [hg0]; rfl, hm1, by rw [hws1]; rfl⟩
      obtain ⟨hn, hpn, hsn, hokn⟩ := hu₁.car hc
      have htl : 0 < m₁.threads.size :=
        (hi₁.1.live 0 (by rw [hg₁]; exact (by decide : LPh.out ≠ LPh.gone))).1
      have ho := own_rmw hpn hokn hu₁.ws hop htl (hacq rfl)
      have hsn' := (car_rmw hpn hsn hokn hu₁.ws hop hh).1
      have hf := hu₁.flags
      rw [hg0] at hf
      have hi₂ : (proto E).inv (upd G₁ 0 (gA (.sh j) hn default)) m' :=
        inv_sstep hE hi₁ hg₁ hop hw' hh (by
            rw [upd_self, upd0_1, sv_eq, hw0, hi0]
            show Word.Entry.Val _ (sv3 0 0 1)
            rw [← sv3_inc, ← hs0]; exact rmwEnt_val WS)
          rfl rfl (by simp) rfl rfl rfl (.inl rfl)
          (by
            rw [upd_self, upd0_1]
            exact ⟨(fun k hk => by rw [hk] at hi0; cases hi0), (fun h => by cases h),
              (fun h => by cases h.1), (fun _ _ h => by cases h), hf.jd⟩)
          (by rw [upd0_1]; exact hpn)
          (fun hc' => absurd hc'.1 (by rw [upd_self]; simp [gA, Ph.mustN]))
          (lws_gain hi₁ hop hg₁ hc hpn hsn' ho (by simp [hasP, upd_self, upd0_1, gA, Ph.gave]))
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_RwLock_lockSharedUncancelable.again8, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hop.current, .inl ⟨rfl, hn, hi₂⟩⟩
    · -- it fails: `main` reads write `jx`
      have hi₂ := inv_sread hE hi₁ hop hw' hh
      rw [← upd_same G₁ 0, hg₁] at hi₂
      obtain ⟨v, hv', hvv⟩ := hi₁.2.1.shist jx hj
      have hov : old = v := val_eq hv hvv
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (show (proto E).WP 0 ((callRC (optPayload (some old)) : CM Tgt _ _).run s) _ _ _ _ from
        WP.callRC_ok (v := old) rfl ?_)
      simp only [StateT.run_pure]
      refine WP.pure' ?_
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      refine WP.pure' ?_
      simp only [StateT.run_pure]
      refine WP.pure' ?_
      simp only [Io_RwLock_lockSharedUncancelable.again8, ↓reduceIte]
      exact ⟨⟨by omega, hop.current, by rw [hov]; exact hv', hi₂⟩, .inl (by omega)⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_RwLock_lockSharedUncancelable.again8, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, hc, .inr ⟨rfl, hi⟩⟩

/-- `lockShared` by `main` at `ls j`: it holds the shared lock and owns `n`. -/
theorem lockS_spec (hE : E.Spec) {j : Bool} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat}
    (hi : (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m) :
    (proto E).WP 0 (Io_RwLock_lockSharedUncancelable (bPtr.add 16) io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = 0 ∧ ∃ h, (proto E).inv (upd G' 0 (gA (.sh j) h default)) m') G m d := by
  unfold Io_RwLock_lockSharedUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [wsptr]
  refine WP.bind (wp_load (W := WS) hi (wat (fun _ _ h => h.2.1.ws) (by simp [gA]))
    fun k₁ hk₁ G₁ m₁ m' v jx hg₁ hi₁ hj hv hfl hacq hh hw' hop => ?_)
  have hi₂ := inv_sread hE hi₁ hop hw' hh
  rw [← upd_same G₁ 0, hg₁] at hi₂
  obtain ⟨v', hv', hvv⟩ := hi₁.2.1.shist jx hj
  have hov : v = v' := val_eq hv hvv
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (lsInv E j k₁) (fun _ => 0) (lsPost E j k₁) (ls_body hE j k₁) _
    G₁ m' k₁ ⟨Nat.le_refl _, hop.current, by rw [hov]; exact hv', hi₂⟩))
  rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨hd₂, hc₂, ⟨rfl, h, hi₃⟩ | ⟨rfl, hi₃⟩⟩
  · simp only [StateT.run_pure]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₂, h, hi₃⟩
  · -- the slow path: the mutex, `state += reader`, the unlock
    have hi₄ := inv_lsl hE hi₃
    simp only [StateT.run_bind, bind_assoc]
    rw [wmptr]
    refine WP.bind (WP.callC (WP.mono ?_ (mlock_spec hE (t := 0) (x := .sl j .cas) rfl rfl hi₄)))
    rintro _ G₃ m₃ d₃ ⟨hd₃, hc₃, hi₅⟩
    refine WP.bind (wp_rmw (W := WS) hi₅ (wat (fun _ _ h => h.2.1.ws) (by simp [gA]))
      fun k₄ hk₄ G₄ m₄ m₅ old hg₄ hi₆ hv hU hh hacq hw' hop => ?_)
    have hu := hi₆.2.1
    have hg0 : (G₄ 0).2.2 = .sl j .holds := by rw [hg₄]; rfl
    have hold := sold hu hv
    rw [hg0] at hold; simp only [Ph.rb] at hold
    have hW1 := w_isW hu (by rw [hg0]; simp)
    have hf := hu.flags
    rw [hg0] at hf
    have hone : (G₄ 1).2.2.mp ≠ some .holds := fun h => hf.one ⟨rfl, h⟩
    obtain ⟨hm1, hws1⟩ := w_free hW1 (.inr hone)
    have hc : Car (G₄ 0).2.2 (G₄ 1).2.2 := ⟨by rw [hg0]; rfl, hm1, by rw [hws1]; rfl⟩
    obtain ⟨hn, hpn, hsn, hokn⟩ := hu.car hc
    have htl : 0 < m₄.threads.size :=
      (hi₆.1.live 0 (by rw [hg₄]; exact (by decide : LPh.out ≠ LPh.gone))).1
    have ho := own_rmw hpn hokn hu.ws hop htl (hacq rfl)
    have hsn' := (car_rmw hpn hsn hokn hu.ws hop hh).1
    have hi₇ : (proto E).inv (upd G₄ 0 (gA (.sr j .holds) hn default)) m₅ :=
      inv_sstep hE hi₆ hg₄ hop hw' hh (by
          rw [upd_self, upd0_1, sv_eq]
          show Word.Entry.Val _ (sv3 _ _ 1)
          rw [← sv3_addR (Ph.wb_ib _), ← hold]; exact rmwEnt_val WS)
        rfl rfl (by simp [Ph.setM]) rfl rfl rfl (.inl rfl)
        (by
          rw [upd_self, upd0_1]
          exact ⟨(fun k hk => by rw [hk] at hone; exact absurd rfl hone), (fun h => by cases h),
            (fun h => hone h.2), (fun _ _ h => by cases h; exact .inl rfl), hf.jd⟩)
        (by rw [upd0_1]; exact hpn)
        (fun hc' => absurd hc'.1 (by rw [upd_self]; simp [gA, Ph.mustN]))
        (lws_gain hi₆ hop hg₄ hc hpn hsn' ho (by simp [hasP, upd_self, upd0_1, gA, Ph.gave]))
    refine WP.bind (WP.callC (WP.mono ?_ (munlock_spec hE (t := 0) (x := .sr j .holds)
      (.inl ⟨rfl, j, .holds, by rw [upd_self]; rfl⟩) rfl hi₇)))
    rintro _ G₅ m₆ d₅ ⟨hd₅, hc₆, hi₈⟩
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    exact WP.pure' ⟨by omega, hc₆, hn, hi₈⟩

end Sync.RwLockRead
