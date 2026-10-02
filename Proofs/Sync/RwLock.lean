import Proofs.Sync.Lock
import ZigLean.Conc.Word

/-!
# `rwLockRead` over all schedules

WIP.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

set_option linter.unusedSectionVars false

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
  | ls
  /-- `main` in `lockShared`'s slow path: in the mutex's `lock`, or it holds the mutex. -/
  | sl (p : MP)
  /-- `main` did `state += reader` (it owns `n`) and holds the mutex, or is in its `unlock`. -/
  | sr (p : MP)
  /-- `main` holds the shared lock: it owns `n`. -/
  | sh
  /-- `main` was the last reader while the writer waits: it posts the semaphore. -/
  | po
  /-- `main` after `readShared`. -/
  | dn
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
  | sl p | sr p | wa _ p | wr _ p => some p
  | ws _ | wn _ => some .holds
  | _ => Option.none

/-- The same place, at `p` in the mutex's code. -/
def setM : Ph → MP → Ph
  | sl _, p => sl p
  | sr _, p => sr p
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
  | sr _ | sh => 1
  | _ => 0

/-- `main` must own `n`. -/
def mustN : Ph → Bool
  | sr _ | sh | wn _ => true
  | _ => false

/-- The thread may own `n`. -/
def mayN : Ph → Bool
  | sr _ | sh | po | ws _ | wn _ => true
  | _ => false

/-- In the semaphore's code. -/
def inSem : Ph → Bool
  | po | ws _ => true
  | _ => false

/-- `main`'s places after its spawn. -/
def isMain : Ph → Bool
  | ls | sl _ | sr _ | sh | po | dn | joins => true
  | _ => false

/-- The writer's places (`k ≤ 2` increments). -/
def isW : Ph → Bool
  | wo k | wn k => decide (k ≤ 2)
  | wa k _ | ws k => decide (k < 2)
  | wr k _ => decide (k ≤ 2)
  | wf => true
  | _ => false

end Ph

/-- A thread's place, and its ghost value in the semaphore's code (`S`). -/
structure X (S : Type) where
  ph : Ph := .none
  s : S

abbrev Gh (S : Type) := LG × X S

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
  ws : ∀ k, b = .ws k → a = .sh ∨ a = .po ∨ a = .dn ∨ a = .joins
  /-- `main` posts only while the writer waits. -/
  po : a = .po → ∃ k, b = .ws k
  /-- At most one thread holds the mutex. -/
  one : ¬ (a.mp = some .holds ∧ b.mp = some .holds)

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

/-- No thread owns `n` (`hn`): each access to it happened before the release clock of the
state's newest write, or before every thread. -/
def CarOk (m : Mem) (hn : Heap) : Prop :=
  ∀ e ∈ m.footprint, (e.Touches hn ∨ m.blocks.size ≤ e.block) →
    VClock.le e.clock (last (WS.hist m)).relClock = true ∨ AllLe m e.clock

/-- `n` is in the state word: no thread owns it, and the semaphore does not have it. -/
def Car (a b : Ph) : Prop := a.mayN = false ∧ b.mayN = false

/-- A thread asleep at the mutex: its place, and the other thread `o` holds the mutex (which is
`contended`) or wakes it. -/
def MQ (m : Mem) (x o : Ph) : Prop :=
  x.mp = some .wait ∧ ((o.mp = some .holds ∧ (last (WM.hist m)).Val (2 : BitVec 32)) ∨
    o.mp = some .wake)

/-! ## Facts of the places -/

namespace Ph

/-- A place with a place in the mutex's code (`setM` changes it). -/
def isMx : Ph → Bool
  | sl _ | sr _ | wa _ _ | wr _ _ => true
  | _ => false

theorem mp_setM {x : Ph} (h : x.isMx) (p : MP) : (x.setM p).mp = some p := by
  cases x <;> simp_all [isMx, setM, mp]

@[simp] theorem wb_setM (x : Ph) (p : MP) : (x.setM p).wb = x.wb := by cases x <;> rfl
@[simp] theorem ib_setM (x : Ph) (p : MP) : (x.setM p).ib = x.ib := by cases x <;> rfl
@[simp] theorem rb_setM (x : Ph) (p : MP) : (x.setM p).rb = x.rb := by cases x <;> rfl
@[simp] theorem mayN_setM (x : Ph) (p : MP) : (x.setM p).mayN = x.mayN := by cases x <;> rfl
@[simp] theorem mustN_setM (x : Ph) (p : MP) : (x.setM p).mustN = x.mustN := by cases x <;> rfl
@[simp] theorem cnt_setM (x : Ph) (p : MP) : (x.setM p).cnt = x.cnt := by cases x <;> rfl
@[simp] theorem isMain_setM (x : Ph) (p : MP) : (x.setM p).isMain = x.isMain := by cases x <;> rfl
@[simp] theorem isW_setM (x : Ph) (p : MP) : (x.setM p).isW = x.isW := by cases x <;> rfl
@[simp] theorem inSem_setM (x : Ph) (p : MP) : (x.setM p).inSem = x.inSem := by cases x <;> rfl
@[simp] theorem isMx_setM (x : Ph) (p : MP) : (x.setM p).isMx = x.isMx := by cases x <;> rfl

theorem mx_ne {x : Ph} (h : x.isMx) :
    x ≠ .po ∧ x ≠ .sh ∧ x ≠ .dn ∧ x ≠ .joins ∧ ∀ k, x ≠ .ws k := by
  cases x <;> simp_all [isMx]

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

/-- The semaphore's part of the protocol (module doc): the resource of its mutex (the word at
32), the rest of its invariant, and when it has `n` (a fact of the threads' ghost values `S`). -/
structure Sem (S : Type) where
  R : (ThreadId → X S) → Assn
  inv : (ThreadId → Gh S) → Mem → Prop
  has : (ThreadId → S) → Prop

variable {S : Type} (E : Sem S)

/-- The semaphore's mutex: a lock that owns the semaphore's resource (`E.R`). -/
abbrev L : Lock (Gh S) := Lock.prod 0 32 E.R

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh S) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2.ph) m
  flags : Flags (G 0).2.ph (G 1).2.ph
  io : IoOk m
  blk : BlkOk m
  ws : WS.Ok m
  wm : WM.Ok m
  /-- Each write of the state word is a state. -/
  shist : ∀ j < (WS.hist m).size, ∃ v ∈ sVals, (WS.hist m)[j]!.Val v
  /-- The newest write: the state of the threads' places. -/
  slast : (last (WS.hist m)).Val (sv (G 0).2.ph (G 1).2.ph)
  /-- Each write of the mutex word is `0`, `1` or `2`. -/
  mhist : ∀ j < (WM.hist m).size, ∃ v ∈ mVals, (WM.hist m)[j]!.Val v
  /-- The newest write is `0` if no thread holds the mutex. -/
  mlast : ∃ v ∈ mVals, (last (WM.hist m)).Val v ∧ (v = 0 ↔ ∀ u, (G u).2.ph.mp ≠ some .holds)
  /-- A thread asleep at the mutex. -/
  mq : ∀ w ∈ m.waiters, w.2 = WM.ptr →
    (w.1 = 0 ∧ MQ m (G 0).2.ph (G 1).2.ph) ∨ (w.1 = 1 ∧ MQ m (G 1).2.ph (G 0).2.ph)
  /-- Out of the semaphore's code, a thread is out of its mutex's code. -/
  lph : ∀ u, (G u).2.ph.inSem = false →
    (G u).1.ph = .out ∨ (G u).1.ph = .away ∨ (G u).1.ph = .gone
  /-- A thread's part: nothing, or `n`. -/
  parts : ∀ u, (G u).1.part = Heap.empty ∨ ((G u).2.ph.mayN ∧ NPts (G 1).2.ph.cnt (G u).1.part)
  must : ∀ u, (G u).2.ph.mustN → NPts (G 1).2.ph.cnt (G u).1.part
  /-- `n` in the state word. -/
  car : Car (G 0).2.ph (G 1).2.ph → ∃ hn, NPts (G 1).2.ph.cnt hn ∧ hn.Sub m.heap ∧ CarOk m hn
  /-- The semaphore has `n` only while the writer waits. -/
  nohas : (∀ k, (G 1).2.ph ≠ .ws k) → ¬ E.has (fun u => (G u).2.s)

variable [Inhabited S]

/-- The protocol, in strict mode. -/
def proto : Proto Tgt (Gh S) where
  inv G m := (L E).Inv G m ∧ U E G m ∧ E.inv G m
  init tgt g := match tgt with
    | .writer p => p = bPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, { ph := .wo 0, s := default })
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.ph = .wf
  strict := true
  joins g := g.1.ph = .out ∧ g.2.ph = .joins

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
  /-- `wait` by the writer, who saw a reader: it ends with `n`. -/
  wait : ∀ (k : Nat) (s : S) (G : ThreadId → Gh S) (m : Mem) (d : Nat) (io : Io),
    (proto E).inv (upd G 1 (⟨.out, Heap.empty, Heap.empty⟩, ⟨.ws k, s⟩)) m → m.current = 1 →
    (proto E).WP 1 (Io_Semaphore_waitUncancelable ⟨some 0, 24⟩ io)
      (fun _ G' m' d' => d' ≤ d ∧ m'.current = 1 ∧ ∃ h s', NPts k h ∧
        (proto E).inv (upd G' 1 (⟨.out, h, Heap.empty⟩, ⟨.ws k, s'⟩)) m') G m d
  /-- `post` by `main`, the last reader: it gives `n` to the semaphore. -/
  post : ∀ (h : Heap) (s : S) (G : ThreadId → Gh S) (m : Mem) (d : Nat) (io : Io),
    NPts (G 1).2.ph.cnt h →
    (proto E).inv (upd G 0 (⟨.out, h, Heap.empty⟩, ⟨.po, s⟩)) m → m.current = 0 →
    (proto E).WP 0 (Io_Semaphore_post ⟨some 0, 24⟩ io)
      (fun _ G' m' d' => d' ≤ d ∧ m'.current = 0 ∧ ∃ s',
        (proto E).inv (upd G' 0 (⟨.out, Heap.empty, Heap.empty⟩, ⟨.po, s'⟩)) m') G m d
  /-- A thread asleep at a futex of the semaphore's condition is the writer, while `main` has
  not posted. -/
  live : ∀ G m, (proto E).inv G m → ∀ w ∈ m.waiters, w.2 ≠ (L E).ptr → w.2 ≠ WM.ptr →
    w.1 = 1 ∧ (∃ k, (G 1).2.ph = .ws k) ∧ ((G 0).2.ph = .sh ∨ (G 0).2.ph = .po)
  /-- A step out of the semaphore's code keeps its invariant. -/
  frame : ∀ G G' m m', E.inv G m → Frame m m' →
    (∀ u, (G' u).2.s = (G u).2.s ∧ (G' u).1.held = (G u).1.held ∧
      ((G' u).1.ph = (G u).1.ph ∨ (((G u).1.ph = .out ∨ (G u).1.ph = .away) ∧
        ((G' u).1.ph = .out ∨ (G' u).1.ph = .away)))) →
    E.inv G' m'
  /-- The start, after the spawn: the semaphore's bytes hold `sem0`, no atomic op was done, no
  thread waits, and each access happened before every thread. -/
  start : ∀ G m, (∀ u, (G u).2.s = default) →
    (∀ u, (G u).1.ph = .out ∨ (G u).1.ph = .gone) → BlkOk m →
    curBytes m 0 24 24 = Enc.encode sem0 → m.atomics = #[] → m.waiters = #[] →
    (∀ e ∈ m.footprint, AllLe m e.clock) → E.inv G m
  /-- The resource reads only the ghost values `S`. -/
  R_s : ∀ Y Y' h, (∀ u, (Y' u).s = (Y u).s) → (E.R Y h ↔ E.R Y' h)
  /-- The resource's bytes: the semaphore's (24..48), and `n` while the semaphore has it. -/
  R_at : ∀ Y h, E.R Y h → ∀ l, h l ≠ none →
    l.1 = 0 ∧ ((24 ≤ l.2 ∧ l.2 < 48) ∨ (E.has (fun u => (Y u).s) ∧ 56 ≤ l.2 ∧ l.2 < 60))
  /-- The start of the resource: `permits = 0`. -/
  R0 : ∀ Y A h, (∀ u, (Y u).s = default) → A % 8 = 0 →
    bytesAt (bPtr.add 24) A 64 .stack (Enc.encode (0 : BitVec 64)) h → E.R Y h

/-! ## Basic facts -/

variable {E}

/-- A thread out of the semaphore's mutex, at `x`, with the part `h`. -/
def gA (x : Ph) (h : Heap) (s : S) : Gh S := (⟨.out, h, Heap.empty⟩, ⟨x, s⟩)

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
    (fun u => (upd G t g u).2.ph) = upd (fun u => (G u).2.ph) t g.2.ph := by
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
theorem U_keep {G : ThreadId → Gh S} {m m' : Mem} (hu : U E G m) (hkS : WS.Keep m m')
    (hkM : WM.Keep m m') (ht : m'.threads = m.threads)
    (hq : ∀ w ∈ m'.waiters, w.2 = WM.ptr → w ∈ m.waiters) (hio : IoOk m') (hblk : BlkOk m')
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (NOff e ∧ e.block < m'.blocks.size))
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hcells : ∀ x, 56 ≤ x → x < 60 → m'.heap (0, x) = m.heap (0, x))
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) : U E G m' := by
  have hhS := Word.hist_keep hu.ws hkS
  have hhM := Word.hist_keep hu.wm hkM
  have hall : ∀ c, AllLe m c → AllLe m' c := fun c h u hu' =>
    VClock.le_trans (h u (ht ▸ hu')) (hcl u)
  refine ⟨by unfold Shape at *; rw [ht]; exact hu.shape, hu.flags, hio, hblk, hu.ws.keep hkS,
    hu.wm.keep hkM, by rw [hhS]; exact hu.shist, by rw [hhS]; exact hu.slast,
    by rw [hhM]; exact hu.mhist, by rw [hhM]; exact hu.mlast, fun w hw hp => ?_, hu.lph, hu.parts,
    hu.must, fun hc => ?_, hu.nohas⟩
  · unfold MQ; rw [hhM]; exact hu.mq w (hq w hw hp) hp
  · obtain ⟨hn', hp, hs, hok⟩ := hu.car hc
    exact ⟨hn', hp, car_keep hp hs hok (by rw [hhS]; exact VClock.le_refl _) hfp hbs hcells hall⟩

/-- A change of the ghost values with the same memory: `U` from the facts that depend on
them; the state word and the mutex's places stay. -/
theorem U_ghost {G G' : ThreadId → Gh S} {m : Mem} (hu : U E G m)
    (hsh : Shape (fun u => (G' u).2.ph) m) (hfl : Flags (G' 0).2.ph (G' 1).2.ph)
    (hsv : sv (G' 0).2.ph (G' 1).2.ph = sv (G 0).2.ph (G 1).2.ph)
    (hmp : ∀ u, (G' u).2.ph.mp = (G u).2.ph.mp)
    (hlph : ∀ u, (G' u).2.ph.inSem = false →
      (G' u).1.ph = .out ∨ (G' u).1.ph = .away ∨ (G' u).1.ph = .gone)
    (hparts : ∀ u, (G' u).1.part = Heap.empty ∨
      ((G' u).2.ph.mayN ∧ NPts (G' 1).2.ph.cnt (G' u).1.part))
    (hmust : ∀ u, (G' u).2.ph.mustN → NPts (G' 1).2.ph.cnt (G' u).1.part)
    (hcar : Car (G' 0).2.ph (G' 1).2.ph → ∃ hn, NPts (G' 1).2.ph.cnt hn ∧ hn.Sub m.heap ∧ CarOk m hn)
    (hnh : (∀ k, (G' 1).2.ph ≠ .ws k) → ¬ E.has (fun u => (G' u).2.s)) : U E G' m := by
  refine ⟨hsh, hfl, hu.io, hu.blk, hu.ws, hu.wm, hu.shist, by rw [hsv]; exact hu.slast,
    hu.mhist, ?_, fun w hw hp => ?_, hlph, hparts, hmust, hcar, hnh⟩
  · obtain ⟨v, hv, hl, hz⟩ := hu.mlast
    exact ⟨v, hv, hl, hz.trans (forall_congr' fun u => by rw [hmp])⟩
  · unfold MQ; rw [hmp, hmp]; exact hu.mq w hw hp

/-! ## The heap of the parts and of the resource -/

/-- Bytes that no part and no resource has: below the semaphore, and between its end and `n`. -/
def Free8 (x : Nat) : Prop := x < 24 ∨ (48 ≤ x ∧ x < 56)

theorem R_none (hE : E.Spec) {Y : ThreadId → X S} {h : Heap} (hR : E.R Y h) {x : Nat}
    (hx : Free8 x) : h (0, x) = none := by
  cases e : h (0, x) with
  | none => rfl
  | some c =>
    obtain ⟨-, h1 | ⟨-, h1⟩⟩ := hE.R_at Y h hR (0, x) (by rw [e]; simp) <;>
      (dsimp only at h1; unfold Free8 at hx; omega)

theorem own_none (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    (u : ThreadId) {x : Nat} (hx : Free8 x) : (L E).own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    have hp : (G u).1.part (0, x) = none := by
      rcases hi.2.1.parts u with h | ⟨-, h⟩
      · rw [h]; rfl
      · exact npts_none h (by unfold Free8 at hx; omega)
    simp only [Heap.union_apply, hp, Option.none_or]
    by_cases hh : (L E).ph (G u) = .holds
    · exact R_none hE (hi.1.res u hh) hx
    · rw [show (G u).1.held = (L E).held (G u) from rfl, hi.1.idle u hh]; rfl

/-- A word in the free bytes has no byte of a part or of the resource. -/
theorem off_own (hE : E.Spec) {G : ThreadId → Gh S} {m : Mem} (hi : (proto E).inv G m)
    {n nb : Nat} {W : Word n nb} (hb : W.b = 0) (ho : ∀ x, W.o ≤ x → x < W.o + nb → Free8 x)
    (u : ThreadId) : W.Off ((L E).own G m u) := fun x h1 h2 => by
  rw [hb]; exact own_none hE hi u (ho x h1 h2)

theorem off_R (hE : E.Spec) {n nb : Nat} {W : Word n nb} (hb : W.b = 0)
    (ho : ∀ x, W.o ≤ x → x < W.o + nb → Free8 x) :
    ∀ G hL, (L E).R G hL → W.Off hL := fun _ _ hR x h1 h2 => by
  rw [hb]; exact R_none hE hR (ho x h1 h2)

theorem ws_free : ∀ x, WS.o ≤ x → x < WS.o + 8 → Free8 x := fun x _ h => .inl (by
  simp only [WS] at h; omega)
theorem wm_free : ∀ x, WM.o ≤ x → x < WM.o + 4 → Free8 x := fun x h1 h2 => .inr (by
  simp only [WM] at h1 h2; omega)

theorem apS : Word.Apart (L E) WS := .inr (.inr (by simp [WS, L, Lock.prod]))
theorem apM : Word.Apart (L E) WM := .inr (.inl (by simp [WM, L, Lock.prod]))

/-- An op at a word out of the semaphore's bytes keeps them. -/
theorem frame_op {n nb : Nat} {W : Word n nb} {t : ThreadId} {m m' : Mem} (hop : W.Op t m m')
    (hap : W.b ≠ 0 ∨ W.o + nb ≤ 24 ∨ 48 ≤ W.o) : Frame m m' :=
  ⟨fun W' hb h1 h2 => Word.keep_op hop (by
      rcases hap with h | h | h
      · exact .inl (by rw [hb]; exact h)
      · exact .inr (.inl (by omega))
      · exact .inr (.inr (by omega))),
    by rw [hop.threads], fun w _ => by rw [hop.waiters], hop.clocks⟩

/-! ## The mutex's code -/

/-- Thread `t` at `x` goes to the place `p` in the mutex's code (`g'`). -/
def MSet (G : ThreadId → Gh S) (t : ThreadId) (p : MP) (g' : Gh S) : Prop :=
  (G t).2.ph.isMx ∧ g'.2.ph = (G t).2.ph.setM p ∧ g'.2.s = (G t).2.s ∧ g'.1.part = (G t).1.part ∧
    g'.1.held = (G t).1.held

theorem MSet.ph {G : ThreadId → Gh S} {t : ThreadId} {p : MP} {g' : Gh S} (h : MSet G t p g')
    (u : ThreadId) : (upd G t g' u).2.ph = if u = t then (G u).2.ph.setM p else (G u).2.ph := by
  unfold upd; split
  · rename_i e; subst e; exact h.2.1
  · rfl

/-- A change of a thread's place in the mutex's code, with a step that keeps the state word, `n`,
the threads, `io` and the order of the clocks: `U` from the mutex word's facts. -/
theorem U_mx {G : ThreadId → Gh S} {m m' : Mem} {t : ThreadId} {p : MP} {g' : Gh S}
    (hu : U E G m) (hg : MSet G t p g')
    (hlph : (G t).1.ph = .out ∨ (G t).1.ph = .away → g'.1.ph = .out ∨ g'.1.ph = .away)
    (hl : (G t).1.ph = .out ∨ (G t).1.ph = .away)
    (hkS : WS.Keep m m') (ht : m'.threads = m.threads) (hio : IoOk m') (hblk : BlkOk m')
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (NOff e ∧ e.block < m'.blocks.size))
    (hbs : m.blocks.size ≤ m'.blocks.size)
    (hcells : ∀ x, 56 ≤ x → x < 60 → m'.heap (0, x) = m.heap (0, x))
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hw' : WM.Ok m') (hmh : ∀ j < (WM.hist m').size, ∃ v ∈ mVals, (WM.hist m')[j]!.Val v)
    (hml : ∃ v ∈ mVals, (last (WM.hist m')).Val v ∧
      (v = 0 ↔ ∀ u, (upd G t g' u).2.ph.mp ≠ some .holds))
    (hmq : ∀ w ∈ m'.waiters, w.2 = WM.ptr →
      (w.1 = 0 ∧ MQ m' (upd G t g' 0).2.ph (upd G t g' 1).2.ph) ∨
      (w.1 = 1 ∧ MQ m' (upd G t g' 1).2.ph (upd G t g' 0).2.ph))
    (hone : ¬ ((upd G t g' 0).2.ph.mp = some .holds ∧ (upd G t g' 1).2.ph.mp = some .holds)) :
    U E (upd G t g') m' := by
  have hP := hg.ph
  obtain ⟨hx, hph, hs, hpart, -⟩ := hg
  have hhS := Word.hist_keep hu.ws hkS
  have hall : ∀ c, AllLe m c → AllLe m' c := fun c h u hu' =>
    VClock.le_trans (h u (ht ▸ hu')) (hcl u)
  have hf : ∀ (f : Ph → Nat), (∀ x : Ph, f (x.setM p) = f x) →
      ∀ u, f (upd G t g' u).2.ph = f (G u).2.ph := fun f hfx u => by
    rw [hP]; split
    · exact hfx _
    · rfl
  have hb : ∀ (f : Ph → Bool), (∀ x : Ph, f (x.setM p) = f x) →
      ∀ u, f (upd G t g' u).2.ph = f (G u).2.ph := fun f hfx u => by
    rw [hP]; split
    · exact hfx _
    · rfl
  have hcnt : (upd G t g' 1).2.ph.cnt = (G 1).2.ph.cnt := hf Ph.cnt (fun x => by simp) 1
  have hsv : ∀ a b : Ph, sv (a.setM p) b = sv a b ∧ sv a (b.setM p) = sv a b := fun a b => by
    simp [sv_eq]
  have hsv' : sv (upd G t g' 0).2.ph (upd G t g' 1).2.ph = sv (G 0).2.ph (G 1).2.ph := by
    rw [sv_eq, sv_eq, hf Ph.wb (by simp), hf Ph.ib (by simp), hf Ph.rb (by simp)]
  -- `t`'s place is `main`'s or the writer's (not at its end)
  have ht01 : t = 0 ∨ t = 1 := by
    obtain ⟨-, ⟨-, hp0, hn⟩ | ⟨-, -, -, -, hn⟩⟩ := hu.shape
    · rcases Nat.eq_zero_or_pos t with h | h
      · exact .inl h
      · have := hn t h; change (G t).2.ph = _ at this; rw [this] at hx; cases hx
    · rcases Nat.lt_or_ge t 2 with h | h
      · unfold ThreadId at *; omega
      · have := hn t h; change (G t).2.ph = _ at this; rw [this] at hx; cases hx
  have hY : (G t).2.ph.isMain ∨ ((G t).2.ph.isW ∧ (G t).2.ph ≠ .wf) := by
    have := hu.shape
    obtain ⟨-, ⟨-, hp0, hn⟩ | ⟨-, -, hM, hW, hn⟩⟩ := this
    · exfalso
      rcases Nat.eq_zero_or_pos t with rfl | h
      · change (G 0).2.ph = _ at hp0; rw [hp0] at hx; cases hx
      · have := hn t h; change (G t).2.ph = _ at this; rw [this] at hx; cases hx
    · rcases Nat.lt_or_ge t 2 with h | h
      · rcases (by unfold ThreadId at *; omega : t = 0 ∨ t = 1) with rfl | rfl
        · exact .inl hM
        · exact .inr ⟨hW, fun e => by rw [e] at hx; cases hx⟩
      · have := hn t h; change (G t).2.ph = _ at this; rw [this] at hx; cases hx
  refine ⟨?_, ?_, hio, hblk, hu.ws.keep hkS, hw', by rw [hhS]; exact hu.shist,
    by rw [hhS, hsv']; exact hu.slast, hmh, hml, hmq, fun u hu' => ?_, fun u => ?_, fun u hm => ?_,
    fun hc => ?_, fun hn => ?_⟩
  · rw [ph_upd]; have := shape_upd hu.shape hY (y := g'.2.ph) (by rw [hph]; simp) (by rw [hph]; simp)
    unfold Shape at this ⊢; rw [ht]; exact this
  · obtain ⟨f1, f2, -⟩ := hu.flags
    have hx' := Ph.mx_ne (x := (G t).2.ph.setM p) (by simpa using hx)
    have hx0 := Ph.mx_ne hx
    rcases ht01 with rfl | rfl
    · simp only [upd_self, upd0_1, hph] at hone ⊢
      refine ⟨fun k hk => ?_, fun ha => absurd ha hx'.1, hone⟩
      rcases f1 k hk with h | h | h | h
      · exact absurd h hx0.2.1
      · exact absurd h hx0.1
      · exact absurd h hx0.2.2.1
      · exact absurd h hx0.2.2.2.1
    · simp only [upd_self, upd1_0, hph] at hone ⊢
      refine ⟨fun k hk => absurd hk (hx'.2.2.2.2 k), fun ha => ?_, hone⟩
      obtain ⟨k, hk⟩ := f2 ha
      exact absurd hk (hx0.2.2.2.2 k)
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢
      rcases hlph hl with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · rw [upd_ne _ _ e] at hu' ⊢; exact hu.lph u hu'
  · rw [hcnt]
    by_cases e : u = t
    · subst e; rw [upd_self, hpart, hph]
      rcases hu.parts u with h | ⟨h1, h2⟩
      · exact .inl h
      · exact .inr ⟨by simpa using h1, h2⟩
    · rw [upd_ne _ _ e]; exact hu.parts u
  · rw [hcnt]
    by_cases e : u = t
    · subst e; rw [upd_self, hph] at hm; rw [upd_self, hpart]; exact hu.must u (by simpa using hm)
    · rw [upd_ne _ _ e] at hm ⊢; exact hu.must u hm
  · have hc' : Car (G 0).2.ph (G 1).2.ph := by
      unfold Car at hc ⊢
      rw [hb Ph.mayN (by simp) 0, hb Ph.mayN (by simp) 1] at hc; exact hc
    obtain ⟨hn, hp, hsb, hok⟩ := hu.car hc'
    rw [hcnt]
    exact ⟨hn, hp, car_keep hp hsb hok (by rw [hhS]; exact VClock.le_refl _) hfp hbs hcells hall⟩
  · have hs' : (fun u => (upd G t g' u).2.s) = fun u => (G u).2.s := by
      funext u; unfold upd; split
      · rename_i e; subst e; exact hs
      · rfl
    rw [hs']
    refine hu.nohas fun k hk => hn k ?_
    rw [hP]; split
    · rename_i e; subst e; rw [hk] at hx; cases hx
    · exact hk

end Sync.RwLockRead
