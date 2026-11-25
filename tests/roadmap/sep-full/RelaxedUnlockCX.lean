import ZigLean.Mem.Reuse
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.LockSteps
import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.Local

/-!
# A relaxed `unlock` breaks the lock's invariant (engine ledger #mutex-impl-relaxed-witness)

WIP: part 1, the concrete run.
-/

namespace Zig.RelaxedUnlockCX

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

/-! ## The run -/

/-- The memory a run of `x` returns (the empty memory where it returns none). -/
def resMem {α : Type} : Option (Except Error (α × Mem)) → Mem
  | some (.ok (_, m)) => m
  | _ => {}

/-- A run whose value the kernel computed returns `resMem` of itself. -/
theorem run_of_value {α : Type} {x : MemM α} {m : Mem} {a : α}
    (h : runValue x m = some (.ok a)) : (x.run m).run = some (.ok (a, resMem (x.run m).run)) := by
  unfold runValue at h
  cases e : (x.run m).run with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    cases r with
    | error => cases h
    | ok p =>
      obtain ⟨a', m'⟩ := p
      simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at h
      subst h; rfl

/-- The lock's word: 4 bytes at the start of block 0. -/
def wordPtr : Ptr := ⟨some 0, 0⟩

/-- The protected resource: 8 bytes at the start of block 1. -/
def resPtr : Ptr := ⟨some 1, 0⟩

/-- Thread 0 allocates the word and the resource and zeroes them. -/
def setup : MemM (Ptr × Ptr) := do
  let w ← allocStack 4 4
  let q ← allocStack 8 8
  store (α := BitVec 32) 4 w 0
  store (α := BitVec 64) 8 q 0
  pure (w, q)

/-- The start memory: no global, thread 0 runs. -/
def m00 : Mem := { Mem.ofGlobals Placement.fresh [] with current := 0 }

/-- After `setup`. -/
def mS : Mem := resMem (setup.run m00).run

/-- After thread 0 spawned thread 1. -/
def mF : Mem := resMem (Thread.fork.run { mS with current := 0 }).run

/-- After thread 0's successful `cmpxchg(0 → 1)` with acquire (option 0). -/
def m1 : Mem :=
  resMem ((cmpxchgAs (α := BitVec 32) 0 .acquire .relaxed 4 wordPtr 0 1).run
    { mF with current := 0 }).run

/-- After thread 0's write of `7` to the resource. -/
def m2 : Mem := resMem ((Zig.store 8 resPtr (7 : BitVec 64)).run m1).run

/-- After thread 0's relaxed `xchg(0)` (option 0). -/
def m3 : Mem :=
  resMem ((atomicRmwAs (α := BitVec 32) 0 .xchg .relaxed 4 wordPtr 0).run
    { m2 with current := 0 }).run

theorem setup_value : runValue setup m00 = some (.ok (wordPtr, resPtr)) := by decide +kernel

theorem fork_value : runValue Thread.fork { mS with current := 0 } = some (.ok 1) := by
  decide +kernel

theorem cas_value :
    runValue (cmpxchgAs (α := BitVec 32) 0 .acquire .relaxed 4 wordPtr 0 1)
      { mF with current := 0 } = some (.ok none) := by decide +kernel

theorem store_value : runValue (Zig.store 8 resPtr (7 : BitVec 64)) m1 = some (.ok ()) := by
  decide +kernel

theorem xchg_value :
    runValue (atomicRmwAs (α := BitVec 32) 0 .xchg .relaxed 4 wordPtr 0)
      { m2 with current := 0 } = some (.ok 1) := by decide +kernel

theorem cas_count : 0 < casCount 32 .acquire 4 wordPtr 0 { mF with current := 0 } := by
  decide +kernel

theorem xchg_count : 0 < rmwCount 32 .relaxed 4 wordPtr { m2 with current := 0 } := by
  decide +kernel

/-- The facts of the memory where the lock starts. -/
theorem mF_facts : mF.threads.size = 2 ∧ mF.clocks.size = 2 ∧ mF.current = 0 ∧
    mF.atomics = #[] ∧ mF.waiters = #[] ∧ joinedB mF 1 = false ∧ joinedB mF 0 = false ∧
    VClock.le (mF.clocks[0]!) (mF.clocks[1]!) = true ∧
    VClock.le (mF.clocks[0]!) (mF.clocks[0]!) = true := by
  decide +kernel

/-- **The write that the relaxed `xchg` does not publish**: thread 0's write to the resource is
in the footprint after the `xchg`; its clock is above neither thread 1's clock nor the release
clock of the newest message of the word's location. -/
theorem m3_write : m3.threads.size = 2 ∧ m3.footprint.any (fun e =>
    e.block == 1 && e.off == 0 && e.len == 8 && e.kind.isWrite &&
    !(VClock.le e.clock (m3.clocks[1]!)) &&
    m3.atomics.all fun l => !(l.block == 0 && l.off == 0) ||
      !(VClock.le e.clock (l.msgs.back!).relClock)) = true := by
  decide +kernel

/-! ## Weakest preconditions at a concrete run -/

section Inv

variable {Tgt γ α β σ : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}

/-- A stop where the oracle picks: the thread stopped with some ghost value, and for every
environment that keeps the invariant and every pick the rest holds. -/
theorem wp_pick_inv {count : Mem → Nat} {f : Nat → ConcM Tgt β}
    {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat}
    (h : P.WP t (ConcM.sync (.pick count) >>= f) Q G m (n + 1)) :
    ∃ g, P.inv (upd G t g) m ∧ ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → t < m₁.threads.size →
      ∀ c, (c < count { m₁ with current := t } ∨ count { m₁ with current := t } = 0 ∧ c = 0) →
        P.WP t (f c) Q G₁ { m₁ with current := t } n := by
  obtain ⟨-, g, hi, -, hk⟩ := h
  exact ⟨g, hi, fun G₁ m₁ hg hi₁ ht c hc => hk G₁ m₁ hg hi₁ ht c hc⟩

/-- A step in `MemM` that returns: the rest from its memory. -/
theorem wp_liftMem_bind_inv {x : MemM α} {f : α → ConcM Tgt β}
    {Q : β → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat} {a : α} {m' : Mem}
    (h : P.WP t (ConcM.liftMem x >>= f) Q G m n) (hr : (x.run m).run = some (.ok (a, m')))
    (hs : m'.threads.size = m.threads.size) : P.WP t (f a) Q G m' n := by
  unfold WP at h ⊢
  have e : (ConcM.liftMem x >>= f : ConcM Tgt β) n m = f a n m' := by
    show CoN.bind (CoN.leaf (ExceptT.run (x.run m))) _ = _
    rw [hr]; rfl
  rw [e] at h; rw [hs]; exact h

/-- A step in `MemM` that returns, as the whole run: the post at its memory. -/
theorem wp_liftMem_inv {x : MemM α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat}
    {a : α} {m' : Mem} (h : P.WP t (ConcM.liftMem x) Q G m n)
    (hr : (x.run m).run = some (.ok (a, m'))) : Q a G m' n := by
  unfold WP at h
  have e : (ConcM.liftMem x : ConcM Tgt α) n m = CoN.leaf (some (.ok (a, m'))) := by
    show CoN.leaf (ExceptT.run (x.run m)) = _
    rw [hr]
  rw [e] at h; simp only [Proto.Safe] at h; exact h.2

theorem wp_pure_inv {a : α} {Q : α → (ThreadId → γ) → Mem → Nat → Prop} {n : Nat}
    (h : P.WP t (pure a : ConcM Tgt α) Q G m n) : Q a G m n := by
  change P.Safe t Q m.threads.size G (CoN.leaf (some (.ok (a, m)))) at h
  simp only [Proto.Safe] at h; exact h.2

/-- A pick and the `MemM` step it chooses (an atomic op, `cmpxchgAsC`), as `ConcM` binds. -/
theorem pickCall_eq {count : Mem → Nat} {x : Nat → MemM α} {s : σ} :
    ((do let c ← pickC count; callMC (x c)) : CM Tgt σ α).run s =
      (ConcM.sync (.pick count) >>= fun c => ConcM.liftMem (x c) >>= fun a => pure (a, s)) := by
  funext n m; cases n <;> rfl

end Inv

/-! ## The protocol: the lock alone -/

/-- The resource: the 8 bytes at `resPtr`, with any value. -/
def resR : FAssn := FAssn.ex fun v : BitVec 64 => up (pts resPtr 8 v)

theorem resR_unshared : resR.Unshared :=
  FAssn.Unshared.of_share fun _ ⟨_, _, _, hg⟩ => by rw [hg]; rfl

/-- The lock: `Io.Mutex`'s word at `wordPtr` (contended value `2`), the resource `resR`. -/
abbrev L : FLock (FLG × Unit) := FLock.prod 0 0 (fun _ => resR)

/-- The protocol of the lock alone: its invariant is the lock's. -/
def P : Proto Unit (FLG × Unit) where
  inv G m := ∃ rX, L.Inv G rX m ∧ True
  init _ _ := False
  fin g := g.1.ph = .gone
  joins g := g.1.ph = .out

theorem fits : L.Fits (FPrim.empty _) P (fun _ _ _ => True) (fun _ => True) :=
  FLock.Fits.ofLockAll (fun _ _ => Iff.rfl) (fun _ h => h) (fun _ h => h)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => FLock.NoGather.of_R L fun _ => resR_unshared)

/-- `Io.Mutex`'s states of the word. -/
def st : LockWord.States (BitVec 32) where
  unl := 0
  one := 1
  two := 2
  c := 2
  bits0 := rfl
  bits1 := rfl
  bits2 := rfl
  dec0 := rfl
  dec1 := rfl
  dec2 := rfl
  ne01 := by decide
  ne02 := by decide
  ne12 := by decide

/-- **`Io.Mutex.unlock` with a relaxed release**: `IoMutexCode.unlockOf`'s `xchg(unlocked)`
(`atomicRmwAsC`: the oracle's pick, then the RMW) with `relaxed` (monotonic) in place of `release`, then the
futex wake if the word was `contended`, written out in `ConcM`. -/
def relaxedUnlock (p : Ptr) (_io : Io) : ConcM Unit Unit := do
  let c ← ConcM.sync (.pick (rmwCount 32 .relaxed 4 p))
  let v ← ConcM.liftMem (atomicRmwAs (α := BitVec 32) c .xchg .relaxed 4 p 0)
  if v == 2 then discard (ConcM.sync (Tgt := Unit) (.wake p 1)) else pure ()

/-- `MutexImpl.unlock_wp` for `relaxedUnlock` (the contended value `2`, `Io.Mutex`'s). -/
def UnlockWp : Prop :=
  ∀ {γ : Type} {L : FLock γ} {P : Proto Unit γ} {U : (ThreadId → γ) → Res → Mem → Prop}
    {ok : γ → Prop} {K : FPrim γ}, L.Fits K P U ok → P.cost = none → ∀ (p : Ptr), p = L.ptr →
    L.c = 2 → ∀ (t : ThreadId) (g : γ), L.ph g = .holds → ok g → ∀ (io : Io) (G : ThreadId → γ)
    (m : Mem) (d : Nat), P.inv (upd G t g) m → m.current = t →
    P.WP t (relaxedUnlock p io) (fun _ G' m' d' => d' ≤ d ∧ m'.current = t ∧
      P.inv (upd G' t (L.set g .out rnil)) m') G m d

/-! ## The start: thread 0 owns the word and the resource, thread 1 runs -/

/-- The setup's post: the word, the resource, their extents, the plain mode. -/
def setupKeep (ps : Ptr × Ptr) : FAssn :=
  (FAssn.ex fun b : BlockId => ⟪ps.1.block = some b⟫ ⋆ bext b 4 .stack) ⋆
    ((FAssn.ex fun b : BlockId => ⟪ps.2.block = some b⟫ ⋆ bext b 8 .stack) ⋆ plain)

def setupPost (ps : Ptr × Ptr) : FAssn :=
  (up (pts ps.1 4 (0#32)) ⋆ up (pts ps.2 8 (0#64))) ⋆ setupKeep ps

theorem setup_spec : FTTriple (globals [] ⋆ plain) setup setupPost := by
  fsym [setup, setupPost, setupKeep, globals]

/-- The parts after the setup and the spawn: thread 0 owns the word `rW`, the resource `rL`
and the rest `rP`; every other thread owns nothing. -/
theorem start_owned : ∃ (own : ThreadId → Res) (rW rL rP : Res), FOwned own rnil mF ∧
    (∀ u, u ≠ 0 → own u = rnil) ∧ own 0 = rsum (rsum rW rL) rP ∧
    FHeap.Disjoint rW.heap rL.heap ∧ FHeap.Disjoint (rsum rW rL).heap rP.heap ∧
    up (pts wordPtr 4 (0#32)) rW ∧ up (pts resPtr 8 (0#64)) rL := by
  have hr := run_of_value setup_value
  have ho : FOwned plainOwn rnil m00 := FOwned.start0_plain Placement.fresh
  have ht : 0 < m00.threads.size := by decide
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hp : (globals [] ⋆ plain) (plainOwn 0) := by
    change (emp ⋆ plain) (plainOwn 0)
    exact Full.sep_comm ((Full.sep_emp (P := plain) (r := plainOwn 0)).mpr
      (by rw [plainOwn_zero]; exact plain_intro))
  have hcm : m00.FConc := ⟨by rw [ho.csize]; exact ht, ho.conc.1, ho.conc.2.1⟩
  have hx := setup_spec m00 (plainOwn 0) _ (hh.addCurF (ho.part_noCur hR)) hp hcm (ho.owns 0 ht)
  rw [hr] at hx
  obtain ⟨r, hh', hq, hcm', how, hs⟩ := hx
  obtain ⟨hnc, hh'⟩ := hh'.dropCurF
  rw [Res.owned_addGh, Res.shared_addGh] at hs
  have ho1 : FOwned (upd plainOwn 0 r) rnil mS :=
    ho.step rfl ht hR hRO hh' hcm' how hs.interL hnc
  have ht1 : 0 < mS.threads.size := by decide +kernel
  have ho2 := ho1.fork (t := 0) (r₁ := r) (r₂ := rnil) (gt := false) ht1
    (by rw [upd_self]; exact (rsum_rnil r).symm) (FHeap.disjoint_empty _) (run_of_value fork_value)
  obtain ⟨child, keep, hd, rfl, hchild, -⟩ := hq
  obtain ⟨wc, qc, hdo, rfl, hw, hqc⟩ := hchild
  refine ⟨_, wc, qc, keep, ho2, fun u hu => ?_, by simp [upd], hdo, hd, hw, hqc⟩
  by_cases h1 : u = 1
  · subst h1; simp [upd]
  · simp [upd, plainOwn, hu, h1]

/-- The ghost values at the start: threads 0 and 1 out of the lock's code, thread 0 with the
part `rP`; no other thread. -/
def G0 (rP : Res) : ThreadId → FLG × Unit := fun u =>
  if u = 0 then ({ ph := .out, part := rP }, ()) else if u = 1 then ({ ph := .out }, ()) else ({}, ())

/-- The cells of `up (pts p a v)`: exactly the bytes from `p` on. -/
theorem pts_cells {T : Type} [Enc T] {b : BlockId} {a : Nat} {v : T} {r : Res}
    (h : up (pts ⟨some b, 0⟩ a v) r) (l : Loc) :
    r.heap l ≠ none ↔ l.1 = b ∧ l.2 < Enc.size T := by
  obtain ⟨⟨A, S, K, bs, -, hsz, -, ⟨b', hb, -, hl⟩, -⟩, -, -⟩ := h
  cases hb
  have := hl l
  simp only [FHeap.erase] at this
  rw [← hsz]
  constructor
  · intro hn
    cases e : r.heap l with
    | none => exact absurd e hn
    | some c =>
      rw [e] at this
      split at this
      · rename_i hc; simp only [Int.toNat_zero, Nat.zero_le, true_and, Nat.zero_add] at hc
        exact hc
      · cases this
  · rintro ⟨h1, h2⟩ e
    rw [e, if_pos ⟨h1, by simp, by simpa using h2⟩] at this
    cases this

/-- **The lock's invariant at the start** (`FLock.Inv.make`). -/
theorem start_inv : ∃ rP, P.inv (G0 rP) mF := by
  obtain ⟨own, rW, rL, rP, ho, hown, h0, hdo, hd, hw, hq⟩ := start_owned
  obtain ⟨hts, hcs, -, hat, hwt, hj1, hj0, hle01, hle00⟩ := mF_facts
  have hd' := FHeap.disjoint_union_left.mp hd
  refine ⟨rP, rnil, FLock.Inv.make (L := L) (m := mF) (G := G0 rP) (own := own) (rX := rnil) (rL := rL)
    (rW := rW) (t := 0) ho hj0 (by rw [hts]; decide) (fun u hu => ?_) ?_
    (FHeap.disjoint_union_right.mpr ⟨hd'.2.symm, hd'.1.symm⟩) hdo.symm
    (fun l => (pts_cells hw l).trans (by simp [LockWord.In, FLock.prod]; intro _; exact Iff.rfl)) hw.2.1 hw.2.2
    (fun u => ?_) (fun u => ?_) ⟨0, hq⟩ ?_ ?_ (fun l hl => by rw [hat] at hl; simp at hl)
    (LockWord.waiters_empty hwt) (fun u hu _ => ?_), trivial⟩
  · rw [hown u hu]
    unfold FLock.own
    split
    · rfl
    · by_cases h1 : u = 1 <;> simp [G0, hu, h1, FLock.prod, Know.union_none]
  · rw [h0]
    show rsum (rsum rW rL) rP = rsum rP (rsum rL rW)
    rw [rsum_comm hd, rsum_comm hdo]
  · by_cases h0 : u = 0
    · subst h0; exact .inl ⟨.inl rfl, by rw [hts]; decide, hj0⟩
    · by_cases h1 : u = 1
      · subst h1; exact .inl ⟨.inl (by simp [G0, FLock.prod]), by rw [hts]; decide, hj1⟩
      · exact .inr (by simp [G0, FLock.prod, h0, h1])
  · by_cases h0 : u = 0
    · subst h0; rfl
    · by_cases h1 : u = 1 <;> simp [G0, FLock.prod, h0, h1]
  · have hsz : 0 < mF.blocks.size := by decide +kernel
    refine ⟨mF.blocks[0]'hsz, Array.getElem?_eq_getElem hsz, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel +revert
  · show (intOfBytes 32 (curBytes mF 0 0 4)).run = some (.ok 0)
    decide +kernel
  · rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
    · exact hle00
    · exact hle01

/-! ## The counterexample -/

/-- The store of the critical section. -/
theorem store_spec :
    FTTriple resR (Zig.store 8 resPtr (7 : BitVec 64)) (fun _ => up (pts resPtr 8 (7 : BitVec 64))) := by
  fsym [resR]

/-- **After the relaxed `xchg` no ghost value gives the invariant**: thread 0's write to the
resource happened neither before thread 1 (out of the lock's code, so the free lock's
`LockWord.Owns` needs it) nor before the release clock of the word's newest message. -/
theorem no_inv_after (G : ThreadId → FLG × Unit) (g : FLG × Unit) (hg : g.1.ph = .out)
    (hfree : ∀ u, u ≠ 0 → (G u).1.ph.held = false) (h1 : (G 1).1.ph ≠ .gone)
    (hi : P.inv (upd G 0 g) m3) : False := by
  obtain ⟨rX, hL, -⟩ := hi
  obtain ⟨rL, -, -, -, hfr, -⟩ := hL.rest
  have hF : L.Free (upd G 0 g) := LockWord.Free.of_held fun u => by
    show (upd G 0 g u).1.ph.held = false
    by_cases h0 : u = 0
    · subst h0; rw [upd_self, hg]; rfl
    · rw [upd_ne _ _ h0]; exact hfree u h0
  obtain ⟨⟨v, ⟨A, S, K, bs, -, hsz, -, ⟨b, hb, -, hl⟩, -⟩, -, -⟩, hown, -⟩ := hfr hF
  cases hb
  have hcell : rL.excl (1, 0) ≠ none := Res.excl_of_erase (by
    rw [hl (1, 0), if_pos ⟨rfl, by simp [resPtr], by simp [resPtr, hsz]; decide⟩]; simp)
  obtain ⟨hts, hany⟩ := m3_write
  obtain ⟨e, he, hp⟩ := Array.any_eq_true'.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Array.all_eq_true',
    Bool.or_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨hb1, ho1⟩, hl1⟩, -⟩, hc1⟩, hrel⟩ := hp
  rcases hown e he (fun h => by cases h) (.inl ⟨0, by omega, by omega, by rw [hb1]; exact hcell⟩)
    with hlive | ⟨i, l, ⟨hf, hli⟩, hle⟩
  · have := hlive 1 (by omega) (by
      show (upd G 0 g 1).1.ph ≠ .gone
      rw [upd_ne _ _ (by decide)]; exact h1)
    rw [hc1] at this; cases this
  · obtain ⟨hi', hpi, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    have hm : m3.atomics[i] = l := by
      rw [Array.getElem?_eq_getElem hi'] at hli; exact Option.some.inj hli
    have := hrel l (hm ▸ Array.getElem_mem hi')
    simp only [Bool.and_eq_true, beq_iff_eq] at hpi
    rw [hm] at hpi
    rcases this with h | h
    · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
      rcases h with h | h
      · exact h hpi.1
      · exact h hpi.2
    · rw [hle] at h; cases h

/-- **A relaxed `unlock` fails `MutexImpl.unlock_wp`** (module doc). -/
theorem relaxed_unlock_not_wp : ¬ UnlockWp := by
  intro H
  obtain ⟨rP, hi0⟩ := start_inv
  -- 1. thread 0 takes the lock: `cmpxchg(0 → 1)` with acquire
  have hcas := FLock.wp_casOn fits st rfl (s := ()) (t := 0) (G := G0 rP) (m := mF) (n := 2 + 1)
    (g := G0 rP 0) rfl trivial trivial (by rw [upd_same]; exact hi0)
    (Q := fun r G₁ m' _ => r.1 = none → m'.current = 0 ∧
      ∃ rL, P.inv (upd G₁ 0 (L.set (G0 rP 0) .holds rL)) m')
    (fun _ _ G₁ m' r hcur hcase hr => by
      rcases hcase with ⟨-, rL, hi⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · exact ⟨hcur, rL, hi⟩
      · rw [e] at hr; cases hr
      · rw [e] at hr; cases hr)
  unfold cmpxchgAsC at hcas
  rw [pickCall_eq] at hcas
  obtain ⟨g1, hig1, hk1⟩ := wp_pick_inv hcas
  have hc1 := hk1 (upd (G0 rP) 0 g1) mF (upd_self _ _ _) hig1 (by decide +kernel) 0
    (.inl cas_count)
  have hc1 := wp_pure_inv (wp_liftMem_bind_inv (f := fun a => pure (a, ())) hc1
    (run_of_value cas_value) (by decide +kernel))
  obtain ⟨hcur1, rL1, hi1⟩ := hc1 rfl
  -- 2. thread 0 writes `7` to the resource
  let G' := upd (upd (G0 rP) 0 g1) 0 (L.set (G0 rP 0) .holds rL1)
  have hst := FLock.Fits.wp_hold fits (x := Zig.store 8 resPtr (7 : BitVec 64)) (G := G')
    (G' := G') (t := 0) (m := m1) (d := 2) (g' := fun r => L.set (G0 rP 0) .holds r)
    (Q := fun _ _ m' _ => m'.current = 0 ∧ ∃ r, P.inv (upd G' 0 (L.set (G0 rP 0) .holds r)) m')
    hi1 hcur1 (by simp only [G', upd_self]; rfl) store_spec (fun _ h => h) (fun _ _ h => ⟨_, h⟩)
    (fun _ => ⟨rfl, by simp only [G', upd_self]; rfl, rfl⟩) (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ r hc _ _ hi => ⟨hc, r, hi⟩)
  obtain ⟨hcur2, r2, hi2⟩ := wp_liftMem_inv hst (run_of_value store_value)
  -- 3. thread 0 runs the relaxed unlock (the hypothesis)
  have hu := H fits rfl L.ptr rfl rfl 0 (L.set (G0 rP 0) .holds r2) rfl trivial default G' m2
    (1 + 1) hi2 hcur2
  unfold relaxedUnlock at hu
  obtain ⟨g3, hig3, hk3⟩ := wp_pick_inv hu
  have hc3 := hk3 (upd G' 0 g3) m2 (upd_self _ _ _) hig3 (by decide +kernel) 0 (.inl xchg_count)
  have hc3 := wp_liftMem_bind_inv hc3 (run_of_value xchg_value) (by decide +kernel)
  obtain ⟨-, -, hi3⟩ := wp_pure_inv hc3
  refine no_inv_after _ _ rfl (fun u hu => ?_) ?_ hi3
  · simp only [G', upd, hu, ↓reduceIte]
    by_cases h1 : u = 1 <;> simp [G0, hu, h1] <;> rfl
  · simp [G', upd, G0]

/-- **No `MutexImpl` has the relaxed unlock** (`Io.Mutex`'s contended value `2`). -/
theorem no_relaxed_mutexImpl : ¬ ∃ mi : MutexImpl Unit, mi.unlock = relaxedUnlock ∧ mi.c = 2 := by
  rintro ⟨mi, hu, hc⟩
  refine relaxed_unlock_not_wp fun hF hcost p hp hLc t g hg hok io G m d hi hcur => ?_
  rw [← hu]
  exact mi.unlock_wp hF hcost hp (hLc.trans hc.symm) t g hg hok io G m d hi hcur

end Zig.RelaxedUnlockCX

#print axioms Zig.RelaxedUnlockCX.relaxed_unlock_not_wp
#print axioms Zig.RelaxedUnlockCX.no_relaxed_mutexImpl
