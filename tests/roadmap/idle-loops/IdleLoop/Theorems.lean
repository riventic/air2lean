import IdleLoop.Steps
import ZigLean.Conc.Total

/-!
# Safety, progress under a fairness premise, and starvation

The client of `IdleLoop/Basic.lean` runs the translated `progress.idle` in a worker that
waits for `main`'s release store, then checks `data`.

- **Safety** (`idle_safe`): under every oracle and every fuel, no run gives an error. In
  particular the worker never reads a value of `data` other than 42 (that would be a panic),
  and no access races. Runs without a result are allowed: the flag may never be set.
- **Progress** (`idle_progress`): if the oracle is eventually cooperative (`Cooperative`), the
  run returns for every large enough fuel. `main` returns only after joining the worker, and
  the worker ends only after its idle loop exits.
- **Starvation** (`idle_starves`): the oracle `fun _ => 1` always runs the worker while it is
  ready. The worker spins and yields forever, `main` never stores, and no fuel gives a result.
  So progress is not a consequence of the hints (`progress_needs_premise`).
-/

namespace IdleLoop.Client

open Zig Zig.Conc Zig.Conc.Proto

variable {σ : Placement}

/-! ## The first turn -/

/-- `main` after the fork. -/
def mem1 (σ : Placement) : Mem :=
  { ({ (mem0 σ) with current := 0 } : Mem) with
    clocks := (({ (mem0 σ) with current := 0 } : Mem).clocks.set! 0
      (VClock.bump (({ (mem0 σ) with current := 0 } : Mem).clocks[0]!) 0)).push
        (VClock.bump (({ (mem0 σ) with current := 0 } : Mem).clocks[0]!) 0)
    threads := ({ (mem0 σ) with current := 0 } : Mem).threads.push { spawner := 0, joined := false } }

/-- Both globals at program start, for every placement: only the alignment of their addresses is
known. -/
theorem mem0_block (b : Nat) (hb : b = 0 ∨ b = 1) :
    ∃ A, A % 4 = 0 ∧ (mem0 σ).blocks[b]? = some ⟨Enc.encode 0#32, 4, .global, true, A⟩ := by
  obtain ⟨A, h⟩ : ∃ A, (mem0 σ).blocks[b]? = some ⟨Enc.encode 0#32, 4, .global, true, A⟩ := by
    rcases hb with rfl | rfl <;> exact ⟨_, by simp [mem0, Mem.ofGlobals_getElem?]; rfl⟩
  exact ⟨A, by simpa using Mem.ofGlobals_addr_mod h (by simp), h⟩

theorem gblk_mem1 (b : Nat) (hb : b = 0 ∨ b = 1) : GBlk (mem1 σ) b := by
  obtain ⟨A, hA, h⟩ := mem0_block (σ := σ) b hb
  exact ⟨_, h, rfl, size_encode_u32 0, rfl, hA⟩

theorem mem1_fp : (mem1 σ).footprint = #[] := rfl

theorem mem1_cur : (mem1 σ).current = 0 := rfl

/-- `main`'s write of 42 to `data`, just after the fork. -/
theorem store_mem1 : ∃ blk, (mem1 σ).blocks[0]? = some blk ∧ blk.bytes.size = 4 ∧
    (store 4 dPtr (42 : BitVec 32)).run (mem1 σ) =
      pure ((), ((mem1 σ).recordAt 0 0 4 .write).write 0 blk 0 (Enc.encode (42 : BitVec 32))) := by
  obtain ⟨blk, hb, hk, hs, hacc⟩ := acc_g (gblk_mem1 0 (.inl rfl)) (len := Enc.size (BitVec 32))
    (by decide)
  refine ⟨blk, hb, hs, ?_⟩
  exact store_run (p := dPtr) (42 : BitVec 32) hacc (by rw [hk]; decide) rfl

/-- The memory after `main`'s write of `data`. -/
theorem inv_mem2 {blk : Block} (hb : (mem1 σ).blocks[0]? = some blk) (hs : blk.bytes.size = 4) :
    Inv false (((mem1 σ).recordAt 0 0 4 .write).write 0 blk 0 (Enc.encode (42 : BitVec 32))) := by
  have hb' : ((mem1 σ).recordAt 0 0 4 .write).blocks[0]? = some blk := by
    simpa [Mem.recordAt] using hb
  have hfit : 0 + (Enc.encode (42 : BitVec 32)).size ≤ blk.bytes.size := by
    rw [size_encode_u32, hs]; omega
  have hcs : (mem1 σ).clocks.size = 2 := by simp [mem1, mem0]
  have hbl : ((mem1 σ).recordAt 0 0 4 .write).blocks = (mem1 σ).blocks := by
    simp [Mem.recordAt]
  have hthr : (((mem1 σ).recordAt 0 0 4 .write).write 0 blk 0
      (Enc.encode (42 : BitVec 32))).threads = thr0 := by
    simp [Mem.write, Mem.recordAt, mem1, mem0, thr0]
  have hcs' : (((mem1 σ).recordAt 0 0 4 .write).write 0 blk 0
      (Enc.encode (42 : BitVec 32))).clocks.size = 2 := by
    simp [Mem.write, Mem.recordAt, mem1, mem0]
  refine {
    thr := hthr
    csize := hcs'
    b0 := GBlk.write hb' hfit ((gblk_mem1 0 (.inl rfl)).congr hbl)
    b1 := GBlk.write hb' hfit ((gblk_mem1 1 (.inr rfl)).congr hbl)
    data := ?_
    flag := .inl ⟨rfl, rfl, ?_⟩
    fp := ?_
    own := ?_ }
  · unfold U32At
    have := curBytes_write_same hb' hfit
    rw [size_encode_u32] at this
    rw [this]
    exact intOfBytes_rmw 42
  · unfold U32At
    rw [curBytes_write_other hb' hfit (.inl (by decide))]
    obtain ⟨A₁, -, hb1⟩ := mem0_block (σ := σ) 1 (.inr rfl)
    replace hb1 : ((mem1 σ).recordAt 0 0 4 .write).blocks[1]? = some
        { bytes := Enc.encode (0 : BitVec 32), align := 4, kind := .global, live := true,
          addr := A₁ } := hb1
    have hc : curBytes ((mem1 σ).recordAt 0 0 4 .write) 1 0 4 = Enc.encode (0 : BitVec 32) := by
      unfold curBytes
      rw [hb1]
      simp only [Option.map_some, Option.getD_some]
      rw [show (4 : Nat) = (Enc.encode (0 : BitVec 32)).size from (size_encode_u32 0).symm]
      simp
    rw [hc]
    exact intOfBytes_rmw 0
  · intro e he
    simp only [Mem.write, Mem.recordAt, mem1_fp, Array.mem_push] at he
    simp at he
    subst he
    exact .inl ⟨rfl, rfl, rfl⟩
  · intro e he
    simp only [Mem.write, Mem.recordAt, mem1_fp, Array.mem_push] at he
    simp at he
    subst he
    refine ⟨by simp [mem1], ?_⟩
    simp only [Mem.write, Mem.recordAt, mem1_cur]
    rw [getElem!_set!_ite]
    simp [hcs, VClock.le_refl]

theorem ready_first {F : Nat} (s : Sched.State Tgt Unit)
    (hm : s.main = .paused ⟨F, .spawn .worker, fun h m => publish h F m⟩) (hk : s.kids = #[]) :
    s.ready = #[0] := by
  unfold Sched.State.ready
  rw [hm, hk]
  rfl

/-- The scheduler state after the fork. -/
def sFork (σ : Placement) (F : Nat) : Sched.State Tgt Unit :=
  { main := .paused ⟨F, .spawn .worker, fun h m => publish h F m⟩,
    kids := #[workerTS .start F], mem := (mem1 σ), step := 1, trace := #[1] }

/-- The run up to `main`'s pick of its store: the first turn spawns the worker and writes
`data`. -/
theorem run_eq (F : Nat) (o : Nat → Nat) :
    (Sched.run dispatch (F + 1) o main (mem0 σ)).run =
      (match Sched.settle 0 (sFork σ F) (publish 1 F (mem1 σ)) with
        | .error e => Sched.outOf e
        | .ok (_, some v, s') => some (.ok (v, s'.mem))
        | .ok (ts, none, s') => (Sched.go dispatch o F { s' with main := ts }).1) := by
  let s0 : Sched.State Tgt Unit :=
    { main := .paused ⟨F, .spawn .worker, fun h m => publish h F m⟩, kids := #[],
      mem := { (mem0 σ) with current := 0 }, step := 0, trace := #[] }
  have hr : (Sched.run dispatch (F + 1) o main (mem0 σ)).run = (Sched.go dispatch o (F + 1) s0).1 := rfl
  have hready : s0.ready = #[0] := ready_first s0 rfl rfl
  have hne : s0.ready.isEmpty = false := by rw [hready]; rfl
  rw [hr, go_main o hne (pick_one o s0 hready) rfl, choose_snd, hready]
  rfl

/-- A run with at least two turns reaches `main`'s store pick and the worker's start. -/
theorem run_init (F : Nat) (o : Nat → Nat) :
    ∃ s1, At (F + 1) .store .start s1 ∧ s1.step = 1 ∧
      (Sched.run dispatch (F + 2) o main (mem0 σ)).run = (Sched.go dispatch o (F + 1) s1).1 := by
  obtain ⟨blk, hb, hs, hst⟩ := store_mem1
  rw [run_eq (F + 1) o]
  have hpub : publish 1 (F + 1) (mem1 σ) = .sync (.pick storeCnt)
      (((mem1 σ).recordAt 0 0 4 .write).write 0 blk 0 (Enc.encode (42 : BitVec 32)))
      fun c m => mainStore c 1 F m := by
    show (CoN.leaf ((store 4 dPtr (42 : BitVec 32)).run (mem1 σ))).bind _ = _
    rw [hst]; rfl
  rw [hpub]
  let M2 := ((mem1 σ).recordAt 0 0 4 .write).write 0 blk 0 (Enc.encode (42 : BitVec 32))
  exact ⟨{ sFork σ (F + 1) with main := .paused (mainP .store F), mem := M2 },
    ⟨F, F + 1, rfl, rfl, inv_mem2 hb hs, by omega, by omega, fun h => by cases h⟩, rfl, rfl⟩

/-- With one turn the run has no result. -/
theorem run_one (o : Nat → Nat) : (Sched.run dispatch 1 o main (mem0 σ)).run = none := by
  obtain ⟨blk, hb, hs, hst⟩ := store_mem1
  rw [run_eq 0 o]
  have hpub : publish 1 0 (mem1 σ) = .leaf none := by
    show (CoN.leaf ((store 4 dPtr (42 : BitVec 32)).run (mem1 σ))).bind _ = _
    rw [hst]; rfl
  rw [hpub]
  rfl

theorem run_zero (o : Nat → Nat) : (Sched.run dispatch 0 o main (mem0 σ)).run = none := rfl

/-! ## Safety under every schedule -/

theorem go_safe (o : Nat → Nat) : ∀ f mp wp (s : Sched.State Tgt Unit), At f mp wp s →
    ∀ e, (Sched.go dispatch o f s).1 ≠ some (.error e) := by
  intro f
  induction f with
  | zero => intro _ _ s _ e h; cases s; simp [Sched.go] at h
  | succ f ih =>
    intro mp wp s hA e h
    rcases turn o hA with ⟨-, hn⟩ | ⟨M, hm⟩ | ⟨mp', wp', s', hA', -, he⟩
    · rw [hn] at h; cases h
    · rw [hm] at h; cases h
    · rw [he] at h; exact ih mp' wp' s' hA' e h

/-- **Safety.** No schedule and no fuel gives an error: no panic (so the worker reads 42 after
the idle loop), no race and no deadlock. A run without a result is allowed. -/
theorem idle_safe (fuel : Nat) (o : Nat → Nat) (e : Error) :
    (Sched.run dispatch fuel o main (mem0 σ)).run ≠ some (.error e) := by
  match fuel with
  | 0 => rw [run_zero]; simp
  | 1 => rw [run_one]; simp
  | F + 2 =>
    obtain ⟨s1, hA, -, hr⟩ := run_init F o
    rw [hr]
    exact go_safe o _ _ _ _ hA e

/-! ## Starvation without a fairness premise -/

/-- The oracle that always prefers the worker while both threads are ready. -/
def favorWorker : Nat → Nat := fun _ => 1

theorem go_starve : ∀ f wp (s : Sched.State Tgt Unit), At f .store wp s →
    (Sched.go dispatch favorWorker f s).1 = none := by
  intro f
  induction f with
  | zero => intro _ s _; cases s; simp [Sched.go]
  | succ f ih =>
    intro wp s hA
    rcases ready_ne hA with ⟨-, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
      have hw : wp ≠ .done := fun h => by obtain ⟨-, -, -, -, -, -, -, h'⟩ := hA; cases h' h
      rcases pick_two favorWorker s hr with ⟨-, h2⟩ | ⟨hsel, -⟩
      · simp [favorWorker] at h2
      · obtain ⟨wp', s', hA', -, he, -⟩ := wstep favorWorker hA hw hne hsel
        rw [he]; exact ih wp' s' hA'
    · cases h
    · cases h

/-- **Starvation.** Under `favorWorker` the run has no result for any fuel: the worker executes
its spin hint and `Thread.yield` in every iteration, and neither hands the processor to `main`. -/
theorem idle_starves (fuel : Nat) : (Sched.run dispatch fuel favorWorker main (mem0 σ)).run = none := by
  match fuel with
  | 0 => exact run_zero _
  | 1 => exact run_one _
  | F + 2 =>
    obtain ⟨s1, hA, -, hr⟩ := run_init F favorWorker
    rw [hr]
    exact go_starve _ _ _ hA

/-! ## Progress under a fairness premise -/

/-- **The fairness premise (THR-09).** From some oracle index on, every choice is option 0:
the scheduler runs the lowest-numbered ready thread (here the setter, `main`), and every atomic
load reads the newest message. -/
def Cooperative (o : Nat → Nat) : Prop := ∃ N, ∀ j, N ≤ j → o j = 0

/-- The turns left before the run ends under a cooperative oracle. -/
def wpot : WorkerAt → Nat
  | .start => 2
  | .load => 1
  | .spin => 3
  | .yld => 2
  | .done => 0

def pot : MainAt → WorkerAt → Nat
  | .store, wp => wpot wp + 2
  | .join, wp => wpot wp + 1

theorem pot_le (mp : MainAt) (wp : WorkerAt) : pot mp wp ≤ 5 := by
  cases mp <;> cases wp <;> decide

theorem go_tail (o : Nat → Nat) (N : Nat) (hN : ∀ j, N ≤ j → o j = 0) :
    ∀ f mp wp (s : Sched.State Tgt Unit), At f mp wp s → N ≤ s.step → pot mp wp < f →
      ∃ M, (Sched.go dispatch o f s).1 = some (.ok ((), M)) := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ h; omega
  | succ f ih =>
    intro mp wp s hA hs hp
    rcases ready_ne hA with ⟨rfl, hr⟩ | ⟨rfl, hw, hr⟩ | ⟨rfl, rfl, hr⟩
    · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
      rcases pick_two o s hr with ⟨hsel, -⟩ | ⟨-, h2⟩
      · rcases mstore o hA hne hsel with ⟨h0, -⟩ | ⟨s', hA', hs', he⟩
        · subst h0; simp [pot] at hp
        · rw [he]
          exact ih .join wp s' hA' (by omega) (by simp [pot] at hp ⊢; omega)
      · rw [hN s.step hs] at h2; cases h2
    · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
      obtain ⟨wp', s', hA', hs', he, h1, h2, h3, -, h5⟩ := wstep o hA hw hne (pick_one o s hr)
      rw [he]
      refine ih .join wp' s' hA' (by omega) ?_
      cases wp with
      | start => rw [h1 rfl]; simp [pot, wpot] at hp ⊢; omega
      | spin => rw [h2 rfl]; simp [pot, wpot] at hp ⊢; omega
      | yld => rw [h3 rfl]; simp [pot, wpot] at hp ⊢; omega
      | load => rw [h5 rfl rfl (hN _ (by omega))]; simp [pot, wpot] at hp ⊢; omega
      | done => exact absurd rfl hw
    · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
      exact mjoin o hA hne (pick_one o s hr)

theorem go_eventually (o : Nat → Nat) (N : Nat) (hN : ∀ j, N ≤ j → o j = 0) :
    ∀ k f mp wp (s : Sched.State Tgt Unit), At f mp wp s → N ≤ s.step + k → k + 6 ≤ f →
      ∃ M, (Sched.go dispatch o f s).1 = some (.ok ((), M)) := by
  intro k
  induction k with
  | zero =>
    intro f mp wp s hA hs hf
    exact go_tail o N hN f mp wp s hA (by omega) (by have := pot_le mp wp; omega)
  | succ k ih =>
    intro f mp wp s hA hs hf
    by_cases hN' : N ≤ s.step
    · exact go_tail o N hN f mp wp s hA hN' (by have := pot_le mp wp; omega)
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rcases turn o hA with ⟨h0, -⟩ | h | ⟨mp', wp', s', hA', hs', he⟩
    · omega
    · exact h
    · rw [he]; exact ih f mp' wp' s' hA' (by omega) (by omega)

/-- **Progress under the fairness premise.** For an eventually cooperative oracle, every large
enough fuel gives a result: `main` joined the worker, so the translated idle loop exited. -/
theorem idle_progress (o : Nat → Nat) (hfair : Cooperative o) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ∃ M, (Sched.run dispatch fuel o main (mem0 σ)).run = some (.ok ((), M)) := by
  obtain ⟨N, hN⟩ := hfair
  refine ⟨N + 8, fun fuel hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F, fuel = F + 2 := ⟨fuel - 2, by omega⟩
  obtain ⟨s1, hA, hs1, hr⟩ := run_init F o
  rw [hr]
  exact go_eventually o N hN N (F + 1) .store .start s1 hA (by omega) (by omega)

/-! ## The premise is needed, and satisfiable -/

theorem favorWorker_not_cooperative : ¬ Cooperative favorWorker := by
  rintro ⟨N, hN⟩
  exact absurd (hN N (Nat.le_refl _)) (by simp [favorWorker])

theorem zero_cooperative : Cooperative (fun _ => 0) := ⟨0, fun _ _ => rfl⟩

/-- **Progress is not derivable without the premise**: the conclusion of `idle_progress` fails
for the legal oracle `favorWorker`. Equivalently, the client is not totally correct in the
sense of `Zig.Conc.Total.EventuallyReturns`. -/
theorem progress_needs_premise :
    ¬ ∀ o : Nat → Nat, ∃ bound, ∀ fuel, bound ≤ fuel →
      ∃ M, (Sched.run dispatch fuel o main (mem0 σ)).run = some (.ok ((), M)) := by
  intro h
  obtain ⟨b, hb⟩ := h favorWorker
  obtain ⟨M, hM⟩ := hb b (Nat.le_refl _)
  rw [idle_starves] at hM
  cases hM

theorem not_eventuallyReturns :
    ¬ Zig.Conc.Total.EventuallyReturns dispatch main (mem0 σ) (fun _ _ => True) := by
  intro h
  obtain ⟨b, hb⟩ := h favorWorker
  obtain ⟨v, m', hr, -⟩ := hb b (Nat.le_refl _)
  rw [idle_starves] at hr
  cases hr

end IdleLoop.Client
