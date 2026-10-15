import Proofs.Cancel.Client
import ZigLean.Conc.Lemmas
import ZigLean.Conc.Progress
import ZigLean.Sep.Full.ThreadOwned
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Sep.Full.Local
import ZigLean.Sep.Full.Auto

/-!
# `cancelClient` over all schedules (C05)

`cancelClient` (`Proofs/Cancel/Client.lean`) makes two heap words `status = 0` and `done = 0`,
runs `worker(status, done)` as a task of an `Io.Group`, gives the task a chance to run
(`spinLoopHint`), cancels the group, reads both words and frees every block. The worker passes
three cancelation points (`Io.futexWait` on a word that does not hold the expected value); after
each it does one step (`done = i + 1`). It writes `status = 1` when it completed all three
steps, and `status = 2` when a cancelation point returned `error.Canceled`.

**Results** (every oracle, every fuel; `cancelClient_spec`):

- the result `(status, done)` satisfies `Outcome`: `(1, 3)` (completed, all work done) or
  `(2, d)` with `d < 3` (canceled, work left). A canceled task is never reported as a completed
  one, and a completion is never reported for unfinished work;
- `main` gets the task's two words back at the join that `Group.cancel` does (`FOwned.fork`
  hands them over at the spawn, `FOwned.join` returns them) and frees them: when `main` returns,
  no byte of the heap is live (`m.heap = Heap.empty`), so cancelation loses no owned resource.

The proof is partial correctness (`run_sound`): a run that gives an error or no result satisfies
the spec. `Proofs/Cancel/Client.lean` and `tests/roadmap/cancellation/Runtime.lean` show that
both outcomes happen and that sampled schedules give no error.

It is in the full-state concurrent separation logic (`docs/sep-threads.md`): a word is its
bytes with its block's full extent (`word`), a thread's `MemM` step is a thread triple
(`FTTriple`) on its part, and the parts are `FOwned`'s.

**Protocol.** A thread's ghost value (`Gh`) is `main` at a phase (`MPh`: at its spawn, at its
spin hint, at its join) with the resource it owns, the task's words `W` and the group `g`, or the
task with the resource it owns, the values of its words and whether it ended. The invariant
(`Inv`): the parts (`FOwned`, next to the start memory's empty rest: every live byte belongs to a
part, `FOwned.cover`), the task's part holds its two words with values allowed by `TaskOk`, and
the threads and the group's tasks at each phase of `main` (`Shape`). The cancelation state
(`Mem.cancels`), the futex queue and `current` are not in the invariant: every step that changes
only them keeps it (`inv_keep`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Cancel.Group

-- Unification must not unfold `WP` into the program (as in `Proofs/Threads/Disjoint.lean`).
attribute [local irreducible] Proto.WP

/-! ## Words -/

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- A 4-byte heap word at `p` (address `A`, block `k`) that holds `v`, with its block's extent. -/
abbrev word (p : Ptr) (A : Nat) (v : BitVec 32) (k : BlockId) : FAssn :=
  up (bytesAt p A 4 .heap (Enc.encode v)) ⋆ bext k 4 .heap

theorem decode_u32 (v : BitVec 32) :
    Enc.decode ((Enc.encode v).extract 0 (0 + Enc.size (BitVec 32))) =
      (pure v : Result (BitVec 32)) := by
  rw [show 0 + Enc.size (BitVec 32) = (Enc.encode v).size from (enc_u32 v).symm,
    Array.extract_size]
  exact LawfulEnc.decode_encode v

theorem word_init {p : Ptr} {A : Nat} {k : BlockId} (hpb : p.block = some k) (h0 : p.off = 0)
    (hA : A % 4 = 0) (w : BitVec 32) :
    FTTriple (up (bytesAt p A 4 .heap (Array.replicate 4 .undef)) ⋆ bext k 4 .heap)
      (Zig.store 4 p w) (fun _ => word p A w k) :=
  (FTTriple.storeAt (k := 0) (a := 4) w hpb (by simp [Ptr.add]) (by decide) (by simp; decide)
    (by simp [h0, hA]) (by decide)).post fun _ _ h => by
      rwa [writeBytes_all (by simp [enc_u32])] at h

theorem word_store {p : Ptr} {A : Nat} {v : BitVec 32} {k : BlockId} (hpb : p.block = some k)
    (h0 : p.off = 0) (hA : A % 4 = 0) (w : BitVec 32) :
    FTTriple (word p A v k) (Zig.store 4 p w) (fun _ => word p A w k) :=
  (FTTriple.storeAt (k := 0) (a := 4) w hpb (by simp [Ptr.add]) (by decide)
    (by rw [enc_u32]; decide) (by simp [h0, hA]) (by decide)).post fun _ _ h => by
      rwa [writeBytes_all (by rw [enc_u32, enc_u32])] at h

theorem word_load {p : Ptr} {A : Nat} {v : BitVec 32} {k : BlockId} (hpb : p.block = some k)
    (h0 : p.off = 0) (hA : A % 4 = 0) :
    FTTriple (word p A v k) (Zig.load (BitVec 32) 4 p) (fun r => ⟪r = v⟫ ⋆ word p A v k) := by
  fsym [FTotalTriple.loadBlock (T := BitVec 32) (A := A) (S := 4) (K := .heap) (al := 4) hpb
    (by decide) (by rw [enc_u32]; decide) (decode_u32 v) (by simp [h0, hA])]

/-- The bytes of a word belong to its resource. -/
theorem word_owns {p : Ptr} {A : Nat} {v : BitVec 32} {k : BlockId} {r : Res}
    (hpb : p.block = some k) (h : word p A v k r) :
    ∀ x, p.off.toNat ≤ x → x < p.off.toNat + 4 → r.heap (k, x) ≠ none := by
  obtain ⟨r₁, r₂, -, rfl, ⟨⟨b, hb, -, hl⟩, -, -⟩, -⟩ := h
  rw [hpb] at hb; cases hb
  intro x h1 h2
  have hx := hl (k, x)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, h1, by rw [enc_u32]; exact h2⟩)] at hx
  simp only [FHeap.union_apply]
  cases e : r₁.heap (k, x) with
  | none => simp [FHeap.erase, e] at hx
  | some _ => simp

/-! ## Protocol -/

/-- The task's two words: `status` at `st` (address `As`, block `ks`), the steps done at `dn`
(`Ad`, `kd`). -/
structure Words where
  st : Ptr
  dn : Ptr
  As : Nat
  Ad : Nat
  ks : BlockId
  kd : BlockId

def Words.Ok (W : Words) : Prop :=
  W.st.block = some W.ks ∧ W.dn.block = some W.kd ∧ W.st.off = 0 ∧ W.dn.off = 0 ∧ W.As % 4 = 0 ∧
    W.Ad % 4 = 0

/-- The two words hold `s` and `d`. -/
def Words.A (W : Words) (s d : BitVec 32) : FAssn := word W.st W.As s W.ks ⋆ word W.dn W.Ad d W.kd

/-- The values of the task's words: while it runs, `status = 0` and at most three steps are
done; when it has ended, `Outcome`. -/
def TaskOk (s d : BitVec 32) : Bool → Prop
  | false => s = 0 ∧ d.toNat ≤ 3
  | true => Outcome (s, d)

/-- Where `main` is: at its spawn, at its spin hint, at its join. -/
inductive MPh where
  | spawn | hint | join
  deriving DecidableEq

/-- A thread's ghost value. -/
inductive Gh where
  | none
  | main (ph : MPh) (r : Res) (W : Words) (g : Ptr)
  | task (r : Res) (W : Words) (s d : BitVec 32) (ended : Bool)

/-- The resource that a thread owns. -/
def Gh.res : Gh → Res
  | .main _ r _ _ | .task r _ _ _ _ => r
  | .none => rnil

/-- The parts of the threads: a joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Res :=
  if joinedB m u then rnil else (G u).res

/-- The protocol's rest: the start memory's (empty) heap, and the plain mode
(`FOwned.start_plainRest`; `main` copies it for its stack block, `FOwned.dupPlain`). -/
abbrev rO : Res := ⟨({} : Mem).fheap, Know.none, Ghost.plain⟩

/-- The threads and the group at each phase of `main`. -/
def Shape (W : Words) (g : Ptr) (G : ThreadId → Gh) (m : Mem) : MPh → Prop
  | .spawn => m.threads.size = 1 ∧ m.groups = #[] ∧ ∀ u, 1 ≤ u → G u = .none
  | .hint => m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
      m.groups = #[(g, 1)] ∧ (∃ r s d e, G 1 = .task r W s d e) ∧ ∀ u, 2 ≤ u → G u = .none
  | .join => m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
      (∃ r s d e, G 1 = .task r W s d e) ∧ ∀ u, 2 ≤ u → G u = .none

/-- The invariant (module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : FOwned (ownOf G m) rO m
  task : ∀ u r W s d e, G u = .task r W s d e → W.Ok ∧ W.A s d r ∧ TaskOk s d e
  main : ∃ ph r W g, G 0 = .main ph r W g ∧ Shape W g G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol (partial correctness). -/
def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .worker st dn => ∃ r W, g = .task r W 0 0 false ∧ W.st = st ∧ W.dn = dn
  fin g := ∃ r W s d, g = .task r W s d true

/-- `main`'s post: the declared outcome, and no live byte is left. -/
def QM : BitVec 32 × BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun r _ m _ => Outcome r ∧ m.heap = Heap.empty

/-! ## Frames -/

theorem joinedB_congr {m m' : Mem} (ht : m'.threads = m.threads) : joinedB m' = joinedB m := by
  funext u; simp only [joinedB, ht]

/-- A step that changes no block, atomic location, thread, clock or recorded access (only
`current`, the futex queue, the cancelation requests or the groups) keeps the invariant if it
keeps the groups. -/
theorem inv_keep {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m)
    (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hf : m'.footprint = m.footprint) (hg : m'.groups = m.groups)
    (hx : m.Aux m' := by exact ⟨rfl, rfl, rfl⟩) :
    Inv G m' := by
  have hown : ownOf G m' = ownOf G m := by funext u; simp only [ownOf, joinedB_congr ht]
  refine ⟨hown ▸ hi.own.keep hb ha ht hc hf hx, hi.task, ?_, ?_⟩
  · obtain ⟨ph, r, W, g, h0, hs⟩ := hi.main
    refine ⟨ph, r, W, g, h0, ?_⟩
    cases ph with
    | spawn => exact ⟨by rw [ht]; exact hs.1, by rw [hg]; exact hs.2.1, hs.2.2⟩
    | hint => exact ⟨by rw [ht]; exact hs.1, by rw [ht]; exact hs.2.1, by rw [hg]; exact hs.2.2.1,
        hs.2.2.2⟩
    | join => exact ⟨by rw [ht]; exact hs.1, by rw [ht]; exact hs.2.1, hs.2.2⟩
  · rw [ht]; exact hi.t0

/-! ## The task -/

/-- A task is thread 1, not joined, and `main` is at its spin hint or at its join. -/
theorem task_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {r W s d e}
    (hi : Inv G m) (hg : G u = .task r W s d e) :
    u = 1 ∧ joinedB m 1 = false ∧ m.threads.size = 2 := by
  obtain ⟨ph, hm, W', g, h0, hs⟩ := hi.main
  have hu0 : u ≠ 0 := fun e => by subst e; rw [h0] at hg; cases hg
  have hrec : m.threads[1]? = some { spawner := 0, joined := false } → joinedB m 1 = false := by
    intro hr; simp [joinedB, hr]
  cases ph with
  | spawn =>
    have := hs.2.2 u (by unfold ThreadId at *; omega); rw [hg] at this; cases this
  | hint =>
    obtain ⟨hsz, hr, -, -, hn⟩ := hs
    have hu1 : u = 1 := by
      by_cases h2 : 2 ≤ u
      · have := hn u h2; rw [hg] at this; cases this
      · unfold ThreadId at *; omega
    exact ⟨hu1, hrec hr, hsz⟩
  | join =>
    obtain ⟨hsz, hr, -, hn⟩ := hs
    have hu1 : u = 1 := by
      by_cases h2 : 2 ≤ u
      · have := hn u h2; rw [hg] at this; cases this
      · unfold ThreadId at *; omega
    exact ⟨hu1, hrec hr, hsz⟩

theorem ownOf_upd {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {g : Gh}
    (ht : m'.threads = m.threads) (hj : joinedB m u = false) :
    ownOf (upd G u g) m' = upd (ownOf G m) u g.res := by
  funext w
  unfold ownOf
  rw [joinedB_congr ht]
  by_cases hw : w = u
  · subst hw; simp only [upd_self]; rw [hj]; rfl
  · rw [upd_ne _ _ hw, upd_ne _ _ hw]

/-- The task's step to the new part `r'` keeps the invariant with its new ghost value. -/
theorem inv_task_step {G : ThreadId → Gh} {m m' : Mem} {r r' : Res} {W : Words}
    {s d s' d' : BitVec 32} {e e' : Bool} (hi : Inv G m) (hg : G 1 = .task r W s d e)
    (ho : FOwned (upd (ownOf G m) 1 r') rO m') (ht : m'.threads = m.threads)
    (hgr : m'.groups = m.groups) (hA : W.A s' d' r') (hok : TaskOk s' d' e') :
    Inv (upd G 1 (.task r' W s' d' e')) m' := by
  obtain ⟨-, hj, -⟩ := task_live hi hg
  have hown := ownOf_upd (G := G) (g := .task r' W s' d' e') ht hj
  refine ⟨by rw [hown]; exact ho, fun u r₁ W₁ s₁ d₁ e₁ hu => ?_, ?_, ?_⟩
  · by_cases h1 : u = 1
    · subst h1; rw [upd_self] at hu; cases hu
      exact ⟨(hi.task 1 _ _ _ _ _ hg).1, hA, hok⟩
    · rw [upd_ne _ _ h1] at hu; exact hi.task u _ _ _ _ _ hu
  · obtain ⟨ph, hm, W', g, h0, hs⟩ := hi.main
    refine ⟨ph, hm, W', g, by rw [upd_ne _ _ (by decide)]; exact h0, ?_⟩
    have hnone : ∀ w, 2 ≤ w → G w = .none → upd G 1 (.task r' W s' d' e') w = .none :=
      fun w hw hn => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn
    cases ph with
    | spawn => have := hs.2.2 1 (Nat.le_refl _); rw [hg] at this; cases this
    | hint =>
      obtain ⟨hsz, hr, hgr0, ⟨r₁, s₁, d₁, e₁, h1⟩, hn⟩ := hs
      rw [hg] at h1; cases h1
      exact ⟨by rw [ht]; exact hsz, by rw [ht]; exact hr, by rw [hgr]; exact hgr0,
        ⟨r', s', d', e', upd_self _ _ _⟩, fun w hw => hnone w hw (hn w hw)⟩
    | join =>
      obtain ⟨hsz, hr, ⟨r₁, s₁, d₁, e₁, h1⟩, hn⟩ := hs
      rw [hg] at h1; cases h1
      exact ⟨by rw [ht]; exact hsz, by rw [ht]; exact hr, ⟨r', s', d', e', upd_self _ _ _⟩,
        fun w hw => hnone w hw (hn w hw)⟩
  · rw [ht]; exact hi.t0

/-! ## Steps that change no heap byte -/

theorem cancelPending_run (m : Mem) : (Thread.cancelPending.run m).run =
    some (.ok (m.current != 0 && m.cancels.contains m.current, m)) := rfl

theorem takeCancel_run (m : Mem) : (Thread.takeCancel.run m).run =
    some (.ok ((), { m with cancels := m.cancels.erase m.current })) := rfl

theorem requestCancel_run (tids : Array ThreadId) (m : Mem) :
    ((Thread.requestCancel tids).run m).run = some (.ok ((), { m with
      cancels := m.cancels ++ tids.filter (· != 0),
      waiters := m.waiters.filter (fun w => !tids.contains w.1),
      woken := m.woken ++ (m.waiters.filter (fun w => tids.contains w.1)).map (·.1) })) := rfl

theorem dropCancels_run (tids : Array ThreadId) (m : Mem) :
    ((Thread.dropCancels tids).run m).run = some (.ok ((), { m with
      cancels := m.cancels.filter (fun u => !tids.contains u) })) := rfl

/-- A `callMC` step whose run is known and keeps the threads. -/
theorem WP.callMC_keep {σ α : Type} {t : ThreadId} {G : ThreadId → Gh} {m m' : Mem} {n : Nat}
    {x : MemM α} {s : σ} {a₀ : α} {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hx : (x.run m).run = some (.ok (a₀, m'))) (h : Q (a₀, s) G m' n)
    (hth : m'.threads = m.threads) : proto.WP t ((callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.callMC (fun e he => by rw [hx] at he; cases he) fun a m'' hr => by
    rw [hx] at hr
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨by rw [hth], h⟩

theorem not_strict : ¬ proto.strict = true := by decide

/-! ## The task's cancelation point -/

theorem wp_lateCancel {G : ThreadId → Gh} {m : Mem} {n : Nat} {gT : Gh}
    (hc : m.current = 1) (hi : Inv (upd G 1 gT) m)
    {Q : Except ErrName Unit × Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ r G' m' k, m'.current = 1 → Inv (upd G' 1 gT) m' → Q (r, ()) G' m' k) :
    proto.WP 1 ((lateCancelC : CM Tgt Unit _).run ()) Q G m n := by
  unfold lateCancelC
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_keep (cancelPending_run m) ?_ rfl)
  dsimp only
  split
  · simp only [StateT.run_bind]
    refine WP.bind (WP.pickC (P := proto) fun k _ => ⟨gT, hi, fun G₂ m₂ hg₂ hi₂ c _ => ?_⟩)
    have hi₂' : Inv (upd G₂ 1 gT) m₂ := by rw [← hg₂, upd_same]; exact hi₂
    dsimp only
    split
    · simp only [StateT.run_bind]
      refine WP.bind (WP.callMC_keep (takeCancel_run _) ?_ rfl)
      exact WP.pure' (hQ _ _ _ _ rfl (inv_keep hi₂' rfl rfl rfl rfl rfl rfl))
    · exact WP.pure' (hQ _ _ _ _ rfl (inv_keep hi₂' rfl rfl rfl rfl rfl rfl))
  · exact WP.pure' (hQ _ _ _ _ hc hi)

/-- The kernel's read of the task's `status` word in a futex wait (a recorded atomic read by the
task, the word's owner) keeps the invariant (`FOwned.recordAt`). -/
theorem inv_read {G : ThreadId → Gh} {m m' : Mem} {r : Res} {W : Words} {s d : BitVec 32}
    {e : Bool} (hc : m.current = 1) (hi : Inv (upd G 1 (.task r W s d e)) m)
    {bid : BlockId} {blk : Block} {o : Nat} (ha : m.access W.st 4 4 = pure (bid, blk, o))
    (hr : ((recordAccess bid o 4 .atomicRead).run m).run = some (.ok ((), m'))) :
    Inv (upd G 1 (.task r W s d e)) m' := by
  obtain ⟨-, rfl⟩ := recordAccess_ok hr
  have hg := upd_self G 1 (Gh.task r W s d e)
  obtain ⟨⟨hsb, -, -, -, -, -⟩, hA, -⟩ := hi.task 1 _ _ _ _ _ hg
  obtain ⟨-, hj, hsz⟩ := task_live hi hg
  have hown : ownOf (upd G 1 (.task r W s d e)) m 1 = r := by simp [ownOf, hj, Gh.res]
  obtain ⟨hpb, hblk, -, -, -, -, rfl⟩ := access_eq ha
  rw [hsb] at hpb; cases hpb
  have hin : ∀ x, W.st.off.toNat ≤ x → x < W.st.off.toNat + 4 →
      (ownOf (upd G 1 (.task r W s d e)) m 1).heap (W.ks, x) ≠ none := by
    rw [hown]
    obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hA
    intro x h1x h2x
    have := word_owns hsb h1 x h1x h2x
    simp only [FHeap.union_apply]
    cases e : r₁.heap (W.ks, x) with
    | none => exact absurd e this
    | some _ => simp
  exact ⟨hi.own.recordAt hc (by rw [hsz]; decide) hin
    (Array.getElem?_eq_some_iff.mp hblk).1, hi.task, hi.main, hi.t0⟩

/-- The task's futex wait at `status` reads the word the task owns, which holds a `u32`: it
throws only errors at which the native program stops (no `.unspecified`; audit
soundness-2026-10-14 S4). -/
theorem wait_native {G : ThreadId → Gh} {m : Mem} {r : Res} {W : Words} {s d : BitVec 32}
    {e : Bool} (hi : Inv (upd G 1 (.task r W s d e)) m) (e' : BitVec 32) (m₀ : Mem)
    (hb₀ : m₀.blocks = m.blocks) :
    ∀ e₁, ((Thread.futexWait W.st e').run m₀).run = some (.error e₁) → e₁.nativeStops := by
  refine Proto.futexWait_native fun b blk o ha => ?_
  have hg := upd_self G 1 (Gh.task r W s d e)
  obtain ⟨⟨hsb, -, h0, -, -, -⟩, hA, -⟩ := hi.task 1 _ _ _ _ _ hg
  obtain ⟨-, hj, hsz⟩ := task_live hi hg
  have hown : ownOf (upd G 1 (.task r W s d e)) m 1 = r := by simp [ownOf, hj, Gh.res]
  obtain ⟨blk', hb', -, -, -, -, hx⟩ := hi.own.bytesOf (t := 1) (by rw [hsz]; decide) hsb
    (by rw [enc_u32]; decide) (hown ▸ hA)
  obtain ⟨hpb, hblk, -, -, -, -, rfl⟩ := access_eq ha
  rw [hsb] at hpb; cases hpb
  rw [hb₀, hb'] at hblk; cases hblk
  rw [h0, enc_u32] at hx
  refine ⟨s, ?_⟩
  have hd : intOfBytes 32 (Enc.encode s) = (pure s : Result (BitVec 32)) := by
    have := LawfulEnc.decode_encode s; exact this
  rw [h0]
  simp only [Int.toNat_zero] at hx ⊢
  rw [hx, hd]; rfl

/-- The task's cancelation point (`io.futexWait(u32, status, 7)`) with the task's ghost value:
whatever it returns, the invariant holds with it. It may sleep, return spuriously, see the value
differ, observe a pending request, or have one delivered. -/
theorem wp_cancelWait {G : ThreadId → Gh} {m : Mem} {n : Nat} {r : Res} {W : Words}
    {s d : BitVec 32} {e : Bool}
    (hc : m.current = 1) (hi : Inv (upd G 1 (.task r W s d e)) m)
    {Q : Except ErrName Unit × Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ x G' m' k, m'.current = 1 → Inv (upd G' 1 (.task r W s d e)) m' → Q (x, ()) G' m' k) :
    proto.WP 1 ((futexWaitCancelableC ⟨⟩ W.st (7 : BitVec 32) : CM Tgt Unit _).run ()) Q G m n := by
  unfold futexWaitCancelableC
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_keep (cancelPending_run m) ?_ rfl)
  dsimp only
  split
  · simp only [StateT.run_bind]
    refine WP.bind (WP.callMC_keep (takeCancel_run _) ?_ rfl)
    exact WP.pure' (hQ _ _ _ _ hc (inv_keep hi rfl rfl rfl rfl rfl rfl))
  · simp only [StateT.run_bind]
    refine WP.bind (WP.futexWaitC (P := proto) fun k _ => ⟨.task r W s d e, hi,
      fun G₁ m₁ hg₁ hi₁ => ⟨fun h => absurd h not_strict, fun _ =>
        ⟨fun h => absurd h not_strict,
          wait_native (G := G₁) (m := m₁) (by rw [← hg₁, upd_same]; exact hi₁) _ _ rfl,
          fun b m' hr => ?_⟩⟩⟩)
    have hi₁' : Inv (upd G₁ 1 (.task r W s d e)) m₁ := by rw [← hg₁, upd_same]; exact hi₁
    have hi₀ : Inv (upd G₁ 1 (.task r W s d e)) { m₁ with current := 1 } :=
      inv_keep hi₁' rfl rfl rfl rfl rfl rfl
    rcases futexWait_ok hr with ⟨-, rfl, rfl⟩ |
      ⟨-, bid, blk, o, v, m₂, ha, hrec, -, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
    all_goals simp only [Bool.false_eq_true, ↓reduceIte]
    · refine wp_lateCancel ?_ ?_ hQ
      · rfl
      · exact inv_keep hi₁' rfl rfl rfl rfl rfl rfl
    · have hI : Inv G₁ m₂ := by
        have := inv_read rfl hi₀ ha hrec
        rwa [← hg₁, upd_same] at this
      refine ⟨inv_keep hI rfl rfl rfl rfl rfl rfl, wp_lateCancel ?_ ?_ hQ⟩
      · rfl
      · exact hi₀
    · refine wp_lateCancel ?_ ?_ hQ
      · rw [(recordAccess_ok hrec).2]; rfl
      · exact inv_read rfl hi₀ ha hrec

/-! ## The task's steps -/

/-- The task's part from the invariant. -/
theorem task_part {G : ThreadId → Gh} {m : Mem} {r : Res} {W : Words} {s d : BitVec 32} {e : Bool}
    (hi : Inv (upd G 1 (.task r W s d e)) m) :
    ownOf (upd G 1 (.task r W s d e)) m 1 = r ∧ W.Ok ∧ W.A s d r ∧ m.threads.size = 2 := by
  have hg := upd_self G 1 (Gh.task r W s d e)
  obtain ⟨hW, hA, -⟩ := hi.task 1 _ _ _ _ _ hg
  obtain ⟨-, hj, hsz⟩ := task_live hi hg
  exact ⟨by simp [ownOf, hj, Gh.res], hW, hA, hsz⟩

/-- The task at its step `i` with `k` steps left: it keeps the invariant at every stop and ends
with `Outcome`. -/
theorem steps_spec (k : Nat) : ∀ (i : Nat) (G : ThreadId → Gh) (m : Mem) (n : Nat) (r : Res)
    (W : Words), i + k = 3 → m.current = 1 →
    Inv (upd G 1 (.task r W 0 (BitVec.ofNat 32 i) false)) m →
    proto.WP 1 ((steps W.st W.dn i k).run ()) (fun a G m d => proto.QKid 1 a.1 G m d) G m n := by
  induction k with
  | zero =>
    intro i G m n r W hik hc hi
    obtain rfl : i = 3 := by omega
    have hg := upd_self G 1 (Gh.task r W 0 (BitVec.ofNat 32 3) false)
    obtain ⟨hown, ⟨hsb, -, hs0, -, hAs, -⟩, hA, hsz⟩ := task_part hi
    simp only [steps]
    refine WP.callMC_fownedS ((word_store hsb hs0 hAs 1).frame) hi.own hc (by rw [hsz]; decide)
      (by rw [hown]; exact hA) fun _ m' r' _ _ ho' hq hs => ?_
    have := inv_task_step hi hg ho' hs.threads hs.groups hq
      (show TaskOk 1 (BitVec.ofNat 32 3) true from .inl ⟨rfl, rfl⟩)
    rw [upd_upd] at this
    exact ⟨_, this, ⟨_, _, _, _, rfl⟩, fun h => absurd h not_strict⟩
  | succ k ih =>
    intro i G m n r W hik hc hi
    simp only [steps, StateT.run_bind]
    refine WP.bind (wp_cancelWait hc hi fun x G' m' k' hc' hi' => ?_)
    have hg' := upd_self G' 1 (Gh.task r W 0 (BitVec.ofNat 32 i) false)
    obtain ⟨hown, ⟨hsb, hdb, hs0, hd0, hAs, hAd⟩, hA, hsz⟩ := task_part hi'
    have hi3 : i < 3 := by omega
    dsimp only
    cases x with
    | error e =>
      refine WP.callMC_fownedS ((word_store hsb hs0 hAs 2).frame) hi'.own hc' (by rw [hsz]; decide)
        (by rw [hown]; exact hA) fun _ m'' r' _ _ ho' hq hs => ?_
      have hok : TaskOk 2 (BitVec.ofNat 32 i) true := .inr ⟨rfl, by
        simp only [BitVec.toNat_ofNat]; omega⟩
      have := inv_task_step hi' hg' ho' hs.threads hs.groups hq hok
      rw [upd_upd] at this
      exact ⟨_, this, ⟨_, _, _, _, rfl⟩, fun h => absurd h not_strict⟩
    | ok u =>
      cases u
      simp only [StateT.run_bind]
      refine WP.bind (WP.callMC_fownedS ((word_store hdb hd0 hAd (BitVec.ofNat 32 (i + 1))).frameL)
        hi'.own hc' (by rw [hsz]; decide) (by rw [hown]; exact hA) fun _ m'' r' _ _ ho' hq hs => ?_)
      have hok : TaskOk 0 (BitVec.ofNat 32 (i + 1)) false := ⟨rfl, by
        simp only [BitVec.toNat_ofNat]; omega⟩
      have := inv_task_step hi' hg' ho' hs.threads hs.groups hq hok
      rw [upd_upd] at this
      exact ih (i + 1) _ _ _ r' W (by omega) (by rw [hs.current, hc']) this

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (n : Nat) (_hu : 0 < u) (hgu : G u = g) (hi : Inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } n := by
  cases tgt with
  | worker st dn =>
    obtain ⟨r, W, rfl, rfl, rfl⟩ := hg
    obtain ⟨rfl, -, -⟩ := task_live hi hgu
    show proto.WP 1 ((steps W.st W.dn 0 3).run' ()) _ G _ n
    rw [StateT.run'_eq]
    refine WP.map (steps_spec 3 0 G _ n r W rfl rfl ?_)
    have e : upd G 1 (Gh.task r W 0 (BitVec.ofNat 32 0) false) = G := by
      rw [show BitVec.ofNat 32 0 = (0 : BitVec 32) from rfl, ← hgu, upd_same]
    rw [e]
    exact inv_keep hi rfl rfl rfl rfl rfl rfl

/-- `main` goes to the phase `ph'` with the same part, after steps that change no heap byte. -/
theorem inv_main {G : ThreadId → Gh} {m m' : Mem} {ph ph' : MPh} {r : Res} {W : Words}
    {g : Ptr} (hi : Inv G m) (hg : G 0 = .main ph r W g) (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (ht : m'.threads = m.threads) (hc : m'.clocks = m.clocks)
    (hf : m'.footprint = m.footprint) (hs : Shape W g (upd G 0 (.main ph' r W g)) m' ph')
    (hx : m.Aux m' := by exact ⟨rfl, rfl, rfl⟩) :
    Inv (upd G 0 (.main ph' r W g)) m' := by
  have hown : ownOf (upd G 0 (.main ph' r W g)) m' = ownOf G m := by
    funext u
    unfold ownOf
    rw [joinedB_congr ht]
    by_cases hu : u = 0
    · subst hu; rw [upd_self, hg]; rfl
    · rw [upd_ne _ _ hu]
  refine ⟨by rw [hown]; exact hi.own.keep hb ha ht hc hf hx, fun u r₁ W₁ s₁ d₁ e₁ hu => ?_,
    ⟨ph', r, W, g, upd_self _ _ _, hs⟩, by rw [ht]; exact hi.t0⟩
  by_cases h0 : u = 0
  · subst h0; rw [upd_self] at hu; cases hu
  · rw [upd_ne _ _ h0] at hu; exact hi.task u _ _ _ _ _ hu

/-! ## `main` -/

theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => rnil) 0 g.res := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.res]; split <;> rfl

theorem groupTake_one {m : Mem} {g : Ptr} (hg : m.groups = #[(g, 1)]) :
    ((Thread.groupTake g).run m).run = some (.ok (#[1], { m with groups := #[] })) := by
  unfold Thread.groupTake
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg]
  simp [StateT.run, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
    bind, ExceptT.bind, ExceptT.bindCont]

theorem sep_lcomm {P Q R : FAssn} {r : Res} (h : (P ⋆ (Q ⋆ R)) r) : (Q ⋆ (P ⋆ R)) r :=
  sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' h))

/-- The start memory holds the parts: no thread owns anything, the rest is empty. -/
theorem start :
    FOwned (upd (fun _ => rnil) 0 rnil) rO { ({} : Mem) with current := 0 } := by
  have hbl : ∀ b : BlockId, ({} : Mem).blocks[b]? = none := fun b => by
    show (#[] : Array Block)[b]? = none; simp
  have hw : ShapesWF (shapes ({} : Mem)) := ⟨fun _ h => (by cases h), List.Pairwise.nil⟩
  have hl : ({} : Mem).LiveLayout :=
    ⟨fun b _ _ _ _ hb => (by rw [hbl b] at hb; cases hb), fun b _ hb => by rw [hbl b] at hb; cases hb⟩
  rw [show upd (fun _ => rnil) 0 rnil = (fun _ => rnil) from upd_same _ _]
  exact (FOwned.start_plainRest (m := {}) rfl rfl hw hl (Mem.MsgCov.of_atomics rfl)).current 0

set_option maxHeartbeats 4000000 in
theorem main_spec (n : Nat) :
    proto.WP 0 cancelClient QM (fun _ => .none) { ({} : Mem) with current := 0 } n := by
  unfold cancelClient
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  -- `status`
  refine WP.bind (WP.callMC_fownedS (by fsym : FTTriple emp _ _) start rfl
    (by decide) ⟨rfl, rfl, rfl⟩ fun st m₁ r₁ _ _ ho₁ hq₁ hs₁ => ?_)
  obtain ⟨As, ks, hA₁⟩ := hq₁
  obtain ⟨⟨hsb, hs0, hAs⟩, hb₁⟩ := sep_lift.mp hA₁
  refine WP.bind (WP.callMC_fownedS (word_init hsb hs0 hAs 0) ho₁ (by rw [hs₁.current]) (by
    rw [hs₁.threads]; decide) hb₁ fun _ m₂ r₂ _ _ ho₂ hq₂ hs₂ => ?_)
  -- `done`
  refine WP.bind (WP.callMC_fownedS ((by fsym : FTTriple emp _ _).frameL.pre
    fun _ h => sep_emp.mpr h) ho₂ (by rw [hs₂.current, hs₁.current])
    (by rw [hs₂.threads, hs₁.threads]; decide) hq₂ fun dn m₃ r₃ _ _ ho₃ hq₃ hs₃ => ?_)
  obtain ⟨Ad, kd, ⟨hdb, hd0, hAd⟩, hb₃⟩ := sep_ex_ex_lift hq₃
  refine WP.bind (WP.callMC_fownedS (word_init hdb hd0 hAd 0).frameL ho₃
    (by rw [hs₃.current, hs₂.current, hs₁.current])
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; decide) hb₃
    fun _ m₄ r₄ _ _ ho₄ hq₄ hs₄ => ?_)
  let W : Words := ⟨st, dn, As, Ad, ks, kd⟩
  have hW : W.Ok := ⟨hsb, hdb, hs0, hd0, hAs, hAd⟩
  -- the group: a stack block in the plain mode, copied out of the rest
  have ho₄' := ho₄.dupPlain (t := 0) (by rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; decide)
    (by simp [Res.Plain, Ghost.plain])
  refine WP.bind (WP.callMC_fownedS (by fsym [FTriple.allocStackDrop] : FTTriple plain _ _).frameL ho₄'
    (by rw [hs₄.current, hs₃.current, hs₂.current, hs₁.current])
    (by rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; decide)
    (by simp only [upd_self]; exact sep_plain_intro hq₄)
    fun g m₅ r₅ _ _ ho₅ hq₅ hs₅ => ?_)
  obtain ⟨Ag, kg, ⟨hgb, hg0, hAg⟩, hb₅⟩ := sep_ex_ex_lift hq₅
  obtain ⟨rW, rG, hdWG, rfl, hWa, hGa⟩ := hb₅
  have hc₅ : m₅.current = 0 := by
    rw [hs₅.current, hs₄.current, hs₃.current, hs₂.current, hs₁.current]
  have ht₅ : m₅.threads = ({} : Mem).threads := by
    rw [hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]
  have hg₅ : m₅.groups = #[] := by
    rw [hs₅.groups, hs₄.groups, hs₃.groups, hs₂.groups, hs₁.groups]
  simp only [upd_upd] at ho₅
  dsimp only
  -- `Group.async`: the task gets the two words
  refine WP.bind (WP.groupAsyncC fun k _ => ⟨.main .spawn (rsum rW rG) W g, ?_,
    fun G₁ m₆ hg₁ hi₆ => ⟨.task rW W 0 0 false, ⟨rW, W, rfl, rfl, rfl⟩, fun child m₇ hf => ?_⟩⟩)
  · refine ⟨by rw [ownOf_main]; exact ho₅, fun u _ _ _ _ _ hu => ?_,
      ⟨.spawn, _, W, g, upd_self _ _ _, ?_⟩, by rw [ht₅]; rfl⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · exact ⟨by rw [ht₅]; rfl, hg₅, fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]⟩
  -- the fork: `child = 1`; `main` keeps the group's block
  obtain ⟨ph, hm, W', g', h0, hsh⟩ := hi₆.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₆, hgr₆, hn₆⟩ := hsh
  have hj₆ := hi₆.t0
  have hown₆ : ownOf G₁ m₆ 0 = ⟨rG.heap ∪ rW.heap, rG.know.union rW.know, rG.gh.add rW.gh⟩ := by
    simp only [ownOf, joinedB, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      hg₁, Gh.res]
    exact rsum_comm hdWG
  have ho₇ := FOwned.fork (hi₆.own.current 0) (by rw [hsz₆]; decide) hown₆ hdWG.symm hf
  rw [Proto.fork_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  simp only [hsz₆] at ho₇ ⊢
  have hjb6 : ∀ u, joinedB m₆ u = false := by
    intro u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rfl
    · rw [Array.getElem?_eq_none (by rw [hsz₆]; unfold ThreadId at *; omega)]; simp
  have hjb7 : ∀ M : Mem, M.threads = m₆.threads.push { spawner := 0, joined := false } →
      ∀ u, joinedB M u = false := by
    intro M hM u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rfl
    · rw [hM]; simp only [Array.getElem?_push, hsz₆]
      split
      · simp
      · rw [Array.getElem?_eq_none (by rw [hsz₆]; unfold ThreadId at *; omega)]; simp
  have e : ∀ M : Mem, M.threads = m₆.threads.push { spawner := 0, joined := false } →
      ownOf (upd (upd G₁ 1 (.task rW W 0 0 false)) 0 (.main .hint rG W g)) M =
        upd (upd (ownOf G₁ m₆) 0 rG) 1 rW := by
    intro M hM
    funext u
    simp only [ownOf, hjb7 M hM, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : u = 0
    · subst h0; simp [upd, Gh.res]
    · by_cases h1 : u = 1
      · subst h1; simp [upd, Gh.res]
      · simp [upd, h0, h1, ownOf, hjb6]
  -- the spin hint: the task may run
  refine WP.bind ?_
  show proto.WP 0 (Zig.spinLoopHint >>= fun a => pure (a, ((), ()).snd)) _ _ _ _
  refine WP.bind (WP.spinLoopHint fun k₁ _ => ⟨.main .hint rG W g, ?_,
    fun G₂ m₈ hg₂ hi₈ => WP.pure' ?_⟩)
  · refine ⟨by rw [e _ rfl]; exact ho₇.keep rfl rfl rfl rfl rfl, fun u r₁ W₁ s₁ d₁ e₁ hu => ?_,
      ⟨.hint, rG, W, g, upd_self _ _ _, ?_⟩, ?_⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact ⟨hW, hWa, rfl, by decide⟩
        · rw [upd_ne _ _ h1, hn₆ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by simp [hsz₆], by simp [Array.getElem_push, hsz₆],
        by simp [hgr₆],
        ⟨rW, 0, 0, false, by simp [upd]⟩, fun u hu => ?_⟩
      rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
        hn₆ u (by unfold ThreadId at *; omega)]
    · simp only [Array.getElem?_push, hsz₆]; exact hj₆
  -- `Group.cancel`: the take of the task, its cancelation request, the join
  obtain ⟨ph, hm, W', g', h0, hsh⟩ := hi₈.main
  rw [hg₂] at h0; cases h0
  obtain ⟨hsz₈, hr₈, hgr₈, ⟨rT₈, sT₈, dT₈, eT₈, h1₈⟩, hn₈⟩ := hsh
  refine WP.bind ?_
  unfold groupCancelC
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_keep (groupTake_one hgr₈) ?_ rfl)
  dsimp only
  refine WP.bind (WP.callMC_keep (requestCancel_run _ _) ?_ rfl)
  dsimp only
  rw [← Array.forIn_toList]
  simp only [List.forIn_cons, List.forIn_nil, StateT.run_bind, bind_assoc]
  refine WP.bind (WP.joinC fun k₂ _ => ⟨.main .join rG W g, ?_, fun G₃ m₉ hg₃ hi₉ =>
    ⟨fun h => absurd h not_strict, fun hfin => ⟨fun h => absurd h not_strict, fun m₁₀ hj => ?_⟩⟩⟩)
  · refine inv_main hi₈ hg₂ rfl rfl rfl rfl rfl ⟨hsz₈, hr₈, ⟨rT₈, sT₈, dT₈, eT₈, ?_⟩, fun u hu => ?_⟩
    · rw [upd_ne _ _ (by decide)]; exact h1₈
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn₈ u hu
  -- the join: `main` takes the task's words back
  obtain ⟨ph, hm, W', g', h0, hsh⟩ := hi₉.main
  rw [hg₃] at h0; cases h0
  obtain ⟨hsz₉, hr₉, ⟨rT, s₉, d₉, e₉, h1₉⟩, hn₉⟩ := hsh
  obtain ⟨rT', W'', s', d', hf1⟩ := hfin
  rw [h1₉] at hf1
  simp only [Gh.task.injEq] at hf1
  obtain ⟨rfl, -, rfl, rfl, rfl⟩ := hf1
  obtain ⟨-, hTA, hout⟩ := hi₉.task 1 _ _ _ _ _ h1₉
  have hown0 : ownOf G₃ m₉ 0 = rG := by simp [ownOf, joinedB, hg₃, Gh.res]
  have hown1 : ownOf G₃ m₉ 1 = rT := by simp [ownOf, joinedB, hr₉, h1₉, Gh.res]
  have hdisj : FHeap.Disjoint rG.heap rT.heap := by
    have := hi₉.own.disj (u := 0) (v := 1) (by rw [hsz₉]; decide) (by rw [hsz₉]; decide) (by decide)
    rwa [hown0, hown1] at this
  have ho₁₀ := FOwned.join (hi₉.own.current 0) (by rw [hsz₉]; decide) (show (1 : ThreadId) ≠ 0 by decide) hj
  obtain ⟨rec, -, -, hm₁₀⟩ := Proto.join_eq hj
  rw [hown0, hown1] at ho₁₀
  have hc₁₀ : m₁₀.current = 0 := by rw [hm₁₀]
  have ht₁₀ : m₁₀.threads.size = 2 := by rw [hm₁₀]; simp [hsz₉]
  refine WP.bind (WP.pure' ?_)
  dsimp only
  refine WP.bind (WP.pure' ?_)
  dsimp only
  have hm₁₁ : FOwned (upd (upd (ownOf G₃ m₉) 1 rnil) 0 (rsum rG rT)) rO
      { m₁₀ with cancels := m₁₀.cancels.filter (fun u => !(#[1] : Array ThreadId).contains u) } :=
    ho₁₀.keep rfl rfl rfl rfl rfl
  refine WP.callMC_keep (dropCancels_run _ _) ?_ rfl
  dsimp only
  have hP : ((up (bytesAt g Ag 16 .stack (Array.replicate 16 .undef)) ⋆ bext kg 16 .stack) ⋆
      W.A s₉ d₉) (rsum rG rT) := ⟨rG, rT, hdisj, rfl, hGa, hTA⟩
  -- `status.*`, `done.*`
  refine WP.bind (WP.callMC_fownedS ((word_load hsb hs0 hAs).frame.frameL.post
    fun _ _ h => sep_lcomm (sep_mono_right (fun _ h => sep_assoc h) h))
    hm₁₁ hc₁₀ (by rw [ht₁₀]; decide) hP fun r₁ m₁₂ r₁₂ _ _ ho₁₂ hq₁₂ hs₁₂ => ?_)
  obtain ⟨rfl, hP₁₂⟩ := sep_lift.mp hq₁₂
  refine WP.bind (WP.callMC_fownedS ((word_load hdb hd0 hAd).frameL.frameL.post
    fun _ _ h => sep_lcomm (sep_mono_right (fun _ h => sep_lcomm h) h)) ho₁₂
    (by rw [hs₁₂.current, hc₁₀]) (by rw [hs₁₂.threads, ht₁₀]; decide) hP₁₂
    fun r₂ m₁₃ r₁₃ _ _ ho₁₃ hq₁₃ hs₁₃ => ?_)
  obtain ⟨rfl, hP₁₃⟩ := sep_lift.mp hq₁₃
  -- the frees
  refine WP.bind (WP.callMC_fownedS (by fsym [enc_u32] : FTTriple _ _ _) ho₁₃
    (by rw [hs₁₃.current, hs₁₂.current, hc₁₀]) (by rw [hs₁₃.threads, hs₁₂.threads, ht₁₀]; decide)
    hP₁₃ fun _ m₁₄ r₁₄ _ _ ho₁₄ hq₁₄ hs₁₄ => ?_)
  refine WP.bind (WP.callMC_fownedS (by fsym [enc_u32] : FTTriple _ _ _) ho₁₄
    (by rw [hs₁₄.current, hs₁₃.current, hs₁₂.current, hc₁₀])
    (by rw [hs₁₄.threads, hs₁₃.threads, hs₁₂.threads, ht₁₀]; decide)
    hq₁₄ fun _ m₁₅ r₁₅ _ _ ho₁₅ hq₁₅ hs₁₅ => ?_)
  refine WP.bind (WP.callMC_fownedS (by fsym : FTTriple _ _ _) ho₁₅
    (by rw [hs₁₅.current, hs₁₄.current, hs₁₃.current, hs₁₂.current, hc₁₀])
    (by rw [hs₁₅.threads, hs₁₄.threads, hs₁₃.threads, hs₁₂.threads, ht₁₀]; decide)
    hq₁₅ fun _ m₁₆ r₁₆ _ _ ho₁₆ hq₁₆ hs₁₆ => ?_)
  have he : r₁₆.heap = FHeap.empty := hq₁₆.1
  refine WP.pure' ⟨hout, ho₁₆.heap_empty (fun u _ => ?_) (fheap_empty_mem)⟩
  by_cases h0 : u = 0
  · subst h0; rw [upd_self]; exact he
  · simp only [upd_upd]
    rw [upd_ne _ _ h0]
    by_cases h1 : u = 1
    · subst h1; rw [upd_self]
    · rw [upd_ne _ _ h1]
      simp [ownOf, hn₉ u (by unfold ThreadId at *; omega), Gh.res]

/-! ## The results -/

/-- **Every result of `cancelClient` is the declared outcome, and no heap byte is live when
`main` returns** (every oracle `o`, every `fuel`): the task completed all its work (`(1, 3)`) or
was canceled with work left (`(2, d)`, `d < 3`), and its words came back to `main`, which freed
them. -/
theorem cancelClient_spec (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {v : BitVec 32 × BitVec 32} {m : Mem}
    (h : (Sched.run env dispatch fuel o cancelClient {}).run = some (.ok (v, m))) :
    Outcome v ∧ m.heap = Heap.empty := by
  obtain ⟨_, _, hq⟩ := proto.run_sound env (Proto.of_available henv) dispatch (fun _ => .none) dispatch_spec
    (fun h => absurd h not_strict) rfl main_spec h
  exact hq

/-- A canceled task is never reported as a completed one, and a result always names an
outcome (`status` is never the initial `0`). -/
theorem cancelClient_canceled_not_completed (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat}
    {v : BitVec 32 × BitVec 32} {m : Mem}
    (h : (Sched.run env dispatch fuel o cancelClient {}).run = some (.ok (v, m))) :
    v.1 ≠ 0 ∧ (v.1 = 2 → v.2 ≠ 3) ∧ (v.2 = 3 ∨ v.1 = 2) := by
  rcases (cancelClient_spec env henv h).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1]; decide, fun h' => absurd (h1 ▸ h' : (1 : BitVec 32) = 2) (by decide),
      .inl h2⟩
  · refine ⟨by rw [h1]; decide, fun _ h3 => ?_, .inr h1⟩
    rw [h3] at h2; exact absurd h2 (by decide)

/-! ## Strength (`docs/sep-threads.md`): the legacy proof's statements, verbatim -/

example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {v : BitVec 32 × BitVec 32} {m : Mem}
    (h : (Sched.run env dispatch fuel o cancelClient {}).run = some (.ok (v, m))) :
    Outcome v ∧ m.heap = Heap.empty :=
  cancelClient_spec env henv h

example (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat}
    {v : BitVec 32 × BitVec 32} {m : Mem}
    (h : (Sched.run env dispatch fuel o cancelClient {}).run = some (.ok (v, m))) :
    v.1 ≠ 0 ∧ (v.1 = 2 → v.2 ≠ 3) ∧ (v.2 = 3 ∨ v.1 = 2) :=
  cancelClient_canceled_not_completed env henv h

end Cancel.Group
