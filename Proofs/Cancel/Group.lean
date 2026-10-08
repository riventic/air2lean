import Proofs.Cancel.Client
import ZigLean.Conc.Csl
import ZigLean.Conc.Transfer
import ZigLean.Conc.Lemmas

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
- `main` gets the task's two words back at the join that `Group.cancel` does (C01 transfer:
  `Owned.fork` hands them over at the spawn, `Owned.join` returns them) and frees them: when
  `main` returns, no byte of the heap is live (`m.heap = Heap.empty`), so cancelation loses no
  owned resource.

The proof is partial correctness (`run_sound`): a run that gives an error or no result satisfies
the spec. `Proofs/Cancel/Client.lean` and `tests/roadmap/cancellation/Runtime.lean` show that
both outcomes happen and that sampled schedules give no error.

**Protocol.** A thread's ghost value (`Gh`) is `main` at a phase (`MPh`: at its spawn, at its
spin hint, at its join) with the heap it owns, the task's words `W` and the group `g`, or the
task with the heap it owns, the values of its words and whether it ended. The invariant (`Inv`):
the parts of the heap (`Owned`), every live byte belongs to a part (`Covered`), the task's heap
holds its two words with values allowed by `TaskOk`, and the threads and the group's tasks at
each phase of `main` (`Shape`). The cancelation state (`Mem.cancels`), the futex queue and
`current` are not in the invariant: every step that changes only them keeps it (`inv_keep`).
-/

open Zig Zig.Conc Zig.Conc.Proto Assn

namespace Cancel.Group

/-! ## Words -/

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- A 4-byte heap word at `p` (address `A`) that holds `v`. -/
def word (p : Ptr) (A : Nat) (v : BitVec 32) : Assn := bytesAt p A 4 .heap (Enc.encode v)

theorem decode_u32 (v : BitVec 32) :
    Enc.decode ((Enc.encode v).extract 0 (0 + Enc.size (BitVec 32))) =
      (pure v : Result (BitVec 32)) := by
  rw [show 0 + Enc.size (BitVec 32) = (Enc.encode v).size from (enc_u32 v).symm,
    Array.extract_size]
  exact LawfulEnc.decode_encode v

theorem word_init {p : Ptr} {A : Nat} (h0 : p.off = 0) (hA : A % 4 = 0) (w : BitVec 32) :
    TTriple (bytesAt p A 4 .heap (Array.replicate 4 .undef)) (Zig.store 4 p w)
      (fun _ => word p A w) :=
  (TTriple.storeAt (k := 0) (a := 4) w (by simp [Ptr.add]) (by decide) (by simp; decide)
    (by simp [h0, hA]) (by decide)).conseq (fun _ h => h) fun _ _ h => by
      rwa [writeBytes_all (by simp [enc_u32])] at h

theorem word_store {p : Ptr} {A : Nat} {v : BitVec 32} (h0 : p.off = 0) (hA : A % 4 = 0)
    (w : BitVec 32) : TTriple (word p A v) (Zig.store 4 p w) (fun _ => word p A w) :=
  (TTriple.storeAt (k := 0) (a := 4) w (by simp [Ptr.add]) (by decide)
    (by rw [enc_u32]; decide) (by simp [h0, hA]) (by decide)).conseq (fun _ h => h)
    fun _ _ h => by rwa [writeBytes_all (by rw [enc_u32, enc_u32])] at h

theorem word_load {p : Ptr} {A : Nat} {v : BitVec 32} (h0 : p.off = 0) (hA : A % 4 = 0) :
    TTriple (word p A v) (Zig.load (BitVec 32) 4 p) (fun r => ⌜r = v⌝ ∗ word p A v) :=
  TTriple.loadAt (k := 0) (a := 4) (v := v) (by simp [Ptr.add]) (by decide)
    (by rw [enc_u32]; decide) (by simp [h0, hA]) (decode_u32 v)

theorem word_free {p : Ptr} {A : Nat} {v : BitVec 32} (h0 : p.off = 0) :
    TTriple (word p A v) (Zig.free p) (fun _ => emp) :=
  TTriple.free (enc_u32 v) h0 (by decide)

/-- An allocation on the heap next to the heap `R` that the thread owns. -/
theorem alloc_heap_next {R : Assn} :
    TTriple R (Zig.alloc .heap 4 4) (fun p => R ∗ Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % 4 = 0⌝ ∗ bytesAt p A 4 .heap (Array.replicate 4 .undef)) :=
  (TTriple.alloc .heap 4 4 (by decide)).frameL.conseq (fun _ h => sep_emp.mpr h) fun _ _ h => h

/-! ## Protocol -/

/-- The task's two words: `status` at `st` (address `As`), the steps done at `dn` (`Ad`). -/
structure Words where
  st : Ptr
  dn : Ptr
  As : Nat
  Ad : Nat

def Words.Ok (W : Words) : Prop := W.st.off = 0 ∧ W.dn.off = 0 ∧ W.As % 4 = 0 ∧ W.Ad % 4 = 0

/-- The two words hold `s` and `d`. -/
def Words.A (W : Words) (s d : BitVec 32) : Assn := word W.st W.As s ∗ word W.dn W.Ad d

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
  | main (ph : MPh) (h : Heap) (W : Words) (g : Ptr)
  | task (h : Heap) (W : Words) (s d : BitVec 32) (ended : Bool)

def Gh.heap : Gh → Heap
  | .main _ h _ _ | .task h _ _ _ _ => h
  | .none => Heap.empty

/-- The heaps of the threads: a joined thread owns nothing. -/
def ownOf (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : Heap :=
  if joinedB m u then Heap.empty else (G u).heap

/-- Every live byte belongs to a part. -/
def Covered (own : ThreadId → Heap) (m : Mem) : Prop :=
  ∀ l c, m.heap l = some c → ∃ u, own u l ≠ none

/-- The threads and the group at each phase of `main`. -/
def Shape (W : Words) (g : Ptr) (G : ThreadId → Gh) (m : Mem) : MPh → Prop
  | .spawn => m.threads.size = 1 ∧ m.groups = #[] ∧ ∀ u, 1 ≤ u → G u = .none
  | .hint => m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
      m.groups = #[(g, 1)] ∧ (∃ h s d e, G 1 = .task h W s d e) ∧ ∀ u, 2 ≤ u → G u = .none
  | .join => m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
      (∃ h s d e, G 1 = .task h W s d e) ∧ ∀ u, 2 ≤ u → G u = .none

/-- The invariant (module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  own : Owned (ownOf G m) m
  cover : Covered (ownOf G m) m
  task : ∀ u h W s d e, G u = .task h W s d e → W.Ok ∧ W.A s d h ∧ TaskOk s d e
  main : ∃ ph h W g, G 0 = .main ph h W g ∧ Shape W g G m ph
  t0 : m.threads[0]? = some { spawner := 0, joined := true }

/-- The protocol (partial correctness). -/
def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .worker st dn => ∃ h W, g = .task h W 0 0 false ∧ W.st = st ∧ W.dn = dn
  fin g := ∃ h W s d, g = .task h W s d true

/-- `main`'s post: the declared outcome, and no live byte is left. -/
def QM : BitVec 32 × BitVec 32 → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun r _ m _ => Outcome r ∧ m.heap = Heap.empty

/-! ## Frames -/

theorem heap_congr {m m' : Mem} (hb : m'.blocks = m.blocks) : m'.heap = m.heap := by
  funext ⟨b, o⟩
  simp only [Mem.heap, hb]

theorem joinedB_congr {m m' : Mem} (ht : m'.threads = m.threads) : joinedB m' = joinedB m := by
  funext u; simp only [joinedB, ht]

/-- A step that changes no block, thread, clock or footprint entry (only `current`, the futex
queue, the cancelation requests or the groups) keeps the parts. -/
theorem owned_keep {own : ThreadId → Heap} {m m' : Mem} (ho : Owned own m)
    (hb : m'.blocks = m.blocks) (ht : m'.threads = m.threads) (hc : m'.clocks = m.clocks)
    (hf : m'.footprint = m.footprint) : Owned own m' :=
  ho.keep (by rw [ht]) (by rw [hc]) (fun u => by rw [heap_congr hb]; exact ho.sub u)
    (by rw [hb]; exact Nat.le_refl _) (fun u _ => by rw [hc]; exact VClock.le_refl _)
    (fun e he => .inl (by rw [hf] at he; exact he))

/-- `inv_keep` for a step that keeps the groups. -/
theorem inv_keep {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m)
    (hb : m'.blocks = m.blocks) (ht : m'.threads = m.threads) (hc : m'.clocks = m.clocks)
    (hf : m'.footprint = m.footprint) (hg : m'.groups = m.groups) : Inv G m' := by
  have hown : ownOf G m' = ownOf G m := by funext u; simp only [ownOf, joinedB_congr ht]
  refine ⟨hown ▸ owned_keep hi.own hb ht hc hf, ?_, hi.task, ?_, ?_⟩
  · rw [hown]; intro l c hl; rw [heap_congr hb] at hl; exact hi.cover l c hl
  · obtain ⟨ph, h, W, g, h0, hs⟩ := hi.main
    refine ⟨ph, h, W, g, h0, ?_⟩
    cases ph with
    | spawn => exact ⟨by rw [ht]; exact hs.1, by rw [hg]; exact hs.2.1, hs.2.2⟩
    | hint => exact ⟨by rw [ht]; exact hs.1, by rw [ht]; exact hs.2.1, by rw [hg]; exact hs.2.2.1,
        hs.2.2.2⟩
    | join => exact ⟨by rw [ht]; exact hs.1, by rw [ht]; exact hs.2.1, hs.2.2⟩
  · rw [ht]; exact hi.t0

/-- A thread step with a triple: the covering moves with the step's part. -/
theorem cover_step {own : ThreadId → Heap} {m m' : Mem} {t : ThreadId} {hQ : Heap}
    (hcv : Covered own m) (hm' : m'.heap = hQ ∪ m.heap.diff (own t)) :
    Covered (upd own t hQ) m' := by
  intro l c hl
  rw [hm', Heap.union_apply] at hl
  cases hq : hQ l with
  | some c' => exact ⟨t, by rw [upd_self, hq]; simp⟩
  | none =>
    rw [hq, Option.none_or] at hl
    unfold Heap.diff at hl
    split at hl
    · rename_i hn
      obtain ⟨u, hu⟩ := hcv l c hl
      have hut : u ≠ t := fun e => by subst e; exact hu hn
      exact ⟨u, by rw [upd_ne _ _ hut]; exact hu⟩
    · cases hl

/-- A `callMC` step of thread `t` with a triple on its part `h`: the parts and the covering
after it, and what the step kept (`StepIn`). -/
theorem WP.callMC_step {σ α : Type} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {n : Nat}
    {x : MemM α} {s : σ} {Pa : Assn} {Qa : α → Assn} {own : ThreadId → Heap} {h : Heap}
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (ht : TTriple Pa x Qa) (ho : Owned (upd own t h) m) (hcv : Covered (upd own t h) m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa h)
    (k : ∀ a m' h', Owned (upd own t h') m' → Covered (upd own t h') m' → Qa a h' →
      StepIn (m.heap.diff h) m m' → Q (a, s) G m' n) :
    proto.WP t ((callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.liftM_owned ht ho hc htl (by rw [upd_self]; exact hp) fun a m' hQ _ ho' hq hs hm' _ => by
    have hcv' := cover_step hcv hm'
    rw [upd_upd] at ho' hcv'
    rw [upd_self] at hs
    exact k a m' hQ ho' hcv' hq hs

/-! ## The task -/

/-- A task is thread 1, not joined, and `main` is at its spin hint or at its join. -/
theorem task_live {G : ThreadId → Gh} {m : Mem} {u : ThreadId} {h W s d e}
    (hi : Inv G m) (hg : G u = .task h W s d e) :
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
    ownOf (upd G u g) m' = upd (ownOf G m) u g.heap := by
  funext w
  unfold ownOf
  rw [joinedB_congr ht]
  by_cases hw : w = u
  · subst hw; simp only [upd_self]; rw [hj]; rfl
  · rw [upd_ne _ _ hw, upd_ne _ _ hw]

/-- The task's step to new words `h'` keeps the invariant with its new ghost value. -/
theorem inv_task_step {G : ThreadId → Gh} {m m' : Mem} {h h' : Heap} {W : Words}
    {s d s' d' : BitVec 32} {e e' : Bool} (hi : Inv G m) (hg : G 1 = .task h W s d e)
    (ho : Owned (upd (ownOf G m) 1 h') m') (hcv : Covered (upd (ownOf G m) 1 h') m')
    (ht : m'.threads = m.threads) (hgr : m'.groups = m.groups) (hA : W.A s' d' h')
    (hok : TaskOk s' d' e') : Inv (upd G 1 (.task h' W s' d' e')) m' := by
  obtain ⟨-, hj, -⟩ := task_live hi hg
  have hown := ownOf_upd (G := G) (g := .task h' W s' d' e') ht hj
  refine ⟨by rw [hown]; exact ho, by rw [hown]; exact hcv, fun u h₁ W₁ s₁ d₁ e₁ hu => ?_, ?_, ?_⟩
  · by_cases h1 : u = 1
    · subst h1; rw [upd_self] at hu; cases hu
      exact ⟨(hi.task 1 _ _ _ _ _ hg).1, hA, hok⟩
    · rw [upd_ne _ _ h1] at hu; exact hi.task u _ _ _ _ _ hu
  · obtain ⟨ph, hm, W', g, h0, hs⟩ := hi.main
    refine ⟨ph, hm, W', g, by rw [upd_ne _ _ (by decide)]; exact h0, ?_⟩
    have hnone : ∀ w, 2 ≤ w → G w = .none → upd G 1 (.task h' W s' d' e') w = .none :=
      fun w hw hn => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact hn
    cases ph with
    | spawn => have := hs.2.2 1 (Nat.le_refl _); rw [hg] at this; cases this
    | hint =>
      obtain ⟨hsz, hr, hgr0, ⟨h₁, s₁, d₁, e₁, h1⟩, hn⟩ := hs
      rw [hg] at h1; cases h1
      exact ⟨by rw [ht]; exact hsz, by rw [ht]; exact hr, by rw [hgr]; exact hgr0,
        ⟨h', s', d', e', upd_self _ _ _⟩, fun w hw => hnone w hw (hn w hw)⟩
    | join =>
      obtain ⟨hsz, hr, ⟨h₁, s₁, d₁, e₁, h1⟩, hn⟩ := hs
      rw [hg] at h1; cases h1
      exact ⟨by rw [ht]; exact hsz, by rw [ht]; exact hr, ⟨h', s', d', e', upd_self _ _ _⟩,
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

/-- The rest of `futexWaitCancelableC` after its futex wait. -/
def afterWait {σ : Type} : CM Tgt σ (Except ErrName Unit) := do
  if ← callMC Thread.cancelPending then
    if (← pickC (fun _ => 2)) = cancelDelivered then
      callMC Thread.takeCancel
      pure (.error "Canceled")
    else pure (.ok ())
  else pure (.ok ())

theorem futexWaitCancelableC_eq {σ : Type} (p : Ptr) (e : BitVec 32) :
    (futexWaitCancelableC ⟨⟩ p e : CM Tgt σ (Except ErrName Unit)) = (do
      if ← callMC Thread.cancelPending then
        callMC Thread.takeCancel
        pure (.error "Canceled")
      else
        futexWaitC ⟨⟩ p e
        afterWait) := rfl

theorem wp_afterWait {G : ThreadId → Gh} {m : Mem} {n : Nat} {gT : Gh}
    (hc : m.current = 1) (hi : Inv (upd G 1 gT) m)
    {Q : Except ErrName Unit × Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ r G' m' k, m'.current = 1 → Inv (upd G' 1 gT) m' → Q (r, ()) G' m' k) :
    proto.WP 1 ((afterWait : CM Tgt Unit _).run ()) Q G m n := by
  unfold afterWait
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
      exact WP.pure' (hQ _ _ _ _ rfl (inv_keep hi₂' rfl rfl rfl rfl rfl))
    · exact WP.pure' (hQ _ _ _ _ rfl (inv_keep hi₂' rfl rfl rfl rfl rfl))
  · exact WP.pure' (hQ _ _ _ _ hc hi)

/-- The task's cancelation point (`io.futexWait(u32, status, 7)`) with the task's ghost value
`gT`: whatever it returns, the invariant holds with `gT`. It may sleep, return spuriously, see
the value differ, observe a pending request, or have one delivered. -/
theorem wp_cancelWait {G : ThreadId → Gh} {m : Mem} {n : Nat} {gT : Gh} {p : Ptr}
    (hc : m.current = 1) (hi : Inv (upd G 1 gT) m)
    {Q : Except ErrName Unit × Unit → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ r G' m' k, m'.current = 1 → Inv (upd G' 1 gT) m' → Q (r, ()) G' m' k) :
    proto.WP 1 ((futexWaitCancelableC ⟨⟩ p (7 : BitVec 32) : CM Tgt Unit _).run ()) Q G m n := by
  rw [futexWaitCancelableC_eq]
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_keep (cancelPending_run m) ?_ rfl)
  dsimp only
  split
  · simp only [StateT.run_bind]
    refine WP.bind (WP.callMC_keep (takeCancel_run _) ?_ rfl)
    exact WP.pure' (hQ _ _ _ _ hc (inv_keep hi rfl rfl rfl rfl rfl))
  · simp only [StateT.run_bind]
    refine WP.bind (WP.futexWaitC (P := proto) fun k _ => ⟨gT, hi,
      fun G₁ m₁ hg₁ hi₁ => ⟨fun h => absurd h not_strict, fun _ =>
        ⟨fun h => absurd h not_strict, fun b m' hr => ?_⟩⟩⟩)
    have hi₁' : Inv (upd G₁ 1 gT) m₁ := by rw [← hg₁, upd_same]; exact hi₁
    rcases futexWait_ok hr with ⟨-, rfl, rfl⟩ | ⟨-, -, -, -, -, -, -, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
    all_goals simp only [Bool.false_eq_true, ↓reduceIte]
    · refine wp_afterWait ?_ ?_ hQ
      · rfl
      · exact inv_keep hi₁' rfl rfl rfl rfl rfl
    · refine ⟨inv_keep hi₁ rfl rfl rfl rfl rfl, wp_afterWait ?_ ?_ hQ⟩
      · rfl
      · exact inv_keep hi₁' rfl rfl rfl rfl rfl
    · refine wp_afterWait ?_ ?_ hQ
      · rfl
      · exact inv_keep hi₁' rfl rfl rfl rfl rfl

/-! ## The task's steps -/

/-- The task at its step `i` with `k` steps left: it keeps the invariant at every stop and ends
with `Outcome`. -/
theorem steps_spec (k : Nat) : ∀ (i : Nat) (G : ThreadId → Gh) (m : Mem) (n : Nat) (h : Heap)
    (W : Words), i + k = 3 → m.current = 1 →
    Inv (upd G 1 (.task h W 0 (BitVec.ofNat 32 i) false)) m →
    proto.WP 1 ((steps W.st W.dn i k).run ()) (fun a G m d => proto.QKid 1 a.1 G m d) G m n := by
  induction k with
  | zero =>
    intro i G m n h W hik hc hi
    obtain rfl : i = 3 := by omega
    have hg := upd_self G 1 (Gh.task h W 0 (BitVec.ofNat 32 3) false)
    obtain ⟨⟨hs0, -, hAs, -⟩, hA, -⟩ := hi.task 1 _ _ _ _ _ hg
    obtain ⟨-, hj, hsz⟩ := task_live hi hg
    have hown : ownOf (upd G 1 (.task h W 0 (BitVec.ofNat 32 3) false)) m 1 = h := by
      simp [ownOf, hj, Gh.heap]
    have ho := hi.own
    have hcv := hi.cover
    rw [← upd_same (ownOf _ m) 1, hown] at ho hcv
    simp only [steps]
    refine WP.callMC_step ((word_store hs0 hAs 1).frame) ho hcv hc (by rw [hsz]; decide) hA
      fun _ m' h' ho' hcv' hq hs => ?_
    have := inv_task_step hi hg ho' hcv' hs.threads hs.groups hq
      (show TaskOk 1 (BitVec.ofNat 32 3) true from .inl ⟨rfl, rfl⟩)
    rw [upd_upd] at this
    exact ⟨_, this, ⟨_, _, _, _, rfl⟩, fun h => absurd h not_strict⟩
  | succ k ih =>
    intro i G m n h W hik hc hi
    simp only [steps, StateT.run_bind]
    refine WP.bind (wp_cancelWait hc hi fun r G' m' k' hc' hi' => ?_)
    have hg' := upd_self G' 1 (Gh.task h W 0 (BitVec.ofNat 32 i) false)
    obtain ⟨⟨hs0, hd0, hAs, hAd⟩, hA, -⟩ := hi'.task 1 _ _ _ _ _ hg'
    obtain ⟨-, hj, hsz⟩ := task_live hi' hg'
    have hown : ownOf (upd G' 1 (.task h W 0 (BitVec.ofNat 32 i) false)) m' 1 = h := by
      simp [ownOf, hj, Gh.heap]
    have ho := hi'.own
    have hcv := hi'.cover
    rw [← upd_same (ownOf _ m') 1, hown] at ho hcv
    have hi3 : i < 3 := by omega
    dsimp only
    cases r with
    | error e =>
      refine WP.callMC_step ((word_store hs0 hAs 2).frame) ho hcv hc' (by rw [hsz]; decide) hA
        fun _ m'' h' ho' hcv' hq hs => ?_
      have hok : TaskOk 2 (BitVec.ofNat 32 i) true := .inr ⟨rfl, by
        simp only [BitVec.toNat_ofNat]; omega⟩
      have := inv_task_step hi' hg' ho' hcv' hs.threads hs.groups hq hok
      rw [upd_upd] at this
      exact ⟨_, this, ⟨_, _, _, _, rfl⟩, fun h => absurd h not_strict⟩
    | ok u =>
      cases u
      simp only [StateT.run_bind]
      refine WP.bind (WP.callMC_step ((word_store hd0 hAd (BitVec.ofNat 32 (i + 1))).frameL) ho
        hcv hc' (by rw [hsz]; decide) hA fun _ m'' h' ho' hcv' hq hs => ?_)
      have hok : TaskOk 0 (BitVec.ofNat 32 (i + 1)) false := ⟨rfl, by
        simp only [BitVec.toNat_ofNat]; omega⟩
      have := inv_task_step hi' hg' ho' hcv' hs.threads hs.groups hq hok
      rw [upd_upd] at this
      exact ih (i + 1) _ _ _ h' W (by omega) (by rw [hs.current, hc']) this

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (n : Nat) (_hu : 0 < u) (hgu : G u = g) (hi : Inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } n := by
  cases tgt with
  | worker st dn =>
    obtain ⟨h, W, rfl, rfl, rfl⟩ := hg
    obtain ⟨rfl, -, -⟩ := task_live hi hgu
    show proto.WP 1 ((steps W.st W.dn 0 3).run' ()) _ G _ n
    rw [StateT.run'_eq]
    refine WP.map (steps_spec 3 0 G _ n h W rfl rfl ?_)
    have e : upd G 1 (Gh.task h W 0 (BitVec.ofNat 32 0) false) = G := by
      rw [show BitVec.ofNat 32 0 = (0 : BitVec 32) from rfl, ← hgu, upd_same]
    rw [e]
    exact inv_keep hi rfl rfl rfl rfl rfl

/-- A spawn: `t` gives `h₂` of its part `h₁ ∪ h₂` to the new thread `c`; the covering moves. -/
theorem cover_fork {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId} {h₁ h₂ : Heap}
    (hcv : Covered own m) (hb : m'.blocks = m.blocks) (hs : own t = h₁ ∪ h₂)
    (hc : own c = Heap.empty) (htc : t ≠ c) : Covered (upd (upd own t h₁) c h₂) m' := by
  intro l x hl
  rw [heap_congr hb] at hl
  obtain ⟨u, hu⟩ := hcv l x hl
  by_cases hut : u = t
  · subst hut
    rw [hs, Heap.union_apply] at hu
    cases h1 : h₁ l with
    | some y => exact ⟨u, by rw [upd_ne _ _ htc, upd_self, h1]; simp⟩
    | none =>
      rw [h1, Option.none_or] at hu
      exact ⟨c, by rw [upd_self]; exact hu⟩
  · by_cases huc : u = c
    · subst huc; rw [hc] at hu; exact absurd rfl hu
    · exact ⟨u, by rw [upd_ne _ _ huc, upd_ne _ _ hut]; exact hu⟩

/-- A join: `t` takes the part of `u`; the covering moves. -/
theorem cover_join {own : ThreadId → Heap} {m m' : Mem} {t u : ThreadId} (hcv : Covered own m)
    (hb : m'.blocks = m.blocks) (hut : u ≠ t) :
    Covered (upd (upd own t (own t ∪ own u)) u Heap.empty) m' := by
  intro l x hl
  rw [heap_congr hb] at hl
  obtain ⟨w, hw⟩ := hcv l x hl
  refine ⟨if w = u then t else w, ?_⟩
  by_cases hwu : w = u
  · subst hwu
    rw [if_pos rfl, upd_ne _ _ (Ne.symm hut), upd_self, Heap.union_apply]
    cases h : own t l <;> simp_all
  · rw [if_neg hwu, upd_ne _ _ hwu]
    by_cases hwt : w = t
    · subst hwt
      rw [upd_self, Heap.union_apply]
      cases h : own w l <;> simp_all
    · rw [upd_ne _ _ hwt]; exact hw

/-- `main` goes to the phase `ph'` with the same heap, after steps that change no heap byte. -/
theorem inv_main {G : ThreadId → Gh} {m m' : Mem} {ph ph' : MPh} {h : Heap} {W : Words}
    {g : Ptr} (hi : Inv G m) (hg : G 0 = .main ph h W g) (hb : m'.blocks = m.blocks)
    (ht : m'.threads = m.threads) (hc : m'.clocks = m.clocks) (hf : m'.footprint = m.footprint)
    (hs : Shape W g (upd G 0 (.main ph' h W g)) m' ph') :
    Inv (upd G 0 (.main ph' h W g)) m' := by
  have hown : ownOf (upd G 0 (.main ph' h W g)) m' = ownOf G m := by
    funext u
    unfold ownOf
    rw [joinedB_congr ht]
    by_cases hu : u = 0
    · subst hu; rw [upd_self, hg]; rfl
    · rw [upd_ne _ _ hu]
  refine ⟨by rw [hown]; exact owned_keep hi.own hb ht hc hf, by
    rw [hown]; intro l c hl; rw [heap_congr hb] at hl; exact hi.cover l c hl,
    fun u h₁ W₁ s₁ d₁ e₁ hu => ?_, ⟨ph', h, W, g, upd_self _ _ _, hs⟩, by rw [ht]; exact hi.t0⟩
  by_cases h0 : u = 0
  · subst h0; rw [upd_self] at hu; cases hu
  · rw [upd_ne _ _ h0] at hu; exact hi.task u _ _ _ _ _ hu

/-! ## `main` -/

theorem ownOf_main (m : Mem) (g : Gh) :
    ownOf (upd (fun _ => .none) 0 g) m = upd (fun _ => Heap.empty) 0 g.heap := by
  funext u
  by_cases hu : u = 0
  · subst hu; simp [ownOf, joinedB, upd]
  · simp only [ownOf, upd, hu, ↓reduceIte, Gh.heap]; split <;> rfl

theorem groupTake_one {m : Mem} {g : Ptr} (hg : m.groups = #[(g, 1)]) :
    ((Thread.groupTake g).run m).run = some (.ok (#[1], { m with groups := #[] })) := by
  unfold Thread.groupTake
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hg]
  simp [StateT.run, set, StateT.set, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
    bind, StateT.bind, ExceptT.bind, ExceptT.bindCont]

/-- `free` of the first word. -/
theorem free_front {R : Assn} {p : Ptr} {A : Nat} {v : BitVec 32} (h0 : p.off = 0) :
    TTriple (word p A v ∗ R) (Zig.free p) (fun _ => R) :=
  (word_free h0).frame.conseq (fun _ h => h) fun _ _ h => sep_emp.mp (sep_comm h)

/-- No part owns a byte: no byte is live. -/
theorem heap_empty {own : ThreadId → Heap} {m : Mem} (hcv : Covered own m)
    (h0 : ∀ u, own u = Heap.empty) : m.heap = Heap.empty := by
  funext l
  cases hl : m.heap l with
  | none => rfl
  | some c =>
    obtain ⟨u, hu⟩ := hcv l c hl
    rw [h0 u] at hu
    exact absurd rfl hu

set_option maxHeartbeats 4000000 in
theorem main_spec (n : Nat) :
    proto.WP 0 cancelClient QM (fun _ => .none) { ({} : Mem) with current := 0 } n := by
  unfold cancelClient
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  have ho₀ : Owned (upd (fun _ => Heap.empty) 0 Heap.empty) { ({} : Mem) with current := 0 } := by
    rw [show upd (fun _ => Heap.empty) 0 Heap.empty = (fun _ => Heap.empty) from upd_same _ _]
    exact Owned.start rfl rfl
  have hcv₀ : Covered (upd (fun _ => Heap.empty) 0 Heap.empty)
      { ({} : Mem) with current := 0 } := by
    intro ⟨b, o⟩ c hl; simp [Mem.heap] at hl
  -- `status`
  refine WP.bind (WP.callMC_step (TTriple.alloc .heap 4 4 (by decide)) ho₀ hcv₀ rfl (by decide)
    rfl fun st m₁ h₁ ho₁ hcv₁ hq₁ hs₁ => ?_)
  obtain ⟨As, hA₁⟩ := hq₁
  obtain ⟨⟨hs0, hAs⟩, hb₁⟩ := sep_lift.mp hA₁
  refine WP.bind (WP.callMC_step (word_init hs0 hAs 0) ho₁ hcv₁ (by rw [hs₁.current]) (by
    rw [hs₁.threads]; decide) hb₁ fun _ m₂ h₂ ho₂ hcv₂ hq₂ hs₂ => ?_)
  -- `done`
  refine WP.bind (WP.callMC_step alloc_heap_next ho₂ hcv₂ (by rw [hs₂.current, hs₁.current])
    (by rw [hs₂.threads, hs₁.threads]; decide) hq₂ fun dn m₃ h₃ ho₃ hcv₃ hq₃ hs₃ => ?_)
  obtain ⟨Ad, ⟨hd0, hAd⟩, hb₃⟩ := sep_ex_lift hq₃
  refine WP.bind (WP.callMC_step (word_init hd0 hAd 0).frameL ho₃ hcv₃
    (by rw [hs₃.current, hs₂.current, hs₁.current])
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; decide) hb₃
    fun _ m₄ h₄ ho₄ hcv₄ hq₄ hs₄ => ?_)
  let W : Words := ⟨st, dn, As, Ad⟩
  have hW : W.Ok := ⟨hs0, hd0, hAs, hAd⟩
  -- the group
  refine WP.bind (WP.callMC_step (alloc_next 16 8 (by decide)) ho₄ hcv₄
    (by rw [hs₄.current, hs₃.current, hs₂.current, hs₁.current])
    (by rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; decide) hq₄
    fun g m₅ h₅ ho₅ hcv₅ hq₅ hs₅ => ?_)
  obtain ⟨Ag, ⟨hg0, hAg⟩, hb₅⟩ := sep_ex_lift hq₅
  obtain ⟨hW₅, hG, hdWG, rfl, hWa, hGa⟩ := hb₅
  have hc₅ : m₅.current = 0 := by
    rw [hs₅.current, hs₄.current, hs₃.current, hs₂.current, hs₁.current]
  have ht₅ : m₅.threads = ({} : Mem).threads := by
    rw [hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]
  have hg₅ : m₅.groups = #[] := by
    rw [hs₅.groups, hs₄.groups, hs₃.groups, hs₂.groups, hs₁.groups]
  dsimp only
  -- `Group.async`: the task gets the two words
  refine WP.bind (WP.groupAsyncC fun k _ => ⟨.main .spawn (hW₅ ∪ hG) W g, ?_,
    fun G₁ m₆ hg₁ hi₆ => ⟨.task hW₅ W 0 0 false, ⟨hW₅, W, rfl, rfl, rfl⟩, fun child m₇ hf => ?_⟩⟩)
  · refine ⟨by rw [ownOf_main]; exact ho₅, by rw [ownOf_main]; exact hcv₅,
      fun u _ _ _ _ _ hu => ?_, ⟨.spawn, _, W, g, upd_self _ _ _, ?_⟩, by rw [ht₅]; rfl⟩
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu; cases hu
    · exact ⟨by rw [ht₅]; rfl, hg₅, fun u hu => by rw [upd_ne _ _ (by unfold ThreadId at *; omega)]⟩
  -- the fork: `child = 1`
  obtain ⟨ph, hm, W', g', h0, hsh⟩ := hi₆.main
  rw [hg₁] at h0; cases h0
  obtain ⟨hsz₆, hgr₆, hn₆⟩ := hsh
  have ho₆ := hi₆.own
  have hcv₆ := hi₆.cover
  have hj₆ := hi₆.t0
  rw [Proto.fork_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  simp only [hsz₆]
  have hown₆ : ownOf G₁ m₆ 0 = hG ∪ hW₅ := by
    simp only [ownOf, joinedB, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      hg₁, Gh.heap]
    exact Heap.union_comm hdWG
  have ho₇ := Owned.fork (ho₆.current 0) (by rw [hsz₆]; decide) hown₆ hdWG.symm
    (Proto.fork_run _)
  simp only [hsz₆] at ho₇
  have hjb6 : ∀ u, joinedB m₆ u = false := by
    intro u; unfold joinedB
    by_cases hu : u = 0
    · subst hu; rfl
    · rw [Array.getElem?_eq_none (by rw [hsz₆]; unfold ThreadId at *; omega)]; simp
  have hn₁ : ∀ u, 1 ≤ u → ownOf G₁ m₆ u = Heap.empty := by
    intro u hu; simp [ownOf, hjb6, hn₆ u hu, Gh.heap]
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
      ownOf (upd (upd G₁ 1 (.task hW₅ W 0 0 false)) 0 (.main .hint hG W g)) M =
        upd (upd (ownOf G₁ m₆) 0 hG) 1 hW₅ := by
    intro M hM
    funext u
    simp only [ownOf, hjb7 M hM, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : u = 0
    · subst h0; simp [upd, Gh.heap]
    · by_cases h1 : u = 1
      · subst h1; simp [upd, Gh.heap]
      · simp [upd, h0, h1, ownOf, hjb6]
  -- the spin hint: the task may run
  refine WP.bind ?_
  show proto.WP 0 (Zig.spinLoopHint >>= fun a => pure (a, ((), ()).snd)) _ _ _ _
  refine WP.bind (WP.spinLoopHint fun k₁ _ => ⟨.main .hint hG W g, ?_,
    fun G₂ m₈ hg₂ hi₈ => WP.pure' ?_⟩)
  · refine ⟨by rw [e _ rfl]; exact owned_keep ho₇ rfl rfl rfl rfl, ?_, fun u h₁ W₁ s₁ d₁ e₁ hu => ?_,
      ⟨.hint, hG, W, g, upd_self _ _ _, ?_⟩, ?_⟩
    · rw [e _ rfl]
      exact cover_fork hcv₆ rfl hown₆ (hn₁ 1 (Nat.le_refl _)) (by decide)
    · by_cases h0 : u = 0
      · subst h0; rw [upd_self] at hu; cases hu
      · rw [upd_ne _ _ h0] at hu
        by_cases h1 : u = 1
        · subst h1; rw [upd_self] at hu; cases hu
          exact ⟨hW, hWa, rfl, by decide⟩
        · rw [upd_ne _ _ h1, hn₆ u (by unfold ThreadId at *; omega)] at hu; cases hu
    · refine ⟨by simp [hsz₆], by simp [Array.getElem?_push, Array.getElem_push, hsz₆],
        by simp [hgr₆],
        ⟨hW₅, 0, 0, false, by simp [upd]⟩, fun u hu => ?_⟩
      rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega),
        hn₆ u (by unfold ThreadId at *; omega)]
    · simp only [Array.getElem?_push, hsz₆]; exact hj₆
  sorry

end Cancel.Group
