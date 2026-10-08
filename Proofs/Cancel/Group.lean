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

end Cancel.Group
