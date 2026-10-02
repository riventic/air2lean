import Proofs.Sync.Semaphore

/-!
# `semaphoreCounter` over all schedules

`semaphoreCounter` spawns one thread; each of the two threads adds 1 two times to a counter `n`,
between `wait` and `post` of an `Io.Semaphore` with one permit (translated from Zig 0.16.0's std
code; the futex under it is the model). The result is 4 under every schedule
(`semaphoreCounter_spec`), and no schedule gives an error (`semaphoreCounter_safe`): no data race
on `n`, and no deadlock.

The proof uses the semaphore's specs (`Proofs/Sync/Semaphore.lean`): the free permit owns `n`
(`Sem.Res`), and the thread that took the permit owns `n` in its part. The value of `n` is the
number of increments of both threads. The proof of `main` follows `Proofs/Sync/Mutex.lean`.

- **Ghost values** (`SGh Ph`): the semaphore's mutex's part, the place in the semaphore's
  condition, and where the thread is in `main` or `semWork` (`Ph`): its number of increments,
  and if it has the permit.
- **The rest of the invariant** (`U`): the threads (`Shape`), the bytes of `io` (`IoOk`), the
  parts (`n` for the thread with the permit), the futex queue (only the semaphore's two futexes),
  at most one thread with the permit, and a thread at the condition has no permit.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

namespace Sync.SemCounter

/-- Where a thread is, outside the semaphore's code. -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- A thread in `semWork`: it did `k` increments; `hold`: it has the permit. -/
  | work (k : Nat) (hold : Bool)
  /-- `main` at its join. -/
  | joins
  /-- The kid has ended. -/
  | fin

/-- The increments of a thread. -/
def Ph.count : Ph → Nat
  | .work k _ => k
  | .joins | .fin => 2
  | _ => 0

/-- The thread has the permit. -/
def Ph.holds : Ph → Bool
  | .work _ b => b
  | _ => false

/-- The `SemCounter` (block 0): `io` at 0, the semaphore at 16, `n` at 40. -/
def cPtr : Ptr := ⟨some 0, 0⟩
def nPtr : Ptr := cPtr.add 40

/-- The increments of both threads. -/
def sum (X : ThreadId → Ph) : Nat := (X 0).count + (X 1).count

/-- A thread has the permit. -/
def held (X : ThreadId → Ph) : Bool := (X 0).holds || (X 1).holds

/-- `n` holds the increments of both threads. -/
def NP (X : ThreadId → Ph) : Assn := pts nPtr 4 (BitVec.ofNat 32 (sum X))

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- The bytes of `n`: 40..44 of block 0. -/
theorem np_off {v : BitVec 32} {h : Heap} (hp : pts nPtr 4 v h) {x : Nat}
    (hx : ¬ (40 ≤ x ∧ x < 44)) : h (0, x) = none := by
  obtain ⟨A, Sz, K, bs, -, hs, -, ⟨b, hb, -, hl⟩, -⟩ := hp
  cases hb
  rw [hl, if_neg]
  rintro ⟨-, h1, h2⟩
  rw [hs, show Enc.size (BitVec 32) = 4 from rfl] at h2
  simp only [nPtr, cPtr, Ptr.add] at h1 h2
  exact hx ⟨by simpa using h1, by simpa using h2⟩

/-- The semaphore: its free permit owns `n`. -/
def S : Sem Ph where
  b := 0
  o := 16
  pv X := if held X then 0 else 1
  Res X := if held X then emp else NP X
  res_off X h hR x h1 h2 := by
    by_cases hh : held X = true
    · simp only [hh, ↓reduceIte] at hR; rw [hR]; rfl
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at hR; exact np_off hR (by omega)
  wx p := ∃ k, p = .work k false

abbrev Gh := SGh Ph

/-- The places of the threads in `main` or `semWork`. -/
abbrev XG (G : ThreadId → Gh) : ThreadId → Ph := fun u => (G u).2.2

/-- Each access to the bytes of `io` (0..16) is a read, or happened before every thread. -/
def IoOk (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.off < 16 → e.kind = .read ∨ AllLe m e.clock

/-- The threads: `main` alone before its spawn; then `main` and the kid. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ X 0 = .pre ∧ ∀ u, 1 ≤ u → X u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (X 0 = .joins ∨ ∃ k ≤ 2, ∃ b, X 0 = .work k b) ∧ (X 1 = .fin ∨ ∃ k ≤ 2, ∃ b, X 1 = .work k b) ∧
    ∀ u, 2 ≤ u → X u = .none))

/-- Block 0 is the live `SemCounter`: 48 bytes on the stack, at an address that is a multiple
of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 48 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (XG G) m
  io : IoOk m
  parts : ∀ u, if (G u).2.2.holds then NP (XG G) (G u).1.part else (G u).1.part = Heap.empty
  blk : BlkOk m
  q : ∀ w ∈ m.waiters, w.2 = S.L.ptr ∨ w.2 = S.WE.ptr
  one : (G 0).2.2.holds = false ∨ (G 1).2.2.holds = false
  wx : ∀ u, (G u).2.1.waits = true → ∃ k, (G u).2.2 = .work k false

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := S.L.Inv G m ∧ S.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .semWork p => p = cPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, .none, .work 0 false)
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2.2 = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 4 ∧ joinedAll 0 m


/-! ## The protocol has the semaphore -/

theorem shape_work {X : ThreadId → Ph} {m : Mem} {t k : Nat} {b : Bool} (h : Shape X m)
    (hx : X t = .work k b) : t < 2 ∧ m.threads.size = 2 ∧ k ≤ 2 := by
  obtain ⟨-, ⟨-, h0, h1⟩ | ⟨hs, -, h0, h1, h2⟩⟩ := h
  · by_cases ht : t = 0
    · subst ht; rw [h0] at hx; cases hx
    · rw [h1 t (Nat.pos_of_ne_zero ht)] at hx; cases hx
  · have htl : t < 2 := by
      by_cases hc : t < 2
      · exact hc
      · rw [h2 t (Nat.le_of_not_lt hc)] at hx; cases hx
    refine ⟨htl, hs, ?_⟩
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rcases h0 with h0 | ⟨k', hk, b', h0⟩ <;> rw [h0] at hx <;> cases hx; exact hk
    · rcases h1 with h1 | ⟨k', hk, b', h1⟩ <;> rw [h1] at hx <;> cases hx; exact hk

/-- A thread with the permit is in `semWork`. -/
theorem holds_work {p : Ph} (h : p.holds = true) : ∃ k, p = .work k true := by
  cases p <;> simp_all [Ph.holds]

/-- The cell of byte `x < 48` of the `SemCounter`. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 48) : m.heap (0, x) ≠ none := by
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

/-- No thread owns a byte of `io`. -/
theorem own_io {G : ThreadId → Gh} {m : Mem} (hl : S.L.Inv G m) (hu : U G m) (u : ThreadId)
    {x : Nat} (hx : x < 16) : S.L.own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    have hp : (G u).1.part (0, x) = none := by
      have := hu.parts u
      split at this
      · exact np_off this (by omega)
      · rw [this]; rfl
    rw [Heap.union_apply, hp, Option.none_or]
    by_cases hh : S.L.ph (G u) = .holds
    · obtain ⟨hp, hr, -, he, hpp, hrr⟩ := hl.res u hh
      rw [show (G u).1.held = S.L.held (G u) from rfl, he]
      have h1 : hp (0, x) = none := by
        cases hc : hp (0, x) with
        | none => rfl
        | some c =>
          have := (Sem.pts_cells (S := S) hpp (l := (0, x)) (by rw [hc]; simp)).2.1
          simp [S] at this; omega
      have h2 : hr (0, x) = none := by
        change (if held _ then emp else NP _) hr at hrr
        split at hrr
        · rw [hrr]; rfl
        · exact np_off hrr (by omega)
      simp [Heap.union_apply, h1, h2]
    · rw [show (G u).1.held = S.L.held (G u) from rfl, hl.idle u hh]; rfl

/-- A zero permit count: a thread has the permit. -/
theorem held_of_pz {G : ThreadId → Gh} {m : Mem} (hl : S.L.Inv G m) (hpz : S.PZ m) :
    held (XG G) = true := by
  obtain ⟨hz, hzp, hzs⟩ := hpz
  have hR : ∃ hL, S.L.R G hL ∧ hL.Sub m.heap := by
    by_cases hf : ∃ u, S.L.ph (G u) = .holds
    · obtain ⟨u, hu⟩ := hf
      obtain ⟨hlv, hjt⟩ := hl.live u (by rw [hu]; decide)
      refine ⟨_, hl.res u hu, fun l c h => hl.own.sub u l c ?_⟩
      rw [Lock.own_live hjt]
      show (S.L.part (G u) ∪ S.L.held (G u)) l = some c
      rw [Heap.union_of_right ((hl.pdisj u l).resolve_right (by rw [h]; simp))]; exact h
    · obtain ⟨hL, hR, hs, -⟩ := hl.free (fun u h => hf ⟨u, h⟩)
      exact ⟨hL, hR, hs⟩
  obtain ⟨hL, ⟨hp, hr, -, rfl, hpp, -⟩, hs⟩ := hR
  have := Sem.pts_eq (S := S) hpp (fun l c h => hs l c (by simp [h])) hzp hzs
  change (if held _ then (0 : BitVec 64) else 1) = 0 at this
  split at this
  · assumption
  · cases this

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (g : Gh) (hu : U G m)
    (hs : S.Step t m m') (h2 : g.2.2 = (G t).2.2) (hp : g.1.part = (G t).1.part)
    (hw : g.2.1.waits = true → (G t).2.1.waits = true ∨ S.wx g.2.2) : U (upd G t g) m' := by
  have hX : XG (upd G t g) = XG G := funext fun u => by
    show (upd G t g u).2.2 = _; unfold upd; split
    · rename_i e; subst e; exact h2
    · rfl
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, blk_keep hu.blk (hs.cells _ ?_), fun w hw' => ?_,
    ?_, fun u hu' => ?_⟩
  · rw [hX]; have := hu.shape; unfold Shape at this ⊢; rw [hs.threads]; exact this
  · rcases hs.fp e he with h' | ⟨-, -, ho', -⟩
    · rcases hu.io e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr fun u hu' => VClock.le_trans (h'' u (by rw [← hs.threads]; exact hu'))
          (hs.clocks u)
    · exact absurd ho (by simp [S] at ho'; omega)
  · rw [hX]; by_cases e : u = t
    · subst e; rw [upd_self, h2, hp]; exact hu.parts u
    · rw [upd_ne _ _ e]; exact hu.parts u
  · rintro ⟨-, h1, -⟩; simp [S] at h1
  · by_cases h1 : w.2 = S.L.ptr
    · exact .inl h1
    · by_cases h2 : w.2 = S.WE.ptr
      · exact .inr h2
      · exact hu.q w (hs.waiters w hw' h1 h2)
  · have h0 := congrFun hX 0; have h1 := congrFun hX 1
    simp only [XG] at h0 h1; rw [h0, h1]; exact hu.one
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢
      rcases hw hu' with h | h
      · rw [h2]; exact hu.wx u h
      · exact h
    · rw [upd_ne _ _ e] at hu' ⊢; exact hu.wx u hu'

theorem own_step (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (g : Gh) (hQ : Heap)
    (hl : S.L.Inv G m) (hu : U G m) (hs : StepIn (m.heap.diff (S.L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (S.L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (S.L.own G m t))) (h2 : g.2 = (G t).2)
    (hp : g.1.part = (G t).1.part) : U (upd G t g) m' := by
  have hX : XG (upd G t g) = XG G := funext fun u => by
    show (upd G t g u).2.2 = _; unfold upd; split
    · rename_i e; subst e; rw [h2]
    · rfl
  have hrest : ∀ x, x < 16 → m.heap.diff (S.L.own G m t) (0, x) = m.heap (0, x) := fun x hx => by
    simp [Heap.diff, own_io hl hu t hx]
  have hS : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact h2
    · rfl
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, blk_keep hu.blk ?_, fun w hw => ?_, ?_,
    fun u hu' => ?_⟩
  · rw [hX]; have := hu.shape; unfold Shape at this ⊢; rw [hs.threads]; exact this
  · rcases hs.fp e he with h' | ⟨-, hnt, -⟩
    · rcases hu.io e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr (allLe_stepIn hs h'')
    · exact absurd ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [hb, hrest _ ho]; exact blk_heap hu.blk (by omega)⟩ hnt
  · rw [hX]; by_cases e : u = t
    · subst e; rw [upd_self, h2, hp]; exact hu.parts u
    · rw [upd_ne _ _ e]; exact hu.parts u
  · rw [hm', Heap.union_of_right ((hd (0, 0)).resolve_right (by
      rw [hrest 0 (by decide)]; exact blk_heap hu.blk (by decide))), hrest 0 (by decide)]
  · rw [hs.waiters] at hw; exact hu.q w hw
  · rw [hS 0, hS 1]; exact hu.one
  · rw [hS] at hu' ⊢; exact hu.wx u hu'

theorem fits : S.Fits proto U where
  inv _ _ := Iff.rfl
  fin _ h := h.1
  joins _ h := h.1
  stable := stable
  own G m m' t g hQ hl hu hs hm' hd _ _ h2 hp _ := own_step G m m' t g hQ hl hu hs hm' hd h2 hp
  waits _ _ w hi hw _ := hi.2.2.q w hw
  live G m r i jr sn e hi hr hpz hall := by
    obtain ⟨hl, hs, hu⟩ := hi
    have hh := held_of_pz hl hpz
    obtain ⟨v, hv⟩ : ∃ v, (G v).2.2.holds = true := by
      simp only [held, Bool.or_eq_true] at hh
      rcases hh with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨k, hk⟩ := holds_work hv
    obtain ⟨hv2, hs2, -⟩ := shape_work hu.shape hk
    rcases hall v (by omega) with hf | hq | hj
    · rw [hf.2] at hv; cases hv
    · obtain ⟨i', hi', he⟩ := Array.any_eq_true.mp hq
      have he : (m.waiters[i']).1 = v := by simpa using he
      have hw := Array.getElem_mem hi'
      rcases hu.q _ hw with hL | hE
      · -- a waiter at the mutex: its lock witness goes on
        obtain ⟨v', hv', hq', hb, -⟩ := hl.wit (Array.any_eq_true.mpr ⟨i', hi', by simp [hL]⟩)
        rcases hall v' hv' with h | h | h
        · rw [show S.L.ph (G v') = .gone from h.1] at hb; cases hb
        · rw [hq'] at h; cases h
        · rw [show S.L.ph (G v') = .out from h.1] at hb; cases hb
      · obtain ⟨i'', jr', e', h1, -⟩ := hs.q _ hw hE
        rw [he] at h1
        obtain ⟨k', hk'⟩ := hu.wx v (by rw [h1]; rfl)
        rw [hk'] at hv; cases hv
    · rw [hj.2] at hv; cases hv


/-! ## `io` -/

/-- The mutex's resource has no byte of `io`. -/
theorem R_io {Y : ThreadId → SPh × Ph} {h : Heap} (hR : S.R Y h) {x : Nat} (hx : x < 16) :
    h (0, x) = none := by
  obtain ⟨hp, hr, -, rfl, hpp, hrr⟩ := hR
  have h1 : hp (0, x) = none := by
    cases hc : hp (0, x) with
    | none => rfl
    | some c =>
      have := (Sem.pts_cells (S := S) hpp (l := (0, x)) (by rw [hc]; simp)).2.1
      simp [S] at this; omega
  have h2 : hr (0, x) = none := by
    change (if held _ then emp else NP _) hr at hrr
    split at hrr
    · rw [hrr]; rfl
    · exact np_off hrr (by omega)
  simp [Heap.union_apply, h1, h2]

theorem noRace_io {m : Mem} (hio : IoOk m) (ht : m.current < m.threads.size) :
    NoRace m 0 0 16 .read :=
  noRace_of fun e he hb _ h2 => by
    rcases hio e he hb (by omega) with h | h
    · exact .inr (by rw [h]; rfl)
    · exact .inl (h _ ht)

/-- A read of `io` (bytes 0..16): no race, and the invariant holds after it. -/
theorem step_io {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (ht : m.current < m.threads.size) :
    (load Io 8 cPtr).run m = pure (⟨⟩, m.recordAt 0 0 16 .read) ∧
      proto.inv G (m.recordAt 0 0 16 .read) := by
  obtain ⟨hl, hs, hu⟩ := hi
  obtain ⟨blk, hblk, hlv, hsz, ha, hk⟩ := hu.blk
  have hacc : m.access cPtr (Enc.size Io) 8 = pure (0, blk, 0) :=
    access_of (p := cPtr) rfl hblk hlv (by decide)
      (by rw [show Enc.size Io = 16 from rfl]; simp [cPtr, hsz]) (by simpa [cPtr] using ha)
  have hk' : ∀ (W : Word 32 4), (W = S.WS ∨ W = S.WE) → W.Keep m (m.recordAt 0 0 16 .read) :=
    fun W hW => Word.keep_read m (by decide) (.inr (.inl (by rcases hW with rfl | rfl <;> decide)))
  refine ⟨load_run hacc rfl (noRace_io hu.io ht), hl.read (b := 0) (o := 0) (n := 16)
      (Array.getElem?_eq_some_iff.mp hblk).1 (by decide)
      (fun u x _ hx => own_io hl hu u (by omega)) (fun hL hR x _ hx => R_io hR (by omega))
      (.inr (.inl (by decide))),
    hs.mono (hs.ws.keep (hk' _ (.inl rfl))) (hs.we.keep (hk' _ (.inr rfl)))
      (Word.hist_keep hs.ws (hk' _ (.inl rfl))) (Word.hist_keep hs.we (hk' _ (.inr rfl)))
      (recordAt_le m _ _ _ _) (fun c ⟨i, l, h1, h2⟩ => ⟨i, l, h1, h2⟩) (fun h => .inl h)
      (fun w hw _ => .inl hw) (by simp [Mem.recordAt]),
    ⟨hu.shape, fun e he hb ho => ?_, hu.parts, hu.blk, hu.q, hu.one, hu.wx⟩⟩
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · rcases hu.io e he hb ho with h | h
    · exact .inl h
    · exact .inr fun u hu => VClock.le_trans (h u hu) (recordAt_le m 0 0 16 .read u)
  · exact .inl rfl

/-- A read of `io` by thread `t` in generated code. -/
theorem wp_io {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh}
    (hi : proto.inv (upd G t g) m) (hc : m.current = t) (ht : t < m.threads.size)
    {Q : Io × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.current = t → m'.threads = m.threads → proto.inv (upd G t g) m' →
      Q (⟨⟩, s) G m' d) :
    proto.WP t ((liftM (load Io 8 cPtr) : CM Tgt σ Io).run s) Q G m d := by
  obtain ⟨hrun, hi'⟩ := step_io hi (hc ▸ ht)
  refine WP.liftM (fun e he => (MemM.noErr_of_run hrun e he).elim) fun v m' hr => ?_
  rw [hrun] at hr
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  cases v
  exact ⟨rfl, h _ hc rfl hi'⟩

end Sync.SemCounter
