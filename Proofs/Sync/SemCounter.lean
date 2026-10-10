import ZigLean.Conc.Unroll
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

attribute [local irreducible] Proto.WP

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
    (hw : g.2.1.waits = true → (G t).2.1.waits = true ∨ S.wx g.2.2)
    (_ : (g.1.ph ≠ (G t).1.ph ∨ g.2.1 ≠ (G t).2.1) → S.inS g.2.2) : U (upd G t g) m' := by
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
  waits _ _ w _ _ _ _ hi hw _ := hi.2.2.q w hw
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
      (fun w hw _ => .inl hw) (Sem.allLe_keep (recordAt_le m _ _ _ _) (by simp [Mem.recordAt])),
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


/-! ## `n`, by the thread with the permit -/

theorem XG_upd (G : ThreadId → Gh) (t : ThreadId) (g : Gh) :
    XG (upd G t g) = upd (XG G) t g.2.2 := by
  funext u; show (upd G t g u).2.2 = _; unfold upd; split <;> rfl

/-- A thread in `semWork` goes to `work k' b'`, or `main` to `joins`, or the kid to `fin`. -/
theorem shape_set {X : ThreadId → Ph} {m : Mem} {t k : Nat} {b : Bool} (h : Shape X m)
    (hx : X t = .work k b) (p : Ph) (hp : (∃ k' ≤ 2, ∃ b', p = .work k' b') ∨ (t = 0 ∧ p = .joins) ∨
      (t = 1 ∧ p = .fin)) : Shape (upd X t p) m := by
  obtain ⟨htl, -, -⟩ := shape_work h hx
  obtain ⟨h00, ⟨-, h0, h1⟩ | ⟨hs, hr, h0, h1, h2⟩⟩ := h
  · rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rw [h0] at hx; cases hx
    · rw [h1 1 (Nat.le_refl _)] at hx; cases hx
  refine ⟨h00, .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩⟩
  · by_cases ht : t = 0
    · subst ht; rw [upd_self]
      rcases hp with ⟨k', hk, b', rfl⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
      · exact .inr ⟨k', hk, b', rfl⟩
      · exact .inl rfl
      · cases h
    · rw [upd_ne _ _ (Ne.symm ht)]; exact h0
  · by_cases ht : t = 1
    · subst ht; rw [upd_self]
      rcases hp with ⟨k', hk, b', rfl⟩ | ⟨h, -⟩ | ⟨-, rfl⟩
      · exact .inr ⟨k', hk, b', rfl⟩
      · cases h
      · exact .inl rfl
    · rw [upd_ne _ _ (Ne.symm ht)]; exact h1
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h2 u hu

/-- With a thread that has the permit, the mutex's resource is the permit count 0. -/
theorem R_held {Y Y' : ThreadId → SPh × Ph} (h : held (Sem.xs Y) = true) (h' : held (Sem.xs Y') = true)
    (hL : Heap) : S.R Y hL ↔ S.R Y' hL := by
  show (pts S.ptr 8 (if held _ then 0 else 1) ∗ (if held _ then emp else NP _)) hL ↔
    (pts S.ptr 8 (if held _ then 0 else 1) ∗ (if held _ then emp else NP _)) hL
  rw [h, h']; simp

/-- The other thread has no permit. -/
theorem other_free {G : ThreadId → Gh} {m : Mem} (hu : U G m) {t k : Nat} (hk : (G t).2.2 = .work k true)
    {u : ThreadId} (hut : u ≠ t) : (G u).2.2.holds = false := by
  cases hu' : (G u).2.2.holds
  · rfl
  · exfalso
    obtain ⟨k', hk'⟩ := holds_work hu'
    obtain ⟨ht2, -, -⟩ := shape_work hu.shape hk
    obtain ⟨hu2, -, -⟩ := shape_work hu.shape hk'
    have : t = 0 ∧ u = 1 ∨ t = 1 ∧ u = 0 := by unfold ThreadId at *; omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hu.one with h | h <;> simp_all [Ph.holds]

/-- The load or the store of `n` by thread `t`, which has the permit, after `k` increments; after
it, `t` did `k'` increments. -/
theorem wp_n {σ β : Type} {c : MemM β} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem}
    {d : Nat} {h : Heap} {k k' : Nat} {v' : BitVec 32} {r₀ : β}
    {Q : β × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hi : proto.inv (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true)) m) (hc : m.current = t)
    (ht : TTriple (pts nPtr 4 (BitVec.ofNat 32 (sum (XG (upd G t (⟨.out, h, Heap.empty⟩, .none,
      .work k true)))))) c (fun r => ⌜r = r₀⌝ ∗ pts nPtr 4 v'))
    (hv' : v' = BitVec.ofNat 32 (sum (XG (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k' true)))))
    (hk' : k' ≤ 2)
    (hq : ∀ m' h', m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (⟨.out, h', Heap.empty⟩, .none, .work k' true)) m' → Q (r₀, s) G m' d) :
    proto.WP t ((liftM c : CM Tgt σ β).run s) Q G m d := by
  obtain ⟨hl, hs, hu⟩ := hi
  have hgt : (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true) t).2.2 = .work k true := by
    rw [upd_self]
  obtain ⟨ht2, hs2, -⟩ := shape_work hu.shape hgt
  have hph : S.L.ph (upd G t (⟨.out, h, Heap.empty⟩, SPh.none, Ph.work k true) t) = .out := by
    rw [upd_self]; rfl
  obtain ⟨htl, hjt⟩ := hl.live t (by rw [hph]; decide)
  have hown : S.L.own (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true)) m t = h := by
    rw [Lock.own_live hjt, upd_self]; exact Heap.union_empty h
  have hpart : NP (XG (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true))) h := by
    have := hu.parts t; rw [upd_self] at this; simp only [Ph.holds, ↓reduceIte] at this; exact this
  refine WP.liftM_owned ht hl.own hc htl (by rw [hown]; exact hpart)
    fun a m' hQ _ ho' hq' hst hm' hd => ?_
  obtain ⟨rfl, hpQ⟩ := sep_lift.mp hq'
  rw [hown] at hst hm' hd
  let g' : Gh := (⟨.out, hQ, Heap.empty⟩, .none, .work k' true)
  have hX : XG (upd (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true)) t g') =
      XG (upd G t g') := by rw [upd_upd]
  have hheld : ∀ G₀ : ThreadId → Gh, (G₀ t).2.2.holds = true → held (XG G₀) = true := fun G₀ h₀ => by
    simp only [held, Bool.or_eq_true]
    rcases (show t = 0 ∨ t = 1 by unfold ThreadId at *; omega) with rfl | rfl
    · exact .inl h₀
    · exact .inr h₀
  have hl' := hl.stepIn (g := g') hc hjt
    (by show Owned (upd _ t (hQ ∪ Heap.empty)) m'; rw [Heap.union_empty]; exact ho')
    (by rw [hown]; exact hst)
    (by rw [hown]; show m'.heap = (hQ ∪ Heap.empty) ∪ _; rw [Heap.union_empty]; exact hm')
    (by rw [hown]; show Heap.Disjoint (hQ ∪ Heap.empty) _; rw [Heap.union_empty]; exact hd)
    (by rw [upd_self]; rfl) (Heap.disjoint_empty _) (fun _ => rfl)
    (fun _ hL hR => (R_held (hheld _ (by rw [upd_self]; rfl)) (hheld _ (by rw [upd_self]; rfl)) hL).mp hR)
    (fun h₀ => by cases h₀)
  rw [upd_upd] at hl'
  have hnone : ∀ x, ¬ (40 ≤ x ∧ x < 44) → m'.heap (0, x) = m.heap (0, x) := fun x hx => by
    rw [hm', Heap.union_apply, np_off hpQ hx, Option.none_or]
    simp [Heap.diff, np_off hpart hx]
  have hpz : S.PZ m → S.PZ m' ∨ ∃ v, (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true) v).2.1 = .pst :=
    fun hz => .inl (Sem.PZ.mono hz fun x h1 h2 => hnone x (by simp [S] at h1 h2; omega))
  have hs' := (hs.stepIn hl (by rw [hown]; exact hst) (by rw [hown]; exact hm')
    (by rw [hown]; exact hd) hpz).congrG (G' := upd G t g') (fun u => by unfold upd; split <;> rfl)
    (fun u => by unfold upd; split <;> exact Iff.rfl) (fun u x h1 h2 => by
      by_cases e : u = t
      · subst e; rw [upd_self]; exact np_off hpQ (by simp [S] at h1 h2; omega)
      · rw [upd_ne _ _ e]; have := hs.off u x h1 h2; rwa [upd_ne _ _ e] at this)
  have hXn : XG (upd G t g') = upd (XG (upd G t (⟨.out, h, Heap.empty⟩, .none, .work k true))) t
      (.work k' true) := by rw [XG_upd, XG_upd, upd_upd]
  have hoth : ∀ u, u ≠ t → (G u).2.2.holds = false := fun u hut => by
    have := other_free hu hgt hut; rwa [upd_ne _ _ hut] at this
  refine hq m' hQ (hst.current.trans hc) hst.threads ⟨hl', hs', ⟨?_, fun e he hb ho => ?_,
    fun u => ?_, blk_keep hu.blk (hnone 0 (by omega)), fun w hw => ?_, ?_, fun u hu' => ?_⟩⟩
  · rw [hXn]; have := shape_set hu.shape hgt (.work k' true) (.inl ⟨k', hk', true, rfl⟩)
    unfold Shape at this ⊢; rw [hst.threads]; exact this
  · rcases hst.fp e he with h' | ⟨-, hnt, -⟩
    · rcases hu.io e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr (allLe_stepIn hst h'')
    · exact absurd ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [hb]; simp [Heap.diff, np_off hpart (show ¬ (40 ≤ e.off ∧ e.off < 44) by omega)]
        exact blk_heap hu.blk (by omega)⟩ hnt
  · by_cases e : u = t
    · subst e; rw [upd_self]
      show NP (XG (upd G u g')) hQ
      rw [hv'] at hpQ; unfold NP
      rw [show XG (upd G u g') = XG (upd G u (⟨.out, h, Heap.empty⟩, .none, .work k' true)) by
        rw [XG_upd, XG_upd]]
      exact hpQ
    · rw [upd_ne _ _ e]
      have := hu.parts u; rw [upd_ne _ _ e, hoth u e] at this
      rw [hoth u e]; exact this
  · rw [hst.waiters] at hw; exact hu.q w hw
  · rcases (show t = 0 ∨ t = 1 by unfold ThreadId at *; omega) with rfl | rfl
    · exact .inr (by rw [upd_ne _ _ (by decide)]; exact hoth 1 (by decide))
    · exact .inl (by rw [upd_ne _ _ (by decide)]; exact hoth 0 (by decide))
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu'; cases hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.wx u (by rw [upd_ne _ _ e]; exact hu')
      rwa [upd_ne _ _ e] at this


/-! ## The semaphore's specs for this protocol -/

/-- A new ghost value `g'` of thread `t`, with the same memory and the same sum. -/
theorem np_e {X : ThreadId → Ph} {h : Heap} : NP X (Heap.empty ∪ h) ↔ NP X h := by
  rw [Heap.empty_union]

theorem U_retag {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g g' : Gh} (hu : U (upd G t g) m)
    (hsh : Shape (XG (upd G t g')) m)
    (hpt : if g'.2.2.holds then NP (XG (upd G t g')) g'.1.part else g'.1.part = Heap.empty)
    (hsum : sum (XG (upd G t g')) = sum (XG (upd G t g)))
    (hone : g'.2.2.holds = false ∨ ∀ u, u ≠ t → (G u).2.2.holds = false)
    (hwx : g'.2.1.waits = true → ∃ k, g'.2.2 = .work k false) : U (upd G t g') m := by
  refine ⟨hsh, hu.io, fun u => ?_, hu.blk, hu.q, ?_, fun u hu' => ?_⟩
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hpt
    · have := hu.parts u
      rw [upd_ne _ _ e] at this ⊢
      unfold NP at this ⊢; rw [hsum]; exact this
  · have h0 := hu.one
    rcases hone with h | h
    · by_cases e0 : t = 0
      · subst e0; exact .inl (by rw [upd_self]; exact h)
      · by_cases e1 : t = 1
        · subst e1; exact .inr (by rw [upd_self]; exact h)
        · rw [upd_ne _ _ (Ne.symm e0), upd_ne _ _ (Ne.symm e1)] at h0 ⊢; exact h0
    · by_cases e0 : t = 0
      · subst e0; exact .inr (by rw [upd_ne _ _ (by decide)]; exact h 1 (by decide))
      · exact .inl (by rw [upd_ne _ _ (Ne.symm e0)]; exact h 0 (Ne.symm e0))
  · by_cases e : u = t
    · subst e; rw [upd_self] at hu' ⊢; exact hwx hu'
    · rw [upd_ne _ _ e] at hu' ⊢; have := hu.wx u (by rw [upd_ne _ _ e]; exact hu')
      rwa [upd_ne _ _ e] at this

/-- `n` has a byte. -/
theorem np_cell {v : BitVec 32} {h : Heap} (hp : pts nPtr 4 v h) : h (0, 40) ≠ none := by
  obtain ⟨A, Sz, K, bs, -, hs, -, hb, -⟩ := hp
  exact bytesAt_in hb rfl (by simp [nPtr, cPtr, Ptr.add]) (by
    rw [hs, show Enc.size (BitVec 32) = 4 from rfl]; simp [nPtr, cPtr, Ptr.add])

/-- The sum after a change of the permit flag of thread `t`. -/
theorem sum_flag (X : ThreadId → Ph) (t k : Nat) (b b' : Bool) (hx : X t = .work k b) :
    sum (upd X t (.work k b')) = sum X := by
  unfold sum
  by_cases h0 : t = 0
  · subst h0; rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), hx]; rfl
  · by_cases h1 : t = 1
    · subst h1; rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), hx]; rfl
    · rw [upd_ne _ _ (Ne.symm h0), upd_ne _ _ (Ne.symm h1)]

section Specs

variable (t : ThreadId) (k : Nat)

/-- In `wait`, no other thread waits at the condition: the thread with the permit is neither
`t` nor a waiter. -/
theorem hone_w : ∀ G' m', proto.inv G' m' → (G' t).2.2 = .work k false →
    (G' t).1.ph = .holds → S.PZ m' → ∀ u, u ≠ t → ∀ i jr sn e, (G' u).2.1 ≠ .reg i jr sn e := by
  intro G' m' hi hx _ hpz u hut i jr sn e hr
  obtain ⟨hl, -, hu⟩ := hi
  obtain ⟨ku, hku⟩ := hu.wx u (by rw [hr]; rfl)
  have hh := held_of_pz hl hpz
  obtain ⟨ht2, -, -⟩ := shape_work hu.shape hx
  obtain ⟨hu2, -, -⟩ := shape_work hu.shape hku
  simp only [held, Bool.or_eq_true, XG] at hh
  have : t = 0 ∧ u = 1 ∨ t = 1 ∧ u = 0 := by unfold ThreadId at *; omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hx, hku] at hh <;> simp [Ph.holds] at hh

theorem hmv_w (ht : t < 2) : ∀ Y : ThreadId → Ph, Y t = .work k false → S.pv Y ≠ 0 →
    S.pv (upd Y t (.work k true)) = S.pv Y - 1 ∧
    ∀ hr, S.Res Y hr → ∃ h₁ h₂, hr = h₁ ∪ h₂ ∧ Heap.Disjoint h₁ h₂ ∧
      S.Res (upd Y t (.work k true)) h₁ ∧ (fun h => ∃ v : BitVec 32, pts nPtr 4 v h) h₂ := by
  intro Y hY hpv
  have hn : held Y = false := by
    cases h : held Y
    · rfl
    · exact absurd (by show (if held Y then (0 : BitVec 64) else 1) = 0; rw [h]; rfl) hpv
  have hy : held (upd Y t (.work k true)) = true := by
    simp only [held, Bool.or_eq_true]
    rcases (show t = 0 ∨ t = 1 by unfold ThreadId at *; omega) with rfl | rfl
    · exact .inl (by rw [upd_self]; rfl)
    · exact .inr (by rw [upd_self]; rfl)
  refine ⟨?_, fun hr hR => ⟨Heap.empty, hr, (Heap.empty_union hr).symm, Heap.disjoint_empty _ |>.symm, ?_, ?_⟩⟩
  · show (if held _ then (0 : BitVec 64) else 1) = (if held Y then (0 : BitVec 64) else 1) - 1
    rw [hy, hn]; rfl
  · show (if held _ then emp else NP _) Heap.empty; rw [hy]; rfl
  · have : (if held Y then emp else NP Y) hr := hR
    rw [hn] at this; exact ⟨_, this⟩

/-- With no permit taken, no thread has it. -/
theorem holds_of_held {X : ThreadId → Ph} {m : Mem} (hs : Shape X m) (hn : held X = false) (u : ThreadId) :
    (X u).holds = false := by
  simp only [held, Bool.or_eq_false_iff] at hn
  by_cases h0 : u = 0
  · subst h0; exact hn.1
  · by_cases h1 : u = 1
    · subst h1; exact hn.2
    · rcases hs.2 with ⟨-, -, h⟩ | ⟨-, -, -, -, h⟩
      · rw [h u (by unfold ThreadId at *; omega)]; rfl
      · rw [h u (by unfold ThreadId at *; omega)]; rfl

theorem hU_w : ∀ G m h₁ h₂ h₃ h₄, (fun h => ∃ v : BitVec 32, pts nPtr 4 v h) h₃ →
    Heap.Disjoint h₄ h₃ →
    S.Res (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false) u).2) (h₄ ∪ h₃) →
    U (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false)) m →
    U (upd G t (⟨.holds, Heap.empty ∪ h₃, h₂⟩, .none, .work k true)) m := by
  intro G m h₁ h₂ h₃ h₄ ⟨v, hv⟩ hd hR hu
  have hx : XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false)) t = .work k false := by
    show (upd G t _ t).2.2 = _; rw [upd_self]
  have hR' : (if held (XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false))) then emp
      else NP (XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false)))) (h₄ ∪ h₃) := hR
  have hn : held (XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false))) = false := by
    cases h : held (XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false)))
    · rfl
    · exfalso; rw [h] at hR'
      have := congrFun hR' (0, 40)
      simp only [Heap.union_apply, Heap.empty, Option.or_eq_none_iff] at this
      exact np_cell hv this.2
  rw [hn] at hR'
  simp only [Bool.false_eq_true, ↓reduceIte] at hR'
  have hve := Sem.pts_same hv (Heap.sub_union_right hd) hR' (fun _ _ h => h)
  have hX' : XG (upd G t (⟨.holds, Heap.empty ∪ h₃, h₂⟩, .none, .work k true)) =
      upd (XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false))) t (.work k true) := by
    rw [XG_upd, XG_upd, upd_upd]
  have hsum := sum_flag _ t k false true hx
  refine U_retag hu (by rw [hX']; exact shape_set hu.shape hx _ (.inl ⟨k, (shape_work hu.shape hx).2.2,
    true, rfl⟩)) ?_ (by rw [hX', hsum]) (.inr fun u hut => ?_) (fun h => by cases h)
  · show NP _ (Heap.empty ∪ h₃)
    refine np_e.mpr ?_
    unfold NP; rw [hX', hsum, ← hve]; exact hv
  · have := holds_of_held hu.shape hn u
    show (G u).2.2.holds = false
    have e : XG (upd G t (⟨.holds, Heap.empty, h₁⟩, .none, .work k false)) u = (G u).2.2 := by
      show (upd G t _ u).2.2 = _; rw [upd_ne _ _ hut]
    rwa [e] at this

variable (h₃ : Heap)

theorem hmv_p (ht : t < 2) : ∀ G m hL,
    proto.inv (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true)) m →
    S.pv (upd (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2) t
        (.work k false)) =
      S.pv (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2) + 1 ∧
    (S.pv (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2)).toNat
      + 1 < 2 ^ 64 ∧
    ∀ hr, S.Res (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2) hr →
      Heap.Disjoint h₃ hr →
      S.Res (upd (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2) t
        (.work k false)) (h₃ ∪ hr) := by
  intro G m hL hi
  obtain ⟨-, -, hu⟩ := hi
  have hx : XG (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true)) t = .work k true := by
    show (upd G t _ t).2.2 = _; rw [upd_self]
  have hy : held (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2)
      = true := by
    change held (XG _) = true
    simp only [held, Bool.or_eq_true]
    rcases (show t = 0 ∨ t = 1 by unfold ThreadId at *; omega) with rfl | rfl
    · exact .inl (by rw [hx]; rfl)
    · exact .inr (by rw [hx]; rfl)
  have hoth : ∀ u, u ≠ t → (XG (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true)) u).holds
      = false := fun u hut => other_free hu hx hut
  have hn : held (upd (Sem.xs fun u => (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true) u).2) t
      (.work k false)) = false := by
    change held (upd (XG _) t _) = false
    simp only [held, Bool.or_eq_false_iff]
    rcases (show t = 0 ∨ t = 1 by unfold ThreadId at *; omega) with rfl | rfl
    · exact ⟨by rw [upd_self]; rfl, by rw [upd_ne _ _ (by decide)]; exact hoth 1 (by decide)⟩
    · exact ⟨by rw [upd_ne _ _ (by decide)]; exact hoth 0 (by decide), by rw [upd_self]; rfl⟩
  refine ⟨?_, ?_, fun hr hR hd => ?_⟩
  · show (if held _ then (0 : BitVec 64) else 1) = (if held _ then (0 : BitVec 64) else 1) + 1
    rw [hn, hy]; rfl
  · show (if held _ then (0 : BitVec 64) else 1).toNat + 1 < _
    rw [hy]; decide
  · have hR' : (if held _ then emp else NP _) hr := hR
    rw [hy] at hR'
    change hr = Heap.empty at hR'
    subst hR'
    show (if held _ then emp else NP _) (h₃ ∪ Heap.empty)
    rw [hn, Heap.union_empty]; simp only [Bool.false_eq_true, ↓reduceIte]
    change NP (upd (XG (upd G t (⟨.holds, Heap.empty ∪ h₃, hL⟩, .pst, .work k true))) t (.work k false)) h₃
    have := hu.parts t
    rw [upd_self] at this
    simp only [Ph.holds, ↓reduceIte] at this
    refine np_e.mp ?_
    unfold NP at this ⊢
    rw [sum_flag _ t k true false hx]; exact this

theorem hU_p : ∀ G m h₁ h₂, U (upd G t (⟨.holds, Heap.empty ∪ h₃, h₁⟩, .pst, .work k true)) m →
    U (upd G t (⟨.holds, Heap.empty, h₂⟩, .pst, .work k false)) m := by
  intro G m h₁ h₂ hu
  have hx : XG (upd G t (⟨.holds, Heap.empty ∪ h₃, h₁⟩, .pst, .work k true)) t = .work k true := by
    show (upd G t _ t).2.2 = _; rw [upd_self]
  have hX' : XG (upd G t (⟨.holds, Heap.empty, h₂⟩, .pst, .work k false)) =
      upd (XG (upd G t (⟨.holds, Heap.empty ∪ h₃, h₁⟩, .pst, .work k true))) t (.work k false) := by
    rw [XG_upd, XG_upd, upd_upd]
  refine U_retag hu (by rw [hX']; exact shape_set hu.shape hx _ (.inl ⟨k, (shape_work hu.shape hx).2.2,
    false, rfl⟩)) (by show Heap.empty = Heap.empty; rfl) (by rw [hX', sum_flag _ t k true false hx])
    (.inl rfl) (fun h => by cases h)

end Specs


/-! ## `semWork` -/

/-- A thread in `semWork` without the permit, after `k` increments. -/
def gOut (k : Nat) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .none, .work k false)

theorem sum_le {X : ThreadId → Ph} {m : Mem} {t k : Nat} {b : Bool} (h : Shape X m)
    (hx : X t = .work k b) : sum X ≤ k + 2 := by
  obtain ⟨htl, hs2, -⟩ := shape_work h hx
  obtain ⟨-, ⟨hs1, -, -⟩ | ⟨-, -, h0, h1, -⟩⟩ := h
  · omega
  have c0 : (X 0).count ≤ 2 := by
    rcases h0 with h0 | ⟨k', hk, b', h0⟩ <;> rw [h0]
    · decide
    · exact hk
  have c1 : (X 1).count ≤ 2 := by
    rcases h1 with h1 | ⟨k', hk, b', h1⟩ <;> rw [h1]
    · decide
    · exact hk
  unfold sum
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [hx]; show k + _ ≤ _; omega
  · rw [hx]; show _ + k ≤ _; omega

theorem sum_succ {X : ThreadId → Ph} {t k : Nat} {b : Bool} (ht : t < 2) (hx : X t = .work k b) :
    sum (upd X t (.work (k + 1) b)) = sum X + 1 := by
  unfold sum
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), hx]; simp only [Ph.count]; omega
  · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), hx]; simp only [Ph.count]; omega

/-- `semWork`'s loop invariant: thread `t` did `local1` increments, without the permit. -/
def workInv (t : ThreadId) (s : semWorkLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = t ∧ s.local1.toNat ≤ 2 ∧ proto.inv (upd G t (gOut s.local1.toNat)) m

/-- `semWork`'s loop ends after 2 increments. -/
def workPost (t : ThreadId) (r : semWorkExit × semWorkLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  r.1 = .br3 ∧ m.current = t ∧ proto.inv (upd G t (gOut 2)) m

/-- A field pointer of the 48-byte `SemCounter` (block 0, `BlkOk`) is formed (`ptrProject`,
MM-3). -/
theorem projC {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {k : Nat} (hk : k ≤ 48) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hi.2.2.blk
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

theorem loop4_body (t : ThreadId) (s : semWorkLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : workInv t s G m d) :
    proto.WP t ((semWork.loop4 cPtr).run s) (fun r G' m' d' =>
      if semWork.again4 r.1 then workInv t r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : semWorkLocals) => 0) s)
      else workPost t r G' m' d') G m d := by
  obtain ⟨hc, hle, hi⟩ := h
  unfold semWork.loop4
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hx : XG (upd G t (gOut s.local1.toNat)) t = .work s.local1.toNat false := by
    show (upd G t (gOut _) t).2.2 = _; rw [upd_self]; rfl
  obtain ⟨ht2, hs2, -⟩ := shape_work hi.2.2.shape hx
  have htl : t < m.threads.size := by rw [hs2]; exact ht2
  split
  · rename_i hlt
    have hlt' : s.local1.toNat < 2 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callMC_ptrProject (projC hi (k := 16) (by decide)) ?_)
    dsimp only
    rw [show cPtr.add 16 = S.ptr from rfl]
    -- the read of `io`, then `wait`
    refine WP.bind (wp_io hi hc htl fun m₁ hc₁ ht₁ hi₁ => ?_)
    refine WP.bind (WP.callC (WP.mono ?_ (Sem.wait_spec fits t Heap.empty (.work s.local1.toNat false)
      (.work s.local1.toNat true) (fun h => ∃ v : BitVec 32, pts nPtr 4 v h) _
      (hone_w t _) ⟨_, rfl⟩ trivial trivial (hmv_w t _ ht2) (hU_w t _) G m₁ d hi₁)))
    rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, h₃, -, hi₂⟩
    refine WP.bind (WP.callMC_ptrProject (projC hi₂ (k := 40) (by decide)) ?_)
    dsimp only
    rw [show cPtr.add 40 = nPtr from rfl]
    -- the load of `n`
    refine WP.bind (wp_n hi₂ hc₂ (TTriple.load (by decide)) rfl (by omega)
      fun m₃ h₄ hc₃ ht₃ hi₃ => ?_)
    have hx₂ : XG (upd G₂ t (⟨.out, Heap.empty ∪ h₃, Heap.empty⟩, .none, .work s.local1.toNat true)) t =
        .work s.local1.toNat true := by show (upd G₂ t _ t).2.2 = _; rw [upd_self]
    have hsum := sum_le hi₂.2.2.shape hx₂
    generalize hS : sum (XG (upd G₂ t (⟨.out, Heap.empty ∪ h₃, Heap.empty⟩, .none,
      .work s.local1.toNat true))) = S at hsum ⊢
    have hS3 : S + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega : S + 1 ≤ 4) (by decide)
    have hS32 : (BitVec.ofNat 32 S).toNat = S := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    -- the add
    refine WP.bind (WP.callRC (fun e he => (add_one_noErr (by rw [hS32]; exact hS3) e he).elim)
      fun v₃ hadd => ?_)
    have hv₃ := add_one_ok hadd (by rw [hS32]; exact hS3)
    rw [hS32] at hv₃
    -- the store
    have hsucc : sum (XG (upd G₂ t (⟨.out, h₄, Heap.empty⟩, .none, .work (s.local1.toNat + 1) true))) =
        S + 1 := by
      rw [← hS, XG_upd, XG_upd]
      have := sum_succ (X := upd (XG G₂) t (.work s.local1.toNat true)) ht2 (upd_self _ _ _)
      rw [upd_upd] at this; exact this
    refine WP.bind (wp_n (r₀ := ()) hi₃ hc₃ (TTriple.conseq (TTriple.store (by decide) v₃) (fun _ h => h)
      fun _ _ hq => sep_lift.mpr ⟨Subsingleton.elim _ _, hq⟩) (by
        apply BitVec.eq_of_toNat_eq
        rw [hv₃, hsucc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS3]) (by omega)
      fun m₄ h₅ hc₄ ht₄ hi₄ => ?_)
    -- the read of `io`, then `post`
    have htl₄ : t < m₄.threads.size := by
      have hx₄ : XG (upd G₂ t (⟨.out, h₅, Heap.empty⟩, .none, .work (s.local1.toNat + 1) true)) t =
          .work (s.local1.toNat + 1) true := by show (upd G₂ t _ t).2.2 = _; rw [upd_self]
      obtain ⟨ht2', h2, -⟩ := shape_work hi₄.2.2.shape hx₄; rw [h2]; exact ht2'
    refine WP.bind (WP.callMC_ptrProject (projC hi₄ (k := 16) (by decide)) ?_)
    dsimp only
    rw [show cPtr.add 16 = (Sync.SemCounter.S).ptr from rfl]
    refine WP.bind (wp_io hi₄ hc₄ htl₄ fun m₅ hc₅ ht₅ hi₅ => ?_)
    refine WP.bind (WP.callC (WP.mono ?_ (Sem.post_spec fits t Heap.empty h₅
      (.work (s.local1.toNat + 1) true) (.work (s.local1.toNat + 1) false) _ trivial trivial (hmv_p t _ h₅ ht2)
      (hU_p t _ h₅) (fun _ => .inl rfl) G₂ m₅ d₂ (by rw [Heap.empty_union]; exact hi₅))))
    rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
    simp only [StateT.run_pure, pure_bind]
    -- the next repeat
    simp only [StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he =>
      (add_one_noErr (a := s.local1) (by have := s.local1.isLt; omega) e he).elim) fun i24 hadd' => ?_)
    have h24 := add_one_ok (a := s.local1) hadd' (by have := s.local1.isLt; omega)
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [semWork.again4, ↓reduceIte]
    refine ⟨⟨hc₆, by simp only; omega, by simp only; rw [h24]; exact hi₆⟩, .inl (by omega)⟩
  · rename_i hge
    have hge' : ¬ s.local1.toNat < 2 := by simpa [lt, BitVec.ult] using hge
    have heq : s.local1.toNat = 2 := by omega
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [semWork.again4, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc, heq ▸ hi⟩


theorem work_spec (t : ThreadId) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G t (gOut 0)) m) (hc : m.current = t) :
    proto.WP t (semWork cPtr) (fun _ G' m' _ => m'.current = t ∧ proto.inv (upd G' t (gOut 2)) m')
      G m d := by
  unfold semWork
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (workInv t) (fun _ => 0) (workPost t) (loop4_body t) _ G m d
    ⟨hc, by decide, by simpa using hi⟩))
  rintro ⟨e, s'⟩ G' m' d' ⟨rfl, hc', hi'⟩
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  exact WP.pure' ⟨hc', hi'⟩

/-! ## The ends of the threads -/

/-- A thread at the end of `semWork`: its place in `main` or `semWork` is `p` (`joins` for `main`;
`fin` and `gone` for the kid). -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hi : proto.inv (upd G t (gOut 2)) m) (hg : g.1 = ⟨.out, Heap.empty, Heap.empty⟩ ∨
      g.1 = ⟨.gone, Heap.empty, Heap.empty⟩) (hg2 : g.2.1 = .none)
    (hp : (t = 0 ∧ g.2.2 = .joins) ∨ (t = 1 ∧ g.2.2 = .fin)) :
    proto.inv (upd G t g) m := by
  obtain ⟨hl, hs, hu⟩ := hi
  have hx : XG (upd G t (gOut 2)) t = .work 2 false := by
    show (upd G t (gOut 2) t).2.2 = _; rw [upd_self]; rfl
  have hX : XG (upd G t g) = upd (XG (upd G t (gOut 2))) t g.2.2 := by rw [XG_upd, XG_upd, upd_upd]
  have hsum : sum (XG (upd G t g)) = sum (XG (upd G t (gOut 2))) := by
    rw [hX]; unfold sum
    rcases hp with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), h2, hx]; rfl
    · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), h2, hx]; rfl
  have hheld : held (XG (upd G t g)) = held (XG (upd G t (gOut 2))) := by
    rw [hX]; simp only [held]
    rcases hp with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
    · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), h2, hx]; rfl
    · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), h2, hx]; rfl
  have hR : ∀ hL, S.L.R (upd G t (gOut 2)) hL → S.L.R (upd (upd G t (gOut 2)) t g) hL := by
    intro hL h
    rw [upd_upd]
    have h' : (pts S.ptr 8 (if held (XG (upd G t (gOut 2))) then (0 : BitVec 64) else 1) ∗
      (if held (XG (upd G t (gOut 2))) then emp else NP (XG (upd G t (gOut 2))))) hL := h
    change (pts S.ptr 8 (if held (XG (upd G t g)) then (0 : BitVec 64) else 1) ∗
      (if held (XG (upd G t g)) then emp else NP (XG (upd G t g)))) hL
    rw [hheld]; unfold NP; rw [hsum]; exact h'
  have hl' := hl.ghost (t := t) (g := g) (by rw [upd_self]; rfl)
    (by rcases hg with h | h <;> simp [Lock.prod, h])
    (by rw [upd_self]; rcases hg with h | h <;> simp [Lock.prod, h, gOut])
    (by rcases hg with h | h <;> simp [Lock.prod, h])
    (fun _ => hl.live t (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))) hR
  rw [upd_upd] at hl'
  have hs' : S.Inv (upd G t g) m := by
    have := hs.congrG (G' := upd G t g) (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self, hg2]; rfl
      · rw [upd_ne _ _ e, upd_ne _ _ e]) (fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, upd_self]; rcases hg with h | h <;> simp [h, gOut]
      · rw [upd_ne _ _ e, upd_ne _ _ e]) (fun u x h1 h2 => by
      by_cases e : u = t
      · subst e; rw [upd_self]; rcases hg with h | h <;> rw [h] <;> rfl
      · rw [upd_ne _ _ e]; have := hs.off u x h1 h2; rwa [upd_ne _ _ e] at this)
    exact this
  refine ⟨hl', hs', U_retag hu ?_ ?_ hsum ?_ (fun h => by rw [hg2] at h; cases h)⟩
  · rw [hX]; exact shape_set hu.shape hx _ (by
      rcases hp with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · exact .inr (.inl ⟨rfl, h2⟩)
      · exact .inr (.inr ⟨rfl, h2⟩))
  · have hh : g.2.2.holds = false := by rcases hp with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> rfl
    rw [hh]; rcases hg with h | h <;> rw [h] <;> simp
  · left; rcases hp with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> rfl

/-- The kid spawned no thread. -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : proto.inv G m)
    (hu : 0 < u) : joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, h⟩ := hi.2.2.shape
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have h0' : ∀ h : 0 < m.threads.size, (m.threads[0]'h).spawner = 0 := by
    intro h; rw [Array.getElem?_eq_getElem h] at h0; rw [Option.some.inj h0]
  rcases h with ⟨h1, -, -⟩ | ⟨h2, h1, -⟩
  · have : i = 0 := by omega
    subst this
    rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
    · rw [Array.getElem?_eq_getElem hi'] at h1
      rw [Option.some.inj h1] at hs; exact absurd hs (Nat.ne_of_lt hu)

/-- The kid: `semWork` on the `SemCounter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | semWork p =>
    obtain ⟨rfl, rfl⟩ := hg
    show proto.WP u ((fun _ => ()) <$> semWork cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (work_spec u G _ d
      (by rw [show gOut 0 = G u from hgu.symm, upd_same]
          exact fits.cur u u m.woken hi) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    have hx : XG (upd G' u (gOut 2)) u = .work 2 false := by
      show (upd G' u (gOut 2) u).2.2 = _; rw [upd_self]; rfl
    obtain ⟨hu2, -, -⟩ := shape_work hi'.2.2.shape hx
    have hu1 : u = 1 := by unfold ThreadId at *; omega
    subst hu1
    exact ⟨_, inv_end (g := (⟨.gone, Heap.empty, Heap.empty⟩, .none, .fin)) hi' (.inr rfl) rfl
      (.inr ⟨rfl, rfl⟩), ⟨rfl, rfl⟩, fun _ => joinedAll_kid hi' hu⟩
  | producer p => cases hg
  | work p => cases hg
  | writer p => cases hg


/-! ## `main`'s start -/

theorem enc_io (io : Io) : (Enc.encode io).size = 16 := by
  show (Array.replicate 16 _).size = 16; simp

/-- The initial semaphore: one permit. -/
def sem0 : Io_Semaphore :=
  { mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex),
    cond := ({ state := ({ raw := (Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } :
      atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } :
      Io_Condition),
    permits := (1 : BitVec 64) }

theorem sem_size : (Enc.encode sem0).size = 24 := by decide +kernel
theorem sem_c : (Enc.encode sem0).extract 0 8 = Enc.encode (1 : BitVec 64) := by decide +kernel
theorem sem_m : ((Enc.encode sem0).extract 8 24).extract 0 4 = Enc.encode (0 : BitVec 32) := by
  decide +kernel
theorem sem_w : (Enc.encode sem0).extract 8 12 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem sem_s : (Enc.encode sem0).extract 12 16 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem sem_e : (Enc.encode sem0).extract 16 20 = Enc.encode (0 : BitVec 32) := by decide +kernel

/-- `main`'s ghost value before its spawn. -/
def gPre : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .none, .pre)

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, .none, .none)

/-- `main` at its join. -/
def gJoin : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .none, .joins)

/-- The `SemCounter` in four parts, after `main`'s stores: `io`, the semaphore, `n`, the
padding. -/
def Parts (io : Io) (A : Nat) (pb : Array Byte) : Assn :=
  bytesAt cPtr A 48 .stack (Enc.encode io) ∗ (bytesAt (cPtr.add 16) A 48 .stack (Enc.encode sem0) ∗
    (bytesAt nPtr A 48 .stack (Enc.encode (0 : BitVec 32)) ∗ bytesAt (cPtr.add 44) A 48 .stack pb))

theorem allLe_one {m : Mem} {c : VClock} (h1 : m.threads.size = 1)
    (h : VClock.le c (m.clocks[0]!) = true) : AllLe m c := fun u hu => by
  rw [h1] at hu
  have : u = 0 := by omega
  subst this; exact h

/-- Before the spawn: `main` alone owns the `SemCounter`. The semaphore starts: its mutex owns the
permit count and `n`; the rest belongs to no thread. -/
theorem inv_pre {m : Mem} {io : Io} {A : Nat} {pb : Array Byte} {h : Heap}
    (ho : Owned (upd (fun _ => Heap.empty) 0 h) m) (hp : Parts io A pb h) (hA : A % 8 = 0)
    (hth : m.threads = #[{ spawner := 0, joined := true }]) (hat : m.atomics = #[])
    (hq : m.waiters = #[]) : proto.inv (upd G0 0 gPre) m := by
  obtain ⟨hI, h2, dI, rfl, hio, hS, h3, dS, rfl, hs, hN, hP, dN, rfl, hn, -⟩ := hp
  obtain ⟨hC, hR1, dC, rfl, hC₁, hR1'⟩ := bytesAt_split hs (k := 8) (by rw [sem_size]; decide)
  obtain ⟨hW, hCo, dW, rfl, hW₁, -⟩ := bytesAt_split hR1' (k := 4) (by simp [sem_size])
  have hsub := ho.sub 0; rw [upd_self] at hsub
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have sI : hI.Sub m.heap := Heap.sub_union_left.trans hsub
  have s2 : (((hC ∪ (hW ∪ hCo)) ∪ (hN ∪ hP))).Sub m.heap :=
    (Heap.sub_union_right dI).trans hsub
  have sS : (hC ∪ (hW ∪ hCo)).Sub m.heap := Heap.sub_union_left.trans s2
  have sN : hN.Sub m.heap := (Heap.sub_union_left.trans (Heap.sub_union_right dS)).trans s2
  have sW : hW.Sub m.heap := (Heap.sub_union_left.trans (Heap.sub_union_right dC)).trans sS
  -- block 0 and its bytes
  obtain ⟨blk, hblk, hl, hA', hS', hK', -⟩ := bytesAt_blk (m := m) hio sI rfl
    (by rw [enc_io]; decide)
  obtain ⟨blk₂, hblk₂, -, -, -, -, hxs⟩ := bytesAt_blk (m := m) hs sS rfl (by rw [sem_size]; decide)
  rw [hblk] at hblk₂; cases hblk₂
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have hword : ∀ o, 16 ≤ o → o + 4 ≤ 40 → blk.bytes.extract o (o + 4) =
      (Enc.encode sem0).extract (o - 16) (o - 12) := by
    intro o h1 h2
    have := congrArg (fun a => Array.extract a (o - 16) (o - 12)) hxs
    simp only [Array.extract_extract] at this
    rw [← this]
    simp only [show (cPtr.add 16).off.toNat = 16 from rfl, sem_size]
    congr 1 <;> omega
  -- each access to a byte of `main`'s part happened before `main`
  have hown : ∀ e ∈ m.footprint, e.Touches (hI ∪ ((hC ∪ (hW ∪ hCo)) ∪ (hN ∪ hP))) →
      AllLe m e.clock := fun e he ht => allLe_one h1 (by
    have := ho.owns 0 (by rw [h1]; decide) e he (.inl (by rw [upd_self]; exact ht)); exact this)
  have hcellS : ∀ x, 16 ≤ x → x < 40 → (hI ∪ ((hC ∪ (hW ∪ hCo)) ∪ (hN ∪ hP))) (0, x) ≠ none :=
    fun x a b => ((Heap.sub_union_left.trans (Heap.sub_union_right dI))).ne
      (bytesAt_in hs rfl (by simp [cPtr, Ptr.add]; omega) (by simp [cPtr, Ptr.add, sem_size]; omega))
  have hwi : ∀ W : Word 32 4, W.b = 0 → W.o % 4 = 0 → 28 ≤ W.o → W.o + 4 ≤ 36 →
      (Enc.encode sem0).extract (W.o - 16) (W.o - 12) = Enc.encode (0 : BitVec 32) →
      W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) := fun W hb h4 h1' h2' he =>
    Sem.word_init hb hblk hl (by omega) (by rw [hA']; omega) hK' hat
      (by rw [hword W.o (by omega) (by omega), he]; exact intOfBytes_rmw 0)
      (fun e he' hh => hown e he' (Word.touches_of hh fun x a b => by
        rw [hb]; exact hcellS x (by omega) (by omega)))
  obtain ⟨hwsOk, hwsz, hwsv⟩ := hwi S.WS rfl (by decide) (by decide) (by decide) sem_s
  obtain ⟨hweOk, hwez, -⟩ := hwi S.WE rfl (by decide) (by decide) (by decide) sem_e
  have hno : ∀ i l, ¬ S.WE.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hE0 : (S.WE.hist m)[0]!.clock = #[] := by rw [Word.hist_none hno]; rfl
  have hcellW : ∀ x, 24 ≤ x → x < 24 + 4 → hW (0, x) ≠ none := fun x h1 h2 =>
    bytesAt_in hW₁ rfl (by simp [cPtr, Ptr.add]; omega)
      (by simp [cPtr, Ptr.add, sem_size]; omega)
  have h0 : S.L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 24 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hword 24 (by decide) (by decide), sem_w]
    exact intOfBytes_rmw 0
  -- `main` keeps the permit count, `n` and the mutex; the rest belongs to no thread
  obtain ⟨dCW, dCCo⟩ := Heap.disjoint_union_right.mp dC
  obtain ⟨dSN, dSP⟩ := Heap.disjoint_union_right.mp dS
  obtain ⟨dCN, dWCoN⟩ := Heap.disjoint_union_left.mp dSN
  obtain ⟨dWN, -⟩ := Heap.disjoint_union_left.mp dWCoN
  have hsub : (Heap.empty ∪ ((hC ∪ hN) ∪ hW)).Sub (hI ∪ ((hC ∪ (hW ∪ hCo)) ∪ (hN ∪ hP))) := by
    rw [Heap.empty_union]
    refine Heap.union_sub (Heap.union_sub ?_ ?_) ?_
    · exact (Heap.sub_union_left.trans Heap.sub_union_left).trans (Heap.sub_union_right dI)
    · exact (Heap.sub_union_left.trans (Heap.sub_union_right dS)).trans (Heap.sub_union_right dI)
    · exact ((Heap.sub_union_left.trans (Heap.sub_union_right dC)).trans Heap.sub_union_left).trans
        (Heap.sub_union_right dI)
  have ho' := ho.shrink (t := 0) (by rw [upd_self]; exact hsub)
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 gPre u = G0 u := fun u h => upd_ne _ _ h
  have hjt : joinedB m 0 = false := rfl
  have hpC : pts S.ptr 8 (1 : BitVec 64) hC :=
    ⟨A, 48, .stack, _, by simp [S, Sem.ptr]; omega, by rw [sem_c]; exact LawfulEnc.size_encode _,
      by rw [sem_c]; exact LawfulEnc.decode_encode _, hC₁, by decide⟩
  have hpN : NP (XG (upd G0 0 gPre)) hN :=
    ⟨A, 48, .stack, Enc.encode (0 : BitVec 32), by simp [nPtr, cPtr, Ptr.add]; omega, enc_u32 0,
      LawfulEnc.decode_encode _, hn, by decide⟩
  refine ⟨Inv.make (t := 0) (hL := hC ∪ hN) (hW := hW) ho' hjt (fun u hu => ?_)
    (by rw [upd_self]; rfl) (by rw [upd_self]; exact fun _ => .inl rfl)
    (Heap.disjoint_union_left.mpr ⟨dCW, dWN.symm⟩) (fun u => ?_) (fun u => ?_)
    ⟨hC, hN, dCN, rfl, hpC, hpN⟩ hcellW
    ⟨blk, hblk, hl, by rw [hS']; decide, by show (blk.addr + 24) % 4 = 0; rw [hA']; omega,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (fun u hu => ?_) (by rw [h1]; decide),
    Sem.Inv.start (S := S) hwsOk hweOk hwsz hwsv hwez (by rw [hE0]; exact Sem.allLe_nil m)
      (fun u => by unfold upd; split <;> rfl) (fun w hw => by rw [hq] at hw; simp at hw)
      (fun u x _ _ => by unfold upd; split <;> rfl),
    ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by show (upd G0 0 gPre 0).2.2 = _; rw [upd_self]; rfl,
      fun u hu => by show (upd G0 0 gPre u).2.2 = _; rw [hGu u (by unfold ThreadId at *; omega)]; rfl⟩⟩,
      fun e he hb ho16 => .inr (hown e he ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [hb]; simp only [Heap.union_apply]
        have := bytesAt_in hio rfl (by simp [cPtr]) (by simp [cPtr, enc_io]; omega) (x := e.off)
        cases e' : hI (0, e.off) with
        | none => exact absurd e' this
        | some c => simp⟩),
      fun u => by unfold upd; split <;> rfl, hbk, fun w hw => by rw [hq] at hw; simp at hw,
      .inl (by show (upd G0 0 gPre 0).2.2.holds = false; rw [upd_self]; rfl),
      fun u hu => by unfold upd at hu; split at hu <;> cases hu⟩⟩
  · rw [upd_ne _ _ hu]
    unfold Lock.own; rw [hGu u hu]; split <;> rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, by rw [h1]; decide, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · have : u = 0 := by rw [h1] at hu; omega
    subst this; exact VClock.le_refl _


theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (semaphoreCounter io) QM G0 { mem0 σ with current := 0 } d := by
  unfold semaphoreCounter
  -- the `SemCounter`: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 48 8 (by decide))
    (Owned.start rfl rfl) rfl (by simp [mem0, Mem.ofGlobals]) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl] at hb₁ ⊢
  -- its four parts
  obtain ⟨hI, hR₁, dI, rfl, hI₁, hR₁'⟩ := bytesAt_split hb₁ (k := 16) (by simp)
  obtain ⟨hS, hR₂, dS, rfl, hS₁, hR₂'⟩ := bytesAt_split hR₁' (k := 24) (by simp)
  obtain ⟨hN, hP, dN, rfl, hN₁, hP₁⟩ := bytesAt_split hR₂' (k := 4) (by simp)
  have hsI : ((Array.replicate 48 Byte.undef).extract 0 16).size = 16 := by simp
  have hsS : (((Array.replicate 48 Byte.undef).extract 16).extract 0 24).size = 24 := by simp
  have hsN : ((((Array.replicate 48 Byte.undef).extract 16).extract 24).extract 0 4).size = 4 := by
    simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `io`, the semaphore, `n`
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 (hI ∪ (hS ∪ (hN ∪ hP)))) m₁ := ho₁
  have F₁ : (bytesAt cPtr A 48 .stack ((Array.replicate 48 Byte.undef).extract 0 16) ∗
      (bytesAt (cPtr.add 16) A 48 .stack (((Array.replicate 48 Byte.undef).extract 16).extract 0 24) ∗
        (bytesAt ((cPtr.add 16).add 24) A 48 .stack
          ((((Array.replicate 48 Byte.undef).extract 16).extract 24).extract 0 4) ∗
         bytesAt (((cPtr.add 16).add 24).add 4) A 48 .stack
          ((((Array.replicate 48 Byte.undef).extract 16).extract 24).extract 4))))
      (hI ∪ (hS ∪ (hN ∪ hP))) := ⟨hI, _, dI, rfl, hI₁, hS, _, dS, rfl, hS₁, hN, hP, dN, rfl, hN₁, hP₁⟩
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := cPtr) (A := A) (S := 48) (K := .stack) (k := 0)
    (a := 8) io rfl (by decide) (by rw [hsI]; decide) (by simp [cPtr]; omega) (by decide)).frame)
    ho₁' hc₁ (by rw [hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₁)
    fun _ m₂ h₂ _ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  have hwI : (writeBytes ((Array.replicate 48 Byte.undef).extract 0 16) 0 (Enc.encode io)).size = 16 := by
    rw [writeBytes_size _ _ _ (by simp [enc_io])]; exact hsI
  have pr₂ : (ptrProject cPtr (·.add 16)).run m₂ = pure (cPtr.add 16, m₂) := by
    have hs₂' : h₂.Sub m₂.heap := by simpa [upd_self] using ho₂.sub 0
    obtain ⟨hx, hy, dxy, hxy, hbx, -⟩ := F₂
    rw [hxy] at hs₂'
    exact bytesAt_ptrProject_sub hbx (Heap.sub_union_left.trans hs₂') (k := 16)
      (by rw [hwI]; exact Nat.le_refl _) (by rw [hwI]; decide)
  refine WP.bind (WP.callMC_ptrProject pr₂ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := cPtr.add 16) (A := A) (S := 48) (K := .stack)
    (k := 0) (a := 8) sem0 (by rw [sem_size]; rfl) rfl (by decide)
    (by rw [hsS]; decide) (by simp [cPtr, Ptr.add]; omega) (by decide)).frame.frameL) ho₂
    (hs₂.current.trans hc₁) (by rw [hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₂)
    fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  have pr₃ : (ptrProject cPtr (·.add 40)).run m₃ = pure ((cPtr.add 16).add 24, m₃) := by
    have hs₃' : h₃.Sub m₃.heap := by simpa [upd_self] using ho₃.sub 0
    obtain ⟨hx, hy, dxy, hxy, hbx, hyy⟩ := F₃
    obtain ⟨hz, hw, dzw, hzw, -, hww⟩ := hyy
    obtain ⟨hn, hp', dnp, hnw, hbn, -⟩ := hww
    rw [hxy] at hs₃'
    have hsy : hy.Sub m₃.heap := (Heap.sub_union_right dxy).trans hs₃'
    rw [hzw] at hsy
    have hsw : hw.Sub m₃.heap := (Heap.sub_union_right dzw).trans hsy
    rw [hnw] at hsw
    have i0 : m₃.inBounds cPtr = true := by
      simpa using bytesAt_inBounds_sub hbx (Heap.sub_union_left.trans hs₃') (k := 0) (by simp)
        (by rw [hwI]; decide)
    have i40 : m₃.inBounds ((cPtr.add 16).add 24) = true := by
      simpa using bytesAt_inBounds_sub hbn (Heap.sub_union_left.trans hsw) (k := 0) (by simp)
        (by simp)
    exact ptrProject_add_run i0 i40
  refine WP.bind (WP.callMC_ptrProject pr₃ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := (cPtr.add 16).add 24) (A := A) (S := 48)
    (K := .stack) (k := 0) (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsN]; decide)
    (by simp [cPtr, Ptr.add]; omega) (by decide)).frame.frameL.frameL) ho₃
    (hs₃.current.trans (hs₂.current.trans hc₁))
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₃)
    fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans (hs₃.current.trans (hs₂.current.trans hc₁))
  have hth₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₄ : m₄.atomics = #[] := by rw [hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₄ : m₄.waiters = #[] := by rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hPa : Parts io A ((((Array.replicate 48 Byte.undef).extract 16).extract 24).extract 4) h₄ := by
    rw [writeBytes_all (by rw [hsI, enc_io]), writeBytes_all (by rw [hsS, sem_size]),
      writeBytes_all (by rw [hsN, enc_u32])] at F₄
    exact F₄
  -- the spawn
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, inv_pre ho₄ hPa hA8 hth₄ hat₄ hq₄, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gOut 0, ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  -- after the stop: `main` alone, at `gPre`
  obtain ⟨hl₅, hs₅, hu₅⟩ := hi₅
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hu₅.shape
  rotate_left
  · exfalso; rcases h0 with h0 | ⟨k', -, b', h0⟩ <;> change (G₁ 0).2.2 = _ at h0 <;> rw [hg₁] at h0 <;>
      cases h0
  have hcs₅ : m₅.clocks.size = 1 := by rw [hl₅.own.csize, hs1]
  have hk : ∀ W : Word 32 4, W.Keep m₅ m₆ := fun _ =>
    Word.keep_fork (t := 0) (by rw [hs1]; decide) (by rw [hcs₅, hs1]) hf
  obtain ⟨hch, hm₆⟩ := Lock.fork_eq hf
  rw [hs1] at hch
  subst hch hm₆
  obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m₅.clocks) (t := 0) (by rw [hcs₅]; decide)
  have hg1 : (G₁ 1).1.ph = .gone := by
    by_cases e : (G₁ 1).1.ph = .gone
    · exact e
    · exact absurd (hl₅.live 1 e).1 (by rw [hs1]; decide)
  have h1n : (G₁ 1).2.1 = .none := by
    have hX1 : (G₁ 1).2.2 = .none := hnone 1 (Nat.le_refl _)
    cases e : (G₁ 1).2.1 with
    | none => rfl
    | reg i jr sn e' =>
      obtain ⟨k', hk'⟩ := hu₅.wx 1 (by rw [e]; rfl); rw [hX1] at hk'; cases hk'
    | _ => have := hs₅.crit 1 (by rw [e]; rfl); rw [hg1] at this; cases this
  have hsum₀ : ∀ X : ThreadId → Ph, (X 0 = .pre ∨ X 0 = .work 0 false) →
      (X 1 = .none ∨ X 1 = .work 0 false) → held X = false ∧ sum X = 0 := by
    intro X h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [held, sum, h0, h1, Ph.holds, Ph.count]
  have hX₁ := hsum₀ (XG G₁) (.inl (by show (G₁ 0).2.2 = _; rw [hg₁]; rfl)) (.inl (hnone 1 (Nat.le_refl _)))
  have hX₆ := hsum₀ (XG (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0)))
    (.inr (by show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 0).2.2 = _; rw [upd_self]; rfl))
    (.inr (by show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 1).2.2 = _
              rw [upd_ne _ _ (by decide), upd_self]; rfl))
  have hGo : ∀ u, 2 ≤ u → upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) u = G₁ u := fun u hu => by
    rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
  have hi₆ : proto.inv (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0))
      { m₅ with
        current := 0
        clocks := (m₅.clocks.set! 0 (VClock.bump (m₅.clocks[0]!) 0)).push
          (VClock.bump (m₅.clocks[0]!) 0)
        threads := m₅.threads.push { spawner := 0, joined := false } } := by
    refine ⟨hl₅.fork (t := 0) (by rw [hg₁]; rfl) hf (by rw [hg₁]; rfl) (fun _ => .inl rfl) rfl rfl
        rfl rfl fun hL hR => ?_, ?_, ⟨⟨?_, .inr ⟨by simp [hs1], ?_, .inr ⟨0, by decide, false, ?_⟩,
      .inr ⟨0, by decide, false, ?_⟩, fun u hu => ?_⟩⟩, fun e he hb ho16 => ?_, fun u => ?_,
      hu₅.blk, hu₅.q, .inl (by rw [upd_self]; rfl), fun u hu => ?_⟩⟩
    · have h' : (pts S.ptr 8 (if held (XG G₁) then (0 : BitVec 64) else 1) ∗
        (if held (XG G₁) then emp else NP (XG G₁))) hL := hR
      change (pts S.ptr 8 (if held (XG (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0))) then (0 : BitVec 64)
        else 1) ∗ (if held (XG (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0))) then emp
        else NP (XG (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0))))) hL
      rw [hX₆.1]; rw [hX₁.1] at h'; unfold NP at h' ⊢; rw [hX₆.2]; rw [hX₁.2] at h'; exact h'
    · refine (hs₅.mono (hs₅.ws.keep (hk _)) (hs₅.we.keep (hk _)) (Word.hist_keep hs₅.ws (hk _))
        (Word.hist_keep hs₅.we (hk _)) (fun u => ?_) (fun c ⟨i, l, h1, h2⟩ => ⟨i, l, h1, h2⟩)
        (fun h => .inl h) (fun w hw _ => .inl hw) (fun c h u hu => ?_)).congrG (fun u => ?_)
        (fun u => ?_) (fun u x h1 h2 => ?_)
      · by_cases hu : u < m₅.clocks.size
        · exact hcl u hu
        · rw [getElem!_neg m₅.clocks u hu]; exact VClock.le_iff.mpr fun i => by show (#[] : Array Nat).getD i 0 ≤ _; simp
      · simp only [Array.size_push, hs1] at hu
        rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
        · exact VClock.le_trans (h 0 (by rw [hs1]; decide)) (hcl 0 (by rw [hcs₅]; decide))
        · rw [← hcs₅]; exact VClock.le_trans (h 0 (by rw [hs1]; decide)) hcn
      · by_cases e0 : u = 0
        · subst e0; rw [upd_self, hg₁]; rfl
        · by_cases e1 : u = 1
          · subst e1; rw [upd_ne _ _ (by decide), upd_self, h1n]; rfl
          · rw [upd_ne _ _ e0, upd_ne _ _ e1]
      · by_cases e0 : u = 0
        · subst e0; rw [upd_self, hg₁]; exact Iff.rfl
        · by_cases e1 : u = 1
          · subst e1; rw [upd_ne _ _ (by decide), upd_self, hg1]
            simp [gOut]
          · rw [upd_ne _ _ e0, upd_ne _ _ e1]
      · by_cases e0 : u = 0
        · subst e0; rw [upd_self]; rfl
        · by_cases e1 : u = 1
          · subst e1; rw [upd_ne _ _ (by decide), upd_self]; rfl
          · rw [upd_ne _ _ e0, upd_ne _ _ e1]; exact hs₅.off u x h1 h2
    · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
    · simp only [Array.getElem?_push, hs1, ↓reduceIte]
    · show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 0).2.2 = _; rw [upd_self]; rfl
    · show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 1).2.2 = _; rw [upd_ne _ _ (by decide), upd_self]; rfl
    · show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) u).2.2 = _
      rw [hGo u hu]; exact hnone u (by unfold ThreadId at *; omega)
    · rcases hu₅.io e he hb ho16 with h | h
      · exact .inl h
      · refine .inr fun u hu => ?_
        simp only [Array.size_push, hs1] at hu
        rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
        · exact VClock.le_trans (h 0 (by rw [hs1]; decide)) (hcl 0 (by rw [hcs₅]; decide))
        · rw [← hcs₅]; exact VClock.le_trans (h 0 (by rw [hs1]; decide)) hcn
    · by_cases e0 : u = 0
      · subst e0; rw [upd_self]; rfl
      · by_cases e1 : u = 1
        · subst e1; rw [upd_ne _ _ (by decide), upd_self]; rfl
        · rw [hGo u (by unfold ThreadId at *; omega)]
          have hn : (G₁ u).2.2 = .none := hnone u (by unfold ThreadId at *; omega)
          have := hu₅.parts u; rw [hn] at this ⊢; simpa [Ph.holds] using this
    · by_cases e0 : u = 0
      · subst e0; rw [upd_self] at hu; cases hu
      · by_cases e1 : u = 1
        · subst e1; rw [upd_ne _ _ (by decide), upd_self] at hu; cases hu
        · rw [hGo u (by unfold ThreadId at *; omega)] at hu ⊢; exact hu₅.wx u hu
  simp only [StateT.run_bind]
  -- `semWork`
  refine WP.bind (WP.callC (WP.mono ?_ (work_spec 0 _ _ k hi₆ rfl)))
  rintro _ G₂ m₇ d₂ ⟨hc₇, hi₇⟩
  -- the join of the kid
  have hiJ := inv_end (g := gJoin) hi₇ (.inl rfl) rfl (.inl ⟨rfl, rfl⟩)
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨gJoin, hiJ, fun G₃ m₈ hg₃ hi₈ => ?_⟩)
  have hsh₈ := hi₈.2.2.shape
  obtain ⟨h08, ⟨-, h0, -⟩ | ⟨hs2, hr1, -, -, hn2⟩⟩ := hsh₈
  · exfalso; change (G₃ 0).2.2 = _ at h0; rw [hg₃] at h0; cases h0
  refine ⟨fun _ => ⟨by decide, by rw [hs2]; decide, ⟨rfl, rfl⟩, by simp [Thread.joinValid, Mem.isGated, hr1]⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₈ with current := 0 }) hr1 rfl rfl, fun m₉ hj => ?_⟩⟩
  -- `main` takes the kid's part, then the semaphore's resource
  let gEnd : Gh := (⟨.out, S.L.part (G₃ 0) ∪ S.L.own G₃ m₈ 1, Heap.empty⟩, .none, .joins)
  have hX₃ : (fun u => (upd G₃ 0 gEnd u).2) = fun u => (G₃ u).2 := by
    funext u; unfold upd; split
    · rename_i h; subst h; rw [hg₃]; rfl
    · rfl
  have hL₉ := hi₈.1.join (t := 0) (u := 1) (g := gEnd) (by decide) (by decide)
    (by rw [hg₃]; rfl) hfin.1 hj rfl rfl rfl (fun hL hR => by
      show S.R _ hL; rw [hX₃]; exact hR)
  obtain ⟨rec, hrec, -, hm₉⟩ := join_eq hj
  have hth₉ : m₉.threads = m₈.threads.set! 1 { rec with joined := true } := by rw [hm₉]
  have hs₉ : m₉.threads.size = 2 := by rw [hth₉, Array.size_set!, hs2]
  have hc₉ : m₉.current = 0 := by rw [hm₉]
  have hcs₈ : m₈.clocks.size = 2 := by rw [hi₈.1.own.csize, hs2]
  have hfree : S.L.Free (upd G₃ 0 gEnd) := by
    intro u hu
    by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hu; cases hu
    · rw [upd_ne _ _ h0] at hu
      obtain ⟨hu2, -⟩ := hi₈.1.live u (by rw [hu]; decide)
      have : u = 1 := by unfold ThreadId at *; omega
      subst this; change (G₃ 1).1.ph = _ at hu; rw [hfin.1] at hu; cases hu
  have hall₉ : ∀ u < m₉.threads.size, VClock.le (m₉.clocks[u]!) (m₉.clocks[0]!) = true :=
    fun u hu => by
    rw [hm₉]
    simp only
    rw [Proto.getElem!_set!_ite, Proto.getElem!_set!_ite]
    simp only [true_and, show 0 < m₈.clocks.size by omega, ↓reduceIte]
    rw [hs₉] at hu
    by_cases h0 : u = 0
    · subst h0; simp [VClock.le_refl]
    · have : u = 1 := by omega
      subst this
      exact VClock.le_merge_right _ _
  obtain ⟨hL, hR, hdLW, hd, ho⟩ := hL₉.take (t := 0) (by rw [hs₉]; decide) hfree
    (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)) hall₉
  -- `n` holds 4
  have hR' : S.R (fun u => (G₃ u).2) hL := by
    have : S.L.R (upd G₃ 0 gEnd) hL := hR
    change S.R _ hL at this; rwa [hX₃] at this
  have hh : held (XG G₃) = false := by
    simp only [held, XG, hg₃, hfin.2]; rfl
  have h4 : sum (XG G₃) = 4 := by simp only [sum, XG, hg₃, hfin.2]; rfl
  obtain ⟨hp, hr, dpr, rfl, -, hnr⟩ := hR'
  have hn4 : pts nPtr 4 (BitVec.ofNat 32 4) hr := by
    have : (if held (XG G₃) then emp else NP (XG G₃)) hr := hnr
    rw [hh] at this; simp only [Bool.false_eq_true, ↓reduceIte] at this
    unfold NP at this; rw [h4] at this; exact this
  let own₉ := S.L.own (upd G₃ 0 gEnd) m₉
  obtain ⟨dpW, drW⟩ := Heap.disjoint_union_left.mp hdLW
  have hd₀ := (Heap.disjoint_union_right.mp hd).1
  obtain ⟨dp0, dr0⟩ := Heap.disjoint_union_right.mp hd₀
  have hd' : Heap.Disjoint hr (hp ∪ (own₉ 0 ∪ S.L.wordH m₉)) :=
    Heap.disjoint_union_right.mpr ⟨dpr.symm, Heap.disjoint_union_right.mpr ⟨dr0.symm, drW⟩⟩
  have heq : own₉ 0 ∪ ((hp ∪ hr) ∪ S.L.wordH m₉) = hr ∪ (hp ∪ (own₉ 0 ∪ S.L.wordH m₉)) := by
    rw [Heap.union_left_comm hd₀, Heap.union_comm dpr, Heap.union_assoc]
  -- the pointer to `n`, then its load
  have pr₉ : (ptrProject cPtr (·.add 40)).run m₉ = pure (nPtr, m₉) := by
    obtain ⟨blk₀, hblk₀, -, hsz₀, -⟩ := hi₈.2.2.blk
    have hb₉ : m₉.blocks = m₈.blocks := by rw [hm₉]
    exact ptrProject_block_run (by rw [hb₉]; exact hblk₀) rfl (by decide) (by simp [cPtr, hsz₀])
  refine WP.bind (WP.callMC_ptrProject pr₉ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned (TTriple.load (p := nPtr) (a := 4) (v := BitVec.ofNat 32 4)
    (by decide)).frame ho hc₉ (by rw [hs₉]; decide)
    (by rw [upd_self, heq]; exact ⟨hr, _, hd', rfl, hn4, rfl⟩) fun a m₁₀ hQ hr' ho' hq hs₁₀ _ _ => ?_)
  obtain ⟨h₁, h₂, -, -, hq₁, -⟩ := hq
  obtain ⟨rfl, -⟩ := sep_lift.mp hq₁
  obtain ⟨b, blk, o, -, -, -, hm₁₀⟩ := load_ok hr'
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the free of the `SemCounter`
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hi₈.2.2.blk
  have hb₁₀ : m₁₀.blocks = m₈.blocks := by rw [hm₁₀]; simp [Mem.recordAt, hm₉]
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (by rw [hb₁₀]; exact hblk₀) hl₀
      (by rw [hm₁₀]; exact ((Mem.ClocksLe.of_threads hL₉.own.csize (by rw [hc₉]; exact hall₉)).recordAt
        _ _ _ _).freeRaces _ _) e he).elim)
    fun _ m₁₁ hfr => ?_)
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  refine ⟨rfl, WP.pure' ⟨rfl, fun r hr hsp => ?_⟩⟩
  -- every thread is joined
  have hth₁₀ : m₁₀.threads = m₉.threads := by rw [hm₁₀]; rfl
  simp only [hth₁₀, hth₉] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · rename_i hne
    have : i = 0 := by omega
    subst this
    rw [Array.getElem?_eq_getElem (by omega)] at h08
    rw [Option.some.inj h08]

/-! ## The results -/

/-- **`semaphoreCounter` gives 4 under every schedule** (every oracle `o`, every `fuel`). -/
theorem semaphoreCounter_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)}
    {m : Mem} (io : Io)
    (h : (Sched.run env dispatch fuel o (semaphoreCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 4 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- **No run of `semaphoreCounter` gives an error**: no data race on `n`, no deadlock, no panic,
under every schedule. -/
theorem semaphoreCounter_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run env dispatch fuel o (semaphoreCounter io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the semaphore counter returns 4 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem semaphoreCounter_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (semaphoreCounter ⟨⟩) (mem0 σ)) = some 4 :=
  ⟨.fresh, by unroll_sched 10⟩

end Sync.SemCounter
