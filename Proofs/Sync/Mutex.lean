import ZigLean.Conc.Unroll
import Proofs.Sync.Lock

/-!
# `mutexCounter` over all schedules

`mutexCounter` spawns one thread; each of the two threads adds 1 two times to a counter, under
an `Io.Mutex` (translated from Zig 0.16.0's std code; the futex under it is the model). The
result is 4 under every schedule (`mutexCounter_spec`), and no schedule gives an error
(`mutexCounter_safe`): no data race on the counter, and no deadlock at the futex.

The proof uses the rules of a lock that owns a resource (`ZigLean/Conc/Lock.lean`,
`ZigLean/Conc/LockRules.lean`): the mutex (bytes 16..20 of the `Counter`, block 0) owns the
counter (bytes 20..24), whose value is the number of increments of both threads (`R`). This file
proves the rest:

- **Ghost values** (`Gh = LG × Ph`): the lock's part (`LG`), and where the thread is in `main` or
  `work` (`Ph`), with its number of increments.
- **The rest of the invariant** (`U`): the threads (`Shape`), the bytes of `io` (each access is a
  read, or happened before every thread: `IoOk`), and no thread has a part of the heap.
- **`lock`, `unlock`**: `Proofs/Sync/Lock.lean` (the control flow of the generated code, with the
  rules of a lock).
- **`work`**: the reads of `io` (`Inv.read`); the load and the store of the counter on the
  resource that the thread holds (`WP.liftM_owned`, `Inv.stepIn`).
- **`main`**: before its spawn it owns the `Counter`; it gives the mutex and the counter to the
  lock (`Inv.make`) and keeps `io` as bytes that each thread only reads. After its join it takes
  the counter back (`Inv.take`) and reads 4.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

namespace Sync.MutexCounter

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- A thread in `work`: it did `k` increments. -/
  | work (k : Nat)
  /-- `main` at its join. -/
  | joins
  /-- The kid has ended. -/
  | fin

/-- The increments of a thread. -/
def Ph.count : Ph → Nat
  | .work k => k
  | .joins | .fin => 2
  | _ => 0

abbrev Gh := LG × Ph

/-- The `Counter` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩

/-- The increments of both threads. -/
def sum (X : ThreadId → Ph) : Nat := (X 0).count + (X 1).count

/-- The counter holds the increments of both threads. -/
def R (X : ThreadId → Ph) : Assn := pts (cPtr.add 20) 4 (BitVec.ofNat 32 (sum X))

/-- The `Io.Mutex`: bytes 16..20 of the `Counter`. It owns the counter. -/
abbrev L : Lock Gh := Lock.prod 0 16 R

/-- Each access to the bytes of `io` (0..16 of the `Counter`) is a read, or happened before every
thread. -/
def IoOk (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.off < 16 → e.kind = .read ∨ AllLe m e.clock

/-- The threads: `main` alone before its spawn; then `main` and the kid, which `main` spawned
and did not join yet. -/
def Shape (X : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ X 0 = .pre ∧ ∀ u, 1 ≤ u → X u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (X 0 = .joins ∨ ∃ k ≤ 2, X 0 = .work k) ∧ (X 1 = .fin ∨ ∃ k ≤ 2, X 1 = .work k) ∧
    ∀ u, 2 ≤ u → X u = .none))

/-- Block 0 is the live `Counter`: 24 bytes on the stack, at an address that is a multiple of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 24 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : IoOk m
  parts : ∀ u, (G u).1.part = Heap.empty
  blk : BlkOk m

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := L.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .work p => p = cPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, .work 0)
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2 = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 4 ∧ joinedAll 0 m

/-! ## The protocol has the lock -/

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Heap)
    (_ : L.ph (G t) ≠ .gone) (hu : U G m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) m' := by
  obtain ⟨hsh, hio, hpart, hblk⟩ := hu
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, ?_⟩
  · rw [snd_set]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · rcases hs.fp e he with h' | ⟨hb', ho', -⟩
    · rcases hio e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr (hs.allLe h'')
    · exact absurd ho (by rw [ho']; decide)
  · unfold upd; split
    · rename_i e; subst e; exact hpart u
    · exact hpart u
  · obtain ⟨blk, hb, hl, hsz, ha, hk⟩ := hblk
    rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
    · exact ⟨blk, by rw [e]; exact hb, hl, hsz, ha, hk⟩
    · have h1' : m.blocks[0]? = some blk' := h1
      rw [hb] at h1'; cases h1'
      refine ⟨{ blk with bytes := writeBytes blk.bytes 16 bs }, ?_, hl, ?_, ha, hk⟩
      · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
          (Array.getElem?_eq_some_iff.mp hb).1]; rfl
      · show (writeBytes blk.bytes 16 bs).size = 24
        rw [writeBytes_size _ _ _ (by rw [h3, hsz]; decide), hsz]

theorem fits : L.Fits proto U :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, stable⟩

/-- The word: `L.ptr`. -/
theorem mptr : cPtr.add 16 = L.ptr := rfl

/-- A field pointer of the 24-byte `Counter` (block 0, `BlkOk`) is formed (`ptrProject`,
MM-3). -/
theorem projC {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {k : Nat} (hk : k ≤ 24) :
    (ptrProject cPtr (·.add k)).run m = pure (cPtr.add k, m) := by
  obtain ⟨blk, hb, -, hsz, -⟩ := hi.2.blk
  exact ptrProject_block_run hb rfl (by decide) (by simp [cPtr, hsz]; omega)

/-! ## The threads and the heap -/

theorem shape_work {X : ThreadId → Ph} {m : Mem} {t k : Nat} (h : Shape X m) (hx : X t = .work k) :
    t < 2 ∧ m.threads.size = 2 ∧ k ≤ 2 := by
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
    · rcases h0 with h0 | ⟨k', hk, h0⟩ <;> rw [h0] at hx <;> cases hx; exact hk
    · rcases h1 with h1 | ⟨k', hk, h1⟩ <;> rw [h1] at hx <;> cases hx; exact hk

/-- A thread in `work` goes to `work k'` (`k' ≤ 2`). -/
theorem shape_upd {X : ThreadId → Ph} {m : Mem} {t k k' : Nat} (h : Shape X m)
    (hx : X t = .work k) (hk : k' ≤ 2) (p : Ph) (hp : p = .work k' ∨ (t = 0 ∧ p = .joins) ∨
      (t = 1 ∧ p = .fin)) : Shape (upd X t p) m := by
  obtain ⟨htl, -, -⟩ := shape_work h hx
  obtain ⟨h00, ⟨-, h0, h1⟩ | ⟨hs, hr, h0, h1, h2⟩⟩ := h
  · rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · rw [h0] at hx; cases hx
    · rw [h1 1 (Nat.le_refl _)] at hx; cases hx
  refine ⟨h00, .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩⟩
  · by_cases ht : t = 0
    · subst ht; rw [upd_self]
      rcases hp with rfl | ⟨-, rfl⟩ | ⟨h, -⟩
      · exact .inr ⟨k', hk, rfl⟩
      · exact .inl rfl
      · cases h
    · rw [upd_ne _ _ (Ne.symm ht)]; exact h0
  · by_cases ht : t = 1
    · subst ht; rw [upd_self]
      rcases hp with rfl | ⟨h, -⟩ | ⟨-, rfl⟩
      · exact .inr ⟨k', hk, rfl⟩
      · cases h
      · exact .inl rfl
    · rw [upd_ne _ _ (Ne.symm ht)]; exact h1
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact h2 u hu

/-- The counter's bytes: none before byte 20. -/
theorem pts_none {v : BitVec 32} {h : Heap} (hp : pts (cPtr.add 20) 4 v h) {x : Nat}
    (hx : x < 20) : h (0, x) = none := by
  obtain ⟨A, S, K, bs, -, -, -, ⟨b, hb, -, hl⟩, -⟩ := hp
  cases hb
  rw [hl, if_neg]
  simp only [cPtr, Ptr.add, not_and, Nat.not_lt]
  intro _ h; simp at h; omega

/-- No thread owns a byte before the counter. -/
theorem own_none {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (u : ThreadId) {x : Nat}
    (hx : x < 20) : L.own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    rw [hi.2.parts u, Heap.empty_union]
    by_cases hh : L.ph (G u) = .holds
    · exact pts_none (hi.1.res u hh) hx
    · rw [show (G u).1.held = L.held (G u) from rfl, hi.1.idle u hh]; rfl

/-- The cell of byte `x < 24` of the `Counter`. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 24) : m.heap (0, x) ≠ none := by
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

/-- A step of thread `t` on its own part (`WP.liftM_owned`) keeps `U`, with `t`'s new ghost value
`g` (no part) and its new place `p` in `main` or `work`. -/
theorem U_stepIn {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g : Gh} {hQ : Heap}
    (hi : proto.inv G m) (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own G m t)))
    (hsh : Shape (upd (fun u => (G u).2) t g.2) m) (hpart : g.1.part = Heap.empty) :
    U (upd G t g) m' := by
  have hrest : ∀ x, x < 16 → m.heap.diff (L.own G m t) (0, x) = m.heap (0, x) := fun x hx => by
    simp [Heap.diff, own_none hi t (show x < 20 by omega)]
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, blk_keep hi.2.blk ?_⟩
  · rw [snd_upd]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
  · rcases hs.fp e he with h' | ⟨-, hnt, -⟩
    · rcases hi.2.io e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr (allLe_stepIn hs h'')
    · exact absurd ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [hb, hrest _ ho]; exact blk_heap hi.2.blk (by omega)⟩ hnt
  · unfold upd; split
    · exact hpart
    · exact hi.2.parts u
  · rw [hm', Heap.union_of_right ((hd (0, 0)).resolve_right (by
      rw [hrest 0 (by decide)]; exact blk_heap hi.2.blk (by decide))), hrest 0 (by decide)]

/-! ## `io` -/

theorem noRace_io {m : Mem} (hio : IoOk m) (ht : m.current < m.threads.size) :
    NoRace m 0 0 16 .read :=
  noRace_of fun e he hb _ h2 => by
    rcases hio e he hb (by omega) with h | h
    · exact .inr (by rw [h]; rfl)
    · exact .inl (h _ ht)

/-- A read of `io` (bytes 0..16 of the `Counter`): no race, and the invariant holds after it. -/
theorem step_io {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (ht : m.current < m.threads.size) :
    (load Io 8 cPtr).run m = pure (⟨⟩, m.recordAt 0 0 16 .read) ∧
      proto.inv G (m.recordAt 0 0 16 .read) := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hi.2.blk
  have hacc : m.access cPtr (Enc.size Io) 8 = pure (0, blk, 0) :=
    access_of (p := cPtr) rfl hblk hl (by decide)
      (by rw [show Enc.size Io = 16 from rfl]; simp [cPtr, hs]) (by simpa [cPtr] using ha)
  refine ⟨load_run hacc rfl (noRace_io hi.2.io ht), ?_, ?_⟩
  · refine hi.1.read (b := 0) (o := 0) (n := 16) (Array.getElem?_eq_some_iff.mp hblk).1 (by decide)
      (fun u x _ hx => own_none hi u (by omega)) (fun hL hR x _ hx => pts_none hR (by omega))
      (.inr (.inl (by decide)))
  · refine ⟨hi.2.shape, fun e he hb ho => ?_, hi.2.parts, hi.2.blk⟩
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · rcases hi.2.io e he hb ho with h | h
      · exact .inl h
      · exact .inr fun u hu => VClock.le_trans (h u hu) (recordAt_le m 0 0 16 .read u)
    · exact .inl rfl

theorem io_noErr {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (ht : m.current < m.threads.size) (e : Error) : ((load Io 8 cPtr).run m).run ≠ some (.error e) :=
  MemM.noErr_of_run (step_io hi ht).1 e

/-! ## `work` -/

/-- A thread in `work` at `out`, after `k` increments. -/
def gOut (k : Nat) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .work k)

/-- A thread in `work` that holds the mutex and the counter `h`, after `k` increments. -/
def gHold (k : Nat) (h : Heap) : Gh := (⟨.holds, Heap.empty, h⟩, .work k)

/-- The sum, when one thread did `k` increments: at most `k + 2`. -/
theorem sum_le {X : ThreadId → Ph} {m : Mem} {t k : Nat} (h : Shape X m) (hx : X t = .work k) :
    sum X ≤ k + 2 := by
  obtain ⟨htl, hs2, -⟩ := shape_work h hx
  obtain ⟨-, ⟨hs1, -, -⟩ | ⟨-, -, h0, h1, -⟩⟩ := h
  · omega
  have c0 : (X 0).count ≤ 2 := by
    rcases h0 with h0 | ⟨k', hk, h0⟩
    · rw [h0]; decide
    · rw [h0]; exact hk
  have c1 : (X 1).count ≤ 2 := by
    rcases h1 with h1 | ⟨k', hk, h1⟩
    · rw [h1]; decide
    · rw [h1]; exact hk
  unfold sum
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [hx]; exact Nat.add_le_add_left c1 k
  · rw [hx, Nat.add_comm]; exact Nat.add_le_add_left c0 k

/-- One more increment of thread `t`: the sum is one more. -/
theorem sum_succ {X : ThreadId → Ph} {t k : Nat} (ht : t < 2) (hx : X t = .work k) :
    sum (upd X t (.work (k + 1))) = sum X + 1 := by
  unfold sum
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), hx]; simp only [Ph.count]; omega
  · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), hx]; simp only [Ph.count]; omega

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

/-- The holder's load of the counter: the increments of both threads. -/
theorem wp_cntLoad {σ : Type} {s : σ} {t : ThreadId} {k : Nat} {hL : Heap} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} (hi : proto.inv (upd G t (gHold k hL)) m) (hc : m.current = t)
    {Q : BitVec 32 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gHold k hQ)) m' →
      Q (BitVec.ofNat 32 (sum fun u => (upd G t (gHold k hL) u).2), s) G m' d) :
    proto.WP t ((liftM (load (BitVec 32) 4 (cPtr.add 20)) : CM Tgt σ (BitVec 32)).run s) Q G m d := by
  have hh : L.ph (upd G t (gHold k hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gHold k hL) u).2) hL := by
    have := hi.1.res t hh
    rwa [show L.held (upd G t (gHold k hL) t) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G t (gHold k hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned (TTriple.load (by decide)) hi.1.own hc ht (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  obtain ⟨rfl, hq'⟩ := sep_lift.mp hq
  have hQe : L.part (gHold k hQ) ∪ L.held (gHold k hQ) = hQ := Heap.empty_union hQ
  have hl := hi.1.stepIn (g := gHold k hQ) hc hjt (by rw [hQe]; exact ho') hs (by rw [hQe]; exact hm')
    (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl) (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gHold k hL)) t (gHold k hQ) u).2) hQ
      rw [snd_upd_upd G t (gHold k hL) (gHold k hQ) rfl]; exact hq')
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have hx : (fun u => (upd G t (gHold k hL) u).2) t = .work k := by
    show (upd G t (gHold k hL) t).2 = _; rw [upd_self]; rfl
  have := U_stepIn (g := gHold k hQ) hi hs hm' hd (by
    show Shape (upd _ t (Ph.work k)) m
    rw [← hx, upd_same]; exact hi.2.shape) rfl
  rwa [upd_upd] at this

/-- The holder's store of `w`, the increments of both threads after its next one. -/
theorem wp_cntStore {σ : Type} {s : σ} {t : ThreadId} {k : Nat} {hL : Heap} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} (w : BitVec 32) (hi : proto.inv (upd G t (gHold k hL)) m)
    (hc : m.current = t) (hk : k < 2)
    (hw : w = BitVec.ofNat 32 (sum fun u => (upd G t (gHold (k + 1) hL) u).2))
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gHold (k + 1) hQ)) m' → Q ((), s) G m' d) :
    proto.WP t ((liftM (store (α := BitVec 32) 4 (cPtr.add 20) w) : CM Tgt σ Unit).run s) Q G m d := by
  have hh : L.ph (upd G t (gHold k hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gHold k hL) u).2) hL := by
    have := hi.1.res t hh
    rwa [show L.held (upd G t (gHold k hL) t) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G t (gHold k hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned (TTriple.store (by decide) w) hi.1.own hc ht (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  have hQe : L.part (gHold (k + 1) hQ) ∪ L.held (gHold (k + 1) hQ) = hQ := Heap.empty_union hQ
  have hX : (fun u => (upd (upd G t (gHold k hL)) t (gHold (k + 1) hQ) u).2) =
      fun u => (upd G t (gHold (k + 1) hL) u).2 := by
    rw [upd_upd]; funext u; unfold upd; split <;> rfl
  have hl := hi.1.stepIn (g := gHold (k + 1) hQ) hc hjt (by rw [hQe]; exact ho') hs
    (by rw [hQe]; exact hm') (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl)
    (fun h => absurd rfl h) (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gHold k hL)) t (gHold (k + 1) hQ) u).2) hQ
      rw [hX]; unfold R; rw [← hw]; exact hq)
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have hx : (fun u => (upd G t (gHold k hL) u).2) t = .work k := by
    show (upd G t (gHold k hL) t).2 = _; rw [upd_self]; rfl
  have := U_stepIn (g := gHold (k + 1) hQ) hi hs hm' hd
    (shape_upd hi.2.shape hx (by omega) _ (.inl rfl)) rfl
  rwa [upd_upd] at this

/-- `work`'s loop invariant: thread `t` did `local1` increments and is at `out`. -/
def workInv (t : ThreadId) (s : workLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = t ∧ s.local1.toNat ≤ 2 ∧ proto.inv (upd G t (gOut s.local1.toNat)) m

/-- `work`'s loop ends after 2 increments. -/
def workPost (t : ThreadId) (r : workExit × workLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) :
    Prop :=
  r.1 = .br3 ∧ m.current = t ∧ proto.inv (upd G t (gOut 2)) m

theorem loop4_body (t : ThreadId) (s : workLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : workInv t s G m d) :
    proto.WP t ((work.loop4 cPtr).run s) (fun r G' m' d' =>
      if work.again4 r.1 then workInv t r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : workLocals) => 0) s)
      else workPost t r G' m' d') G m d := by
  obtain ⟨hc, hle, hi⟩ := h
  unfold work.loop4
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hx : (fun u => (upd G t (gOut s.local1.toNat) u).2) t = .work s.local1.toNat := by
    show (upd G t (gOut _) t).2 = _; rw [upd_self]; rfl
  obtain ⟨ht2, hs2, -⟩ := shape_work hi.2.shape hx
  have htl : t < m.threads.size := by rw [hs2]; exact ht2
  split
  · rename_i hlt
    have hlt' : s.local1.toNat < 2 := by simpa [lt, BitVec.ult] using hlt
    simp only [StateT.run_bind, bind_assoc]
    refine WP.bind (WP.callMC_ptrProject (projC hi (k := 16) (by decide)) ?_)
    dsimp only
    -- the read of `io`
    refine WP.bind (wp_io hi hc htl fun m₁ hc₁ ht₁ hi₁ => ?_)
    -- `lock`
    refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_spec fits mptr rfl t (gOut s.local1.toNat) rfl _ G
      m₁ d hi₁)))
    rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL, hi₂⟩
    have hi₂' : proto.inv (upd G₂ t (gHold s.local1.toNat hL)) m₂ := hi₂
    refine WP.bind (WP.callMC_ptrProject (projC hi₂' (k := 20) (by decide)) ?_)
    dsimp only
    -- the load of the counter
    refine WP.bind (wp_cntLoad hi₂' hc₂ fun m₃ hQ hc₃ ht₃ hi₃ => ?_)
    have hx₂ : (fun u => (upd G₂ t (gHold s.local1.toNat hL) u).2) t = .work s.local1.toNat := by
      show (upd G₂ t (gHold _ hL) t).2 = _; rw [upd_self]; rfl
    have hsum := sum_le hi₂'.2.shape hx₂
    generalize hS : (sum fun u => (upd G₂ t (gHold s.local1.toNat hL) u).2) = S at hsum ⊢
    have hS3 : S + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega : S + 1 ≤ 4) (by decide)
    have hS32 : (BitVec.ofNat 32 S).toNat = S := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    -- the add
    refine WP.bind (WP.callRC (fun e he => (add_one_noErr (by rw [hS32]; exact hS3) e he).elim)
      fun v₃ hadd => ?_)
    have hv₃ := add_one_ok hadd (by rw [hS32]; exact hS3)
    rw [hS32] at hv₃
    -- the store
    have hsucc : (sum fun u => (upd G₂ t (gHold (s.local1.toNat + 1) hQ) u).2) = S + 1 := by
      rw [← hS, snd_upd, snd_upd]
      have := sum_succ (X := upd (fun u => (G₂ u).2) t (.work s.local1.toNat)) ht2 (upd_self _ _ _)
      rw [upd_upd] at this; exact this
    refine WP.bind (wp_cntStore v₃ hi₃ hc₃ hlt' (by
      apply BitVec.eq_of_toNat_eq
      rw [hv₃, hsucc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS3]) fun m₄ hQ' hc₄ ht₄ hi₄ => ?_)
    -- the read of `io`
    have htl₄ : t < m₄.threads.size :=
      (hi₄.1.live t (by rw [upd_self]; exact (by decide : LPh.holds ≠ LPh.gone))).1
    refine WP.bind (WP.callMC_ptrProject (projC hi₄ (k := 16) (by decide)) ?_)
    dsimp only
    refine WP.bind (wp_io hi₄ hc₄ htl₄ fun m₅ hc₅ ht₅ hi₅ => ?_)
    -- `unlock`
    refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_spec fits mptr rfl t (gHold (s.local1.toNat + 1) hQ') rfl _ G₂
      m₅ d₂ hi₅)))
    rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
    simp only [StateT.run_pure, pure_bind]
    -- the next repeat
    simp only [StateT.run_bind]
    refine WP.bind (WP.callRC (fun e he =>
      (add_one_noErr (a := s.local1) (by have := s.local1.isLt; omega) e he).elim) fun i24 hadd' => ?_)
    have h24 := add_one_ok (a := s.local1) hadd' (by have := s.local1.isLt; omega)
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [work.again4, ↓reduceIte]
    refine ⟨⟨hc₆, by simp only; omega, by simp only; rw [h24]; exact hi₆⟩, .inl (by omega)⟩
  · rename_i hge
    have hge' : ¬ s.local1.toNat < 2 := by simpa [lt, BitVec.ult] using hge
    have heq : s.local1.toNat = 2 := by omega
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [work.again4, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hc, heq ▸ hi⟩

theorem work_spec (t : ThreadId) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G t (gOut 0)) m) (hc : m.current = t) :
    proto.WP t (work cPtr) (fun _ G' m' _ => m'.current = t ∧ proto.inv (upd G' t (gOut 2)) m')
      G m d := by
  unfold work
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

/-! ## The kid -/

/-- A thread at the end of `work`: the same ghost value, but its place in `main` or `work` is `p`
(`joins` for `main`, `fin` and `gone` for the kid). -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh}
    (hi : proto.inv (upd G t (gOut 2)) m) (hg : g.1 = ⟨.out, Heap.empty, Heap.empty⟩ ∨
      g.1 = ⟨.gone, Heap.empty, Heap.empty⟩)
    (hp : (t = 0 ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, .joins)) ∨
      (t = 1 ∧ g = (⟨.gone, Heap.empty, Heap.empty⟩, .fin))) :
    proto.inv (upd G t g) m := by
  have hx : (fun u => (upd G t (gOut 2) u).2) t = .work 2 := by
    show (upd G t (gOut 2) t).2 = _; rw [upd_self]; rfl
  obtain ⟨ht2, -, -⟩ := shape_work hi.2.shape hx
  have hX : (fun u => (upd (upd G t (gOut 2)) t g u).2) = upd (fun u => (upd G t (gOut 2) u).2) t g.2 :=
    snd_upd _ _ _
  have hsum : sum (fun u => (upd (upd G t (gOut 2)) t g u).2) = sum (fun u => (upd G t (gOut 2) u).2) := by
    rw [hX]; unfold sum
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0)]; show 2 + _ = _; rw [hx]; rfl
    · rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1)]; show _ + 2 = _; rw [hx]; rfl
  have hl := hi.1.ghost (t := t) (g := g) (by rw [upd_self]; rfl)
    (by rcases hg with h | h <;> simp [Lock.prod, L, h])
    (by rw [upd_self]; rcases hg with h | h <;> simp [L, Lock.prod, h, gOut])
    (by rcases hg with h | h <;> simp [L, Lock.prod, h])
    (fun hph => by
      refine hi.1.live t ?_
      rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone))
    (fun hL hR => by
      have hR' : R (fun u => (upd G t (gOut 2) u).2) hL := hR
      show R _ hL; unfold R at hR' ⊢; rw [hsum]; exact hR')
  rw [upd_upd] at hl
  refine ⟨hl, ?_⟩
  have hu := hi.2
  refine ⟨?_, hu.io, fun u => ?_, hu.blk⟩
  · rw [snd_upd]
    have := shape_upd hu.shape hx (Nat.le_refl 2) g.2 (by
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inr (.inr ⟨rfl, rfl⟩))
    rw [snd_upd, upd_upd] at this; exact this
  · unfold upd; split
    · rcases hg with h | h <;> rw [h]
    · rename_i h; have := hu.parts u; rwa [upd_ne _ _ h] at this

/-- The kid spawned no thread. -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : proto.inv G m)
    (hu : 0 < u) : joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, h⟩ := hi.2.shape
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

/-- The kid: `work` on the `Counter`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | work p =>
    obtain ⟨rfl, rfl⟩ := hg
    show proto.WP u ((fun _ => ()) <$> work cPtr) _ G _ d
    refine WP.map (WP.mono ?_ (work_spec u G _ d
      (by rw [show gOut 0 = G u from hgu.symm, upd_same]
          exact fits.cur u hi (by rw [hgu]; exact (by decide : LPh.out ≠ LPh.gone))) rfl))
    rintro _ G' m' _ ⟨-, hi'⟩
    have hx : (fun v => (upd G' u (gOut 2) v).2) u = .work 2 := by
      show (upd G' u (gOut 2) u).2 = _; rw [upd_self]; rfl
    obtain ⟨hu2, -, -⟩ := shape_work hi'.2.shape hx
    have hu1 : u = 1 := by unfold ThreadId at *; omega
    subst hu1
    exact ⟨_, inv_end hi' (.inr rfl) (.inr ⟨rfl, rfl⟩), ⟨rfl, rfl⟩,
      fun _ => joinedAll_kid hi' hu⟩
  | producer p => cases hg
  | semWork p => cases hg
  | writer p => cases hg

/-! ## `main` -/

theorem enc_io (io : Io) : (Enc.encode io).size = 16 := by
  show (Array.replicate 16 _).size = 16; simp

/-- The initial mutex. -/
def mutex0 : Io_Mutex := { state := { raw := Io_Mutex_State.unlocked } }

theorem enc_mutex : Enc.encode mutex0 = Enc.encode (0 : BitVec 32) := by decide +kernel

theorem enc_u32 (v : BitVec 32) : (Enc.encode v).size = 4 := LawfulEnc.size_encode v

/-- `main`'s ghost value before its spawn. -/
def gPre : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .pre)

/-- The start: no thread. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, .none)

/-- `main` at its join. -/
def gJoin : Gh := (⟨.out, Heap.empty, Heap.empty⟩, .joins)

/-- The `Counter` in three parts, after `main`'s stores: `io`, the mutex, the counter. -/
def Parts (io : Io) (A : Nat) : Assn :=
  bytesAt cPtr A 24 .stack (Enc.encode io) ∗ (bytesAt (cPtr.add 16) A 24 .stack (Enc.encode mutex0) ∗
    bytesAt (cPtr.add 20) A 24 .stack (Enc.encode (0 : BitVec 32)))

/-- Before the spawn: `main` alone owns the `Counter`, with its three parts. The lock starts:
it owns the mutex and the counter; `io` belongs to no thread. -/
theorem inv_pre {m : Mem} {io : Io} {A : Nat} {h : Heap} (ho : Owned (upd (fun _ => Heap.empty) 0 h) m)
    (hp : Parts io A h) (hA : A % 8 = 0) (hth : m.threads = #[{ spawner := 0, joined := true }])
    (hat : m.atomics = #[]) (hq : m.waiters = #[]) :
    proto.inv (upd G0 0 gPre) m := by
  obtain ⟨hI, hWC, dI, rfl, hio, hW, hC, dWC, rfl, hw, hc⟩ := hp
  have hs : (hI ∪ (hW ∪ hC)).Sub m.heap := by have := ho.sub 0; rwa [upd_self] at this
  have hsW : hW.Sub m.heap := (Heap.sub_union_left.trans (Heap.sub_union_right dI)).trans hs
  have hsI : hI.Sub m.heap := Heap.sub_union_left.trans hs
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  have hcell : ∀ x, x < 16 → hI (0, x) ≠ none := fun x hx =>
    bytesAt_in hio rfl (by simp [cPtr]) (by simp [cPtr, enc_io]; omega)
  have hcellW : ∀ x, 16 ≤ x → x < 16 + 4 → hW (0, x) ≠ none := fun x h1 h2 =>
    bytesAt_in hw rfl (by simp [cPtr, Ptr.add]; omega)
      (by simp [cPtr, Ptr.add, enc_mutex, enc_u32]; omega)
  -- block 0, and the mutex's bytes
  obtain ⟨blk, hblk, hl, hA', hS', hK', -⟩ := bytesAt_blk (m := m) hio hsI rfl
    (by rw [enc_io]; decide)
  obtain ⟨blk', hblk', -, -, -, -, hx⟩ := bytesAt_blk (m := m) hw hsW rfl
    (by rw [enc_mutex, enc_u32]; decide)
  rw [hblk] at hblk'; cases hblk'
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 16 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [show (16 : Nat) = (cPtr.add 16).off.toNat from rfl, show 4 = (Enc.encode mutex0).size by
      rw [enc_mutex, enc_u32], hx, enc_mutex]
    exact intOfBytes_rmw 0
  -- main keeps the mutex and the counter; `io` belongs to no thread
  have hsub : (Heap.empty ∪ (hC ∪ hW)).Sub (hI ∪ (hW ∪ hC)) := by
    rw [Heap.empty_union, Heap.union_comm dWC.symm]; exact Heap.sub_union_right dI
  have ho' := ho.shrink (t := 0) (by rw [upd_self]; exact hsub)
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 gPre u = G0 u := fun u h => upd_ne _ _ h
  have hjt : joinedB m 0 = false := rfl
  refine ⟨Inv.make (t := 0) (hL := hC) (hW := hW) ho' hjt (fun u hu => ?_) (by rw [upd_self]; rfl)
    (by rw [upd_self]; exact fun _ => .inl rfl) dWC.symm (fun u => ?_) (fun u => ?_) ?_
    (fun x h1 h2 => hcellW x h1 h2) ⟨blk, hblk, hl, by rw [hS']; decide,
      by show (blk.addr + 16) % 4 = 0; rw [hA']; omega,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (fun u hu => ?_) (by rw [h1]; decide), ?_⟩
  · rw [upd_ne _ _ hu]
    unfold Lock.own; rw [hGu u hu]; split <;> rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; exact .inl ⟨rfl, by rw [h1]; decide, rfl⟩
    · rw [hGu u hu]; exact .inr rfl
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · -- the counter holds `0`
    show pts (cPtr.add 20) 4 (BitVec.ofNat 32 (sum _)) hC
    have hsum : sum (fun u => (upd G0 0 gPre u).2) = 0 := by
      show (upd G0 0 gPre 0).2.count + (upd G0 0 gPre 1).2.count = 0
      rw [upd_self, hGu 1 (by decide)]; rfl
    rw [hsum]
    exact ⟨A, 24, .stack, Enc.encode (0 : BitVec 32), by simp [cPtr, Ptr.add]; omega, enc_u32 0,
      LawfulEnc.decode_encode _, hc, by decide⟩
  · have : u = 0 := by rw [h1] at hu; omega
    subst this; exact VClock.le_refl _
  · refine ⟨⟨by rw [hth]; rfl, .inl ⟨h1, by show (upd G0 0 gPre 0).2 = _; rw [upd_self]; rfl,
      fun u hu => ?_⟩⟩,
      fun e he hb ho16 => .inr fun u hu => ?_, fun u => ?_, hbk⟩
    · show (upd G0 0 gPre u).2 = _; rw [hGu u (by unfold ThreadId at *; omega)]; rfl
    · have : u = 0 := by rw [h1] at hu; omega
      subst this
      have := ho.owns 0 (by rw [h1]; decide) e he (.inl ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [upd_self, hb]; simp only [Heap.union_apply]
        have := hcell e.off ho16
        cases e' : hI (0, e.off) with
        | none => exact absurd e' this
        | some c => simp⟩)
      exact this
    · by_cases hu : u = 0
      · subst hu; rw [upd_self]; rfl
      · rw [hGu u hu]; rfl

theorem main_spec (σ : Placement) (io : Io) (d : Nat) :
    proto.WP 0 (mutexCounter io) QM G0 { mem0 σ with current := 0 } d := by
  unfold mutexCounter
  -- the `Counter`: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 24 8 (by decide))
    (Owned.start rfl rfl) rfl (by simp [mem0, Mem.ofGlobals]) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 σ with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = cPtr from rfl] at hb₁ ⊢
  -- its three parts
  obtain ⟨hI, hR₁, dI, rfl, hI₁, hR₁'⟩ := bytesAt_split hb₁ (k := 16) (by simp)
  obtain ⟨hW, hC, dWC, rfl, hW₁, hC₁⟩ := bytesAt_split hR₁' (k := 4) (by simp)
  have hsI : ((Array.replicate 24 Byte.undef).extract 0 16).size = 16 := by simp
  have hsW : (((Array.replicate 24 Byte.undef).extract 16).extract 0 4).size = 4 := by simp
  have hsC : (((Array.replicate 24 Byte.undef).extract 16).extract 4).size = 4 := by simp
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  -- `io`, the mutex, the counter
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 (hI ∪ (hW ∪ hC))) m₁ := ho₁
  have F₁ : (bytesAt cPtr A 24 .stack ((Array.replicate 24 Byte.undef).extract 0 16) ∗
      (bytesAt (cPtr.add 16) A 24 .stack (((Array.replicate 24 Byte.undef).extract 16).extract 0 4) ∗
        bytesAt ((cPtr.add 16).add 4) A 24 .stack (((Array.replicate 24 Byte.undef).extract 16).extract 4)))
      (hI ∪ (hW ∪ hC)) := ⟨hI, hW ∪ hC, dI, rfl, hI₁, hW, hC, dWC, rfl, hW₁, hC₁⟩
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := cPtr) (A := A) (S := 24) (K := .stack) (k := 0) (a := 8) io rfl (by decide)
    (by rw [hsI]; decide) (by simp [cPtr]; omega) (by decide)).frame) ho₁' hc₁ (by
      rw [hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₁) fun _ m₂ h₂ _ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  have hwI : (writeBytes ((Array.replicate 24 Byte.undef).extract 0 16) 0 (Enc.encode io)).size = 16 := by
    rw [writeBytes_size _ _ _ (by simp [enc_io])]; exact hsI
  have pr₂ : (ptrProject cPtr (·.add 16)).run m₂ = pure (cPtr.add 16, m₂) := by
    have hs₂' : h₂.Sub m₂.heap := by simpa [upd_self] using ho₂.sub 0
    obtain ⟨hx, hy, dxy, hxy, hbx, -⟩ := F₂
    rw [hxy] at hs₂'
    exact bytesAt_ptrProject_sub hbx (Heap.sub_union_left.trans hs₂') (k := 16)
      (by rw [hwI]; exact Nat.le_refl _) (by rw [hwI]; decide)
  refine WP.bind (WP.callMC_ptrProject pr₂ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := cPtr.add 16) (A := A) (S := 24) (K := .stack) (k := 0) (a := 4) mutex0
    (by rw [enc_mutex, enc_u32]; rfl) rfl (by decide)
    (by rw [hsW]; decide) (by simp [cPtr, Ptr.add]; omega) (by decide)).frame.frameL) ho₂
    (hs₂.current.trans hc₁) (by rw [hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₂)
    fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  have pr₃ : (ptrProject cPtr (·.add 20)).run m₃ = pure ((cPtr.add 16).add 4, m₃) := by
    have hs₃' : h₃.Sub m₃.heap := by simpa [upd_self] using ho₃.sub 0
    obtain ⟨hx, hy, dxy, hxy, hbx, hyy⟩ := F₃
    obtain ⟨hz, hw, dzw, hzw, -, hbw⟩ := hyy
    rw [hxy] at hs₃'
    have hsy : hy.Sub m₃.heap := (Heap.sub_union_right dxy).trans hs₃'
    rw [hzw] at hsy
    have i0 : m₃.inBounds cPtr = true := by
      simpa using bytesAt_inBounds_sub hbx (Heap.sub_union_left.trans hs₃') (k := 0) (by simp)
        (by rw [hwI]; decide)
    have i20 : m₃.inBounds ((cPtr.add 16).add 4) = true := by
      simpa using bytesAt_inBounds_sub hbw ((Heap.sub_union_right dzw).trans hsy) (k := 0)
        (by simp) (by rw [hsC]; decide)
    exact ptrProject_add_run i0 i20
  refine WP.bind (WP.callMC_ptrProject pr₃ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := (cPtr.add 16).add 4) (A := A) (S := 24) (K := .stack) (k := 0)
    (a := 4) (0 : BitVec 32) rfl (by decide) (by rw [hsC]; decide) (by simp [cPtr, Ptr.add]; omega)
    (by decide)).frameL.frameL) ho₃ (hs₃.current.trans (hs₂.current.trans hc₁))
    (by rw [hs₃.threads, hs₂.threads, hs₁.threads]; simp [mem0, Mem.ofGlobals]) (by rw [upd_self]; exact F₃)
    fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans (hs₃.current.trans (hs₂.current.trans hc₁))
  have hth₄ : m₄.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₄ : m₄.atomics = #[] := by rw [hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₄ : m₄.waiters = #[] := by rw [hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hP : Parts io A h₄ := by
    rw [writeBytes_all (by rw [hsI, enc_io]), writeBytes_all (by rw [hsW, enc_mutex, enc_u32]),
      writeBytes_all (by rw [hsC, enc_u32])] at F₄
    exact F₄
  -- the spawn
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, inv_pre ho₄ hP hA8 hth₄ hat₄ hq₄, fun G₁ m₅ hg₁ hi₅ =>
    ⟨gOut 0, ⟨rfl, rfl⟩, fun child m₆ hf => ?_⟩⟩)
  -- after the stop: `main` alone, at `gPre`
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, h0, -⟩⟩ := hi₅.2.shape
  rotate_left
  · exfalso; change (G₁ 0).2 = _ ∨ _ at h0
    simp [hg₁, gPre] at h0
  have hcs₅ : m₅.clocks.size = 1 := by rw [hi₅.1.own.csize, hs1]
  obtain ⟨hch, hm₆⟩ := Lock.fork_eq hf
  rw [hs1] at hch
  subst hch hm₆
  have hsum₀ : ∀ X : ThreadId → Ph, X 0 = .pre ∨ X 0 = .work 0 → X 1 = .none ∨ X 1 = .work 0 →
      sum X = 0 := by
    intro X h0 h1
    unfold sum
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] <;> rfl
  have hX₅ : ∀ u, (G₁ u).2 = if u = 0 then .pre else .none := by
    intro u; split
    · rename_i h; subst h; rw [hg₁]; rfl
    · exact hnone u (by unfold ThreadId at *; omega)
  have hi₆ : proto.inv (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0))
      { m₅ with
        current := 0
        clocks := (m₅.clocks.set! 0 (VClock.bump (m₅.clocks[0]!) 0)).push
          (VClock.bump (m₅.clocks[0]!) 0)
        threads := m₅.threads.push { spawner := 0, joined := false } } := by
    refine ⟨?_, ⟨⟨?_, .inr ⟨by simp [hs1], ?_, .inr ⟨0, by decide, ?_⟩, .inr ⟨0, by decide, ?_⟩,
      fun u hu => ?_⟩⟩, fun e he hb ho16 => ?_, fun u => ?_, hi₅.2.blk⟩⟩
    · refine hi₅.1.fork (t := 0) (by rw [hg₁]; rfl) hf (by rw [hg₁]; rfl) (fun _ => .inl rfl) rfl rfl
        rfl rfl fun hL hR => ?_
      have hR' : R (fun u => (G₁ u).2) hL := hR
      show R _ hL
      unfold R at hR' ⊢
      rw [hsum₀ _ (by rw [hX₅]; simp) (by rw [hX₅]; simp)] at hR'
      rw [hsum₀ _ (.inr (by show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 0).2 = _; rw [upd_self]; rfl))
        (.inr (by show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 1).2 = _
                  rw [upd_ne _ _ (by decide), upd_self]; rfl))]
      exact hR'
    · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
    · simp only [Array.getElem?_push, hs1, ↓reduceIte]
    · show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 0).2 = _; rw [upd_self]; rfl
    · show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) 1).2 = _; rw [upd_ne _ _ (by decide), upd_self]; rfl
    · show (upd (upd G₁ 1 (gOut 0)) 0 (gOut 0) u).2 = _
      rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
      exact hnone u (by unfold ThreadId at *; omega)
    · rcases hi₅.2.io e he hb ho16 with h | h
      · exact .inl h
      · obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m₅.clocks) (t := 0) (by rw [hcs₅]; decide)
        refine .inr fun u hu => ?_
        simp only [Array.size_push, hs1] at hu
        rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
        · exact VClock.le_trans (h 0 (by rw [hs1]; decide)) (hcl 0 (by rw [hcs₅]; decide))
        · rw [← hcs₅]; exact VClock.le_trans (h 0 (by rw [hs1]; decide)) hcn
    · unfold upd; split
      · rfl
      · split
        · rfl
        · exact hi₅.2.parts u
  simp only [StateT.run_bind]
  -- `work`
  refine WP.bind (WP.callC (WP.mono ?_ (work_spec 0 _ _ k hi₆ rfl)))
  rintro _ G₂ m₇ d₂ ⟨hc₇, hi₇⟩
  -- the join of the kid
  have hiJ := inv_end hi₇ (.inl rfl) (.inl ⟨rfl, rfl⟩)
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨gJoin, hiJ, fun G₃ m₈ hg₃ hi₈ => ?_⟩)
  have hsh₈ := hi₈.2.shape
  obtain ⟨h08, ⟨-, h0, -⟩ | ⟨hs2, hr1, -, -, hn2⟩⟩ := hsh₈
  · exfalso; change (G₃ 0).2 = _ at h0; rw [hg₃] at h0; cases h0
  refine ⟨fun _ => ⟨by decide, by rw [hs2]; decide, ⟨rfl, rfl⟩, by simp [Thread.joinValid, Mem.isGated, hr1]⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₈ with current := 0 }) hr1 rfl rfl, fun m₉ hj => ?_⟩⟩
  -- `main` takes the kid's part, then the lock's resource
  let gEnd : Gh := (⟨.out, L.part (G₃ 0) ∪ L.own G₃ m₈ 1, Heap.empty⟩, .joins)
  have hX₃ : (fun u => (upd G₃ 0 gEnd u).2) = fun u => (G₃ u).2 := by
    funext u; unfold upd; split
    · rename_i h; subst h; rw [hg₃]; rfl
    · rfl
  have hL₉ := hi₈.1.join (t := 0) (u := 1) (g := gEnd) (by decide) (by decide)
    (by rw [hg₃]; rfl) hfin.1 hj rfl rfl rfl (fun hL hR => by
      show R _ hL; rw [hX₃]; exact hR)
  obtain ⟨rec, hrec, -, hm₉⟩ := join_eq hj
  have hth₉ : m₉.threads = m₈.threads.set! 1 { rec with joined := true } := by rw [hm₉]
  have hs₉ : m₉.threads.size = 2 := by rw [hth₉, Array.size_set!, hs2]
  have hc₉ : m₉.current = 0 := by rw [hm₉]
  have hcs₈ : m₈.clocks.size = 2 := by rw [hi₈.1.own.csize, hs2]
  have hfree : L.Free (upd G₃ 0 gEnd) := by
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
    simp only [true_and, show 0 < m₈.clocks.size by omega, ↓reduceIte, show (0 : Nat) = 0 from rfl]
    rw [hs₉] at hu
    by_cases h0 : u = 0
    · subst h0; simp [VClock.le_refl]
    · have : u = 1 := by omega
      subst this
      exact VClock.le_merge_right _ _
  obtain ⟨hL, hR, hdLW, hd, ho⟩ := hL₉.take (t := 0) (by rw [hs₉]; decide) hfree (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)) hall₉
  -- the counter holds 4
  have hR4 : pts (cPtr.add 20) 4 (BitVec.ofNat 32 4) hL := by
    have : R (fun u => (upd G₃ 0 gEnd u).2) hL := hR
    rw [hX₃] at this
    have h4 : sum (fun u => (G₃ u).2) = 4 := by
      show (G₃ 0).2.count + (G₃ 1).2.count = 4
      rw [hg₃, hfin.2]; rfl
    unfold R at this; rw [h4] at this; exact this
  let own₉ := L.own (upd G₃ 0 gEnd) m₉
  have hd' : Heap.Disjoint hL (own₉ 0 ∪ L.wordH m₉) :=
    Heap.disjoint_union_right.mpr ⟨(Heap.disjoint_union_right.mp hd).1.symm, hdLW⟩
  have heq : own₉ 0 ∪ (hL ∪ L.wordH m₉) = hL ∪ (own₉ 0 ∪ L.wordH m₉) :=
    Heap.union_left_comm (Heap.disjoint_union_right.mp hd).1
  -- the counter's pointer, then its load
  have pr₉ : (ptrProject cPtr (·.add 20)).run m₉ = pure (cPtr.add 20, m₉) := by
    obtain ⟨blk₀, hblk₀, -, hsz₀, -⟩ := hi₈.2.blk
    have hb₉ : m₉.blocks = m₈.blocks := by rw [hm₉]
    exact ptrProject_block_run (by rw [hb₉]; exact hblk₀) rfl (by decide)
      (by simp [cPtr, hsz₀])
  refine WP.bind (WP.callMC_ptrProject pr₉ ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned (TTriple.load (p := cPtr.add 20) (a := 4) (v := BitVec.ofNat 32 4)
    (by decide)).frame ho hc₉ (by rw [hs₉]; decide)
    (by rw [upd_self, heq]; exact ⟨hL, _, hd', rfl, hR4, rfl⟩) fun a m₁₀ hQ hr ho' hq hs₁₀ _ _ => ?_)
  obtain ⟨h₁, h₂, -, -, hq₁, -⟩ := hq
  obtain ⟨rfl, -⟩ := sep_lift.mp hq₁
  obtain ⟨b, blk, o, -, -, -, hm₁₀⟩ := load_ok hr
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the free of the `Counter`
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hi₈.2.blk
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

/-- **`mutexCounter` gives 4 under every schedule** (every oracle `o`, every `fuel`). -/
theorem mutexCounter_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run env dispatch fuel o (mutexCounter io) (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 4 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ io) h
  exact hv

/-- **No run of `mutexCounter` gives an error**: no data race on the counter, no deadlock at the
futex, no panic, under every schedule. -/
theorem mutexCounter_safe (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run env dispatch fuel o (mutexCounter io) (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ io)

/-- One schedule completes: under the oracle that always picks option 0, the mutex counter returns 4 within
fuel 1000, from `mem0` with the translation's spawn policy. The kernel computes the run, with
each loop cut after 10 iterations (`unroll_sched`, `ZigLean/Conc/Unroll.lean`). -/
theorem mutexCounter_completes :
    ∃ σ, Witness.okVal (Sched.run ⟨.any, .available⟩ dispatch 1000 (fun _ => 0) (mutexCounter ⟨⟩) (mem0 σ)) = some 4 :=
  ⟨.fresh, by unroll_sched 10⟩

end Sync.MutexCounter
