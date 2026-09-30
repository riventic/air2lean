import Proofs.Sync.Gen
import ZigLean.Conc.Lemmas

/-!
# `mutexCounter` over all schedules

`mutexCounter` spawns one thread; each of the two threads adds 1 two times to a counter, under
an `Io.Mutex` (translated from Zig 0.16.0's std code; the futex under it is the model). The
result is 4 under every schedule (`mutexCounter_spec`), and no schedule gives an error
(`mutexCounter_safe`): no data race on the counter, and no deadlock at the futex.

**Protocol.** A thread's ghost value (`Gh`): for a thread in `work`, how many increments it did
and where it is in the mutex code (`Ph`); `main` before its spawn and at its join; the kid at
its end. The invariant (`Inv`):

- The mutex word (bytes 16..20 of the `Counter` block, block 0) is `0` if no thread holds the
  mutex, else `1` or `2`. At most one thread holds it.
- The mutex is one atomic location whose messages are an RMW chain (`ALoc.Chain`): so an RMW
  reads the newest message only, and a `cmpxchg` that succeeds reads it too. Every message
  holds `0`, `1` or `2`.
- The counter (bytes 20..24) holds the number of increments of both threads.
- **No data race.** Each access to the counter happened before the holder's clock, or, if no
  thread holds the mutex, before the release clock of the newest message (`LockLe`). An unlock
  is a release RMW, a lock an acquire RMW, so the next holder's clock is above every access.
- **No deadlock.** A thread in the futex queue waits at the mutex, and the other thread holds
  the mutex with the word `2` (so its unlock wakes), or it is at that wake. So the queue has at
  most one thread, and if it has one, the other thread can go on (`Live`).
-/

open Zig Zig.Conc Zig.Conc.Proto Sync

namespace Sync.MutexCounter

/-- Where a thread in `work` stops. -/
inductive Ph where
  /-- At a pick of `lock`: it does not hold the mutex. -/
  | out
  /-- At a futex wait of `lock`. -/
  | wait
  /-- At the pick of `unlock`: it holds the mutex. -/
  | holds
  /-- At the futex wake of `unlock`. -/
  | wake
  deriving DecidableEq

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- A thread in `work`: it did `k` increments; it stops at `ph`. -/
  | work (k : Nat) (ph : Ph)
  /-- `main` at its join. -/
  | joins
  /-- The kid has ended. -/
  | fin
  deriving DecidableEq

/-- The increments of a thread. -/
def Gh.count : Gh → Nat
  | .work k _ => k
  | .joins | .fin => 2
  | _ => 0

/-- Thread `u` holds the mutex. -/
def Hold (G : ThreadId → Gh) (u : ThreadId) : Prop := ∃ k, G u = .work k .holds

/-- Thread `u` is at a futex wait of `lock`. -/
def Waits (G : ThreadId → Gh) (u : ThreadId) : Prop := ∃ k, G u = .work k .wait

/-- Thread `u` is at the futex wake of `unlock`. -/
def Wakes (G : ThreadId → Gh) (u : ThreadId) : Prop := ∃ k, G u = .work k .wake

/-- The `Counter` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩

/-- The mutex: bytes 16..20 of the `Counter`. -/
def mPtr : Ptr := ⟨some 0, 16⟩

/-- The bytes `o..o+4` of block 0 hold the `u32` `v`. -/
def U32At (m : Mem) (o : Nat) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m 0 o 4)).run = some (.ok v)

/-- Block 0 is a live stack block of 24 bytes at an address that is a multiple of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 24 ∧
    blk.kind = .stack ∧ blk.addr % 8 = 0

/-- The mutex's atomic location: none yet, or one RMW chain of messages that hold `0`, `1` or
`2`, whose newest message has the block's bytes. -/
def LocOk (m : Mem) : Prop :=
  (m.atomics = #[] ∧ U32At m 16 0) ∨ ∃ l, m.atomics = #[l] ∧ l.block = 0 ∧ l.off = 16 ∧ l.len = 4 ∧
    0 < l.msgs.size ∧ l.Chain ∧
    (∀ j (h : j < l.msgs.size), ∃ w < 3, (intOfBytes 32 l.msgs[j].bytes).run =
      some (.ok (BitVec.ofNat 32 w))) ∧
    ALoc.lastBytes l = curBytes m 0 16 4

/-- The clock `c` happened before the holder's clock, or, if no thread holds the mutex, before
the release clock of the newest message of the mutex. -/
def LockLe (G : ThreadId → Gh) (m : Mem) (c : VClock) : Prop :=
  (∀ u, Hold G u → VClock.le c (m.clocks[u]!) = true) ∧
  ((∀ u, ¬ Hold G u) → ∃ l, m.atomics = #[l] ∧ VClock.le c (l.msgs.back!).relClock = true)

/-- A footprint entry: a write that happened before every thread (the start of `main`), a read
of `io`, an atomic access to the mutex, or an access to the counter under the mutex. -/
def FpOk (G : ThreadId → Gh) (m : Mem) (e : FootprintEntry) : Prop :=
  e.block = 0 ∧
  ((e.kind = .write ∧ ∀ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true) ∨
   (e.kind = .read ∧ e.off = 0 ∧ e.len = 16) ∨
   (e.kind.isAtomic = true ∧ e.off = 16 ∧ e.len = 4) ∨
   (e.off = 20 ∧ e.len = 4 ∧ LockLe G m e.clock))

/-- The threads: `main` alone before its spawn; then `main` and the kid, which `main` spawned
and did not join yet. -/
def ThrOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧ m.clocks.size = m.threads.size ∧
  ((m.threads.size = 1 ∧ G 0 = .pre ∧ ∀ u, 1 ≤ u → G u = .none) ∨
   (m.threads.size = 2 ∧ (∃ r, m.threads[1]? = some r ∧ r.spawner = 0 ∧ r.joined = false) ∧
    (G 0 = .joins ∨ ∃ k ph, k ≤ 2 ∧ G 0 = .work k ph) ∧
    (G 1 = .fin ∨ ∃ k ph, k ≤ 2 ∧ G 1 = .work k ph) ∧ ∀ u, 2 ≤ u → G u = .none))

/-- The futex queue: at most one thread, which waits at the mutex, and the other thread holds
the mutex with the word `2`, or is at the wake of its unlock. -/
def FqOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.waiters.size ≤ 1 ∧ ∀ w ∈ m.waiters, w.2 = mPtr ∧ Waits G w.1 ∧
    ∃ v, v ≠ w.1 ∧ ((Hold G v ∧ U32At m 16 2) ∨ Wakes G v)

/-- The invariant (see the module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  thr : ThrOk G m
  blk : BlkOk m
  cnt : U32At m 20 (BitVec.ofNat 32 ((G 0).count + (G 1).count))
  word : ∃ w < 3, U32At m 16 (BitVec.ofNat 32 w) ∧ (w = 0 ↔ ∀ u, ¬ Hold G u)
  one : ∀ u v, Hold G u → Hold G v → u = v
  loc : LocOk m
  fq : FqOk G m
  fp : ∀ e ∈ m.footprint, FpOk G m e
  own : ∀ e ∈ m.footprint, e.tid < m.threads.size ∧ VClock.le e.clock (m.clocks[e.tid]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv
  init
    | .work p => if p = cPtr then some (.work 0 .out) else none
    | _ => none
  fin g := g = .fin
  strict := true
  joins g := g = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 4 ∧ joinedAll 0 m

/-! ## Frame: steps that keep the invariant -/

theorem getElem!_set! {α : Type} [Inhabited α] (xs : Array α) (i u : Nat) (v : α) :
    (xs.set! i v)[u]! = if u = i ∧ i < xs.size then v else xs[u]! := by
  by_cases hu : u < xs.size
  · rw [getElem!_pos _ u (by simp [hu]), getElem!_pos xs u hu]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hu]
    by_cases h : i = u
    · subst h; simp [hu]
    · simp [h, Ne.symm h]
  · rw [getElem!_neg _ u (by simp [hu]), getElem!_neg xs u hu]
    split
    · rename_i h; exact absurd (h.1 ▸ h.2) hu
    · rfl

theorem VClock.merge_le {a b c : VClock} (ha : VClock.le a c = true) (hb : VClock.le b c = true) :
    VClock.le (VClock.merge a b) c = true :=
  VClock.le_iff.mpr fun i => by
    rw [VClock.get_merge]
    exact Nat.max_le.mpr ⟨VClock.le_iff.mp ha i, VClock.le_iff.mp hb i⟩

/-- `m'` is `m` with clocks that are not smaller. -/
structure Grows (m m' : Mem) : Prop where
  threads : m'.threads = m.threads
  blocks : m'.blocks = m.blocks
  atomics : m'.atomics = m.atomics
  footprint : m'.footprint = m.footprint
  waiters : m'.waiters = m.waiters
  csize : m'.clocks.size = m.clocks.size
  cle : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true

theorem curBytes_congr {m m' : Mem} (h : m'.blocks = m.blocks) (b o len : Nat) :
    curBytes m' b o len = curBytes m b o len := by
  unfold curBytes; rw [h]

theorem lockLe_grow {G : ThreadId → Gh} {m m' : Mem} {c : VClock} (hg : Grows m m')
    (h : LockLe G m c) : LockLe G m' c :=
  ⟨fun u hu => VClock.le_trans (h.1 u hu) (hg.cle u), fun hn => by
    obtain ⟨l, hl, hle⟩ := h.2 hn
    exact ⟨l, hg.atomics ▸ hl, hle⟩⟩

theorem Inv.grow {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : Grows m m') :
    Inv G m' where
  thr := by
    unfold ThrOk; rw [hg.threads, hg.csize]; exact hi.thr
  blk := by unfold BlkOk; rw [hg.blocks]; exact hi.blk
  cnt := by unfold U32At; rw [curBytes_congr hg.blocks]; exact hi.cnt
  word := by
    obtain ⟨w, hw, hu, hh⟩ := hi.word
    exact ⟨w, hw, by unfold U32At; rw [curBytes_congr hg.blocks]; exact hu, hh⟩
  one := hi.one
  loc := by unfold LocOk U32At; rw [hg.atomics, curBytes_congr hg.blocks]; exact hi.loc
  fq := by
    unfold FqOk U32At; rw [hg.waiters, curBytes_congr hg.blocks]; exact hi.fq
  fp := by
    intro e he
    rw [hg.footprint] at he
    obtain ⟨hb, h⟩ := hi.fp e he
    refine ⟨hb, ?_⟩
    rcases h with ⟨hk, hle⟩ | h | h | ⟨ho, hl, hle⟩
    · exact .inl ⟨hk, fun u hu => VClock.le_trans (hle u (hg.threads ▸ hu)) (hg.cle u)⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨ho, hl, lockLe_grow hg hle⟩))
  own := by
    intro e he
    rw [hg.footprint] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨hg.threads ▸ h1, VClock.le_trans h2 (hg.cle _)⟩

theorem Grows.refl (m : Mem) : Grows m m :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => VClock.le_refl _⟩

theorem Grows.trans {m₁ m₂ m₃ : Mem} (h₁ : Grows m₁ m₂) (h₂ : Grows m₂ m₃) : Grows m₁ m₃ :=
  ⟨h₂.threads.trans h₁.threads, h₂.blocks.trans h₁.blocks, h₂.atomics.trans h₁.atomics,
    h₂.footprint.trans h₁.footprint, h₂.waiters.trans h₁.waiters, h₂.csize.trans h₁.csize,
    fun u => VClock.le_trans (h₁.cle u) (h₂.cle u)⟩

theorem grows_current (m : Mem) (u : ThreadId) : Grows m { m with current := u } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => VClock.le_refl _⟩

theorem grows_observe (m : Mem) (li id : Nat) : Grows m (observeM m li id) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => VClock.le_refl _⟩

theorem grows_acq (m : Mem) (c : VClock) : Grows m (acqM m c) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [acqM], fun u => ?_⟩
  simp only [acqM]
  rw [getElem!_set!]
  split
  · rename_i h; rw [h.1]; exact VClock.le_merge_left _ _
  · exact VClock.le_refl _

theorem grows_loadM (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) :
    Grows m (loadM m li ord msg) := by
  unfold loadM
  split
  · exact (grows_observe _ _ _).trans (grows_acq _ _)
  · exact grows_observe _ _ _

/-! ## Ghost values: a change of one thread's ghost value -/

theorem lockLe_congr {G G' : ThreadId → Gh} {m : Mem} {c : VClock}
    (hh : ∀ u, Hold G' u ↔ Hold G u) (h : LockLe G m c) : LockLe G' m c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun u hu => h1 u ((hh u).mp hu), fun hn => h2 fun u hu => hn u ((hh u).mpr hu)⟩

/-- The invariant for other ghost values with the same shape, count, holder and waker, whose
futex waiters wait. -/
theorem Inv.congrG {G G' : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hthr : ThrOk G' m)
    (hcnt : (G' 0).count + (G' 1).count = (G 0).count + (G 1).count)
    (hh : ∀ u, Hold G' u ↔ Hold G u) (hwk : ∀ u, Wakes G' u ↔ Wakes G u)
    (hwt : ∀ w ∈ m.waiters, Waits G' w.1) : Inv G' m where
  thr := hthr
  blk := hi.blk
  cnt := hcnt ▸ hi.cnt
  word := by
    obtain ⟨w, hw, hu, hz⟩ := hi.word
    refine ⟨w, hw, hu, hz.trans ?_⟩
    constructor
    · intro h u hu; exact h u ((hh u).mp hu)
    · intro h u hu; exact h u ((hh u).mpr hu)
  one u v hu hv := hi.one u v ((hh u).mp hu) ((hh v).mp hv)
  loc := hi.loc
  fq := by
    refine ⟨hi.fq.1, fun w hw => ?_⟩
    obtain ⟨h1, -, v, hv, h3⟩ := hi.fq.2 w hw
    refine ⟨h1, hwt w hw, v, hv, ?_⟩
    rcases h3 with ⟨h3, h4⟩ | h3
    · exact .inl ⟨(hh v).mpr h3, h4⟩
    · exact .inr ((hwk v).mpr h3)
  fp := by
    intro e he
    obtain ⟨hb, h⟩ := hi.fp e he
    refine ⟨hb, ?_⟩
    rcases h with h | h | h | ⟨ho, hl, hle⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨ho, hl, lockLe_congr hh hle⟩))
  own := hi.own

theorem count_upd {G : ThreadId → Gh} {t : ThreadId} {g : Gh} (h : g.count = (G t).count) :
    (upd G t g 0).count + (upd G t g 1).count = (G 0).count + (G 1).count := by
  by_cases h0 : t = 0
  · subst h0; rw [upd_self, upd_ne _ _ (by decide : (1 : Nat) ≠ 0), h]
  · by_cases h1 : t = 1
    · subst h1; rw [upd_self, upd_ne _ _ (by decide : (0 : Nat) ≠ 1), h]
    · rw [upd_ne _ _ (Ne.symm h0), upd_ne _ _ (Ne.symm h1)]

theorem hold_upd {G : ThreadId → Gh} {t : ThreadId} {g : Gh}
    (h : (∃ k, g = .work k .holds) ↔ Hold G t) (u : ThreadId) : Hold (upd G t g) u ↔ Hold G u := by
  by_cases hu : u = t
  · subst hu; unfold Hold; rw [upd_self]; exact h
  · unfold Hold; rw [upd_ne _ _ hu]

theorem wakes_upd {G : ThreadId → Gh} {t : ThreadId} {g : Gh}
    (h : (∃ k, g = .work k .wake) ↔ Wakes G t) (u : ThreadId) : Wakes (upd G t g) u ↔ Wakes G u := by
  by_cases hu : u = t
  · subst hu; unfold Wakes; rw [upd_self]; exact h
  · unfold Wakes; rw [upd_ne _ _ hu]

/-- A thread in `work`: two threads, and it is one of them. -/
theorem thr_work {G : ThreadId → Gh} {m : Mem} {t k : Nat} {ph : Ph} (h : ThrOk G m)
    (hg : G t = .work k ph) : m.threads.size = 2 ∧ t < 2 ∧ k ≤ 2 := by
  obtain ⟨-, -, ⟨-, h0, h1⟩ | ⟨hs, -, h0, h1, h2⟩⟩ := h
  · by_cases ht : t = 0
    · subst ht; rw [h0] at hg; cases hg
    · rw [h1 t (Nat.pos_of_ne_zero ht)] at hg; cases hg
  · have htl : t < 2 := by
      by_cases hc : t < 2
      · exact hc
      · rw [h2 t (Nat.le_of_not_lt hc)] at hg; cases hg
    refine ⟨hs, htl, ?_⟩
    by_cases ht : t = 0
    · subst ht
      rcases h0 with h0 | ⟨k', ph', hk, h0⟩
      · rw [h0] at hg; cases hg
      · rw [h0] at hg; cases hg; exact hk
    · have : t = 1 := by omega
      subst this
      rcases h1 with h1 | ⟨k', ph', hk, h1⟩
      · rw [h1] at hg; cases hg
      · rw [h1] at hg; cases hg; exact hk

/-- A change of thread `t`'s place in `work`, with the same count and the same role for the
mutex. The new place is a wait, or `t` is not in the futex queue. -/
theorem Inv.retag {G : ThreadId → Gh} {m : Mem} {t k k' : Nat} {ph ph' : Ph} (hi : Inv G m)
    (hg : G t = .work k ph) (hk : k' = k)
    (hh : ph' = .holds ↔ ph = .holds) (hwk : ph' = .wake ↔ ph = .wake)
    (hwt : ph' = .wait ∨ m.waiters.any (·.1 == t) = false) :
    Inv (upd G t (.work k' ph')) m := by
  subst hk
  refine hi.congrG ?_ (count_upd (by rw [hg]; rfl)) (hold_upd ?_) (wakes_upd ?_) ?_
  · obtain ⟨h0, hc, h⟩ := hi.thr
    refine ⟨h0, hc, ?_⟩
    obtain ⟨hs, htl, hkk⟩ := thr_work hi.thr hg
    rcases h with ⟨h1, -, -⟩ | ⟨-, hr, g0, g1, g2⟩
    · omega
    refine .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩
    · by_cases ht : t = 0
      · subst ht; rw [upd_self]; exact .inr ⟨k', ph', hkk, rfl⟩
      · rw [upd_ne _ _ (Ne.symm ht)]; exact g0
    · by_cases ht : t = 1
      · subst ht; rw [upd_self]; exact .inr ⟨k', ph', hkk, rfl⟩
      · rw [upd_ne _ _ (Ne.symm ht)]; exact g1
    · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact g2 u hu
  · rw [Hold, hg]
    constructor
    · rintro ⟨_, h⟩; cases h; exact ⟨k', by rw [hh.mp rfl]⟩
    · rintro ⟨_, h⟩; cases h; exact ⟨k', by rw [hh.mpr rfl]⟩
  · rw [Wakes, hg]
    constructor
    · rintro ⟨_, h⟩; cases h; exact ⟨k', by rw [hwk.mp rfl]⟩
    · rintro ⟨_, h⟩; cases h; exact ⟨k', by rw [hwk.mpr rfl]⟩
  · intro w hw
    obtain ⟨-, hwa, -⟩ := hi.fq.2 w hw
    by_cases hwt' : w.1 = t
    · unfold Waits; rw [hwt', upd_self]
      rcases hwt with rfl | hn
      · exact ⟨k', rfl⟩
      · exfalso
        have : m.waiters.any (·.1 == t) = true := Array.any_eq_true.mpr
          (by obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hw; exact ⟨i, hi, by rw [he, hwt']; simp⟩)
        rw [hn] at this; cases this
    · unfold Waits; rw [upd_ne _ _ hwt']; exact hwa

/-! ## Block 0: access, race check, record -/

/-- An access to block 0 at `o`, of `n` bytes, aligned to 4 or 8. -/
theorem acc0 {m : Mem} (hb : BlkOk m) {o n a : Nat} (hn : o + n ≤ 24) (ha : a = 4 ∨ a = 8)
    (hoa : o % a = 0) :
    ∃ blk, m.blocks[0]? = some blk ∧ blk.bytes.size = 24 ∧
      m.access ⟨some 0, (o : Int)⟩ n a = pure (0, blk, o) := by
  obtain ⟨blk, hblk, hl, hs, -, hadr⟩ := hb
  refine ⟨blk, hblk, hs, ?_⟩
  have e := access_of (p := ⟨some 0, (o : Int)⟩) (n := n) (a := a) (m := m) rfl hblk hl
    (by simp) (by simp only [hs]; omega) (by simp only [Int.toNat_natCast]; rcases ha with rfl | rfl <;> omega)
  simpa using e

/-- A step that bumps the current thread's clock and records the entry `e` keeps the invariant,
if `e` is one of the kinds of `FpOk`. -/
theorem Inv.record {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (hf : FpOk G (m.recordAt b o len k)
      { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current, block := b,
        off := o, len := len, kind := k }) :
    Inv G (m.recordAt b o len k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.thr.2.1]; exact ht
  let m₁ : Mem := { m with clocks := m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current) }
  have hg : Grows m m₁ := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [m₁], fun u => ?_⟩
    simp only [m₁]
    rw [getElem!_set!]
    split
    · rename_i h; rw [h.1]; exact VClock.le_bump _ _
    · exact VClock.le_refl _
  have hi₁ := hi.grow hg
  have hcur : (m.recordAt b o len k).clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current := by
    simp only [Mem.recordAt]; rw [getElem!_set!]; simp [hcs]
  exact {
    thr := hi₁.thr, blk := hi₁.blk, cnt := hi₁.cnt, word := hi₁.word, one := hi₁.one,
    loc := hi₁.loc, fq := hi₁.fq
    fp := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.fp e he
      · exact hf
    own := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.own e he
      · exact ⟨ht, by rw [hcur]; exact VClock.le_refl _⟩ }

/-- The race check of an access by the current thread to block 0: an entry that the access
overlaps is a write before every thread, or it does not race with it. -/
theorem noRace0 {G : ThreadId → Gh} {m : Mem} {o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (h : ∀ e ∈ m.footprint, FpOk G m e → o < e.off + e.len → e.off < o + len →
      (e.kind = .write ∧ ∀ u < m.threads.size, VClock.le e.clock (m.clocks[u]!) = true) ∨
      VClock.le e.clock (m.clocks[m.current]!) = true ∨ racePair e.kind k = none) :
    NoRace m 0 o len k := by
  refine noRace_of fun e he hb h1 h2 => ?_
  rcases h e he (hi.fp e he) h1 h2 with ⟨-, hle⟩ | h | h
  · exact .inl (hle _ ht)
  · exact .inl h
  · exact .inr h

/-- A read of `io` (bytes 0..16) does not race. -/
theorem noRace_io {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (ht : m.current < m.threads.size) :
    NoRace m 0 0 16 .read := by
  refine noRace0 hi ht fun e _ hf h1 h2 => ?_
  obtain ⟨-, h | ⟨hk, -⟩ | ⟨-, ho, -⟩ | ⟨ho, -⟩⟩ := hf
  · exact .inl h
  · exact .inr (.inr (by rw [hk]; rfl))
  · omega
  · omega

/-- An atomic access to the mutex (bytes 16..20) does not race. -/
theorem noRace_mutex {G : ThreadId → Gh} {m : Mem} {k : AccessKind} (hk : k.isAtomic = true)
    (hi : Inv G m) (ht : m.current < m.threads.size) : NoRace m 0 16 4 k := by
  refine noRace0 hi ht fun e _ hf h1 h2 => ?_
  obtain ⟨-, h | ⟨-, ho, hl⟩ | ⟨ha, -⟩ | ⟨ho, -⟩⟩ := hf
  · exact .inl h
  · omega
  · refine .inr (.inr ?_)
    unfold racePair; rw [ha, hk]; simp
  · omega

/-- The holder's access to the counter (bytes 20..24) does not race. -/
theorem noRace_cnt {G : ThreadId → Gh} {m : Mem} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size) (hh : Hold G m.current) : NoRace m 0 20 4 k := by
  refine noRace0 hi ht fun e _ hf h1 h2 => ?_
  obtain ⟨-, h | ⟨-, ho, hl⟩ | ⟨-, ho, hl⟩ | ⟨-, -, hle⟩⟩ := hf
  · exact .inl h
  · omega
  · omega
  · exact .inr (.inl (hle.1 _ hh))

/-! ## The mutex's atomic location -/

/-- The mutex's location exists: it is `l`, location 0. -/
def MLoc (m : Mem) (l : ALoc) : Prop :=
  m.atomics = #[l] ∧ l.block = 0 ∧ l.off = 16 ∧ l.len = 4 ∧ 0 < l.msgs.size ∧ l.Chain ∧
    (∀ j (h : j < l.msgs.size), ∃ w < 3, (intOfBytes 32 l.msgs[j].bytes).run =
      some (.ok (BitVec.ofNat 32 w))) ∧
    ALoc.lastBytes l = curBytes m 0 16 4

theorem u32_eq {m : Mem} {o : Nat} {a b : BitVec 32} (ha : U32At m o a) (hb : U32At m o b) :
    a = b := by
  unfold U32At at ha hb; rw [ha] at hb; cases hb; rfl

/-- The word is 0: no thread holds the mutex. -/
theorem noHold_of_zero {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (h0 : U32At m 16 0) :
    ∀ u, ¬ Hold G u := by
  obtain ⟨w, hw, hu, hz⟩ := hi.word
  have e := u32_eq hu h0
  have : w = 0 := by
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact this
  exact hz.mp this

/-- The memory `m₁` is `m` with other atomic locations (and message ids); a footprint entry of
the counter under no holder is not in `m`, if `m` has no location. -/
theorem Inv.atomics {G : ThreadId → Gh} {m m₁ : Mem} {l : ALoc} (hi : Inv G m)
    (hl : MLoc m₁ l) (hb : m₁.blocks = m.blocks) (hc : m₁.clocks = m.clocks)
    (ht : m₁.threads = m.threads) (hf : m₁.footprint = m.footprint) (hw : m₁.waiters = m.waiters)
    (hrel : ∀ l₀, m.atomics = #[l₀] → VClock.le (l₀.msgs.back!).relClock (l.msgs.back!).relClock = true) :
    Inv G m₁ where
  thr := by unfold ThrOk; rw [ht, hc]; exact hi.thr
  blk := by unfold BlkOk; rw [hb]; exact hi.blk
  cnt := by unfold U32At; rw [curBytes_congr hb]; exact hi.cnt
  word := by
    obtain ⟨w, hw, hu, hh⟩ := hi.word
    exact ⟨w, hw, by unfold U32At; rw [curBytes_congr hb]; exact hu, hh⟩
  one := hi.one
  loc := .inr ⟨l, hl⟩
  fq := by unfold FqOk U32At; rw [hw, curBytes_congr hb]; exact hi.fq
  fp := by
    intro e he
    rw [hf] at he
    obtain ⟨hb0, h⟩ := hi.fp e he
    refine ⟨hb0, ?_⟩
    rcases h with ⟨hk, hle⟩ | h | h | ⟨ho, hlen, hle₁, hle₂⟩
    · exact .inl ⟨hk, by rw [ht, hc]; exact hle⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · refine .inr (.inr (.inr ⟨ho, hlen, fun u hu => by rw [hc]; exact hle₁ u hu, fun hn => ?_⟩))
      obtain ⟨l₀, hl₀, hle⟩ := hle₂ hn
      exact ⟨l, hl.1, VClock.le_trans hle (hrel l₀ hl₀)⟩
  own := by rw [hf, ht, hc]; exact hi.own

/-- `locIdx` of the mutex: location 0; the memory is the same but for the location. -/
theorem Inv.locIdx {G : ThreadId → Gh} {m m₁ : Mem} {li : Nat} (hi : Inv G m)
    (h : ((locIdx 0 16 4).run m).run = some (.ok (li, m₁))) :
    li = 0 ∧ Inv G m₁ ∧ (∃ l, MLoc m₁ l) ∧ m₁.blocks = m.blocks ∧ m₁.clocks = m.clocks ∧
      m₁.threads = m.threads ∧ m₁.footprint = m.footprint ∧ m₁.waiters = m.waiters ∧
      m₁.current = m.current := by
  rcases hi.loc with ⟨ha, h0⟩ | ⟨l, ha, hb, ho, hl, hsz, hc, hv, hlast⟩
  · have hn : m.atomics.findIdx? (fun l => l.block == 0 && l.off == 16) = none := by
      rw [ha]; simp
    obtain ⟨rfl, hm₁⟩ := locIdx_new hn h
    obtain ⟨nl, hnl, hnb, hno, hnlen, hns, hn0⟩ : ∃ nl : ALoc, m₁.atomics = #[nl] ∧
        nl.block = 0 ∧ nl.off = 16 ∧ nl.len = 4 ∧ nl.msgs.size = 1 ∧
        ∀ h : 0 < nl.msgs.size, nl.msgs[0].bytes = curBytes m 0 16 4 := by
      subst hm₁; rw [ha]; exact ⟨_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    have hbl : m₁.blocks = m.blocks := by rw [hm₁]
    have hml : MLoc m₁ nl := by
      refine ⟨hnl, hnb, hno, hnlen, by omega, fun j hj => by omega, fun j hj => ?_, ?_⟩
      · obtain rfl : j = 0 := by omega
        exact ⟨0, by decide, by rw [hn0]; exact h0⟩
      · unfold ALoc.lastBytes
        rw [Array.back?_eq_getElem?, hns, Array.getElem?_eq_getElem (by omega),
          curBytes_congr hbl]
        simp [hn0]
    refine ⟨by rw [ha]; rfl, hi.atomics hml hbl (by rw [hm₁]) (by rw [hm₁]) (by rw [hm₁]) (by rw [hm₁])
      (fun l₀ h => by rw [ha] at h; cases h), ⟨_, hml⟩, hbl, by rw [hm₁], by rw [hm₁],
      by rw [hm₁], by rw [hm₁], by rw [hm₁]⟩
  · have hf : m.atomics.findIdx? (fun l => l.block == 0 && l.off == 16) = some 0 := by
      rw [ha]; simp [hb, ho]
    have hl0 : m.atomics[0]! = l := by rw [ha]; rfl
    obtain ⟨rfl, rfl⟩ := locIdx_found hf (by rw [hl0]; exact hl) (by rw [hl0]; exact hlast) h
    exact ⟨rfl, hi, ⟨l, ha, hb, ho, hl, hsz, hc, hv, hlast⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## A write to the mutex (an RMW) -/

theorem bs4 (v : BitVec 32) : (padTo (intSize 32) (intBytes v)).size = 4 :=
  LawfulEnc.size_encode (α := BitVec 32) v

/-- The memory after an RMW at the mutex that read the newest message `rd`. -/
theorem rmw_eff {m₁ M m₂ : Mem} {l : ALoc} {ord : AtomicOrder} {new : BitVec 32} {rd : Msg}
    (hl : MLoc m₁ l) (hb : BlkOk m₁) (hrd : rd = l.msgs[l.msgs.size - 1]!)
    (hm₂ : m₂ = if ord.isAcq then acqM m₁ rd.relClock else m₁)
    (hM : M = rmwM m₁ 0 (l.msgs.size - 1) ord rd new) :
    M.threads = m₁.threads ∧ M.footprint = m₁.footprint ∧ M.waiters = m₁.waiters ∧
      M.current = m₁.current ∧ M.clocks = m₂.clocks ∧ BlkOk M ∧
      curBytes M 0 20 4 = curBytes m₁ 0 20 4 ∧
      curBytes M 0 16 4 = padTo (intSize 32) (intBytes new) ∧ U32At M 16 new ∧
      M.atomics = #[{ l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) }] := by
  obtain ⟨hat, hlb, hlo, -, hsz, -⟩ := hl
  obtain ⟨blk, hblk, hlive, hbs, hk, hadr⟩ := hb
  have h2 : m₂.atomics = m₁.atomics ∧ m₂.blocks = m₁.blocks ∧ m₂.threads = m₁.threads ∧
      m₂.footprint = m₁.footprint ∧ m₂.waiters = m₁.waiters ∧ m₂.current = m₁.current := by
    subst hm₂; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨ha₂, hb₂, ht₂, hf₂, hw₂, hc₂⟩ := h2
  have hl₂ : m₂.atomics[0]! = l := by rw [ha₂, hat]; rfl
  have hblk₂ : m₂.blocks[(m₂.atomics[0]!).block]? = some blk := by rw [hl₂, hlb, hb₂]; exact hblk
  have hins := insertM_last (msg := rmwMsg m₂ ord rd new) hblk₂
  rw [hl₂] at hins
  have hp : l.msgs.size - 1 + 1 = l.msgs.size := by omega
  subst hM
  unfold rmwM
  rw [← hm₂, hp]
  dsimp only
  rw [hins]
  have hsz4 := bs4 new
  have hw : 16 + (rmwMsg m₂ ord rd new).bytes.size ≤ blk.bytes.size := by
    simp only [rmwMsg]; rw [hsz4, hbs]; omega
  have h16 : curBytes (observeM { m₂ with
      blocks := m₂.blocks.set! l.block { blk with bytes := writeBytes blk.bytes l.off (rmwMsg m₂ ord rd new).bytes },
      atomics := m₂.atomics.set! 0 { l with msgs := l.msgs.push (rmwMsg m₂ ord rd new) },
      nextMsg := m₂.nextMsg + 1 } 0 m₂.nextMsg) 0 16 4 = padTo (intSize 32) (intBytes new) := by
    unfold curBytes
    simp only [observeM, hlb, hlo]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (by rw [hb₂]; exact (Array.getElem?_eq_some_iff.mp hblk).1)]
    simp only [Option.map_some, Option.getD_some]
    have := extract_writeBytes blk.bytes 16 (rmwMsg m₂ ord rd new).bytes hw
    simp only [rmwMsg] at this ⊢
    rw [hsz4] at this
    exact this
  refine ⟨ht₂, hf₂, hw₂, hc₂, rfl, ?_, ?_, h16, ?_, ?_⟩
  · refine ⟨{ blk with bytes := writeBytes blk.bytes 16 (rmwMsg m₂ ord rd new).bytes }, ?_, hlive,
      ?_, hk, hadr⟩
    · simp only [observeM, hlb]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (by rw [hb₂]; exact (Array.getElem?_eq_some_iff.mp hblk).1), hlo]
    · show (writeBytes blk.bytes 16 _).size = 24
      rw [writeBytes_size _ _ _ hw, hbs]
  · unfold curBytes
    simp only [observeM, hlb, hlo]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
      (by rw [hb₂]; exact (Array.getElem?_eq_some_iff.mp hblk).1)]
    simp only [Option.map_some, Option.getD_some, hblk]
    exact extract_writeBytes_disjoint _ _ _ _ _ hw (by rw [hbs]; decide)
      (.inl (by simp only [rmwMsg]; rw [hsz4]; decide))
  · unfold U32At; rw [h16]; exact intOfBytes_rmw new
  · simp only [observeM, hat, ha₂]
    rfl

/-- The memory `M` after a write to the mutex: the invariant, from the facts of the write. -/
theorem Inv.mutexWrite {G G' : ThreadId → Gh} {m₁ M : Mem} {l' : ALoc} {w' : Nat} (hi : Inv G m₁)
    (ht : M.threads = m₁.threads) (hf : M.footprint = m₁.footprint)
    (hcs : M.clocks.size = m₁.clocks.size)
    (hcl : ∀ u : Nat, VClock.le (m₁.clocks[u]!) (M.clocks[u]!) = true) (hbk : BlkOk M)
    (h20 : curBytes M 0 20 4 = curBytes m₁ 0 20 4) (hloc : MLoc M l') (hthr : ThrOk G' M)
    (hcnt : (G' 0).count + (G' 1).count = (G 0).count + (G 1).count)
    (hw : w' < 3) (hw16 : U32At M 16 (BitVec.ofNat 32 w')) (hz : w' = 0 ↔ ∀ u, ¬ Hold G' u)
    (hone : ∀ u v, Hold G' u → Hold G' v → u = v) (hfq : FqOk G' M)
    (hlk : ∀ c, LockLe G m₁ c → LockLe G' M c) : Inv G' M where
  thr := hthr
  blk := hbk
  cnt := by unfold U32At; rw [h20, hcnt]; exact hi.cnt
  word := ⟨w', hw, hw16, hz⟩
  one := hone
  loc := .inr ⟨l', hloc⟩
  fq := hfq
  fp := by
    intro e he
    rw [hf] at he
    obtain ⟨hb, h⟩ := hi.fp e he
    refine ⟨hb, ?_⟩
    rcases h with ⟨hk, hle⟩ | h | h | ⟨ho, hl, hle⟩
    · exact .inl ⟨hk, fun u hu => VClock.le_trans (hle u (ht ▸ hu)) (hcl u)⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨ho, hl, hlk _ hle⟩))
  own := by
    intro e he
    rw [hf] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨ht ▸ h1, VClock.le_trans h2 (hcl _)⟩

/-! ## The mutex's values -/

/-- The mutex state of the word `w`. -/
def stOf : Nat → Io_Mutex_State
  | 0 => .unlocked
  | 1 => .locked_once
  | _ => .contended

theorem ofBits_st {w : Nat} (hw : w < 3) :
    (Packed.ofBits? (α := Io_Mutex_State) (BitVec.ofNat 32 w)).run = some (.ok (stOf w)) := by
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2) with rfl | rfl | rfl <;> rfl

theorem bits_unlocked : Packed.toBits Io_Mutex_State.unlocked = BitVec.ofNat 32 0 := rfl
theorem bits_locked : Packed.toBits Io_Mutex_State.locked_once = BitVec.ofNat 32 1 := rfl
theorem bits_contended : Packed.toBits Io_Mutex_State.contended = BitVec.ofNat 32 2 := rfl

theorem ofNat_inj {a b : Nat} (ha : a < 3) (hb : b < 3) (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- The newest message of the mutex holds the word. -/
theorem last_u32 {m : Mem} {l : ALoc} {v : BitVec 32} (hl : MLoc m l)
    (h : (intOfBytes 32 (l.msgs[l.msgs.size - 1]!).bytes).run = some (.ok v)) : U32At m 16 v := by
  obtain ⟨-, -, -, -, hsz, -, -, hlast⟩ := hl
  unfold U32At; rw [← hlast]
  unfold ALoc.lastBytes
  rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  rw [getElem!_pos l.msgs _ (by omega)] at h
  simpa using h

/-- Each message of the mutex holds `0`, `1` or `2`. -/
theorem msg_val {m : Mem} {l : ALoc} {j : Nat} {v : BitVec 32} (hl : MLoc m l) (hj : j < l.msgs.size)
    (h : (intOfBytes 32 (l.msgs[j]!).bytes).run = some (.ok v)) : ∃ w < 3, v = BitVec.ofNat 32 w := by
  obtain ⟨w, hw, hv⟩ := hl.2.2.2.2.2.2.1 j hj
  rw [getElem!_pos l.msgs _ hj, hv] at h
  cases h
  exact ⟨w, hw, rfl⟩

/-- The mutex's access: block 0 at 16. -/
theorem accW_mutex {G : ThreadId → Gh} {m : Mem} {b : BlockId} {blk : Block} {o : Nat}
    (hi : Inv G m) (h : m.accessW mPtr 4 4 = pure (b, blk, o)) : b = 0 ∧ o = 16 := by
  obtain ⟨blk₀, -, -, he⟩ := acc0 (o := 16) (n := 4) (a := 4) hi.blk (by decide) (.inl rfl) rfl
  have ha := (accessW_pure h).1
  have : m.access mPtr 4 4 = m.access ⟨some 0, ((16 : Nat) : Int)⟩ 4 4 := rfl
  rw [this, he] at ha
  cases ha
  exact ⟨rfl, rfl⟩

/-- The mutex after one more RMW message `msg`, of the newest one. -/
theorem mloc_push {m M : Mem} {l : ALoc} {msg : Msg} (hl : MLoc m l)
    (hat : M.atomics = #[{ l with msgs := l.msgs.push msg }])
    (hr : msg.rmwOf = some (l.msgs[l.msgs.size - 1]!).id)
    (hv : ∃ w < 3, (intOfBytes 32 msg.bytes).run = some (.ok (BitVec.ofNat 32 w)))
    (hby : curBytes M 0 16 4 = msg.bytes) : MLoc M { l with msgs := l.msgs.push msg } := by
  obtain ⟨-, hb, ho, hlen, hsz, hc, hval, -⟩ := hl
  refine ⟨hat, hb, ho, hlen, by simp, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · simp only [Array.size_push] at hj
    simp only [Array.getElem_push]
    split
    · split
      · exact hc j (by assumption)
      · omega
    · have : j = l.msgs.size - 1 := by omega
      subst this
      simp only [show l.msgs.size - 1 < l.msgs.size by omega, dite_true]
      rw [hr, getElem!_pos l.msgs _ (by omega)]
  · simp only [Array.getElem_push]
    split
    · exact hval j (by assumption)
    · exact hv
  · unfold ALoc.lastBytes
    simp [hby]

theorem thrOk_upd {G : ThreadId → Gh} {m : Mem} {t k k' : Nat} {ph ph' : Ph} (h : ThrOk G m)
    (hg : G t = .work k ph) (hk : k' ≤ 2) : ThrOk (upd G t (.work k' ph')) m := by
  obtain ⟨hs, htl, -⟩ := thr_work h hg
  obtain ⟨h0, hc, hh⟩ := h
  refine ⟨h0, hc, ?_⟩
  rcases hh with ⟨h1, -, -⟩ | ⟨-, hr, g0, g1, g2⟩
  · omega
  refine .inr ⟨hs, hr, ?_, ?_, fun u hu => ?_⟩
  · by_cases ht : t = 0
    · subst ht; rw [upd_self]; exact .inr ⟨k', ph', hk, rfl⟩
    · rw [upd_ne _ _ (Ne.symm ht)]; exact g0
  · by_cases ht : t = 1
    · subst ht; rw [upd_self]; exact .inr ⟨k', ph', hk, rfl⟩
    · rw [upd_ne _ _ (Ne.symm ht)]; exact g1
  · rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; exact g2 u hu

theorem thrOk_congr {G : ThreadId → Gh} {m m' : Mem} (h : ThrOk G m) (ht : m'.threads = m.threads)
    (hc : m'.clocks.size = m.clocks.size) : ThrOk G m' := by
  unfold ThrOk; rw [ht, hc]; exact h

theorem loadM_current (m : Mem) (li : Nat) (ord : AtomicOrder) (msg : Msg) :
    (loadM m li ord msg).current = m.current := by
  unfold loadM; split <;> rfl

theorem acqM_clock (m : Mem) (c : VClock) (h : m.current < m.clocks.size) :
    (acqM m c).clocks[m.current]! = VClock.merge (m.clocks[m.current]!) c := by
  simp only [acqM]; rw [getElem!_set!]; simp [h]

/-- If no thread held the mutex, only `t` holds it after `t` takes it. -/
theorem hold_take {G : ThreadId → Gh} {t k x : Nat} (hn : ∀ u, ¬ Hold G u)
    (h : Hold (upd G t (.work k .holds)) x) : x = t := by
  obtain ⟨k', hx⟩ := h
  by_cases hxt : x = t
  · exact hxt
  · rw [upd_ne _ _ hxt] at hx; exact absurd ⟨k', hx⟩ (hn x)

/-- The futex queue after thread `t` takes the free mutex: a waiter waits for a waker, which is
not `t`. -/
theorem fq_take {G : ThreadId → Gh} {m M : Mem} {t k : Nat} (hi : Inv G m) (hg : G t = .work k .out)
    (hn : ∀ u, ¬ Hold G u) (hw : M.waiters = m.waiters) :
    FqOk (upd G t (.work k .holds)) M := by
  refine ⟨hw ▸ hi.fq.1, fun w hwm => ?_⟩
  rw [hw] at hwm
  obtain ⟨h1, ⟨k₁, hk₁⟩, v, hv, h3⟩ := hi.fq.2 w hwm
  have hwt : w.1 ≠ t := fun e => by rw [e, hg] at hk₁; cases hk₁
  rcases h3 with ⟨hh, -⟩ | ⟨k₂, hk₂⟩
  · exact absurd hh (hn v)
  have hvt : v ≠ t := fun e => by rw [e, hg] at hk₂; cases hk₂
  exact ⟨h1, ⟨k₁, by rw [upd_ne _ _ hwt]; exact hk₁⟩, v, hv,
    .inr ⟨k₂, by rw [upd_ne _ _ hvt]; exact hk₂⟩⟩

/-- Thread `t` takes the free mutex (the word is `0`) with an acquire RMW that writes `w'` (`1`
or `2`): it holds the mutex, and its clock is above the release clock of the newest message. -/
theorem take_inv {G : ThreadId → Gh} {m₁ M : Mem} {l : ALoc} {t k w' : Nat}
    (hi₁ : Inv G m₁) (hml : MLoc m₁ l) (hg : G t = .work k .out) (hcu : m₁.current = t)
    (h0 : U32At m₁ 16 0) (hw' : w' = 1 ∨ w' = 2)
    (hM : M = rmwM m₁ 0 (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 w')) :
    M.current = t ∧ Inv (upd G t (.work k .holds)) M := by
  obtain ⟨hs2, ht2, hk2⟩ := thr_work hi₁.thr hg
  have hn := noHold_of_zero hi₁ h0
  obtain ⟨ht₃, hf₃, hw₃, hc₃, hcl₃, hbk₃, h20₃, h16₃, -, hat₃⟩ :=
    rmw_eff (new := BitVec.ofNat 32 w') hml hi₁.blk rfl rfl hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  simp only [hacq, ite_true] at hcl₃ hat₃
  have hcs₁ : m₁.current < m₁.clocks.size := by
    rw [hi₁.thr.2.1, hcu, hs2]; exact ht2
  have hw3 : w' < 3 := by omega
  refine ⟨hc₃.trans hcu, ?_⟩
  refine hi₁.mutexWrite (l' := _) (w' := w') ht₃ hf₃ (by rw [hcl₃]; simp [acqM])
    (fun u => by rw [hcl₃]; exact (grows_acq m₁ _).cle u) hbk₃ h20₃
    (mloc_push hml hat₃ rfl ⟨w', hw3, intOfBytes_rmw _⟩ h16₃)
    (thrOk_congr (thrOk_upd hi₁.thr hg hk2) ht₃ (by rw [hcl₃]; simp [acqM]))
    (count_upd (by rw [hg]; rfl)) hw3 (by unfold U32At; rw [h16₃]; exact intOfBytes_rmw _) ?_ ?_
    (fq_take hi₁ hg hn hw₃) ?_
  · constructor
    · intro h; omega
    · intro h; exact absurd ⟨k, upd_self _ _ _⟩ (h t)
  · intro u v hu hv
    rw [hold_take hn hu, hold_take hn hv]
  · rintro cl ⟨-, hle⟩
    obtain ⟨l₀, hl₀, hcl⟩ := hle hn
    rw [hml.1] at hl₀; cases hl₀
    refine ⟨fun u hu => ?_, fun hn' => absurd ⟨k, upd_self _ _ _⟩ (hn' t)⟩
    obtain rfl := hold_take hn hu
    rw [hcl₃, ← hcu, acqM_clock _ _ hcs₁]
    refine VClock.le_trans hcl (VClock.le_trans ?_ (VClock.le_merge_right _ _))
    rw [Array.back!, getElem!_pos l.msgs _ (by have := hml.2.2.2.2.1; omega)]
    exact VClock.le_refl _

/-- `lock`'s first op, `cmpxchg(unlocked → locked_once)`. On success thread `t` holds the mutex:
the word was 0, so no thread held it, and the acquire adopts the release clock of the newest
message. On failure the value read is `1` or `2`, and only `t`'s clock changes. -/
theorem step_cas {G : ThreadId → Gh} {m m' : Mem} {t k c : Nat} {r : Option Io_Mutex_State}
    (hi : Inv G m) (hg : G t = .work k .out) (hc : m.current = t)
    (h : ((cmpxchgAs c .acquire .relaxed 4 mPtr Io_Mutex_State.unlocked
      Io_Mutex_State.locked_once).run m).run = some (.ok (r, m'))) :
    m'.current = t ∧ ((r = none ∧ Inv (upd G t (.work k .holds)) m') ∨
      ((r = some .locked_once ∨ r = some .contended) ∧ Inv G m')) := by
  obtain ⟨hs2, ht2, hk2⟩ := thr_work hi.thr hg
  have htl : m.current < m.threads.size := by rw [hc, hs2]; exact ht2
  have core : ∀ o, ((cmpxchgAt c .acquire .relaxed 4 mPtr (Packed.toBits Io_Mutex_State.unlocked)
      (Packed.toBits Io_Mutex_State.locked_once)).run m).run = some (.ok (o, m')) →
      m'.current = t ∧ ((o = none ∧ Inv (upd G t (.work k .holds)) m') ∨
        (∃ w < 3, w ≠ 0 ∧ o = some (BitVec.ofNat 32 w) ∧ Inv G m')) := by
    intro o ho
    obtain ⟨b, blk, off, li, m₁, pos, old, hacc, -, hl, hpos, hold, hcase⟩ := cmpxchgAt_ok ho
    obtain ⟨rfl, rfl⟩ := accW_mutex hi hacc
    have hir := hi.record (b := 0) (o := 16) (len := 4) (k := .atomicWrite) htl
      ⟨rfl, .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))⟩
    obtain ⟨rfl, hi₁, ⟨l, hml⟩, -, -, ht₁, -, -, hcu₁⟩ := hir.locIdx hl
    have hl0 : m₁.atomics[0]! = l := by rw [hml.1]; rfl
    have hcu : m₁.current = t := by rw [hcu₁]; exact hc
    rcases hcase with ⟨rfl, rfl, hm'⟩ | ⟨hne, rfl, hm'⟩
    · -- success: the newest message holds 0
      have hpl := cas_chain_pos (by rw [hl0]; exact hml.2.2.2.2.2.1) hpos hold
      rw [hl0] at hpl hold hm'
      rw [hpl] at hold hm'
      have h0 := last_u32 hml hold
      exact ⟨(take_inv hi₁ hml hg hcu h0 (.inl rfl) hm').1, .inl ⟨rfl, (take_inv hi₁ hml hg hcu h0 (.inl rfl) hm').2⟩⟩
    · -- failure: a read with the order `relaxed`
      obtain ⟨w, hw, rfl⟩ := msg_val hml (by have := (casOpts_pos hpos).1; rwa [hl0] at this)
        (by rwa [hl0] at hold)
      have hw0 : w ≠ 0 := fun e => hne (by rw [e]; rfl)
      refine ⟨by rw [hm', loadM_current]; exact hcu, .inr ⟨w, hw, hw0, rfl, ?_⟩⟩
      rw [hm']
      exact hi₁.grow (grows_loadM _ _ _ _)
  rcases cmpxchgAs_ok h with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hcu, h1 | ⟨w, -, -, he, -⟩⟩ := core none ho
    · exact ⟨hcu, .inl ⟨rfl, h1.2⟩⟩
    · cases he
  · obtain ⟨hcu, ⟨he, -⟩ | ⟨w, hw, hw0, he, hi'⟩⟩ := core (some b) ho
    · cases he
    · cases he
      rw [ofBits_st hw] at hd
      cases hd
      refine ⟨hcu, .inr ⟨?_, hi'⟩⟩
      rcases (by omega : w = 1 ∨ w = 2) with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl

/-- The word is not 0: a thread holds the mutex. -/
theorem hold_of_word {G : ThreadId → Gh} {m : Mem} {w : Nat} (hi : Inv G m) (hwu : U32At m 16 (BitVec.ofNat 32 w))
    (hw : w < 3) (hw0 : w ≠ 0) : ∃ u, Hold G u := by
  obtain ⟨w₀, hw₀, hu₀, hz⟩ := hi.word
  have e := ofNat_inj hw₀ hw (u32_eq hu₀ hwu)
  subst e
  by_cases hx : ∃ u, Hold G u
  · exact hx
  · exact absurd (hz.mpr fun u hu => hx ⟨u, hu⟩) hw0

/-- Thread `t` writes `2` to the held mutex (`lock`'s loop, an acquire RMW): the holder stays. -/
theorem contend_inv {G : ThreadId → Gh} {m₁ M : Mem} {l : ALoc} {t k w : Nat}
    (hi₁ : Inv G m₁) (hml : MLoc m₁ l) (hg : G t = .work k .out) (hcu : m₁.current = t)
    (hwu : U32At m₁ 16 (BitVec.ofNat 32 w)) (hw : w < 3) (hw0 : w ≠ 0)
    (hM : M = rmwM m₁ 0 (l.msgs.size - 1) .acquire (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 2)) :
    M.current = t ∧ Inv G M := by
  obtain ⟨hs2, ht2, hk2⟩ := thr_work hi₁.thr hg
  obtain ⟨u0, hh⟩ := hold_of_word hi₁ hwu hw hw0
  obtain ⟨ht₃, hf₃, hw₃, hc₃, hcl₃, hbk₃, h20₃, h16₃, hu₃, hat₃⟩ :=
    rmw_eff (new := BitVec.ofNat 32 2) hml hi₁.blk rfl rfl hM
  have hacq : AtomicOrder.acquire.isAcq = true := rfl
  simp only [hacq, ite_true] at hcl₃ hat₃
  refine ⟨hc₃.trans hcu, ?_⟩
  refine hi₁.mutexWrite (l' := _) (w' := 2) ht₃ hf₃ (by rw [hcl₃]; simp [acqM])
    (fun u => by rw [hcl₃]; exact (grows_acq m₁ _).cle u) hbk₃ h20₃
    (mloc_push hml hat₃ rfl ⟨2, by decide, intOfBytes_rmw _⟩ h16₃)
    (thrOk_congr hi₁.thr ht₃ (by rw [hcl₃]; simp [acqM])) rfl (by decide) hu₃ ?_ hi₁.one ?_ ?_
  · exact ⟨fun e => absurd e (by decide), fun hn => absurd hh (hn u0)⟩
  · refine ⟨hw₃ ▸ hi₁.fq.1, fun x hx => ?_⟩
    rw [hw₃] at hx
    obtain ⟨h1, h2, v, hv, h3⟩ := hi₁.fq.2 x hx
    refine ⟨h1, h2, v, hv, ?_⟩
    rcases h3 with ⟨hv', -⟩ | h3
    · exact .inl ⟨hv', hu₃⟩
    · exact .inr h3
  · rintro cl ⟨h1, -⟩
    refine ⟨fun u hu => VClock.le_trans (h1 u hu) ?_, fun hn => absurd hh (hn u0)⟩
    rw [hcl₃]; exact (grows_acq m₁ _).cle u

/-- `lock`'s loop, `xchg(contended)` with an acquire: if the word was `0`, thread `t` holds the
mutex; else the holder stays, and the word is `2`. -/
theorem step_xlock {G : ThreadId → Gh} {m m' : Mem} {t k c : Nat} {r : Io_Mutex_State}
    (hi : Inv G m) (hg : G t = .work k .out) (hc : m.current = t)
    (h : ((atomicRmwAs c .xchg .acquire 4 mPtr Io_Mutex_State.contended).run m).run =
      some (.ok (r, m'))) :
    m'.current = t ∧ ((r = .unlocked ∧ Inv (upd G t (.work k .holds)) m') ∨
      (r ≠ .unlocked ∧ Inv G m')) := by
  obtain ⟨hs2, ht2, hk2⟩ := thr_work hi.thr hg
  have htl : m.current < m.threads.size := by rw [hc, hs2]; exact ht2
  obtain ⟨b, hb, hd⟩ := atomicRmwAs_ok h
  obtain ⟨b0, blk, off, li, m₁, pos, hacc, -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok hb
  obtain ⟨rfl, rfl⟩ := accW_mutex hi hacc
  have hir := hi.record (b := 0) (o := 16) (len := 4) (k := .atomicWrite) htl
    ⟨rfl, .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))⟩
  obtain ⟨rfl, hi₁, ⟨l, hml⟩, -, -, -, -, -, hcu₁⟩ := hir.locIdx hl
  have hl0 : m₁.atomics[0]! = l := by rw [hml.1]; rfl
  have hcu : m₁.current = t := by rw [hcu₁]; exact hc
  have hpl := rmw_chain_pos (by rw [hl0]; exact hml.2.2.2.2.1) (by rw [hl0]; exact hml.2.2.2.2.2.1) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨w, hw, rfl⟩ := msg_val hml (by have := hml.2.2.2.2.1; omega) hold
  have hwu := last_u32 hml hold
  have happ : RmwOp.xchg.apply false (BitVec.ofNat 32 w) (Packed.toBits Io_Mutex_State.contended) =
      BitVec.ofNat 32 2 := rfl
  rw [happ] at hm'
  rw [ofBits_st hw] at hd
  cases hd
  by_cases hw0 : w = 0
  · subst hw0
    obtain ⟨hcM, hiM⟩ := take_inv hi₁ hml hg hcu hwu (.inr rfl) hm'
    exact ⟨hcM, .inl ⟨rfl, hiM⟩⟩
  · obtain ⟨hcM, hiM⟩ := contend_inv hi₁ hml hg hcu hwu hw hw0 hm'
    refine ⟨hcM, .inr ⟨?_, hiM⟩⟩
    rcases (by omega : w = 1 ∨ w = 2) with rfl | rfl <;> decide

/-- Thread `t` holds the mutex: the word is `1` or `2`. -/
theorem word_of_hold {G : ThreadId → Gh} {m : Mem} {t w : Nat} (hi : Inv G m) (hh : Hold G t)
    (hwu : U32At m 16 (BitVec.ofNat 32 w)) (hw : w < 3) : w ≠ 0 := by
  obtain ⟨w₀, hw₀, hu₀, hz⟩ := hi.word
  have e := ofNat_inj hw₀ hw (u32_eq hu₀ hwu)
  subst e
  exact fun h0 => hz.mp h0 t hh

/-- The holder `t` writes `0` (`unlock`, a release RMW) where the word was `w`: no thread holds
the mutex; if `w = 2`, `t` is at the wake of its unlock, else no thread waits. The release clock
of the new message is above `t`'s clock. -/
theorem release_inv {G : ThreadId → Gh} {m₁ M : Mem} {l : ALoc} {t k w : Nat} {ph : Ph}
    (hi₁ : Inv G m₁) (hml : MLoc m₁ l) (hg : G t = .work k .holds) (hcu : m₁.current = t)
    (hwu : U32At m₁ 16 (BitVec.ofNat 32 w)) (hw : w < 3)
    (hph : (w = 1 ∧ ph = .out) ∨ (w = 2 ∧ ph = .wake))
    (hM : M = rmwM m₁ 0 (l.msgs.size - 1) .release (l.msgs[l.msgs.size - 1]!)
      (BitVec.ofNat 32 0)) :
    M.current = t ∧ Inv (upd G t (.work k ph)) M := by
  obtain ⟨hs2, ht2, hk2⟩ := thr_work hi₁.thr hg
  have hht : Hold G t := ⟨k, hg⟩
  have honly : ∀ u, Hold G u → u = t := fun u hu => hi₁.one u t hu hht
  have hph' : ph ≠ .holds := by rcases hph with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hn : ∀ u, ¬ Hold (upd G t (.work k ph)) u := by
    rintro u ⟨k', hu⟩
    by_cases hut : u = t
    · subst hut; rw [upd_self] at hu; cases hu; exact hph' rfl
    · rw [upd_ne _ _ hut] at hu; exact hut (honly u ⟨k', hu⟩)
  obtain ⟨ht₃, hf₃, hw₃, hc₃, hcl₃, hbk₃, h20₃, h16₃, hu₃, hat₃⟩ :=
    rmw_eff (new := BitVec.ofNat 32 0) hml hi₁.blk rfl rfl hM
  have hacq : AtomicOrder.release.isAcq = false := rfl
  have hrel : AtomicOrder.release.isRel = true := rfl
  simp only [hacq, Bool.false_eq_true, ite_false] at hcl₃ hat₃
  refine ⟨hc₃.trans hcu, ?_⟩
  refine hi₁.mutexWrite (l' := _) (w' := 0) ht₃ hf₃ (by rw [hcl₃])
    (fun u => by rw [hcl₃]; exact VClock.le_refl _) hbk₃ h20₃
    (mloc_push hml hat₃ rfl ⟨0, by decide, intOfBytes_rmw _⟩ h16₃)
    (thrOk_congr (thrOk_upd hi₁.thr hg hk2) ht₃ (by rw [hcl₃]))
    (count_upd (by rw [hg]; rfl)) (by decide) hu₃ ⟨fun _ => hn, fun _ => rfl⟩
    (fun u _ hu => absurd hu (hn u)) ?_ ?_
  · refine ⟨hw₃ ▸ hi₁.fq.1, fun x hx => ?_⟩
    rw [hw₃] at hx
    obtain ⟨h1, ⟨k₁, hk₁⟩, v, hv, h3⟩ := hi₁.fq.2 x hx
    have hxt : x.1 ≠ t := fun e => by rw [e, hg] at hk₁; cases hk₁
    have hx2 := (thr_work hi₁.thr hk₁).2.1
    refine ⟨h1, ⟨k₁, by rw [upd_ne _ _ hxt]; exact hk₁⟩, t, Ne.symm hxt, ?_⟩
    rcases h3 with ⟨hv', h2⟩ | ⟨k₂, hk₂⟩
    · have e := ofNat_inj hw (by decide) (u32_eq hwu h2)
      subst e
      rcases hph with ⟨h, -⟩ | ⟨-, rfl⟩
      · cases h
      · exact .inr ⟨k, upd_self _ _ _⟩
    · have hvt : v ≠ t := fun e => by rw [e, hg] at hk₂; cases hk₂
      have hv2 := (thr_work hi₁.thr hk₂).2.1
      exfalso
      unfold ThreadId at *
      omega
  · rintro cl ⟨h1, -⟩
    refine ⟨fun u hu => absurd hu (hn u), fun _ => ⟨_, hat₃, ?_⟩⟩
    rw [Array.back!, getElem!_pos _ _ (by simp)]
    simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq, rmwMsg, hrel, ite_true]
    rw [hcu]
    exact VClock.le_trans (h1 t hht) (VClock.le_merge_right _ _)

/-- `unlock`'s `xchg(unlocked)` with a release, by the holder `t`: the word was `1` (no thread
waits) or `2` (`t` goes to the wake). -/
theorem step_unlock {G : ThreadId → Gh} {m m' : Mem} {t k c : Nat} {r : Io_Mutex_State}
    (hi : Inv G m) (hg : G t = .work k .holds) (hc : m.current = t)
    (h : ((atomicRmwAs c .xchg .release 4 mPtr Io_Mutex_State.unlocked).run m).run =
      some (.ok (r, m'))) :
    m'.current = t ∧ ((r = .locked_once ∧ Inv (upd G t (.work k .out)) m') ∨
      (r = .contended ∧ Inv (upd G t (.work k .wake)) m')) := by
  obtain ⟨hs2, ht2, hk2⟩ := thr_work hi.thr hg
  have htl : m.current < m.threads.size := by rw [hc, hs2]; exact ht2
  obtain ⟨b, hb, hd⟩ := atomicRmwAs_ok h
  obtain ⟨b0, blk, off, li, m₁, pos, hacc, -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok hb
  obtain ⟨rfl, rfl⟩ := accW_mutex hi hacc
  have hir := hi.record (b := 0) (o := 16) (len := 4) (k := .atomicWrite) htl
    ⟨rfl, .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))⟩
  obtain ⟨rfl, hi₁, ⟨l, hml⟩, -, -, -, -, -, hcu₁⟩ := hir.locIdx hl
  have hl0 : m₁.atomics[0]! = l := by rw [hml.1]; rfl
  have hcu : m₁.current = t := by rw [hcu₁]; exact hc
  have hpl := rmw_chain_pos (by rw [hl0]; exact hml.2.2.2.2.1) (by rw [hl0]; exact hml.2.2.2.2.2.1) hpos
  rw [hl0] at hpl hold hm'
  rw [hpl] at hold hm'
  obtain ⟨w, hw, rfl⟩ := msg_val hml (by have := hml.2.2.2.2.1; omega) hold
  have hwu := last_u32 hml hold
  have hw0 := word_of_hold hi₁ ⟨k, hg⟩ hwu hw
  have happ : RmwOp.xchg.apply false (BitVec.ofNat 32 w) (Packed.toBits Io_Mutex_State.unlocked) =
      BitVec.ofNat 32 0 := rfl
  rw [happ] at hm'
  rw [ofBits_st hw] at hd
  cases hd
  rcases (by omega : w = 1 ∨ w = 2) with rfl | rfl
  · obtain ⟨hcM, hiM⟩ := release_inv (ph := .out) hi₁ hml hg hcu hwu hw (.inl ⟨rfl, rfl⟩) hm'
    exact ⟨hcM, .inl ⟨rfl, hiM⟩⟩
  · obtain ⟨hcM, hiM⟩ := release_inv (ph := .wake) hi₁ hml hg hcu hwu hw (.inr ⟨rfl, rfl⟩) hm'
    exact ⟨hcM, .inr ⟨rfl, hiM⟩⟩

/-! ## The futex -/

/-- A thread in the futex queue: the other thread holds the mutex or is at the wake of its
unlock, so it does not wait at a join, has not ended, and is not in the queue. -/
theorem live {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (t : ThreadId) : proto.Live t G m := by
  intro hw hall
  obtain ⟨i, hi', -⟩ := Array.any_eq_true.mp hw
  obtain ⟨-, -, v, -, h3⟩ := hi.fq.2 _ (Array.getElem_mem hi')
  obtain ⟨k₂, ph, hk₂, hph⟩ : ∃ k ph, G v = .work k ph ∧ ph ≠ .wait := by
    rcases h3 with ⟨⟨k₂, hk₂⟩, -⟩ | ⟨k₂, hk₂⟩
    · exact ⟨k₂, _, hk₂, by decide⟩
    · exact ⟨k₂, _, hk₂, by decide⟩
  obtain ⟨hs2, hv2, -⟩ := thr_work hi.thr hk₂
  rcases hall v (by rw [hs2]; exact hv2) with h | h | h
  · change G v = .fin at h; rw [hk₂] at h; cases h
  · obtain ⟨j, hj, hej⟩ := Array.any_eq_true.mp h
    obtain ⟨-, ⟨k₃, hk₃⟩, -⟩ := hi.fq.2 _ (Array.getElem_mem hj)
    have : (m.waiters[j]).1 = v := by simpa using hej
    rw [this, hk₂] at hk₃
    cases hk₃
    exact hph rfl
  · change G v = .joins at h; rw [hk₂] at h; cases h

/-- The invariant with another futex queue. -/
theorem Inv.withQ {G : ThreadId → Gh} {m : Mem} {q : Array (ThreadId × Ptr)} {z : Array ThreadId}
    (hi : Inv G m) (hq : FqOk G { m with waiters := q, woken := z }) :
    Inv G { m with waiters := q, woken := z } :=
  { hi with fq := hq }

/-- The invariant of a memory with the same fields but the futex queue. -/
theorem Inv.frameQ {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (ht : m'.threads = m.threads)
    (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics) (hf : m'.footprint = m.footprint)
    (hc : m'.clocks = m.clocks) (hq : FqOk G m') : Inv G m' where
  thr := by unfold ThrOk; rw [ht, hc]; exact hi.thr
  blk := by unfold BlkOk; rw [hb]; exact hi.blk
  cnt := by unfold U32At; rw [curBytes_congr hb]; exact hi.cnt
  word := by
    obtain ⟨w, hw, hu, hh⟩ := hi.word
    exact ⟨w, hw, by unfold U32At; rw [curBytes_congr hb]; exact hu, hh⟩
  one := hi.one
  loc := by unfold LocOk U32At; rw [ha, curBytes_congr hb]; exact hi.loc
  fq := hq
  fp := by
    intro e he
    rw [hf] at he
    obtain ⟨hb0, h⟩ := hi.fp e he
    refine ⟨hb0, ?_⟩
    rcases h with ⟨hk, hle⟩ | h | h | ⟨ho, hl, hle₁, hle₂⟩
    · exact .inl ⟨hk, by rw [ht, hc]; exact hle⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨ho, hl, fun u hu => by rw [hc]; exact hle₁ u hu,
        fun hn => by rw [ha]; exact hle₂ hn⟩))
  own := by rw [hf, ht, hc]; exact hi.own

/-- The invariant for other ghost values with the same shape, count and holder, and a futex
queue that keeps `FqOk`. -/
theorem Inv.congrF {G G' : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hthr : ThrOk G' m)
    (hcnt : (G' 0).count + (G' 1).count = (G 0).count + (G 1).count)
    (hh : ∀ u, Hold G' u ↔ Hold G u) (hfq : FqOk G' m) : Inv G' m where
  thr := hthr
  blk := hi.blk
  cnt := hcnt ▸ hi.cnt
  word := by
    obtain ⟨w, hw, hu, hz⟩ := hi.word
    refine ⟨w, hw, hu, hz.trans ?_⟩
    constructor
    · intro h u hu; exact h u ((hh u).mp hu)
    · intro h u hu; exact h u ((hh u).mpr hu)
  one u v hu hv := hi.one u v ((hh u).mp hu) ((hh v).mp hv)
  loc := hi.loc
  fq := hfq
  fp := by
    intro e he
    obtain ⟨hb, h⟩ := hi.fp e he
    refine ⟨hb, ?_⟩
    rcases h with h | h | h | ⟨ho, hl, hle⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨ho, hl, lockLe_congr hh hle⟩))
  own := hi.own

/-- Two threads: three different ids of threads in `work` do not exist. -/
theorem two_threads {G : ThreadId → Gh} {m : Mem} {a b c ka kb kc : Nat} {pa pb pc : Ph}
    (h : ThrOk G m) (ha : G a = .work ka pa) (hb : G b = .work kb pb) (hc : G c = .work kc pc)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have := (thr_work h ha).2.1
  have := (thr_work h hb).2.1
  have := (thr_work h hc).2.1
  omega

/-- A thread at its futex wait is not in the queue: then no thread is, since the waker of a
waiter would be the third thread. -/
theorem q_empty {G : ThreadId → Gh} {m : Mem} {t k : Nat} (hi : Inv G m) (hg : G t = .work k .wait)
    (hq : m.waiters.any (·.1 == t) = false) : m.waiters = #[] := by
  apply Array.eq_empty_of_size_eq_zero
  by_cases hne : m.waiters.size = 0
  · exact hne
  exfalso
  have hi0 : 0 < m.waiters.size := Nat.pos_of_ne_zero hne
  obtain ⟨-, ⟨k₁, hk₁⟩, v, hv, h3⟩ := hi.fq.2 _ (Array.getElem_mem hi0)
  have hxt : m.waiters[0].1 ≠ t := by
    intro e
    have : m.waiters.any (·.1 == t) = true := Array.any_eq_true.mpr ⟨0, hi0, by simp [e]⟩
    rw [hq] at this; cases this
  obtain ⟨k₂, ph, hk₂, hph⟩ : ∃ k ph, G v = .work k ph ∧ ph ≠ .wait := by
    rcases h3 with ⟨⟨k₂, hk₂⟩, -⟩ | ⟨k₂, hk₂⟩
    · exact ⟨k₂, _, hk₂, by decide⟩
    · exact ⟨k₂, _, hk₂, by decide⟩
  have hvt : v ≠ t := fun e => by rw [e, hg] at hk₂; cases hk₂; exact hph rfl
  exact two_threads hi.thr hk₁ hk₂ hg (Ne.symm hv) hxt hvt

theorem fq_nil {G : ThreadId → Gh} {m : Mem} (h : m.waiters = #[]) : FqOk G m :=
  ⟨by rw [h]; decide, fun w hw => by rw [h] at hw; simp at hw⟩

/-- Thread `t` changes its place in `work`, and the queue is empty. -/
theorem Inv.retagQ {G : ThreadId → Gh} {m : Mem} {t k k' : Nat} {ph ph' : Ph} (hi : Inv G m)
    (hg : G t = .work k ph) (hk : k' = k) (hh : ph' = .holds ↔ ph = .holds)
    (hq : m.waiters = #[]) : Inv (upd G t (.work k' ph')) m := by
  subst hk
  obtain ⟨-, -, hk2⟩ := thr_work hi.thr hg
  refine hi.congrF (thrOk_upd hi.thr hg hk2) (count_upd (by rw [hg]; rfl)) (hold_upd ?_) (fq_nil hq)
  rw [Hold, hg]
  constructor
  · rintro ⟨_, h⟩; cases h; exact ⟨k', by rw [hh.mp rfl]⟩
  · rintro ⟨_, h⟩; cases h; exact ⟨k', by rw [hh.mpr rfl]⟩

/-- `lock`'s futex wait at the mutex for `2`, by thread `t`, which is not in the queue. If it
sleeps, the word is `2`, so the other thread holds the mutex, and the invariant holds with `t`
in the queue. If it goes on, `t` is out of the queue. -/
theorem wait_step {G : ThreadId → Gh} {m m' : Mem} {t k : Nat} {e : BitVec 32} {b : Bool}
    (hi : Inv G m) (hg : G t = .work k .wait) (hq : m.waiters.any (·.1 == t) = false)
    (he : e = BitVec.ofNat 32 2)
    (h : ((Thread.futexWait mPtr e).run { m with current := t }).run = some (.ok (b, m'))) :
    if b then Inv G m' else (m'.current = t ∧ Inv (upd G t (.work k .out)) m') := by
  have hq0 := q_empty hi hg hq
  rcases futexWait_ok h with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, hv, ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · refine ⟨rfl, ?_⟩
    have hi' : Inv G _ := hi.frameQ (m' := { m with current := t, woken := m.woken.erase t })
      rfl rfl rfl rfl rfl (fq_nil hq0)
    exact hi'.retagQ (ph' := .out) hg rfl (by decide) hq0
  · -- sleeps: the word is `2`
    obtain ⟨blk₀, hblk₀, -, he₀⟩ := acc0 (o := 16) (n := 4) (a := 4) hi.blk (by decide) (.inl rfl) rfl
    have : ({ m with current := t } : Mem).access mPtr 4 4 = m.access ⟨some 0, ((16 : Nat) : Int)⟩ 4 4 := rfl
    rw [this, he₀] at ha
    cases ha
    have h2 : U32At m 16 (BitVec.ofNat 32 2) := by
      unfold U32At curBytes; rw [hblk₀]; exact he ▸ hv
    obtain ⟨u, hu⟩ := hold_of_word hi h2 (by decide) (by decide)
    have hut : u ≠ t := fun e => by obtain ⟨k', hk'⟩ := hu; rw [e, hg] at hk'; cases hk'
    simp only [↓reduceIte]
    refine hi.frameQ rfl rfl rfl rfl rfl ⟨by simp [hq0], fun w hw => ?_⟩
    simp only [hq0, List.push_toArray, List.nil_append, Array.mem_toArray, List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, ⟨k, hg⟩, u, hut, .inl ⟨hu, h2⟩⟩
  · exact ⟨rfl, (hi.grow (grows_current m t)).retag (ph' := .out) hg rfl (by decide) (by decide) (.inr hq)⟩

/-- `unlock`'s futex wake at the mutex, by thread `t` at its wake: the queue had at most the
other thread, and now it is empty. -/
theorem wake_step {G : ThreadId → Gh} {m m' : Mem} {t k n : Nat} (hi : Inv G m)
    (hg : G t = .work k .wake) (hn : 1 ≤ n)
    (h : ((Thread.futexWake mPtr n).run { m with current := t }).run = some (.ok ((), m'))) :
    m'.current = t ∧ Inv (upd G t (.work k .out)) m' := by
  have hm' := modify_ok h
  have hnil : m'.waiters = #[] := by
    rw [hm']
    show m.waiters.filter _ = #[]
    have hsz := hi.fq.1
    rcases (by omega : m.waiters.size = 0 ∨ m.waiters.size = 1) with h0 | h1
    · rw [Array.eq_empty_of_size_eq_zero h0]; rfl
    · obtain ⟨x, hx⟩ : ∃ x, m.waiters = #[x] := by
        have : m.waiters.toList.length = 1 := by simpa using h1
        obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp this
        exact ⟨x, Array.toList_inj.mp (by simp [hx])⟩
      have hx2 : x.2 = mPtr := (hi.fq.2 x (by rw [hx]; simp)).1
      have hex : (#[x].filter (·.2 == mPtr)).extract 0 n = #[x] := by
        apply Array.toList_inj.mp
        simp only [hx2, Array.toList_extract, Array.filter, List.extract]
        simp [hx2]
        exact List.take_of_length_le (by simp; omega)
      rw [hx, hex]
      simp
  have hi' : Inv G m' := hi.frameQ (by rw [hm']) (by rw [hm']) (by rw [hm']) (by rw [hm'])
    (by rw [hm']) (fq_nil hnil)
  exact ⟨by rw [hm'], hi'.retagQ (ph' := .out) hg rfl (by decide) hnil⟩

end Sync.MutexCounter
