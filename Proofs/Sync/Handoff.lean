import ZigLean.Conc.WeakWord
import ZigLean.VersionGate
import Proofs.Sync.Lock
import ZigLean.Conc.Word

/-!
# `handoff` over all schedules

`handoff` spawns a producer. The producer sets `v = 7` and `ready = true` under an `Io.Mutex`,
signals an `Io.Condition` and sets an `Io.Event`. `main` waits on the condition until `ready`,
reads `v`, waits on the event and joins the producer. All three sync objects are translated from
Zig 0.16.0's std code; the futex under them is the model. The result is 7 under every schedule
(`handoff_spec`), and no schedule gives an error (`handoff_safe`): no data race, no deadlock at a
futex, no `unreachable`.

The mutex (bytes 16..20 of the `Box`, block 0) is a lock that owns `v` and `ready` (bytes 32..37,
`R`; `ZigLean/Conc/Lock.lean`). The condition's state and epoch (bytes 20..24, 24..28) and the
event (bytes 28..32) are shared atomic words (`ZigLean/Conc/Word.lean`). This file proves the
rest:

- **Ghost values** (`Gh = LG × X`): the lock's part, the thread's place (`Ph`), and its writes
  to the condition (`cw`) and to the event (`vw`).
- **The writes of the shared words** (`SOk`, `EOk`, `VOk`): they follow from the ghost values.
  The state: `waiters += 1` by `main`, `signals += 1` by the producer, then `main` takes the
  signal. The epoch: `+ 1` by the producer after its signal. The event: `waiting` by `main`,
  `is_set` by the producer.
- **Clocks**: the producer reads the state after `main`'s `waiters += 1`, which happened before
  the mutex's release (`RegHB`); the producer's signal happened before its `epoch += 1` (`pc`,
  `sig`), so a reader of epoch 1 reads the signal (`seen`); `main` reads its own `waiting` or a
  newer write (`vclk`).
- **`ready` in the resource**: while `main` holds the mutex with `ready = false` in its resource,
  the producer is before its store of `ready` (`R_rdy`, `rdy_now`); so `main` registers only
  before the producer's signal (`Flags.late`).
- **The futex queue** (`QOk`): only `main` sleeps at the epoch or the event, and only while the
  producer has not woken it. So a thread that sleeps there is not the last one.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

namespace Sync.Handoff

-- Unification must not unfold `WP` into the program (as in `Proofs/Sync/RwLock.lean`).
attribute [local irreducible] Proto.WP

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` before the condition's first epoch load (or after a `ready` that was set). -/
  | run
  /-- `main` in `Condition.wait`: it loaded epoch 0. -/
  | ep
  /-- `main` did `waiters += 1`. -/
  | reg
  /-- `main` in the condition's loop, with epoch 0: it can sleep at the epoch. -/
  | wt
  /-- `main` loaded epoch 1, after the producer's signal. -/
  | seen
  /-- `main` took the signal. -/
  | cons
  /-- `main` in `Event.wait`, before its `cmpxchg`. -/
  | ev0
  /-- `main` wrote `waiting`: it can sleep at the event. -/
  | ev1
  /-- `main` saw the event set. -/
  | evd
  /-- `main` at its join. -/
  | joins
  /-- The producer before (or in) `lock`. -/
  | lk
  /-- The producer holds the mutex. -/
  | hl
  /-- The producer stored `v = 7`. -/
  | v7
  /-- The producer stored `ready = true` (until its `unlock`, and in `signal` before its load of
  the state). -/
  | rdy
  /-- The producer loaded the state `(1, 0)`: before its `cmpxchg`. -/
  | sg1
  /-- The producer did `signals += 1`. -/
  | sgp
  /-- The producer did `epoch += 1`, before its wake. -/
  | wk
  /-- The producer in `Event.set`, before its `xchg`. -/
  | set
  /-- The producer's `xchg` read `waiting`: before its wake. -/
  | setw
  /-- The producer has ended (or is at its end). -/
  | fin
  deriving DecidableEq

/-- The order of a thread's places. -/
def Ph.rank : Ph → Nat
  | .none | .pre => 0
  | .run | .lk => 1
  | .ep | .hl => 2
  | .reg | .v7 => 3
  | .wt | .rdy => 4
  | .seen => 5
  | .cons | .sg1 => 6
  | .ev0 | .sgp => 7
  | .ev1 | .wk => 8
  | .evd | .set => 9
  | .joins | .setw => 10
  | .fin => 11

/-- `main`'s places. -/
def Ph.isMain : Ph → Bool
  | .pre | .run | .ep | .reg | .wt | .seen | .cons | .ev0 | .ev1 | .evd | .joins => true
  | _ => false

/-- The producer's places. -/
def Ph.isProd : Ph → Bool
  | .lk | .hl | .v7 | .rdy | .sg1 | .sgp | .wk | .set | .setw | .fin => true
  | _ => false

/-- `main` after it took the signal. -/
def Ph.post : Ph → Bool
  | .cons | .ev0 | .ev1 | .evd | .joins => true
  | _ => false

/-- A thread's place and its writes: `cw`, it wrote the condition's state (`main`:
`waiters += 1`; the producer: `signals += 1`); `vw`, it wrote the event (`main`: `waiting`; the
producer: `is_set`). -/
structure X where
  ph : Ph := .none
  cw : Bool := false
  vw : Bool := false
  deriving DecidableEq

abbrev Gh := LG × X

/-- The `Box` (block 0). -/
def bPtr : Ptr := ⟨some 0, 0⟩

/-- `v`, from the producer's place. -/
def vOf (x : X) : Nat := if x.ph.isProd ∧ 3 ≤ x.ph.rank then 7 else 0

/-- `ready`, from the producer's place. -/
def rdyOf (x : X) : Bool := x.ph.isProd && decide (4 ≤ x.ph.rank)

/-- The mutex's resource: `v` and `ready`, from the producer's place. -/
def R (X : ThreadId → X) : Assn :=
  pts (bPtr.add 32) 4 (BitVec.ofNat 32 (vOf (X 1))) ∗ pts (bPtr.add 36) 1 (rdyOf (X 1))

/-- The `Io.Mutex`: bytes 16..20 of the `Box`. It owns `v` and `ready`. -/
abbrev L : Lock Gh := Lock.prod 0 16 R

/-- The condition's state (bytes 20..24), its epoch (24..28), and the event (28..32). -/
def WS : Word 32 4 := { b := 0, o := 20 }
def WE : Word 32 4 := { b := 0, o := 24 }
def WV : Word 32 4 := { b := 0, o := 28 }

/-- The number of writes of the state after the first. -/
def sN (x0 x1 : X) : Nat :=
  (if x0.cw then 1 else 0) + (if x1.cw then 1 else 0) + (if x0.cw && x0.ph.post then 1 else 0)

/-- The state's writes: `(0, 0)`, `(1, 0)`, `(1, 1)`, `(0, 0)` (`waiters` in the low half). -/
def sv : Nat → BitVec 32
  | 1 => 1
  | 2 => 0x10001
  | _ => 0

/-- The state has the writes `0..n`. -/
def SOk (m : Mem) (n : Nat) : Prop :=
  (WS.hist m).size = n + 1 ∧ ∀ k ≤ n, (WS.hist m)[k]!.Val (sv k)

/-- The number of writes of the epoch after the first: 1 after the producer's `epoch += 1`. -/
def eN (x1 : X) : Nat := if x1.cw && decide (8 ≤ x1.ph.rank) then 1 else 0

/-- The epoch has the writes `0..n`. -/
def EOk (m : Mem) (n : Nat) : Prop :=
  (WE.hist m).size = n + 1 ∧ ∀ k ≤ n, (WE.hist m)[k]!.Val (BitVec.ofNat 32 k)

/-- The event's writes: `unset`, then `main`'s `waiting`, then the producer's `is_set`. -/
def vL (x0 x1 : X) : List Nat := [0] ++ (if x0.vw then [1] else []) ++ (if x1.vw then [2] else [])

/-- The event has the writes `vs`. -/
def VOk (m : Mem) (vs : List Nat) : Prop :=
  (WV.hist m).size = vs.length ∧ ∀ k < vs.length, (WV.hist m)[k]!.Val (BitVec.ofNat 32 vs[k]!)

/-- The places and the writes agree. -/
structure Flags (x0 x1 : X) : Prop where
  /-- The producer signals only after `main`'s `waiters += 1`. -/
  sig : x1.cw → x0.cw
  /-- `main` wrote the state in `reg`, `wt`, `seen` and after it took the signal. -/
  mcw : x0.cw ↔ (x0.ph = .reg ∨ x0.ph = .wt ∨ x0.ph = .seen ∨ (x0.ph.post ∧ x0.cw))
  /-- `main` takes the signal, or sees epoch 1, only after the producer's signal. -/
  cons : x0.cw → (x0.ph.post ∨ x0.ph = .seen) → x1.cw
  /-- The producer wrote the state after `sg1`. -/
  pcw : x1.cw → 7 ≤ x1.ph.rank
  pcw' : (x1.ph = .sgp ∨ x1.ph = .wk) → x1.cw
  /-- `main` wrote `waiting` in `ev1` and after. -/
  mvw : x0.vw → (x0.ph = .ev1 ∨ x0.ph = .evd ∨ x0.ph = .joins)
  mvw' : x0.ph = .ev1 → x0.vw
  /-- The producer wrote `is_set` at its `xchg`; `setw` after it read `waiting`. -/
  pvw : x1.vw ↔ (x1.ph = .setw ∨ (x1.ph = .fin ∧ x1.vw))
  setw : x1.ph = .setw → x0.vw
  /-- After the producer's signal, `main` registered only if the producer signalled. -/
  late : x0.cw → 7 ≤ x1.ph.rank → x1.cw
  /-- The producer at its end wrote `is_set`. -/
  pfin : x1.ph = .fin → x1.vw
  /-- The producer at `sg1` read `main`'s `waiters += 1`. -/
  sg1 : x1.ph = .sg1 → x0.cw

/-- The threads: `main` alone before its spawn; then `main` and the producer, which `main`
spawned and did not join yet. -/
def Shape (X : ThreadId → X) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ X 0 = { ph := .pre } ∧ ∀ u, 1 ≤ u → X u = {}) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (X 0).ph.isMain ∧ (X 0).ph ≠ .pre ∧ (X 1).ph.isProd ∧ ∀ u, 2 ≤ u → X u = {}))

/-- Each access to the bytes of `io` (0..16 of the `Box`) is a read, or happened before every
thread. -/
def IoOk (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.off < 16 → e.kind = .read ∨ AllLe m e.clock

/-- Block 0 is the live `Box`: 40 bytes on the stack, at an address that is a multiple of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 40 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- The producer reads the state after `main`'s `waiters += 1` (write 1): while the producer is
before its `ready = true`, write 1 happened before the holder `main`, before the mutex's newest
message, or before the producer; after it, before the producer. -/
def RegHB (G : ThreadId → Gh) (m : Mem) : Prop :=
  (G 0).2.cw →
    ((G 1).2.ph.rank ≤ 3 → (L.ph (G 0) = .holds ∧
        VClock.le (WS.hist m)[1]!.clock (m.clocks[0]!) = true) ∨
      L.Before m (WS.hist m)[1]!.clock ∨ VClock.le (WS.hist m)[1]!.clock (m.clocks[1]!) = true) ∧
    ((G 1).2.ph = .rdy ∨ (G 1).2.ph = .sg1 →
      VClock.le (WS.hist m)[1]!.clock (m.clocks[1]!) = true)

/-- The futex queue: a thread at another futex than the mutex is `main`, at the epoch while the
producer has not woken it, or at the event while the producer has not set it (or has not woken
it yet). -/
def QOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  ∀ w ∈ m.waiters, w.2 = L.ptr ∨
    (w.1 = 0 ∧ w.2 = WE.ptr ∧ (G 0).2.ph = .wt ∧ (G 1).2.ph.rank < 9) ∨
    (w.1 = 0 ∧ w.2 = WV.ptr ∧ (G 0).2.ph = .ev1 ∧ (G 1).2.ph ≠ .fin)

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : IoOk m
  parts : ∀ u, (G u).1.part = Heap.empty
  blk : BlkOk m
  ws : WS.Ok m
  we : WE.Ok m
  wv : WV.Ok m
  sh : SOk m (sN (G 0).2 (G 1).2)
  eh : EOk m (eN (G 1).2)
  vh : VOk m (vL (G 0).2 (G 1).2)
  flags : Flags (G 0).2 (G 1).2
  reg : RegHB G m
  /-- The producer's `epoch += 1` (a release) happened after its signal. -/
  sig : eN (G 1).2 = 1 →
    VClock.le (WS.hist m)[2]!.clock (WE.hist m)[1]!.relClock = true
  /-- `main` loaded epoch 1 with an acquire: the producer's signal happened before it. -/
  seen : (G 0).2.ph = .seen → VClock.le (WS.hist m)[2]!.clock (m.clocks[0]!) = true
  /-- `main`'s `waiting` happened before it. -/
  vclk : (G 0).2.vw → VClock.le (WV.hist m)[1]!.clock (m.clocks[0]!) = true
  q : QOk G m
  /-- The producer's `signals += 1` happened before it, until its `epoch += 1`. -/
  pc : (G 1).2.ph = .sgp → VClock.le (WS.hist m)[2]!.clock (m.clocks[1]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := L.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .producer p => p = bPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, { ph := .lk })
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.ph = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2.ph = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 7 ∧ joinedAll 0 m

theorem sok_congr {m m' : Mem} {n : Nat} (h : WS.hist m' = WS.hist m) : SOk m' n ↔ SOk m n := by
  unfold SOk; rw [h]

theorem eok_congr {m m' : Mem} {n : Nat} (h : WE.hist m' = WE.hist m) : EOk m' n ↔ EOk m n := by
  unfold EOk; rw [h]

theorem vok_congr {m m' : Mem} {vs : List Nat} (h : WV.hist m' = WV.hist m) :
    VOk m' vs ↔ VOk m vs := by
  unfold VOk; rw [h]

/-! ## The protocol has the lock -/

theorem apS : Word.Apart L WS := .inr (.inl (by decide))
theorem apE : Word.Apart L WE := .inr (.inl (by decide))
theorem apV : Word.Apart L WV := .inr (.inl (by decide))

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Heap)
    (_ : L.ph (G t) ≠ .gone) (hu : U G m) (hs : L.Step t m m')
    (hrel : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) m' := by
  have hX : (fun u => (upd G t (L.set (G t) p h) u).2) = fun u => (G u).2 := snd_set G t p h
  have hX0 : (upd G t (L.set (G t) p h) 0).2 = (G 0).2 := congrFun hX 0
  have hX1 : (upd G t (L.set (G t) p h) 1).2 = (G 1).2 := congrFun hX 1
  have hkS := Word.keep_lockStep hs apS
  have hkE := Word.keep_lockStep hs apE
  have hkV := Word.keep_lockStep hs apV
  have hhS := Word.hist_keep hu.ws hkS
  have hhE := Word.hist_keep hu.we hkE
  have hhV := Word.hist_keep hu.wv hkV
  have hph0 : L.ph (upd G t (L.set (G t) p h) 0) = .holds → L.ph (G 0) = .holds ∨
      (t = 0 ∧ p = .holds) := by
    intro h0; unfold upd at h0; split at h0
    · rename_i e; subst e; exact .inr ⟨rfl, by rw [L.ph_set] at h0; exact h0⟩
    · exact .inl h0
  obtain ⟨hsh, hio, hpart, hblk, hws, hwe, hwv, hS, hE, hV, hfl, hreg, hsig, hseen, hvclk, hq,
    hpc⟩ := hu
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, ?_, hws.keep hkS, hwe.keep hkE, hwv.keep hkV,
    by rw [hX0, hX1, sok_congr hhS]; exact hS, by rw [hX1, eok_congr hhE]; exact hE,
    by rw [hX0, hX1, vok_congr hhV]; exact hV,
    by rw [hX0, hX1]; exact hfl, ?_, by rw [hX1, hhS, hhE]; exact hsig,
    fun h0 => ?_, fun h0 => ?_, fun w hw => ?_, fun h1 => ?_⟩
  · rw [hX]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh
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
      · show (writeBytes blk.bytes 16 bs).size = 40
        rw [writeBytes_size _ _ _ (by rw [h3, hsz]; decide), hsz]
  · -- the producer's read of `waiters += 1`
    intro hcw
    rw [hX0] at hcw; rw [hX1, hhS]
    obtain ⟨h1, h2⟩ := hreg hcw
    refine ⟨fun hr => ?_, fun hr => VClock.le_trans (h2 hr) (hs.clocks 1)⟩
    rcases h1 hr with ⟨hh, hle⟩ | hb | hle
    · by_cases ht0 : t = 0
      · subst ht0
        by_cases hp : p = .holds
        · subst hp
          refine .inl ⟨by unfold upd; simp [L.ph_set], VClock.le_trans hle (hs.clocks 0)⟩
        · exact .inr (.inl (before_le (hrel hh hp) hle))
      · refine .inl ⟨by rw [upd_ne _ _ (Ne.symm ht0)]; exact hh, VClock.le_trans hle (hs.clocks 0)⟩
    · exact .inr (.inl (hs.before _ hb))
    · exact .inr (.inr (VClock.le_trans hle (hs.clocks 1)))
  · rw [hX0] at h0; rw [hhS]; exact VClock.le_trans (hseen h0) (hs.clocks 0)
  · rw [hX0] at h0; rw [hhV]; exact VClock.le_trans (hvclk h0) (hs.clocks 0)
  · by_cases hl : w.2 = L.ptr
    · exact .inl hl
    · have hw' := (hs.waiters w hl).mp hw
      rw [hX0, hX1]; exact hq w hw'
  · rw [hX1] at h1; rw [hhS]; exact VClock.le_trans (hpc h1) (hs.clocks 1)

theorem fits : L.Fits proto U :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, stable⟩

/-- The word: `L.ptr`. -/
theorem mptr : bPtr.add 16 = L.ptr := rfl

/-- A pointer into the 40-byte `Box` (block 0, `BlkOk`) is formed (`ptrProject`, MM-3). -/
theorem projP {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {p : Ptr} {k : Nat}
    (hb : p.block = some 0) (h0 : 0 ≤ p.off) (hk : p.off + k ≤ 40) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) := by
  obtain ⟨blk, hblk, -, hsz, -⟩ := hi.2.blk
  exact ptrProject_block_run hblk hb h0 (by rw [hsz]; exact hk)

theorem projB {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {k : Nat} (hk : k ≤ 40) :
    (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) :=
  projP hi rfl (by decide) (by simp [bPtr]; omega)

/-- `&cond.epoch` once the condition's pointer is `WS.ptr`. -/
theorem projWE {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) :
    (ptrProject WS.ptr (·.add 4)).run m = pure (WE.ptr, m) :=
  projP hi rfl (by decide) (by decide)

/-- `&cond.epoch` from the condition's pointer. -/
theorem projE {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) :
    (ptrProject (bPtr.add 20) (·.add 4)).run m = pure ((bPtr.add 20).add 4, m) :=
  projP hi rfl (by decide) (by decide)

/-! ## The heap -/

/-- The resource's bytes: none before byte 32. -/
theorem R_none {X : ThreadId → X} {h : Heap} (hR : R X h) {x : Nat} (hx : x < 32) :
    h (0, x) = none := by
  obtain ⟨h1, h2, -, rfl, ⟨A, S, K, bs, -, -, -, ⟨b, hb, -, hl⟩, -⟩,
    ⟨A', S', K', bs', -, -, -, ⟨b', hb', -, hl'⟩, -⟩⟩ := hR
  cases hb; cases hb'
  simp only [Heap.union_apply, hl, hl']
  rw [if_neg (by simp only [bPtr, Ptr.add, not_and, Nat.not_lt]; intro _ h; simp at h; omega),
    if_neg (by simp only [bPtr, Ptr.add, not_and, Nat.not_lt]; intro _ h; simp at h; omega)]
  rfl

/-- No thread owns a byte before `v`. -/
theorem own_none {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (u : ThreadId) {x : Nat}
    (hx : x < 32) : L.own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    rw [hi.2.parts u, Heap.empty_union]
    by_cases hh : L.ph (G u) = .holds
    · exact R_none (X := fun u => (G u).2) (hi.1.res u hh) hx
    · rw [show (G u).1.held = L.held (G u) from rfl, hi.1.idle u hh]; rfl

/-- A word before `v` has no byte of a part or of the resource. -/
theorem off_own {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {W : Word 32 4} (hb : W.b = 0)
    (ho : W.o + 4 ≤ 32) (u : ThreadId) : W.Off (L.own G m u) := fun x _ h2 => by
  rw [hb]; exact own_none hi u (by omega)

theorem off_R {W : Word 32 4} (hb : W.b = 0) (ho : W.o + 4 ≤ 32) :
    ∀ G hL, L.R G hL → W.Off hL := fun G _ hR x _ h2 => by
  rw [hb]; exact R_none (X := fun u => (G u).2) hR (by omega)

/-- The cell of byte `x < 40` of the `Box`. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 40) : m.heap (0, x) ≠ none := by
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

/-! ## Steps that keep `U` -/

/-- A step that keeps the three words, the threads, the futex queue, the order of the clocks,
the mutex's newest message, the `Box` and the reads of `io`: `U` with the same ghost values. -/
theorem U_keep {G : ThreadId → Gh} {m m' : Mem} (hu : U G m) (hkS : WS.Keep m m')
    (hkE : WE.Keep m m') (hkV : WV.Keep m m') (ht : m'.threads = m.threads)
    (hq : QOk G m') (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) (hio : IoOk m') (hblk : BlkOk m') : U G m' := by
  have hhS := Word.hist_keep hu.ws hkS
  have hhE := Word.hist_keep hu.we hkE
  have hhV := Word.hist_keep hu.wv hkV
  obtain ⟨hsh, -, hpart, -, hws, hwe, hwv, hS, hE, hV, hfl, hreg, hsig, hseen, hvclk, -, hpc⟩ := hu
  refine ⟨by unfold Shape at hsh ⊢; rw [ht]; exact hsh, hio, hpart, hblk, hws.keep hkS,
    hwe.keep hkE, hwv.keep hkV, (sok_congr hhS).mpr hS, (eok_congr hhE).mpr hE,
    (vok_congr hhV).mpr hV, hfl, fun hcw => ?_, by rw [hhS, hhE]; exact hsig,
    fun h0 => by rw [hhS]; exact VClock.le_trans (hseen h0) (hcl 0),
    fun h0 => by rw [hhV]; exact VClock.le_trans (hvclk h0) (hcl 0), hq,
    fun h1 => by rw [hhS]; exact VClock.le_trans (hpc h1) (hcl 1)⟩
  obtain ⟨h1, h2⟩ := hreg hcw
  rw [hhS]
  refine ⟨fun hr => ?_, fun hr => VClock.le_trans (h2 hr) (hcl 1)⟩
  rcases h1 hr with ⟨hh, hle⟩ | hb | hle
  · exact .inl ⟨hh, VClock.le_trans hle (hcl 0)⟩
  · exact .inr (.inl (hbef _ hb))
  · exact .inr (.inr (VClock.le_trans hle (hcl 1)))

/-- The mutex's newest message stays if the atomic locations do. -/
theorem before_same {m m' : Mem} (ha : m'.atomics = m.atomics) {c : VClock} (h : L.Before m c) :
    L.Before m' c := by
  obtain ⟨i, l, hl, hle⟩ := h
  exact ⟨i, l, by unfold Lock.Loc; rw [ha]; exact hl, hle⟩

/-- A change of the ghost values with the same memory: `U` from the facts that depend on them. -/
theorem U_upd {G G' : ThreadId → Gh} {m : Mem} (hu : U G m)
    (hsh : Shape (fun u => (G' u).2) m) (hpart : ∀ u, (G' u).1.part = Heap.empty)
    (hS : sN (G' 0).2 (G' 1).2 = sN (G 0).2 (G 1).2) (hE : eN (G' 1).2 = eN (G 1).2)
    (hV : vL (G' 0).2 (G' 1).2 = vL (G 0).2 (G 1).2) (hfl : Flags (G' 0).2 (G' 1).2)
    (hreg : RegHB G' m)
    (hseen : (G' 0).2.ph = .seen → VClock.le (WS.hist m)[2]!.clock (m.clocks[0]!) = true)
    (hvclk : (G' 0).2.vw → VClock.le (WV.hist m)[1]!.clock (m.clocks[0]!) = true)
    (hq : QOk G' m)
    (hpc : (G' 1).2.ph = .sgp → VClock.le (WS.hist m)[2]!.clock (m.clocks[1]!) = true) : U G' m :=
  ⟨hsh, hu.io, hpart, hu.blk, hu.ws, hu.we, hu.wv, by rw [hS]; exact hu.sh, by rw [hE]; exact hu.eh,
    by rw [hV]; exact hu.vh, hfl, hreg, fun h => hu.sig (by rw [← hE]; exact h), hseen, hvclk, hq,
    hpc⟩

/-- A step of thread `t` on its own part (`WP.liftMem_owned`), with the same ghost values. -/
theorem U_stepIn {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {hQ : Heap}
    (hi : proto.inv G m) (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own G m t))) : U G m' := by
  have hrest : ∀ x, x < 32 → m.heap.diff (L.own G m t) (0, x) = m.heap (0, x) := fun x hx => by
    simp [Heap.diff, own_none hi t hx]
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    by_cases hu : u = m.current
    · subst hu; exact hs.mine
    · rw [hs.others u hu]; exact VClock.le_refl _
  refine U_keep hi.2 (Word.keep_stepIn hi.2.ws (off_own hi rfl (by decide) t) hs hm' hd)
    (Word.keep_stepIn hi.2.we (off_own hi rfl (by decide) t) hs hm' hd)
    (Word.keep_stepIn hi.2.wv (off_own hi rfl (by decide) t) hs hm' hd) hs.threads
    (fun w hw => hi.2.q w (hs.waiters ▸ hw)) hcl
    (fun _ h => before_same hs.atomics h) (fun e he hb ho => ?_) (blk_keep hi.2.blk ?_)
  · rcases hs.fp e he with h' | ⟨-, hnt, -⟩
    · rcases hi.2.io e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr fun u hu => VClock.le_trans (h'' u (hs.threads ▸ hu)) (hcl u)
    · exact absurd ⟨e.off, Nat.le_refl _, .inr rfl, by
        rw [hb, hrest _ (by omega)]; exact blk_heap hi.2.blk (by omega)⟩ hnt
  · rw [hm', Heap.union_of_right ((hd (0, 0)).resolve_right (by
      rw [hrest 0 (by decide)]; exact blk_heap hi.2.blk (by decide))), hrest 0 (by decide)]

/-! ## `io` -/

theorem noRace_io {m : Mem} (hio : IoOk m) (ht : m.current < m.threads.size) :
    NoRace m 0 0 16 .read :=
  noRace_of fun e he hb _ h2 => by
    rcases hio e he hb (by omega) with h | h
    · exact .inr (by rw [h]; rfl)
    · exact .inl (h _ ht)

/-- A read of `io` (bytes 0..16 of the `Box`): no race, and the invariant holds after it. -/
theorem step_io {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (ht : m.current < m.threads.size) :
    (load Io 8 bPtr).run m = pure (⟨⟩, m.recordAt 0 0 16 .read) ∧
      proto.inv G (m.recordAt 0 0 16 .read) := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hi.2.blk
  have hacc : m.access bPtr (Enc.size Io) 8 = pure (0, blk, 0) :=
    access_of (p := bPtr) rfl hblk hl (by decide)
      (by rw [show Enc.size Io = 16 from rfl]; simp [bPtr, hs]) (by simpa [bPtr] using ha)
  refine ⟨load_run hacc rfl (noRace_io hi.2.io ht), ?_, ?_⟩
  · refine hi.1.read (b := 0) (o := 0) (n := 16) (Array.getElem?_eq_some_iff.mp hblk).1 (by decide)
      (fun u x _ hx => own_none hi u (by omega))
      (fun hL hR x _ hx => R_none (X := fun u => (G u).2) hR (by omega))
      (.inr (.inl (by decide)))
  · refine U_keep hi.2 (Word.keep_read m (by decide) (.inr (.inl (by decide))))
      (Word.keep_read m (by decide) (.inr (.inl (by decide))))
      (Word.keep_read m (by decide) (.inr (.inl (by decide)))) rfl hi.2.q
      (recordAt_le m 0 0 16 .read) (fun _ h => before_same rfl h) (fun e he hb ho => ?_)
      (blk_keep hi.2.blk rfl)
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · rcases hi.2.io e he hb ho with h | h
      · exact .inl h
      · exact .inr fun u hu => VClock.le_trans (h u hu) (recordAt_le m 0 0 16 .read u)
    · exact .inl rfl

/-- A read of `io` by thread `t` in generated code. -/
theorem wp_io {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh}
    (hi : proto.inv (upd G t g) m) (hc : m.current = t) (ht : t < m.threads.size)
    {Q : Io × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m', m'.current = t → m'.threads = m.threads → proto.inv (upd G t g) m' →
      Q (⟨⟩, s) G m' d) :
    proto.WP t ((liftM (load Io 8 bPtr) : CM Tgt σ Io).run s) Q G m d := by
  obtain ⟨hrun, hi'⟩ := step_io hi (hc ▸ ht)
  refine WP.liftM (fun e he => (MemM.noErr_of_run hrun e he).elim) fun v m' hr => ?_
  rw [hrun] at hr
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  cases v
  exact ⟨rfl, h _ hc rfl hi'⟩

/-! ## The ops at the shared words -/

/-- One of the three shared words. -/
def Wd (W : Word 32 4) : Prop := W = WS ∨ W = WE ∨ W = WV

theorem Wd.ok {W : Word 32 4} (hW : Wd W) {G : ThreadId → Gh} {m : Mem} (hu : U G m) : W.Ok m := by
  rcases hW with rfl | rfl | rfl
  · exact hu.ws
  · exact hu.we
  · exact hu.wv

theorem Wd.ap {W : Word 32 4} (hW : Wd W) : Word.Apart L W := by
  rcases hW with rfl | rfl | rfl
  · exact apS
  · exact apE
  · exact apV

theorem Wd.blk {W : Word 32 4} (hW : Wd W) : W.b = 0 ∧ W.o + 4 ≤ 32 := by
  rcases hW with rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

/-- The invariant at a stop of thread `t`: the same, with `current := t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (t : ThreadId) :
    proto.inv G { m with current := t } :=
  ⟨hi.1.current t, U_keep hi.2 (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _)
    (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _)
    (Word.keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _) rfl hi.2.q (fun _ => VClock.le_refl _)
    (fun _ h => before_same rfl h) hi.2.io hi.2.blk⟩

theorem hcs_of {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) :
    m.clocks.size = m.threads.size := hi.1.own.csize

/-- An op at a shared word by thread `t` keeps the lock's invariant. -/
theorem linv_op {W : Word 32 4} (hW : Wd W) {G : ThreadId → Gh} {t : ThreadId} {m m' : Mem}
    (hi : proto.inv G m) (hop : W.Op t m m') : L.Inv G m' :=
  hi.1.wordOp (hW.ok hi.2) hop hW.ap (fun u => off_own hi (hW.blk).1 (hW.blk).2 u)
    (off_R (hW.blk).1 (hW.blk).2 G)

theorem op_of_cur {W : Word 32 4} {t : ThreadId} {m₁ m' : Mem}
    (hop : W.Op t { m₁ with current := t } m') : W.Op t m₁ m' :=
  ⟨hop.current, hop.threads, hop.waiters, hop.woken, hop.groups, hop.csize, hop.others,
    hop.mine, hop.bsize, hop.cells, hop.fp, ⟨hop.locs.new, hop.locs.same⟩, hop.fpt⟩

/-- An atomic load at a shared word, with a decode (`atomicLoadAsC`), by thread `t` (`g`). -/
theorem wp_loadAs {α : Type} [Packed α 32] {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh}
    {m : Mem} {n : Nat} {g : Gh} {W : Word 32 4} (hW : Wd W) {ord : AtomicOrder}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    (hdec : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' b r j, G₁ t = g → proto.inv G₁ m₁ →
      (Packed.ofBits? (α := α) b).run = some (.ok r) →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' → Q (r, s) G₁ m' k) :
    proto.WP t ((atomicLoadAsC α ord 4 W.ptr : CM Tgt σ α).run s) Q G m n := by
  unfold atomicLoadAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  have htl : t < m₁.threads.size := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok hic.2
  refine WP.callMC (fun e he => (atomicLoadAs_noErr (hwc.load_noErr htl (hcs_of hic) hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨j, hj, hv, -⟩ := hwc.load rfl htl (hcs_of hic) hr
    have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
    rw [hh₁] at hj hv
    exact hdec G₁ m₁ hg₁ hi₁ j hj b hv
  obtain ⟨b, hb, hd⟩ := atomicLoadAs_ok hr
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hwc.load rfl htl (hcs_of hic) hb
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hj hv hfl hacq hh
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' b r j hg₁ hi₁ hd hj hv hfl hacq hh hw' (op_of_cur hop)
    (linv_op hW hic hop)⟩

/-- An atomic load of a `u32` at a shared word (`atomicLoadC`), by thread `t` (`g`). -/
theorem wp_load {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {n : Nat} {g : Gh}
    {W : Word 32 4} (hW : Wd W) {ord : AtomicOrder} (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    {Q : BitVec 32 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' v j, G₁ t = g → proto.inv G₁ m₁ →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' → Q (v, s) G₁ m' k) :
    proto.WP t ((atomicLoadC (n := 32) ord 4 W.ptr : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  have htl : t < m₁.threads.size := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok hic.2
  refine WP.callMC (fun e he => (hwc.load_noErr htl (hcs_of hic) hcr e he).elim) fun v m' hr => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hwc.load rfl htl (hcs_of hic) hr
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hj hv hfl hacq hh
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' v j hg₁ hi₁ hj hv hfl hacq hh hw' (op_of_cur hop)
    (linv_op hW hic hop)⟩

/-- The newest write of a word. -/
abbrev last (h : Array Word.Entry) : Word.Entry := h[h.size - 1]!

/-- An RMW of a `u32` at a shared word (`atomicRmwC`), by thread `t` (`g`). -/
theorem wp_rmw {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh} {m : Mem} {n : Nat} {g : Gh}
    {W : Word 32 4} (hW : Wd W) {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec 32}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    {Q : BitVec 32 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' old, G₁ t = g → proto.inv G₁ m₁ →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply signed old v)) →
      (ord.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' → Q (old, s) G₁ m' k) :
    proto.WP t ((atomicRmwC op signed ord 4 W.ptr v : CM Tgt σ (BitVec 32)).run s) Q G m n := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  have htl : t < m₁.threads.size := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok hic.2
  refine WP.callMC (fun e he => (hwc.rmw_noErr htl (hcs_of hic) hcr e he).elim)
    fun old m' hr => ?_
  obtain ⟨hv, hw', hop, hU, hh, hacq⟩ := hwc.rmw rfl htl (hcs_of hic) hr
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hv hh hacq
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old hg₁ hi₁ hv hU hh hacq hw' (op_of_cur hop)
    (linv_op hW hic hop)⟩

/-- An RMW at a shared word, with a decode (`atomicRmwAsC`), by thread `t` (`g`). -/
theorem wp_rmwAs {α : Type} [Packed α 32] {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh}
    {m : Mem} {n : Nat} {g : Gh} {W : Word 32 4} (hW : Wd W) {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    (hdec : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → ∀ b, (last (W.hist m₁)).Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' old r, G₁ t = g → proto.inv G₁ m₁ →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply false old (Packed.toBits v)) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply false old (Packed.toBits v))) →
      (ord.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' → Q (r, s) G₁ m' k) :
    proto.WP t ((atomicRmwAsC op ord 4 W.ptr v : CM Tgt σ α).run s) Q G m n := by
  unfold atomicRmwAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  have htl : t < m₁.threads.size := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok hic.2
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (atomicRmwAs_noErr (hwc.rmw_noErr htl (hcs_of hic) hcr)
    (fun b m' hr => ?_) e he).elim) fun r m' hr => ?_
  · obtain ⟨hv, -⟩ := hwc.rmw rfl htl (hcs_of hic) hr
    rw [hh₁] at hv
    exact hdec G₁ m₁ hg₁ hi₁ b hv
  obtain ⟨old, hb, hd⟩ := atomicRmwAs_ok hr
  obtain ⟨hv, hw', hop, hU, hh, hacq⟩ := hwc.rmw rfl htl (hcs_of hic) hb
  rw [hh₁] at hv hh hacq
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old r hg₁ hi₁ hd hv hU hh hacq hw' (op_of_cur hop)
    (linv_op hW hic hop)⟩

/-- A `cmpxchg` at a shared word, with a decode (`cmpxchgAsC`), by thread `t` (`g`): on success
an RMW of the newest write, which holds `exp`; on failure a read of write `j`. -/
theorem wp_casAs {α : Type} [Packed α 32] {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh}
    {m : Mem} {n : Nat} {g : Gh} {W : Word 32 4} (hW : Wd W) {succ fail : AtomicOrder} {exp new : α}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    (hdec : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m', G₁ t = g → proto.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      L.Inv G₁ m' →
      ((last (W.hist m₁)).Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) (Packed.toBits new)) →
        (succ.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, b ≠ Packed.toBits exp → (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some r, s) G₁ m' k)) :
    proto.WP t ((cmpxchgAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  have htl : t < m₁.threads.size := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok hic.2
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (cmpxchgAs_noErr (hwc.cas_noErr (fail := fail)
    (new := Packed.toBits new) htl (hcs_of hic) hcr) (fun b m' hr => ?_) e he).elim)
    fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, -, hj, hv, -⟩⟩ := hwc.cas rfl htl (hcs_of hic) hr
    · cases he
    · cases he
      rw [hh₁] at hj hv
      exact hdec G₁ m₁ hg₁ hi₁ j hj _ hv
  rcases cmpxchgAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hU, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hwc.cas rfl htl (hcs_of hic) ho
    · rw [hh₁] at hv hh hacq
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        (linv_op hW hic hop)).1 hv hU hh hacq⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hne, hj, hv, hfl, hacq, hh⟩⟩ :=
      hwc.cas rfl htl (hcs_of hic) ho
    · cases he
    · cases he
      rw [hh₁] at hj hv hfl hacq hh
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        (linv_op hW hic hop)).2 j b v hne hd hj hv hfl hacq hh⟩

theorem wp_weakCasAs {α : Type} [Packed α 32] {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh}
    {m : Mem} {n : Nat} {g : Gh} {W : Word 32 4} (hW : Wd W) {succ fail : AtomicOrder} {exp new : α}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    (hdec : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m', G₁ t = g → proto.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      L.Inv G₁ m' →
      ((last (W.hist m₁)).Val (Packed.toBits exp) → W.Holds m' (Packed.toBits new) →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) (Packed.toBits new)) →
        (succ.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b r, (Packed.ofBits? (α := α) b).run = some (.ok r) →
        j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some r, s) G₁ m' k)) :
    proto.WP t ((cmpxchgWeakAsC succ fail 4 W.ptr exp new : CM Tgt σ (Option α)).run s) Q G m n := by
  unfold cmpxchgWeakAsC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  have htl : t < m₁.threads.size := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok hic.2
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (cmpxchgWeakAs_noErr (hwc.weakCas_noErr (fail := fail)
    (new := Packed.toBits new) htl (hcs_of hic) hcr) (fun b m' hr => ?_) e he).elim)
    fun r m' hr => ?_
  · obtain ⟨-, -, ⟨he, -⟩ | ⟨j, old, he, hj, hv, -⟩⟩ := hwc.weakCas rfl htl (hcs_of hic) hr
    · cases he
    · cases he
      rw [hh₁] at hj hv
      exact hdec G₁ m₁ hg₁ hi₁ j hj _ hv
  rcases cmpxchgWeakAs_ok hr with ⟨rfl, ho⟩ | ⟨b, v, rfl, ho, hd⟩
  · obtain ⟨hw', hop, ⟨-, hv, hU, hh, hacq⟩ | ⟨j, old, he, -⟩⟩ := hwc.weakCas rfl htl (hcs_of hic) ho
    · rw [hh₁] at hv hh hacq
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        (linv_op hW hic hop)).1 hv hU hh hacq⟩
    · cases he
  · obtain ⟨hw', hop, ⟨he, -⟩ | ⟨j, old, he, hj, hv, hfl, hacq, hh⟩⟩ :=
      hwc.weakCas rfl htl (hcs_of hic) ho
    · cases he
    · cases he
      rw [hh₁] at hj hv hfl hacq hh
      exact ⟨by rw [hop.threads], (h k hk G₁ m₁ m' hg₁ hi₁ hw' (op_of_cur hop)
        (linv_op hW hic hop)).2 j b v hd hj hv hfl hacq hh⟩


/-! ## `U` after an op at a shared word -/

theorem Wd.lo {W : Word 32 4} (hW : Wd W) : 20 ≤ W.o := by
  rcases hW with rfl | rfl | rfl <;> decide

/-- Two shared words do not overlap. -/
theorem Wd.apart {W W' : Word 32 4} (hW : Wd W) (hW' : Wd W') (hne : W' ≠ W) :
    W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o := by
  rcases hW with rfl | rfl | rfl <;> rcases hW' with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | decide

/-- An op at `W` keeps the writes of another shared word. -/
theorem hist_op {W W' : Word 32 4} (hW : Wd W) (hW' : Wd W') (hne : W' ≠ W) {G : ThreadId → Gh}
    {t : ThreadId} {m₁ m' : Mem} (hu : U G m₁) (hop : W.Op t m₁ m') : W'.hist m' = W'.hist m₁ :=
  Word.hist_keep (hW'.ok hu) (Word.keep_op hop (hW.apart hW' hne))

/-- `U` after an op at a shared word, from the facts that depend on the ghost values and the
writes. -/
theorem U_op {W : Word 32 4} (hW : Wd W) {G G' : ThreadId → Gh} {t : ThreadId} {m₁ m' : Mem}
    (hu : U G m₁) (hop : W.Op t m₁ m') (hw' : W.Ok m')
    (hsh : Shape (fun u => (G' u).2) m₁) (hpart : ∀ u, (G' u).1.part = Heap.empty)
    (hS : SOk m' (sN (G' 0).2 (G' 1).2)) (hE : EOk m' (eN (G' 1).2))
    (hV : VOk m' (vL (G' 0).2 (G' 1).2)) (hfl : Flags (G' 0).2 (G' 1).2) (hreg : RegHB G' m')
    (hsig : eN (G' 1).2 = 1 → VClock.le (WS.hist m')[2]!.clock (WE.hist m')[1]!.relClock = true)
    (hseen : (G' 0).2.ph = .seen → VClock.le (WS.hist m')[2]!.clock (m'.clocks[0]!) = true)
    (hvclk : (G' 0).2.vw → VClock.le (WV.hist m')[1]!.clock (m'.clocks[0]!) = true)
    (hq : QOk G' m')
    (hpc : (G' 1).2.ph = .sgp → VClock.le (WS.hist m')[2]!.clock (m'.clocks[1]!) = true) :
    U G' m' := by
  have hok : ∀ W', Wd W' → W'.Ok m' := by
    intro W' hW'
    by_cases e : W' = W
    · subst e; exact hw'
    · exact (hW'.ok hu).keep (Word.keep_op hop (hW.apart hW' e))
  refine ⟨by unfold Shape at hsh ⊢; rw [hop.threads]; exact hsh, fun e he hb ho => ?_, hpart, ?_,
    hok WS (.inl rfl), hok WE (.inr (.inl rfl)), hok WV (.inr (.inr rfl)), hS, hE, hV, hfl, hreg,
    hsig, hseen, hvclk, hq, hpc⟩
  · rcases hop.fp e he with h' | ⟨hb', ho', -⟩
    · rcases hu.io e h' hb ho with h'' | h''
      · exact .inl h''
      · exact .inr (hop.allLe h'')
    · have := hW.lo; omega
  · refine blk_keep hu.blk (hop.cells _ ?_)
    rintro ⟨-, h, -⟩; have := hW.lo; simp only at h; omega

/-! ## Changes of a ghost value -/

theorem upd1_0 (G : ThreadId → Gh) (g : Gh) : upd G 1 g 0 = G 0 := upd_ne _ _ (by decide)
theorem upd0_1 (G : ThreadId → Gh) (g : Gh) : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)

/-- `R` reads only `v` and `ready` of the producer's place. -/
theorem R_congr {Y Y' : ThreadId → X} (hv : vOf (Y' 1) = vOf (Y 1)) (hr : rdyOf (Y' 1) = rdyOf (Y 1))
    (h : Heap) : R Y' h ↔ R Y h := by
  unfold R; rw [hv, hr]

/-- The threads, after a change of the producer's place. -/
theorem shape_p {G : ThreadId → Gh} {m : Mem} {g g' : Gh}
    (hs : Shape (fun u => (upd G 1 g u).2) m) (hpx : g.2.ph.isProd) (hpr : g'.2.ph.isProd) :
    Shape (fun u => (upd G 1 g' u).2) m := by
  obtain ⟨h00, hc⟩ := hs
  refine ⟨h00, ?_⟩
  rcases hc with ⟨-, -, hn⟩ | ⟨h2, h1, hm, hm', -, hrest⟩
  · have := hn 1 (Nat.le_refl _); simp only [upd_self] at this; rw [this] at hpx; cases hpx
  · refine .inr ⟨h2, h1, ?_, ?_, by simp only [upd_self]; exact hpr, fun u hu => ?_⟩
    · simpa [upd1_0] using hm
    · simpa [upd1_0] using hm'
    · have hu1 : u ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu)
      have := hrest u hu
      simp only [upd_ne _ _ hu1] at this ⊢; exact this

theorem parts_p {G : ThreadId → Gh} {g g' : Gh} (hp : ∀ u, (upd G 1 g u).1.part = Heap.empty)
    (hg : g'.1.part = Heap.empty) : ∀ u, (upd G 1 g' u).1.part = Heap.empty := fun u => by
  have := hp u; unfold upd at this ⊢; split <;> simp_all

/-- A change of the producer's place and writes, with the same lock part, `v`, `ready` and
counts of writes. -/
theorem inv_p {G : ThreadId → Gh} {m : Mem} {a : LG} {x x' : X} (hi : proto.inv (upd G 1 (a, x)) m)
    (hpx : x.ph.isProd) (hpr : x'.ph.isProd) (hv : vOf x' = vOf x) (hr : rdyOf x' = rdyOf x)
    (hcw : x'.cw = x.cw) (hvw : x'.vw = x.vw) (heN : eN x' = eN x) (hfl : Flags (G 0).2 x')
    (hreg : RegHB (upd G 1 (a, x')) m) (hq : QOk (upd G 1 (a, x')) m) (hx' : x'.ph ≠ .sgp) :
    proto.inv (upd G 1 (a, x')) m := by
  have h0 : ∀ g, upd G 1 g 0 = G 0 := upd1_0 G
  refine ⟨hi.1.congr (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun h => ?_), U_upd hi.2 ?_
    (fun u => ?_) ?_ (by simp only [upd_self, heN]) ?_ (by rw [h0, upd_self]; exact hfl) hreg
    (fun h => hi.2.seen (by rw [h0] at h ⊢; exact h))
    (fun h => hi.2.vclk (by rw [h0] at h ⊢; exact h)) hq
    (fun h => absurd (by rw [upd_self] at h; exact h) hx')⟩
  · unfold upd; split <;> rfl
  · unfold upd; split <;> rfl
  · unfold upd; split <;> rfl
  · change R (fun u => (upd G 1 (a, x') u).2) h ↔ R (fun u => (upd G 1 (a, x) u).2) h
    exact R_congr (by simp only [upd_self]; exact hv) (by simp only [upd_self]; exact hr) h
  · exact shape_p hi.2.shape hpx hpr
  · exact parts_p hi.2.parts (by have := hi.2.parts 1; simpa using this) u
  · simp only [h0, upd_self, sN, hcw]
  · simp only [h0, upd_self, vL, hvw]

/-! ## `ready` in the mutex's resource -/

/-- The cell of `ready` in a heap with `R`. -/
theorem R_cell {Y : ThreadId → X} {h : Heap} (hR : R Y h) :
    ∃ bs : Array Byte, bs.size = 1 ∧ Enc.decode bs = pure (rdyOf (Y 1)) ∧
      ∃ A S K, h (0, 36) = some ⟨bs[0]!, A, S, K⟩ := by
  obtain ⟨h1, h2, -, rfl, ⟨A, S, K, bs, -, hs, -, ⟨b, hb, -, hl⟩, -⟩,
    ⟨A', S', K', bs', -, hs', hd', ⟨b', hb', -, hl'⟩, -⟩⟩ := hR
  cases hb; cases hb'
  have hs4 : bs.size = 4 := hs
  have hs1 : bs'.size = 1 := hs'
  refine ⟨bs', hs1, hd', A', S', K', ?_⟩
  simp only [Heap.union_apply, hl, hl']
  rw [if_neg (by simp only [bPtr, Ptr.add, not_and, Nat.not_lt, hs4]; intro _ h; simp at h ⊢),
    if_pos (by simp [bPtr, Ptr.add, hs1])]
  simp [bPtr, Ptr.add]

theorem decode_bool {bs bs' : Array Byte} {a b : Bool} (hs : bs.size = 1) (hs' : bs'.size = 1)
    (h0 : bs[0]! = bs'[0]!) (ha : Enc.decode bs = pure a) (hb : Enc.decode bs' = pure b) :
    a = b := by
  have e1 : bs = bs' := by
    apply Array.ext (by omega)
    intro i h1 h2
    have : i = 0 := by omega
    subst this
    rw [getElem!_pos bs 0 (by omega), getElem!_pos bs' 0 (by omega)] at h0
    exact h0
  subst e1
  rw [ha] at hb
  have := congrArg ExceptT.run hb
  simpa [pure, ExceptT.pure, ExceptT.run, ExceptT.mk] using this

/-- Two views of the same resource give the same `ready`. -/
theorem R_rdy {Y Y' : ThreadId → X} {h : Heap} (hR : R Y h) (hR' : R Y' h) :
    rdyOf (Y 1) = rdyOf (Y' 1) := by
  obtain ⟨bs, hs, hd, A, S, K, hc⟩ := R_cell hR
  obtain ⟨bs', hs', hd', A', S', K', hc'⟩ := R_cell hR'
  rw [hc] at hc'
  simp only [Option.some.injEq, Cell.mk.injEq] at hc'
  exact decode_bool hs hs' hc'.1 hd hd'

/-- A thread's ghost value outside the lock's code, at the place `x`. -/
def gP (x : X) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, x)

/-- A thread's ghost value while it holds the mutex and the resource `h`. -/
def gH (x : X) (h : Heap) : Gh := (⟨.holds, Heap.empty, h⟩, x)

/-! ## `main` -/

theorem get_push_lt {h : Array Word.Entry} {x : Word.Entry} {k : Nat} (hk : k < h.size) :
    (h.push x)[k]! = h[k]! := by
  have h1 : k < (h.push x).size := by simp; omega
  rw [getElem!_pos (h.push x) k h1, getElem!_pos h k hk, Array.getElem_push_lt hk]

theorem get_push_eq {h : Array Word.Entry} {x : Word.Entry} : (h.push x)[h.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]; simp

theorem get_push_eq' {h : Array Word.Entry} {x : Word.Entry} {k : Nat} (hk : k = h.size) :
    (h.push x)[k]! = x := by
  subst hk; exact get_push_eq

theorem rmwEnt_val {M : Mem} {t : ThreadId} {ord : AtomicOrder} {last : Word.Entry}
    {new : BitVec 32} : (Word.rmwEnt M t ord last new).Val new := intOfBytes_rmw new

theorem ofBits_cst (b : BitVec 32) :
    (Packed.ofBits? (α := Io_Condition_State) b).run = some (.ok (Packed.ofBits b)) := rfl

theorem val_eq {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl


theorem upd_g {G : ThreadId → Gh} {t : ThreadId} {g : Gh} (hg : G t = g) : upd G t g = G := by
  rw [← hg]; exact upd_same G t

/-- A memory with the same blocks, atomic locations, footprint, threads and clocks. -/
theorem U_mem {G : ThreadId → Gh} {m m' : Mem} (hu : U G m) (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hf : m'.footprint = m.footprint) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hq : QOk G m') : U G m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hc]; exact VClock.le_refl _
  have hk : ∀ W : Word 32 4, W.Keep m m' := fun W => Word.keep_of hb ha hf ht hcl
  exact U_keep hu (hk WS) (hk WE) (hk WV) ht hq hcl (fun _ h => before_same ha h)
    (by unfold IoOk AllLe; rw [hf, ht, hc]; exact hu.io) (by unfold BlkOk; rw [hb]; exact hu.blk)

/-- A thread at another futex than the mutex is `main`. -/
theorem qok_main {G : ThreadId → Gh} {m : Mem} (hq : QOk G m) {w : ThreadId × Ptr}
    (hw : w ∈ m.waiters) (hl : w.2 ≠ L.ptr) : w.1 = 0 := by
  rcases hq w hw with h | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h hl
  · exact h1
  · exact h1


/-- A thread that sleeps at a futex is not the last one. -/
theorem live_all {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (t : ThreadId) :
    proto.Live t G m := by
  intro hw hall
  obtain ⟨i, hi', he⟩ := Array.any_eq_true.mp hw
  have hwm := Array.getElem_mem hi'
  -- a waiter at the mutex: its witness goes on
  have hnoL := fits.noWaits hi.1 hall
  have hnot : ∀ w ∈ m.waiters, w.2 ≠ L.ptr := fun w hw' e =>
    hnoL (Array.any_eq_true.mpr (by
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hw'
      exact ⟨j, hj, by simp [e]⟩))
  obtain ⟨h00, hc⟩ := hi.2.shape
  rcases hc with ⟨hs1, -, -⟩ | ⟨hs2, -, -, -, hp1, -⟩
  · -- `main` alone: it does not wait at another futex
    rcases hi.2.q _ hwm with h | ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩
    · exact hnot _ hwm h
    all_goals
      rcases hi.2.shape.2 with ⟨-, h0, -⟩ | ⟨h2, -⟩
      · change (G 0).2 = _ at h0; rw [h0] at h3; cases h3
      · omega
  · rcases hall 1 (by omega) with h | h | h
    · -- the producer has ended: `main` does not wait at the epoch or the event
      rcases hi.2.q _ hwm with h' | ⟨-, -, -, h4⟩ | ⟨-, -, -, h4⟩
      · exact hnot _ hwm h'
      · rw [h.2] at h4; simp [Ph.rank] at h4
      · exact h4 h.2
    · obtain ⟨j, hj, hje⟩ := Array.any_eq_true.mp h
      have hm := Array.getElem_mem hj
      have := qok_main hi.2.q hm (hnot _ hm)
      have hje' : (m.waiters[j]).1 = 1 := by simpa using hje
      rw [hje'] at this; cases this
    · rw [h.2] at hp1; cases hp1

/-- `main`'s lock part does not change `R`. -/
theorem linv0 {G : ThreadId → Gh} {m : Mem} {a : LG} {x x' : X} (hL : L.Inv (upd G 0 (a, x)) m) :
    L.Inv (upd G 0 (a, x')) m :=
  hL.congr (fun u => by unfold upd; split <;> rfl) (fun u => by unfold upd; split <;> rfl)
    (fun u => by unfold upd; split <;> rfl) fun h => by
      change R (fun u => (upd G 0 (a, x') u).2) h ↔ R (fun u => (upd G 0 (a, x) u).2) h
      exact R_congr (by rw [upd0_1, upd0_1]) (by rw [upd0_1, upd0_1]) h

/-- The threads, after a change of `main`'s place. -/
theorem shape_m {G : ThreadId → Gh} {m : Mem} {g g' : Gh}
    (hs : Shape (fun u => (upd G 0 g u).2) m) (hpm : g.2.ph ≠ .pre) (hm : g'.2.ph.isMain)
    (hpm' : g'.2.ph ≠ .pre) : Shape (fun u => (upd G 0 g' u).2) m := by
  obtain ⟨h00, hc⟩ := hs
  refine ⟨h00, ?_⟩
  rcases hc with ⟨-, h0, -⟩ | ⟨h2, h1, -, -, hp, hrest⟩
  · simp only [upd_self] at h0; rw [h0] at hpm; exact absurd rfl hpm
  · refine .inr ⟨h2, h1, by simp only [upd_self]; exact hm, by simp only [upd_self]; exact hpm',
      by simpa [upd0_1] using hp, fun u hu => ?_⟩
    have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu)
    have := hrest u hu
    simp only [upd_ne _ _ hu0] at this ⊢; exact this

theorem parts_m {G : ThreadId → Gh} {g g' : Gh} (hp : ∀ u, (upd G 0 g u).1.part = Heap.empty)
    (hg : g'.1.part = Heap.empty) : ∀ u, (upd G 0 g' u).1.part = Heap.empty := fun u => by
  have := hp u; unfold upd at this ⊢; split <;> simp_all

/-- `main`'s lock place, with the same place in `main`'s code: `U` stays if `main` does not hold
the mutex before or after. -/
theorem U_lock0 {G : ThreadId → Gh} {m : Mem} {a a' : LG} {x : X} (hu : U (upd G 0 (a, x)) m)
    (hpa : a'.part = Heap.empty) (ha : a.ph = .holds → a'.ph = .holds) :
    U (upd G 0 (a', x)) m := by
  have hX : (fun u => (upd G 0 (a', x) u).2) = fun u => (upd G 0 (a, x) u).2 := by
    funext u; unfold upd; split <;> rfl
  have h0 : (upd G 0 (a', x) 0).2 = (upd G 0 (a, x) 0).2 := by simp
  have h1 : upd G 0 (a', x) 1 = upd G 0 (a, x) 1 := by rw [upd0_1, upd0_1]
  refine ⟨by rw [hX]; exact hu.shape, hu.io, parts_m hu.parts hpa, hu.blk, hu.ws, hu.we, hu.wv,
    by rw [h0, h1]; exact hu.sh, by rw [h1]; exact hu.eh, by rw [h0, h1]; exact hu.vh,
    by rw [h0, h1]; exact hu.flags, fun hcw => ?_, by rw [h1]; exact hu.sig,
    by rw [h0]; exact hu.seen, by rw [h0]; exact hu.vclk, fun w hw => ?_, by rw [h1]; exact hu.pc⟩
  · rw [h0] at hcw; rw [h1]
    obtain ⟨c1, c2⟩ := hu.reg (by rw [← h0]; exact hcw)
    refine ⟨fun hr => ?_, by rw [← h1]; exact c2⟩
    rcases c1 (by rw [← h1]; exact hr) with ⟨hh, hle⟩ | hb | hle
    · rw [upd_self] at hh; exact .inl ⟨by rw [upd_self]; exact ha hh, hle⟩
    · exact .inr (.inl hb)
    · exact .inr (.inr hle)
  · rcases hu.q w hw with h | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact .inl h
    · exact .inr (.inl ⟨a1, a2, by rw [h0]; exact a3, by rw [h1]; exact a4⟩)
    · exact .inr (.inr ⟨a1, a2, by rw [h0]; exact a3, by rw [h1]; exact a4⟩)

/-- `main` away from the mutex's code, at the futex wait of another sync object. -/
def gA (x : X) : Gh := (⟨.away, Heap.empty, Heap.empty⟩, x)

/-- `main` goes to the futex wait of another sync object (`away`). -/
theorem inv_away {G : ThreadId → Gh} {m : Mem} {x : X} (hi : proto.inv (upd G 0 (gP x)) m) :
    proto.inv (upd G 0 (gA x)) m := by
  have hl := hi.1.ghost (t := 0) (g := gA x) (by rw [upd_self]; rfl) (.inr (.inr rfl))
    (by rw [upd_self]; rfl) rfl (fun _ => hi.1.live 0 (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun hL hR => by
      change R (fun u => (upd (upd G 0 (gP x)) 0 (gA x) u).2) hL
      rw [upd_upd]
      exact (R_congr (Y := fun u => (upd G 0 (gP x) u).2) (by rw [upd0_1, upd0_1])
        (by rw [upd0_1, upd0_1]) hL).mpr hR)
  rw [upd_upd] at hl
  exact ⟨hl, U_lock0 hi.2 rfl (fun h => absurd h (by decide))⟩

/-- `main`'s futex wait at a shared word (`W`, the value `e`), at `out` with the place `x`: it
can sleep while the word is `e` (`hq`: then the futex queue keeps `QOk`). It goes on at `out`
with the same place. -/
theorem wp_mwait {α : Type} {w : Nat} [Packed α w] {σ : Type} {s : σ} {G : ThreadId → Gh}
    {m : Mem} {n : Nat} {x : X} {W : Word 32 4} (hW : Wd W) (hWL : W.ptr ≠ L.ptr) {io : Io} {e : α}
    (hi : proto.inv (upd G 0 (gP x)) m)
    (hq : ∀ G₁ m₁, G₁ 0 = gA x → proto.inv G₁ m₁ → W.Holds m₁ ((Packed.toBits e).setWidth 32) →
      QOk G₁ { m₁ with current := 0, waiters := m₁.waiters.push (0, W.ptr) })
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = 0 → proto.inv (upd G₁ 0 (gP x)) m' →
      Q ((), s) G₁ m' k) :
    proto.WP 0 ((futexWaitC io W.ptr e : CM Tgt σ Unit).run s) Q G m n := by
  refine WP.futexWaitC fun k hk => ⟨gA x, inv_away hi, fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have hw := hW.ok hi₁.2
  have hph : L.ph (G₁ 0) = .away := by rw [hg₁]; rfl
  refine ⟨fun _ => live_all hi₁ 0, fun hq0 => ⟨fun _ => ?_, fun b m' hr => ?_⟩⟩
  · by_cases hwk : ({ m₁ with current := 0 } : Mem).woken.contains
      ({ m₁ with current := 0 } : Mem).current = true
    · exact ⟨_, _, futexWait_run_woken hwk⟩
    · obtain ⟨blk, hb, -, -, ha, -⟩ := hw.access
      obtain ⟨v, hv⟩ := hw.val
      rw [Word.holds_bytes hb] at hv
      exact ⟨_, _, futexWait_run_go (by simpa using hwk) ha hv⟩
  have hl := hi₁.1.waitOff hph hWL hq0 hr
  rcases futexWait_ok hr with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, hv, ⟨hve, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨-, hl'⟩ := hl
    refine h k hk G₁ _ rfl ⟨?_, ?_⟩
    · rw [show gP x = L.set (G₁ 0) .out Heap.empty by rw [hg₁]; rfl]; exact hl'
    · have := U_mem hi₁.2 (m' := { m₁ with current := 0, woken := m₁.woken.erase 0 }) rfl rfl rfl
        rfl rfl hi₁.2.q
      rw [← upd_g hg₁] at this
      exact U_lock0 this rfl (fun h => absurd h (by decide))
  · -- it sleeps: the word is `e`
    simp only [↓reduceIte] at hl ⊢
    refine ⟨?_, ?_⟩
    rotate_left
    · have hl := hi₁.1.spuriousOff hph hq0
      obtain ⟨-, hl'⟩ := hl
      refine h k hk G₁ _ rfl ⟨?_, ?_⟩
      · rw [show gP x = L.set (G₁ 0) .out Heap.empty by rw [hg₁]; rfl]; exact hl'
      · have := U_mem hi₁.2 (m' := { m₁ with current := 0 }) rfl rfl rfl rfl rfl hi₁.2.q
        rw [← upd_g hg₁] at this
        exact U_lock0 this rfl (fun h => absurd h (by decide))
    obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hw.access
    have : ({ m₁ with current := 0 } : Mem).access W.ptr 4 4 = m₁.access W.ptr 4 4 := rfl
    rw [this, ha₀] at ha
    cases ha
    have hU32 : W.Holds m₁ ((Packed.toBits e).setWidth 32) := by
      rw [Word.holds_bytes hb₀, ← hve]; exact hv
    have hq' := hq G₁ m₁ hg₁ hi₁ hU32
    exact ⟨hl, U_mem hi₁.2 rfl rfl rfl rfl rfl hq'⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨-, hl'⟩ := hl
    refine h k hk G₁ _ rfl ⟨?_, ?_⟩
    · rw [show gP x = L.set (G₁ 0) .out Heap.empty by rw [hg₁]; rfl]; exact hl'
    · have := U_mem hi₁.2 (m' := { m₁ with current := 0 }) rfl rfl rfl rfl rfl hi₁.2.q
      rw [← upd_g hg₁] at this
      exact U_lock0 this rfl (fun h => absurd h (by decide))

/-- An op of `main` at a shared word, with `main`'s new place `x'` and the same lock part. -/
theorem inv_mstep {W : Word 32 4} (hW : Wd W) {G : ThreadId → Gh} {m₁ m' : Mem} {a : LG} {x x' : X}
    (hi : proto.inv (upd G 0 (a, x)) m₁) (hw' : W.Ok m') (hop : W.Op 0 m₁ m')
    (hL : L.Inv (upd G 0 (a, x)) m') (hpa : a.part = Heap.empty) (hx : x.ph ≠ .pre)
    (hm : x'.ph.isMain) (hpre : x'.ph ≠ .pre)
    (hS : SOk m' (sN x' (G 1).2)) (hE : EOk m' (eN (G 1).2)) (hV : VOk m' (vL x' (G 1).2))
    (hfl : Flags x' (G 1).2) (hreg : RegHB (upd G 0 (a, x')) m')
    (hsig : eN (G 1).2 = 1 → VClock.le (WS.hist m')[2]!.clock (WE.hist m')[1]!.relClock = true)
    (hseen : x'.ph = .seen → VClock.le (WS.hist m')[2]!.clock (m'.clocks[0]!) = true)
    (hvclk : x'.vw → VClock.le (WV.hist m')[1]!.clock (m'.clocks[0]!) = true)
    (hq : QOk (upd G 0 (a, x')) m')
    (hpc : (G 1).2.ph = .sgp → VClock.le (WS.hist m')[2]!.clock (m'.clocks[1]!) = true) :
    proto.inv (upd G 0 (a, x')) m' :=
  ⟨linv0 hL, U_op hW hi.2 hop hw' (shape_m hi.2.shape hx hm hpre) (parts_m hi.2.parts hpa)
    (by rw [upd_self, upd0_1]; exact hS) (by rw [upd0_1]; exact hE)
    (by rw [upd_self, upd0_1]; exact hV) (by rw [upd_self, upd0_1]; exact hfl) hreg
    (by rw [upd0_1]; exact hsig) (by rw [upd_self]; exact hseen) (by rw [upd_self]; exact hvclk) hq
    (by rw [upd0_1]; exact hpc)⟩

/-- The producer is before its `ready = true` if `main` read `ready = false`. -/
theorem early_of {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (hrd : rdyOf (G 1).2 = false) :
    (G 1).2.ph.rank ≤ 3 ∧ (G 1).2.cw = false ∧ eN (G 1).2 = 0 := by
  obtain ⟨-, hc⟩ := hi.2.shape
  have hfl := hi.2.flags
  rcases hc with ⟨-, h0, h1⟩ | ⟨-, -, -, -, hp, -⟩
  · have := h1 1 (Nat.le_refl _); change (G 1).2 = {} at this
    rw [this]; exact ⟨by decide, rfl, rfl⟩
  · have hr : (G 1).2.ph.rank ≤ 3 := by
      unfold rdyOf at hrd; rw [hp] at hrd; simp at hrd; omega
    have hc : (G 1).2.cw = false := by
      cases e : (G 1).2.cw
      · rfl
      · have := hfl.pcw e; omega
    exact ⟨hr, hc, by simp [eN, hc]⟩

/-- `RegHB` after a step that keeps write 1 of the state, the mutex's newest message and the
ghost values, and makes no clock smaller. -/
theorem RegHB.mono {G : ThreadId → Gh} {m m' : Mem} (h : RegHB G m)
    (hs : (WS.hist m')[1]! = (WS.hist m)[1]!)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) : RegHB G m' := by
  intro hcw
  obtain ⟨h1, h2⟩ := h hcw
  rw [hs]
  refine ⟨fun hr => ?_, fun hr => VClock.le_trans (h2 hr) (hcl 1)⟩
  rcases h1 hr with ⟨hh, hle⟩ | hb | hle
  · exact .inl ⟨hh, VClock.le_trans hle (hcl 0)⟩
  · exact .inr (.inl (hbef _ hb))
  · exact .inr (.inr (VClock.le_trans hle (hcl 1)))

theorem before_op {W : Word 32 4} {t : ThreadId} {m m' : Mem} (hop : W.Op t m m') (hap : Word.Apart L W)
    {c : VClock} (h : L.Before m c) : L.Before m' c := by
  obtain ⟨i, l, hl, hle⟩ := h
  have hne : L.b ≠ W.b ∨ L.o ≠ W.o := by
    rcases hap with h | h | h
    · exact .inl h
    · exact .inr (by omega)
    · exact .inr (by omega)
  exact ⟨i, l, (hop.locs.same L.b L.o hne i l).mpr hl, hle⟩

theorem inv_load {W : Word 32 4} (hW : Wd W) {G : ThreadId → Gh} {m₁ m' : Mem} {t : ThreadId}
    (hi : proto.inv G m₁) (hw' : W.Ok m') (hop : W.Op t m₁ m')
    (hL : L.Inv G m') (hh : W.hist m' = W.hist m₁) : proto.inv G m' := by
  have hu := hi.2
  have hk : ∀ W', Wd W' → W'.hist m' = W'.hist m₁ := fun W' hW' => by
    by_cases e : W' = W
    · subst e; exact hh
    · exact hist_op hW hW' e hu hop
  have hS := hk WS (.inl rfl)
  have hE := hk WE (.inr (.inl rfl))
  have hV := hk WV (.inr (.inr rfl))
  refine ⟨hL, U_op hW hu hop hw' hu.shape hu.parts ((sok_congr hS).mpr hu.sh)
    ((eok_congr hE).mpr hu.eh) ((vok_congr hV).mpr hu.vh) hu.flags
    (hu.reg.mono (by rw [hS]) hop.clocks (fun _ h => before_op hop hW.ap h))
    (fun h => by rw [hS, hE]; exact hu.sig h)
    (fun h => by rw [hS]; exact VClock.le_trans (hu.seen h) (hop.clocks 0))
    (fun h => by rw [hV]; exact VClock.le_trans (hu.vclk h) (hop.clocks 0))
    (fun w hw => hu.q w (hop.waiters ▸ hw))
    (fun h => by rw [hS]; exact VClock.le_trans (hu.pc h) (hop.clocks 1))⟩

/-- A load by `main` at a shared word, with the same ghost values. -/
theorem inv_mload {W : Word 32 4} (hW : Wd W) {G : ThreadId → Gh} {m₁ m' : Mem} {g : Gh}
    (hi : proto.inv (upd G 0 g) m₁) (hw' : W.Ok m') (hop : W.Op 0 m₁ m')
    (hL : L.Inv (upd G 0 g) m') (hh : W.hist m' = W.hist m₁) : proto.inv (upd G 0 g) m' := by
  exact inv_load hW hi hw' hop hL hh

/-- A change of `main`'s place on the same memory. -/
theorem inv_mx {G : ThreadId → Gh} {m : Mem} {a : LG} {x x' : X}
    (hi : proto.inv (upd G 0 (a, x)) m) (hx : x.ph ≠ .pre) (hm : x'.ph.isMain) (hpre : x'.ph ≠ .pre)
    (hS : sN x' (G 1).2 = sN x (G 1).2) (hV : vL x' (G 1).2 = vL x (G 1).2)
    (hfl : Flags x' (G 1).2) (hreg : RegHB (upd G 0 (a, x')) m)
    (hseen : x'.ph = .seen → VClock.le (WS.hist m)[2]!.clock (m.clocks[0]!) = true)
    (hvclk : x'.vw → VClock.le (WV.hist m)[1]!.clock (m.clocks[0]!) = true)
    (hq : QOk (upd G 0 (a, x')) m) : proto.inv (upd G 0 (a, x')) m := by
  have hu := hi.2
  refine ⟨linv0 hi.1, U_upd hu (shape_m hu.shape hx hm hpre)
    (parts_m hu.parts (by have := hu.parts 0; rw [upd_self] at this; exact this))
    (by rw [upd_self, upd_self, upd0_1, upd0_1, hS]) (by rw [upd0_1, upd0_1])
    (by rw [upd_self, upd_self, upd0_1, upd0_1, hV]) (by rw [upd_self, upd0_1]; exact hfl) hreg
    (by rw [upd_self]; exact hseen) (by rw [upd_self]; exact hvclk) hq
    (by rw [upd0_1]; exact fun h => by have := hu.pc; rw [upd0_1] at this; exact this h)⟩

/-- If `main` is not `away`, each thread in the futex queue waits at the mutex. -/
theorem qok_out {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (h0 : L.ph (G 0) ≠ .away) :
    ∀ w ∈ m.waiters, w.2 = L.ptr := by
  intro w hw
  refine Classical.byContradiction fun hne => ?_
  have h1 := qok_main hi.2.q hw hne
  rcases hi.1.fq w hw with ⟨h, -⟩ | ⟨-, h⟩
  · exact hne h
  · rw [h1] at h; exact h0 h

theorem qok_of {G G' : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (h0 : L.ph (G 0) ≠ .away) :
    QOk G' m := fun w hw => .inl (qok_out hi h0 w hw)

/-- `main`'s load of the epoch (acquire) at `wt`: it read 0 (it stays), or 1 (it goes to `seen`). -/
theorem inv_seen {G : ThreadId → Gh} {m₁ m' : Mem} {j : Nat} {v : BitVec 32}
    (hi : proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m₁) (hw' : WE.Ok m') (hop : WE.Op 0 m₁ m')
    (hL : L.Inv (upd G 0 (gP { ph := .wt, cw := true })) m') (hh : WE.hist m' = WE.hist m₁)
    (hj : j < (WE.hist m₁).size) (hv : (WE.hist m₁)[j]!.Val v)
    (hacq : VClock.le (WE.hist m₁)[j]!.relClock (m'.clocks[0]!) = true) :
    (v = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m') ∨
      (v = 1 ∧ proto.inv (upd G 0 (gP { ph := .seen, cw := true })) m') := by
  have hi' := inv_mload (.inr (.inl rfl)) hi hw' hop hL hh
  have hu := hi.2
  obtain ⟨hsz, hval⟩ := hu.eh
  rw [upd0_1] at hsz hval
  have hfl := hu.flags
  rw [upd_self, upd0_1] at hfl
  cases e : eN (G 1).2
  · rw [e] at hsz
    have hj0 : j = 0 := by omega
    subst hj0
    exact .inl ⟨val_eq hv (hval 0 (Nat.zero_le _)), hi'⟩
  · rename_i n
    have hn : n = 0 := by unfold eN at e; split at e <;> simp at e; omega
    subst hn
    rw [e] at hsz hval
    have hc1 : (G 1).2.cw = true ∧ 8 ≤ (G 1).2.ph.rank := by
      unfold eN at e; split at e
      · rename_i h; simpa using h
      · cases e
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact .inl ⟨val_eq hv (hval 0 (by omega)), hi'⟩
    refine .inr ⟨val_eq hv (hval 1 (Nat.le_refl _)), inv_mx hi' (by decide) rfl (by decide)
      (by simp [sN, gP, Ph.post]) (by simp [vL, gP]) ?_ ?_ (fun _ => ?_) (fun h => by cases h)
      (qok_of hi' (by rw [upd_self]; decide))⟩
    · exact ⟨hfl.sig, ⟨fun _ => .inr (.inr (.inl rfl)), fun _ => rfl⟩, fun _ _ => hc1.1, hfl.pcw,
        hfl.pcw', (fun h => by cases h), (fun h => by cases h), hfl.pvw,
        (fun h => by have := hfl.setw h; simp [gP] at this), (fun _ _ => hc1.1), hfl.pfin,
        (fun _ => rfl)⟩
    · intro _
      refine ⟨fun hr => ?_, fun hr => ?_⟩ <;> rw [upd0_1] at hr
      · omega
      · rcases hr with h | h <;> rw [h] at hc1 <;> simp [Ph.rank] at hc1
    · -- the producer's signal happened before the new epoch, which `main` read with an acquire
      have hsig := hi'.2.sig (by rw [upd0_1]; exact e)
      rw [hh] at hsig
      exact VClock.le_trans hsig hacq

/-- The state's writes are `sv 0 .. sv n` with `n ≤ 3`: write `k` has the value `0x10001` iff
`k = 2`. -/
theorem sv_two {k : Nat} (hk : k ≤ 3) (h : sv k = 0x10001) : k = 2 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> first | rfl | cases h

theorem bits_take : Packed.toBits (Io_Condition_State.mk
    ((Packed.ofBits (sv 2) : Io_Condition_State).waiters - 1)
    ((Packed.ofBits (sv 2) : Io_Condition_State).signals - 1)) = sv 3 := by decide +kernel

theorem bits_sv2 : Packed.toBits (Packed.ofBits (sv 2) : Io_Condition_State) = sv 2 := by decide +kernel

/-- `main` at `wt` or `seen`: the producer signalled if the state's newest write is `(1, 1)`. -/
theorem sig_of {G : ThreadId → Gh} {m : Mem} {x : X} (hi : proto.inv (upd G 0 (gP x)) m)
    (hx : x.cw = true) (hp : x.ph.post = false) (hv : (last (WS.hist m)).Val (sv 2)) :
    (WS.hist m).size = 3 ∧ (G 1).2.cw = true := by
  obtain ⟨hsz, hval⟩ := hi.2.sh
  rw [upd_self, upd0_1] at hsz hval
  have hN : sN (gP x).2 (G 1).2 ≤ 2 := by
    simp only [sN, gP, hx, hp]; cases (G 1).2.cw <;> simp
  have := val_eq hv (by
    rw [show last (WS.hist m) = (WS.hist m)[sN (gP x).2 (G 1).2]! by simp [last, hsz]]
    exact hval _ (Nat.le_refl _))
  have h2 := sv_two (by omega) this.symm
  refine ⟨by omega, ?_⟩
  cases e : (G 1).2.cw
  · simp [sN, gP, hx, hp, e] at h2
  · rfl

/-- `main` takes the signal: its `cmpxchg((1, 1) → (0, 0))` (acquire) at `wt` or `seen`. It goes
to `cons`. -/
theorem inv_cons {G : ThreadId → Gh} {m₁ m' : Mem} {x : X} (hx : x.ph = .wt ∨ x.ph = .seen)
    (hcw : x.cw = true) (hvw : x.vw = false)
    (hi : proto.inv (upd G 0 (gP x)) m₁) (hw' : WS.Ok m') (hop : WS.Op 0 m₁ m')
    (hL : L.Inv (upd G 0 (gP x)) m') (hv : (last (WS.hist m₁)).Val (sv 2))
    (hh : WS.hist m' = (WS.hist m₁).push (Word.rmwEnt m' 0 .acquire (last (WS.hist m₁)) (sv 3))) :
    proto.inv (upd G 0 (gP { ph := .cons, cw := true })) m' := by
  have hpo : x.ph.post = false := by rcases hx with h | h <;> rw [h] <;> rfl
  obtain ⟨hsz, hc1⟩ := sig_of hi hcw hpo hv
  have hu := hi.2
  have hfl := hu.flags
  rw [upd_self, upd0_1] at hfl
  have hr7 := hfl.pcw hc1
  have hE := hist_op (.inl rfl) (.inr (.inl rfl)) (by decide) hu hop
  have hV := hist_op (.inl rfl) (.inr (.inr rfl)) (by decide) hu hop
  have h2 : (WS.hist m')[2]! = (WS.hist m₁)[2]! := by rw [hh, get_push_lt (by omega)]
  obtain ⟨-, hval⟩ := hu.sh
  rw [upd_self, upd0_1] at hval
  have hxp : x.ph ≠ .pre := by rcases hx with h | h <;> rw [h] <;> decide
  refine inv_mstep (.inl rfl) hi hw' hop hL rfl hxp rfl (by decide) ⟨?_, fun k hk => ?_⟩ ?_ ?_ ?_
    (fun _ => ⟨fun h => by rw [upd0_1] at h; omega, fun h => by
      rw [upd0_1] at h; rcases h with h | h <;> rw [h] at hr7 <;> simp [Ph.rank] at hr7⟩)
    (fun h => ?_) (fun h => by cases h) (fun h => by cases h)
    (fun w hw => .inl (qok_out hi (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.away)) w
      (hop.waiters ▸ hw))) (fun h => ?_)
  · rw [hh]; simp [sN, hc1, hsz, Ph.post]
  · have hk3 : k ≤ 3 := by simpa [sN, hc1, Ph.post] using hk
    rcases (by omega : k < 3 ∨ k = 3) with hlt | rfl
    · rw [hh, get_push_lt (by omega)]
      exact hval k (by simp [sN, gP, hcw, hpo, hc1]; omega)
    · rw [hh, get_push_eq' hsz.symm]; exact rmwEnt_val
  · rw [eok_congr hE]; have := hu.eh; rw [upd0_1] at this; exact this
  · rw [vok_congr hV]; have := hu.vh; rw [upd_self, upd0_1] at this; simpa [vL, gP, hvw] using this
  · exact ⟨fun _ => rfl, ⟨fun _ => .inr (.inr (.inr ⟨rfl, rfl⟩)), fun _ => rfl⟩, fun _ _ => hc1,
      hfl.pcw, hfl.pcw', (fun h => by cases h), (fun h => by cases h), hfl.pvw,
      (fun h => by have := hfl.setw h; simp [gP, hvw] at this), (fun _ _ => hc1), hfl.pfin,
      (fun _ => rfl)⟩
  · rw [h2, hE]; exact hu.sig (by rw [upd0_1]; exact h)
  · rw [h2]; exact VClock.le_trans (by have := hu.pc; rw [upd0_1] at this; exact this h) (hop.clocks 1)

/-- At `seen`, `main`'s `cmpxchg` does not fail. -/
theorem seen_noFail {G : ThreadId → Gh} {m : Mem} {j : Nat} {b : BitVec 32}
    (hi : proto.inv (upd G 0 (gP { ph := .seen, cw := true })) m) (hne : b ≠ sv 2)
    (hj : j < (WS.hist m).size) (hv : (WS.hist m)[j]!.Val b)
    (hfl : Word.Floor (WS.hist m) (m.clocks[0]!) j) : False := by
  have hu := hi.2
  have hf := hu.flags
  rw [upd_self, upd0_1] at hf
  have hc1 := hf.cons rfl (.inr rfl)
  obtain ⟨hsz, hval⟩ := hu.sh
  rw [upd_self, upd0_1] at hsz hval
  have hN : sN (gP { ph := .seen, cw := true }).2 (G 1).2 = 2 := by simp [sN, gP, hc1, Ph.post]
  rw [hN] at hsz hval
  have hseen := hu.seen (by rw [upd_self]; rfl)
  have := hfl 2 (by omega) hseen
  have hj2 : j = 2 := by omega
  subst hj2
  exact hne (val_eq hv (hval 2 (Nat.le_refl _)))

/-- `main`'s load of the epoch at `run`, while it holds the mutex and read `ready = false`: it
reads 0 and goes to `ep`. -/
theorem inv_ep {G : ThreadId → Gh} {m₁ m' : Mem} {hL : Heap} {j : Nat} {v : BitVec 32}
    (hi : proto.inv (upd G 0 (gH { ph := .run } hL)) m₁) (hrd : rdyOf (G 1).2 = false)
    (hw' : WE.Ok m') (hop : WE.Op 0 m₁ m') (hL' : L.Inv (upd G 0 (gH { ph := .run } hL)) m')
    (hh : WE.hist m' = WE.hist m₁) (hj : j < (WE.hist m₁).size) (hv : (WE.hist m₁)[j]!.Val v) :
    v = 0 ∧ proto.inv (upd G 0 (gH { ph := .ep } hL)) m' := by
  have hu := hi.2
  obtain ⟨hr3, hc1, he0⟩ := early_of hi (by rw [upd0_1]; exact hrd)
  rw [upd0_1] at hr3 hc1 he0
  have hfl := hu.flags
  rw [upd_self, upd0_1] at hfl
  have hv1 : (G 1).2.vw = false := by
    cases e : (G 1).2.vw
    · rfl
    · rcases hfl.pvw.mp e with h | ⟨h, -⟩ <;> rw [h] at hr3 <;> simp [Ph.rank] at hr3
  obtain ⟨hsz, hval⟩ := hu.eh
  rw [upd0_1, he0] at hsz hval
  have hj0 : j = 0 := by omega
  subst hj0
  have hS := hist_op (.inr (.inl rfl)) (.inl rfl) (by decide) hu hop
  have hV := hist_op (.inr (.inl rfl)) (.inr (.inr rfl)) (by decide) hu hop
  refine ⟨val_eq hv (hval 0 (Nat.le_refl _)), inv_mstep (.inr (.inl rfl)) hi hw' hop hL' rfl
    (by decide) rfl (by decide) ?_ ?_ ?_ ?_ ?_ (fun h => ?_) (fun h => by cases h)
    (fun h => by cases h) ?_ (fun h => ?_)⟩
  · rw [sok_congr hS]; have := hu.sh; rw [upd_self, upd0_1] at this; simpa [sN, gH] using this
  · rw [eok_congr hh]; have := hu.eh; rw [upd0_1] at this; exact this
  · rw [vok_congr hV]; have := hu.vh; rw [upd_self, upd0_1] at this; simpa [vL, gH] using this
  · exact ⟨(fun h => by rw [hc1] at h; cases h), (by simp), (fun h => by cases h),
      hfl.pcw, hfl.pcw', (fun h => by cases h), (fun h => by cases h), hfl.pvw,
      (fun h => by rw [h] at hr3; simp [Ph.rank] at hr3), (fun h => by cases h), hfl.pfin,
      (fun h => by rw [h] at hr3; simp [Ph.rank] at hr3)⟩
  · intro h; simp [gH] at h
  · rw [he0] at h; cases h
  · intro w hw
    rw [hop.waiters] at hw
    rcases hu.q w hw with h | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩
    · exact .inl h
    · rw [upd_self] at h3; cases h3
    · rw [upd_self] at h3; cases h3
  · rw [h] at hr3; simp [Ph.rank] at hr3

theorem bits_one : RmwOp.add.apply false (0 : BitVec 32)
    (Packed.toBits (Packed.ofBits (1 : BitVec 32) : Io_Condition_State)) = sv 1 := by decide +kernel

/-- `main`'s `waiters += 1` at `ep` (relaxed), while it holds the mutex: it goes to `reg`. -/
theorem inv_reg {G : ThreadId → Gh} {m₁ m' : Mem} {hL : Heap} {old : BitVec 32}
    (hi : proto.inv (upd G 0 (gH { ph := .ep } hL)) m₁) (hrd : rdyOf (G 1).2 = false)
    (hw' : WS.Ok m') (hop : WS.Op 0 m₁ m') (hL' : L.Inv (upd G 0 (gH { ph := .ep } hL)) m')
    (hv : (last (WS.hist m₁)).Val old)
    (hh : WS.hist m' = (WS.hist m₁).push (Word.rmwEnt m' 0 .relaxed (last (WS.hist m₁))
      (RmwOp.add.apply false old
        (Packed.toBits (Packed.ofBits (1 : BitVec 32) : Io_Condition_State))))) :
    old = 0 ∧ proto.inv (upd G 0 (gH { ph := .reg, cw := true } hL)) m' := by
  have hu := hi.2
  obtain ⟨hr3, hc1, he0⟩ := early_of hi (by rw [upd0_1]; exact hrd)
  rw [upd0_1] at hr3 hc1 he0
  have hfl := hu.flags
  rw [upd_self, upd0_1] at hfl
  obtain ⟨hsz, hval⟩ := hu.sh
  rw [upd_self, upd0_1] at hsz hval
  have hN : sN (gH { ph := .ep } hL).2 (G 1).2 = 0 := by simp [sN, gH, hc1]
  rw [hN] at hsz hval
  have h0 : old = 0 := val_eq hv (by
    rw [show last (WS.hist m₁) = (WS.hist m₁)[0]! by simp [last, hsz]]; exact hval 0 (Nat.le_refl _))
  subst h0
  have hE := hist_op (.inl rfl) (.inr (.inl rfl)) (by decide) hu hop
  have hV := hist_op (.inl rfl) (.inr (.inr rfl)) (by decide) hu hop
  have hlast : (WS.hist m')[1]! = Word.rmwEnt m' 0 .relaxed (last (WS.hist m₁)) (sv 1) := by
    rw [hh, get_push_eq' hsz.symm, bits_one]
  refine ⟨rfl, inv_mstep (.inl rfl) hi hw' hop hL' rfl (by decide) rfl (by decide) ⟨?_, fun k hk => ?_⟩
    ?_ ?_ ?_ (fun hcw => ⟨fun _ => .inl ⟨by rw [upd_self]; rfl, ?_⟩, fun h => ?_⟩) (fun h => ?_)
    (fun h => by cases h) (fun h => by cases h) ?_ (fun h => ?_)⟩
  · rw [hh]; simp [sN, hc1, hsz, Ph.post]
  · have hk1 : k ≤ 1 := by simpa [sN, gH, hc1, Ph.post] using hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [hh, get_push_lt (by omega)]; exact hval 0 (Nat.le_refl _)
    · rw [hlast]; exact rmwEnt_val
  · rw [eok_congr hE]; have := hu.eh; rw [upd0_1] at this; exact this
  · rw [vok_congr hV]; have := hu.vh; rw [upd_self, upd0_1] at this; simpa [vL, gH] using this
  · exact ⟨(fun h => by simp [hc1] at h), ⟨fun _ => .inl rfl, fun _ => rfl⟩,
      (fun _ h => absurd h (by decide)),
      hfl.pcw, hfl.pcw', (fun h => by cases h), (fun h => by cases h), hfl.pvw,
      (fun h => by rw [h] at hr3; simp [Ph.rank] at hr3), (fun _ h => by omega), hfl.pfin,
      (fun _ => rfl)⟩
  · rw [hlast]; exact VClock.le_refl _
  · rw [upd0_1] at h
    rcases h with h | h <;> rw [h] at hr3 <;> simp [Ph.rank] at hr3
  · rw [he0] at h; cases h
  · intro w hw
    rw [hop.waiters] at hw
    rcases hu.q w hw with h | ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩
    · exact .inl h
    · rw [upd_self] at h3; cases h3
    · rw [upd_self] at h3; cases h3
  · rw [h] at hr3; simp [Ph.rank] at hr3

/-! ## `main`'s condition wait -/

theorem main_alive {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) : 0 < m.threads.size :=
  (Array.getElem?_eq_some_iff.mp hi.2.shape.1).1

theorem sub_w : (sub false (Packed.ofBits (sv 2) : Io_Condition_State).waiters (1 : BitVec 16)).run =
    some (.ok ((Packed.ofBits (sv 2) : Io_Condition_State).waiters - 1)) := rfl
theorem sub_s : (sub false (Packed.ofBits (sv 2) : Io_Condition_State).signals (1 : BitVec 16)).run =
    some (.ok ((Packed.ofBits (sv 2) : Io_Condition_State).signals - 1)) := rfl
theorem dbg_true : (debug_assert true).run = some (.ok ()) := rfl

/-- A read of the state by `main` at `wt` or `seen`: write `j ≤ 2`; at `seen`, write 2. -/
theorem state_read {G : ThreadId → Gh} {m : Mem} {x : X} {j : Nat} {b : BitVec 32}
    (hi : proto.inv (upd G 0 (gP x)) m) (hcw : x.cw = true) (hp : x.ph.post = false)
    (hj : j < (WS.hist m).size) (hv : (WS.hist m)[j]!.Val b) :
    j ≤ 2 ∧ b = sv j ∧ (x.ph = .seen → Word.Floor (WS.hist m) (m.clocks[0]!) j → j = 2) := by
  obtain ⟨hsz, hval⟩ := hi.2.sh
  rw [upd_self, upd0_1] at hsz hval
  have hN : sN (gP x).2 (G 1).2 ≤ 2 := by
    simp only [sN, gP, hcw, hp]; cases (G 1).2.cw <;> simp
  refine ⟨by omega, val_eq hv (hval j (by omega)), fun hs hfl => ?_⟩
  have hf := hi.2.flags
  rw [upd_self, upd0_1] at hf
  have hc1 := hf.cons hcw (.inr hs)
  have hN2 : sN (gP x).2 (G 1).2 = 2 := by simp [sN, gP, hcw, hp, hc1]
  have := hfl 2 (by omega) (hi.2.seen (by rw [upd_self]; exact hs))
  omega

/-- `main` sleeps at the epoch only while it is 0: the producer has not done its wake. -/
theorem wt_sleep {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (hg : G 0 = gA { ph := .wt, cw := true }) (hU : WE.Holds m 0) : (G 1).2.ph.rank < 9 := by
  have hf := hi.2.flags
  rw [hg] at hf
  obtain ⟨hsz, hval⟩ := hi.2.eh
  have hl := (hi.2.we.holds_last).mp hU
  have h0 : eN (G 1).2 = 0 := by
    have := val_eq hl (by rw [hsz]; exact hval _ (by simp))
    simp only [Nat.add_sub_cancel] at this
    cases e : eN (G 1).2 with
    | zero => rfl
    | succ n =>
      rw [e] at this
      have hn : n = 0 := by unfold eN at e; split at e <;> simp at e; omega
      subst hn; cases this
  refine Nat.lt_of_not_le fun h9 => ?_
  have hc := hf.late rfl (by omega)
  simp [eN, hc] at h0; omega

theorem sig_pos {k : Nat} (hk : k ≤ 3)
    (h : gt false (Packed.ofBits (sv k) : Io_Condition_State).signals 0 = true) : k = 2 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)


/-- `main` holds the mutex with the resource `hL`, in which `ready` is `false`: the producer has
not stored `ready = true`. -/
theorem rdy_now {G : ThreadId → Gh} {m : Mem} {x : X} {hL : Heap} {Y : ThreadId → X}
    (hi : proto.inv G m) (hg : G 0 = gH x hL) (hR : R Y hL) (hY : rdyOf (Y 1) = false) :
    rdyOf (G 1).2 = false := by
  have hres := hi.1.res 0 (by rw [hg]; rfl)
  rw [show L.held (G 0) = hL by rw [hg]; rfl] at hres
  have := R_rdy (Y := fun u => (G u).2) hres hR
  rw [← hY]; exact this

theorem reg_x0 {G : ThreadId → Gh} {m : Mem} {a : LG} {x x' : X} (h : RegHB (upd G 0 (a, x)) m)
    (hc : x'.cw = x.cw) : RegHB (upd G 0 (a, x')) m := by
  intro hcw
  rw [upd_self] at hcw
  obtain ⟨h1, h2⟩ := h (by rw [upd_self]; rw [← hc]; exact hcw)
  rw [upd0_1] at h1 h2 ⊢
  refine ⟨fun hr => ?_, h2⟩
  rcases h1 hr with ⟨hh, hle⟩ | hb | hle
  · exact .inl ⟨by rw [upd_self] at hh ⊢; exact hh, hle⟩
  · exact .inr (.inl hb)
  · exact .inr (.inr hle)

theorem lt_w : lt false (Packed.ofBits (0 : BitVec 32) : Io_Condition_State).waiters (65535 : BitVec 16) =
    true := by decide +kernel

-- `Condition.waitUncancelable` per translation (`ZigLean.VersionGate`): Zig 0.16.0 calls
-- `waitInner(…, true)`, whose loops also hold the cancelable path; Zig 0.17.0 inlines the
-- uncancelable loops (`loop22`, `loop45`). Each proves `condWait_spec_v*`; `condWait_spec` is the
-- version-neutral statement.
when_defined Io_Condition_waitInner

/-- The inner loop's invariant: `main` at `wt` with epoch 0 and the state value it read, or at
`seen` with epoch 1 and `(1, 1)`. -/
def inv56 (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = 0 ∧
  ((s.epoch = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m ∧
      ∃ k ≤ 3, s.prev_state = Packed.ofBits (sv k)) ∨
    (s.epoch = 1 ∧ proto.inv (upd G 0 (gP { ph := .seen, cw := true })) m ∧
      s.prev_state = Packed.ofBits (sv 2)))

/-- The inner loop ends with `main` at `wt` (no signal to take), or holding the mutex at `cons`. -/
def post56 (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = 0 ∧
  ((r.1 = .br55 ∧ r.2.epoch = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m) ∨
    (r.1 = .ret (.ok ()) ∧ ∃ hL, proto.inv (upd G 0 (gH { ph := .cons, cw := true } hL)) m))

theorem loop56_body (D : Nat) (io : Io) (s : Io_Condition_waitInnerLocals) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (h : inv56 D s G m d) :
    proto.WP 0 ((Io_Condition_waitInner.loop56 (bPtr.add 20) io (bPtr.add 16)).run s) (fun r G' m' d' =>
      if Io_Condition_waitInner.again56 r.1 then inv56 D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
      else post56 D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, hcase⟩ := h
  -- the cases: a signal to take, or none (at `wt`)
  have key : (ps = Packed.ofBits (sv 2) ∧ ∃ x : X, (x.ph = .wt ∨ x.ph = .seen) ∧ x.cw = true ∧
        x.vw = false ∧ proto.inv (upd G 0 (gP x)) m ∧ (x.ph = .wt → ep = 0) ∧
        (x.ph = .seen → ep = 1)) ∨
      (gt false ps.signals 0 = false ∧ ep = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m) := by
    rcases hcase with ⟨he, hi, k, hk, hp⟩ | ⟨he, hi, hp⟩ <;> simp only at he hp
    · cases hg : gt false ps.signals 0
      · exact .inr ⟨rfl, he, hi⟩
      · rw [hp] at hg
        have := sig_pos hk hg
        subst this
        exact .inl ⟨hp, _, .inl rfl, rfl, rfl, hi, (fun _ => he), (fun h => by cases h)⟩
    · exact .inl ⟨hp, _, .inr rfl, rfl, rfl, hi, (fun h => by cases h), (fun _ => he)⟩
  unfold Io_Condition_waitInner.loop56
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_pure]
  simp only [pure_bind]
  rcases key with ⟨rfl, x, hx, hcw, hvw, hi, hxw, hxs⟩ | ⟨hg, rfl, hi⟩
  · rw [if_pos (by decide)]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_w] at he; cases he) fun a ha => ?_))
    have ha' : a = (Packed.ofBits (sv 2) : Io_Condition_State).waiters - 1 := by
      change (sub false _ 1).run = _ at ha; rw [sub_w] at ha; cases ha; rfl
    subst ha'
    refine WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_s] at he; cases he) fun b hb => ?_)
    have hb' : b = (Packed.ofBits (sv 2) : Io_Condition_State).signals - 1 := by
      change (sub false _ 1).run = _ at hb; rw [sub_s] at hb; cases hb; rfl
    subst hb'
    dsimp only
    rw [show bPtr.add 20 = WS.ptr from rfl]
    refine WP.bind (WP.bind (wp_weakCasAs (.inl rfl) (g := gP x) hi (fun _ _ _ hi₁ => main_alive hi₁)
      (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL =>
        ⟨fun hv hU hh hacq => ?_, fun j b r hd hj hv hfl hacq hh => ?_⟩))
    · -- success: `main` takes the signal
      rw [bits_sv2] at hv
      rw [bits_take] at hh
      have hi₂ := inv_cons hx hcw hvw (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop
        (by rw [upd_g hg₁]; exact hL) hv hh
      refine WP.pure' ?_
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_spec fits mptr rfl 0 (gP { ph := .cons, cw := true })
        rfl _ G₁ m' k hi₂)))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL₂, hi₃⟩
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitInner.again56, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hc₂, .inr ⟨rfl, hL₂, hi₃⟩⟩
    · -- failure may keep either the waiting or seen phase.
      have hip : proto.inv (upd G₁ 0 (gP x)) m₁ := by rw [upd_g hg₁]; exact hi₁
      have hi₂ := inv_mload (.inl rfl) hip hw' hop (by rw [upd_g hg₁]; exact hL) hh
      have hp : x.ph.post = false := by rcases hx with h | h <;> rw [h] <;> rfl
      obtain ⟨hj2, hbj, hseen⟩ := state_read hip hcw hp hj hv
      have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
      simp only [StateT.run_pure]
      refine WP.pure' ?_
      simp only [Option.isSome_some, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callRC_ok (v := r) rfl ?_)
      simp only [StateT.run_pure, StateT.run_modify]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitInner.again56, ↓reduceIte]
      refine ⟨⟨by omega, hop.current, ?_⟩, .inl (by omega)⟩
      rcases hx with hwt | hs
      · have hx' : x = { ph := .wt, cw := true } := by
          cases x; simp only at hwt hcw hvw; subst hwt hcw hvw; rfl
        subst hx'
        exact .inl ⟨hxw rfl, hi₂, j, by omega, by rw [hr, hbj]⟩
      · have hx' : x = { ph := .seen, cw := true } := by
          cases x; simp only at hs hcw hvw; subst hs hcw hvw; rfl
        subst hx'
        have hjseen : j = 2 := hseen rfl hfl
        subst hjseen
        exact .inr ⟨hxs rfl, hi₂, by rw [hr, hbj]⟩

  · rw [if_neg (by rw [hg]; simp)]
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Io_Condition_waitInner.again56, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, hc, .inl ⟨rfl, rfl, hi⟩⟩

/-- The outer loop's invariant: `main` at `wt` with epoch 0. -/
def inv23 (D : Nat) (s : Io_Condition_waitInnerLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = 0 ∧ s.epoch = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m

/-- The outer loop ends with `main` holding the mutex at `cons`. -/
def post23 (D : Nat) (r : Io_Condition_waitInnerExit × Io_Condition_waitInnerLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret (.ok ()) ∧ m.current = 0 ∧
    ∃ hL, proto.inv (upd G 0 (gH { ph := .cons, cw := true } hL)) m

theorem loop23_body (D : Nat) (io : Io) (s : Io_Condition_waitInnerLocals) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (h : inv23 D s G m d) :
    proto.WP 0 ((Io_Condition_waitInner.loop23 (bPtr.add 20) io (bPtr.add 16) true).run s)
      (fun r G' m' d' =>
        if Io_Condition_waitInner.again23 r.1 then inv23 D r.2 G' m' d' ∧
          (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitInnerLocals) => 0) s)
        else post23 D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, he, hi⟩ := h
  simp only at he
  subst he
  unfold Io_Condition_waitInner.loop23
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind ?_
  simp only [↓reduceIte]
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind (WP.bind (WP.callMC_ptrProject (projE hi) ?_))
  dsimp only
  rw [show (bPtr.add 20).add 4 = WE.ptr from rfl]
  refine WP.bind (wp_mwait (.inr (.inl rfl)) (by decide) hi (fun G₁ m₁ hg₁ hi₁ hU => ?_)
    fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  · -- it sleeps: `QOk` with `main` at the epoch
    intro w hw
    rcases Array.mem_push.mp hw with hw | rfl
    · exact hi₁.2.q w hw
    · exact .inr (.inl ⟨rfl, rfl, by rw [hg₁]; rfl, wt_sleep hi₁ hg₁ hU⟩)
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  refine WP.bind (WP.callMC_ptrProject (projE hi₁) ?_)
  dsimp only
  rw [show (bPtr.add 20).add 4 = WE.ptr from rfl]
  refine WP.bind (WP.bind (wp_load (.inr (.inl rfl)) (g := gP { ph := .wt, cw := true }) hi₁
    (fun _ _ _ h => main_alive h) fun k₂ hk₂ G₂ m₂ m₃ v j hg₂ hi₂ hj hv hfl hacq hh hw' hop hL => ?_))
  have hcase := inv_seen (G := G₂) (by rw [upd_g hg₂]; exact hi₂) hw' hop (by rw [upd_g hg₂]; exact hL)
    hh hj hv (hacq rfl)
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  rw [show bPtr.add 20 = WS.ptr from rfl]
  -- the state's load, then the inner loop
  obtain ⟨x, hx, hcwx, hvwx, hpx, hi₃⟩ : ∃ x : X, (x.ph = .wt ∧ v = 0 ∨ x.ph = .seen ∧ v = 1) ∧
      x.cw = true ∧ x.vw = false ∧ x.ph.post = false ∧ proto.inv (upd G₂ 0 (gP x)) m₃ := by
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨_, .inl ⟨rfl, rfl⟩, rfl, rfl, rfl, h⟩
    · exact ⟨_, .inr ⟨rfl, rfl⟩, rfl, rfl, rfl, h⟩
  refine WP.bind (WP.bind (WP.bind (wp_loadAs (.inl rfl) (g := gP x) hi₃
    (fun _ _ _ h => main_alive h) (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩)
    fun k₃ hk₃ G₃ m₄ m₅ b r j' hg₃ hi₄ hd hj' hv' hfl' hacq' hh' hw₅ hop₅ hL₅ => ?_)))
  have hi₅ := inv_mload (.inl rfl) (G := G₃) (by rw [upd_g hg₃]; exact hi₄) hw₅ hop₅
    (by rw [upd_g hg₃]; exact hL₅) hh'
  obtain ⟨hj2, hbj, hseen2⟩ := state_read (G := G₃) (by rw [upd_g hg₃]; exact hi₄) hcwx hpx hj' hv'
  have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv56 d) (fun _ => 0) (post56 d) (loop56_body d io) _ G₃
    m₅ k₃ ⟨by omega, hop₅.current, ?_⟩))
  · rintro ⟨e, s'⟩ G₄ m₆ d₄ ⟨hd₄, hc₆, ⟨rfl, hep, hi₆⟩ | ⟨rfl, hL₆, hi₆⟩⟩
    · simp only [StateT.run_pure]
      refine WP.pure' ?_
      dsimp only
      simp only [isNonErr, ↓reduceIte, StateT.run_pure]
      refine WP.pure' (WP.pure' ?_)
      simp only [Io_Condition_waitInner.again23, ↓reduceIte]
      exact ⟨⟨by omega, hc₆, hep, hi₆⟩, .inl (by omega)⟩
    · simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitInner.again23, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, rfl, hc₆, hL₆, hi₆⟩
  · rcases hx with ⟨hwt, rfl⟩ | ⟨hs, rfl⟩
    · have hx' : x = { ph := .wt, cw := true } := by
        cases x; simp only at hwt hcwx hvwx; subst hwt hcwx hvwx; rfl
      subst hx'
      exact .inl ⟨rfl, hi₅, j', by omega, by rw [hr, hbj]⟩
    · have hx' : x = { ph := .seen, cw := true } := by
        cases x; simp only at hs hcwx hvwx; subst hs hcwx hvwx; rfl
      subst hx'
      have := hseen2 rfl hfl'
      subst this
      exact .inr ⟨rfl, hi₅, by rw [hr, hbj]⟩

theorem waitInner_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io) (hL : Heap)
    {Y : ThreadId → X} (hR : R Y hL) (hY : rdyOf (Y 1) = false)
    (hi : proto.inv (upd G 0 (gH { ph := .run } hL)) m) (hc : m.current = 0) :
    proto.WP 0 (Io_Condition_waitInner (bPtr.add 20) io (bPtr.add 16) true) (fun r G' m' d' =>
      d' < d ∧ r = .ok () ∧ m'.current = 0 ∧
        ∃ hL', proto.inv (upd G' 0 (gH { ph := .cons, cw := true } hL')) m') G m d := by
  unfold Io_Condition_waitInner
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  refine WP.bind (WP.callMC_ptrProject (projE hi) ?_)
  dsimp only
  rw [show (bPtr.add 20).add 4 = WE.ptr from rfl]
  refine WP.bind (WP.bind (wp_load (.inr (.inl rfl)) (g := gH { ph := .run } hL) hi
    (fun _ _ _ h => main_alive h) fun k₁ hk₁ G₁ m₁ m₂ v j hg₁ hi₁ hj hv _ _ hh hw' hop hL₁ => ?_))
  have hrd := rdy_now hi₁ hg₁ hR hY
  obtain ⟨rfl, hi₂⟩ := inv_ep (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hrd hw' hop
    (by rw [upd_g hg₁]; exact hL₁) hh hj hv
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  rw [show bPtr.add 20 = WS.ptr from rfl]
  refine WP.bind (WP.bind (WP.bind (wp_rmwAs (.inl rfl) (g := gH { ph := .ep } hL) hi₂
    (fun _ _ _ h => main_alive h) (fun _ _ _ _ b _ => ⟨_, ofBits_cst b⟩)
    fun k₂ hk₂ G₂ m₃ m₄ old r hg₂ hi₃ hd hv₂ _ hh₂ _ hw₂ hop₂ hL₂ => ?_)))
  have hrd₂ := rdy_now hi₃ hg₂ hR hY
  obtain ⟨rfl, hi₄⟩ := inv_reg (G := G₂) (by rw [upd_g hg₂]; exact hi₃) hrd₂ hw₂ hop₂
    (by rw [upd_g hg₂]; exact hL₂) hv₂ hh₂
  have hr : r = Packed.ofBits 0 := by rw [ofBits_cst] at hd; cases hd; rfl
  subst hr
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  rw [lt_w]
  refine WP.bind (WP.callRC_ok dbg_true ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_spec fits mptr rfl 0
    (gH { ph := .reg, cw := true } hL) rfl _ G₂ m₄ k₂ hi₄)))
  rintro _ G₃ m₅ d₃ ⟨hd₃, hc₅, hi₅⟩
  have hi₅' : proto.inv (upd G₃ 0 (gP { ph := .reg, cw := true })) m₅ := hi₅
  have hfl := hi₅'.2.flags
  rw [upd_self, upd0_1] at hfl
  -- `main` goes to the wait loop (`wt`)
  have hi₆ : proto.inv (upd G₃ 0 (gP { ph := .wt, cw := true })) m₅ :=
    inv_mx hi₅' (by decide) rfl (by decide) (by simp [sN, gP, Ph.post]) (by simp [vL, gP])
      ⟨hfl.sig, ⟨fun _ => .inr (.inl rfl), fun _ => rfl⟩, (fun _ h => by cases h <;> contradiction),
        hfl.pcw, hfl.pcw', (fun h => by cases h), (fun h => by cases h), hfl.pvw,
        (fun h => by have := hfl.setw h; simp [gP] at this), hfl.late, hfl.pfin, hfl.sg1⟩
      (reg_x0 hi₅'.2.reg rfl) (fun h => by cases h) (fun h => by cases h)
      (qok_of (G := upd G₃ 0 (gP { ph := .reg, cw := true })) hi₅' (by rw [upd_self]; decide))
  refine WP.mono ?_ (WP.loop _ _ (inv23 d) (fun _ => 0) (post23 d) (loop23_body d io) _ G₃ m₅ d₃
    ⟨by omega, hc₅, rfl, hi₆⟩)
  rintro ⟨e, s'⟩ G₄ m₆ d₄ ⟨hd₄, rfl, hc₆, hL₆, hi₇⟩
  exact WP.pure' ⟨hd₄, rfl, hc₆, hL₆, hi₇⟩

/-- `Condition.waitUncancelable` by `main`, which holds the mutex at `run` and read
`ready = false`: it holds the mutex again at `cons`. -/
theorem condWait_spec_v016 (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io) (hL : Heap)
    {Y : ThreadId → X} (hR : R Y hL) (hY : rdyOf (Y 1) = false)
    (hi : proto.inv (upd G 0 (gH { ph := .run } hL)) m) (hc : m.current = 0) :
    proto.WP 0 (Io_Condition_waitUncancelable (bPtr.add 20) io (bPtr.add 16)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = 0 ∧ ∃ hL', proto.inv (upd G' 0 (gH { ph := .cons, cw := true } hL')) m')
      G m d := by
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  refine WP.bind (WP.callC (WP.mono ?_ (waitInner_spec G m d io hL hR hY hi hc)))
  rintro r G₁ m₁ d₁ ⟨hd₁, rfl, hc₁, hL₁, hi₁⟩
  simp only [StateT.run_pure]
  simp only [pure_bind]
  simp only [isNonErr, ↓reduceIte, StateT.run_pure]
  exact WP.pure' (WP.pure' ⟨hd₁, hc₁, hL₁, hi₁⟩)

end_when

when_defined Io_Condition_waitUncancelable.loop22

/-- The inner loop's invariant: `main` at `wt` with epoch 0 and the state value it read, or at
`seen` with epoch 1 and `(1, 1)`. -/
def inv45 (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = 0 ∧
  ((s.epoch = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m ∧
      ∃ k ≤ 3, s.prev_state = Packed.ofBits (sv k)) ∨
    (s.epoch = 1 ∧ proto.inv (upd G 0 (gP { ph := .seen, cw := true })) m ∧
      s.prev_state = Packed.ofBits (sv 2)))

/-- The inner loop ends with `main` at `wt` (no signal to take), or holding the mutex at `cons`. -/
def post45 (D : Nat) (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ m.current = 0 ∧
  ((r.1 = .br44 ∧ r.2.epoch = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m) ∨
    (r.1 = .ret ∧ ∃ hL, proto.inv (upd G 0 (gH { ph := .cons, cw := true } hL)) m))

theorem loop45_body (D : Nat) (io : Io) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (h : inv45 D s G m d) :
    proto.WP 0 ((Io_Condition_waitUncancelable.loop45 (bPtr.add 20) io (bPtr.add 16)).run s) (fun r G' m' d' =>
      if Io_Condition_waitUncancelable.again45 r.1 then inv45 D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
      else post45 D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, hcase⟩ := h
  -- the cases: a signal to take, or none (at `wt`)
  have key : (ps = Packed.ofBits (sv 2) ∧ ∃ x : X, (x.ph = .wt ∨ x.ph = .seen) ∧ x.cw = true ∧
        x.vw = false ∧ proto.inv (upd G 0 (gP x)) m ∧ (x.ph = .wt → ep = 0) ∧
        (x.ph = .seen → ep = 1)) ∨
      (gt false ps.signals 0 = false ∧ ep = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m) := by
    rcases hcase with ⟨he, hi, k, hk, hp⟩ | ⟨he, hi, hp⟩ <;> simp only at he hp
    · cases hg : gt false ps.signals 0
      · exact .inr ⟨rfl, he, hi⟩
      · rw [hp] at hg
        have := sig_pos hk hg
        subst this
        exact .inl ⟨hp, _, .inl rfl, rfl, rfl, hi, (fun _ => he), (fun h => by cases h)⟩
    · exact .inl ⟨hp, _, .inr rfl, rfl, rfl, hi, (fun h => by cases h), (fun _ => he)⟩
  unfold Io_Condition_waitUncancelable.loop45
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_pure]
  simp only [pure_bind]
  rcases key with ⟨rfl, x, hx, hcw, hvw, hi, hxw, hxs⟩ | ⟨hg, rfl, hi⟩
  · rw [if_pos (by decide)]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_w] at he; cases he) fun a ha => ?_))
    have ha' : a = (Packed.ofBits (sv 2) : Io_Condition_State).waiters - 1 := by
      change (sub false _ 1).run = _ at ha; rw [sub_w] at ha; cases ha; rfl
    subst ha'
    refine WP.bind (WP.callRC (fun e he => by
      change (sub false _ 1).run = _ at he; rw [sub_s] at he; cases he) fun b hb => ?_)
    have hb' : b = (Packed.ofBits (sv 2) : Io_Condition_State).signals - 1 := by
      change (sub false _ 1).run = _ at hb; rw [sub_s] at hb; cases hb; rfl
    subst hb'
    dsimp only
    first
    | rw [show ((bPtr.add 20).add 0).add 0 = WS.ptr from rfl]
    | rw [show (bPtr.add 20 : Ptr) = WS.ptr from rfl]
    refine WP.bind (WP.bind (wp_weakCasAs (.inl rfl) (g := gP x) hi (fun _ _ _ hi₁ => main_alive hi₁)
      (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL =>
        ⟨fun hv hU hh hacq => ?_, fun j b r hd hj hv hfl hacq hh => ?_⟩))
    · -- success: `main` takes the signal
      rw [bits_sv2] at hv
      rw [bits_take] at hh
      have hi₂ := inv_cons hx hcw hvw (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop
        (by rw [upd_g hg₁]; exact hL) hv hh
      refine WP.pure' ?_
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_spec fits mptr rfl 0 (gP { ph := .cons, cw := true })
        rfl _ G₁ m' k hi₂)))
      rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL₂, hi₃⟩
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitUncancelable.again45, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hc₂, .inr ⟨rfl, hL₂, hi₃⟩⟩
    · -- failure may keep either the waiting or seen phase.
      have hip : proto.inv (upd G₁ 0 (gP x)) m₁ := by rw [upd_g hg₁]; exact hi₁
      have hi₂ := inv_mload (.inl rfl) hip hw' hop (by rw [upd_g hg₁]; exact hL) hh
      have hp : x.ph.post = false := by rcases hx with h | h <;> rw [h] <;> rfl
      obtain ⟨hj2, hbj, hseen⟩ := state_read hip hcw hp hj hv
      have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
      simp only [StateT.run_pure]
      refine WP.pure' ?_
      simp only [Option.isSome_some, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.callRC_ok (v := r) rfl ?_)
      simp only [StateT.run_pure, StateT.run_modify]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_waitUncancelable.again45, ↓reduceIte]
      refine ⟨⟨by omega, hop.current, ?_⟩, .inl (by omega)⟩
      rcases hx with hwt | hs
      · have hx' : x = { ph := .wt, cw := true } := by
          cases x; simp only at hwt hcw hvw; subst hwt hcw hvw; rfl
        subst hx'
        exact .inl ⟨hxw rfl, hi₂, j, by omega, by rw [hr, hbj]⟩
      · have hx' : x = { ph := .seen, cw := true } := by
          cases x; simp only at hs hcw hvw; subst hs hcw hvw; rfl
        subst hx'
        have hjseen : j = 2 := hseen rfl hfl
        subst hjseen
        exact .inr ⟨hxs rfl, hi₂, by rw [hr, hbj]⟩

  · rw [if_neg (by rw [hg]; simp)]
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Io_Condition_waitUncancelable.again45, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hD, hc, .inl ⟨rfl, rfl, hi⟩⟩

/-- The outer loop's invariant: `main` at `wt` with epoch 0. -/
def inv22 (D : Nat) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat) :
    Prop :=
  d < D ∧ m.current = 0 ∧ s.epoch = 0 ∧ proto.inv (upd G 0 (gP { ph := .wt, cw := true })) m

/-- The outer loop ends with `main` holding the mutex at `cons`. -/
def post22 (D : Nat) (r : Io_Condition_waitUncancelableExit × Io_Condition_waitUncancelableLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret ∧ m.current = 0 ∧
    ∃ hL, proto.inv (upd G 0 (gH { ph := .cons, cw := true } hL)) m

theorem loop22_body (D : Nat) (io : Io) (s : Io_Condition_waitUncancelableLocals) (G : ThreadId → Gh)
    (m : Mem) (d : Nat) (h : inv22 D s G m d) :
    proto.WP 0 ((Io_Condition_waitUncancelable.loop22 (bPtr.add 20) io (bPtr.add 16)).run s)
      (fun r G' m' d' =>
        if Io_Condition_waitUncancelable.again22 r.1 then inv22 D r.2 G' m' d' ∧
          (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_waitUncancelableLocals) => 0) s)
        else post22 D r G' m' d') G m d := by
  obtain ⟨ep, ps⟩ := s
  obtain ⟨hD, hc, he, hi⟩ := h
  simp only at he
  subst he
  unfold Io_Condition_waitUncancelable.loop22
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
  first
  | rw [show ((bPtr.add 20).add 4).add 0 = WE.ptr from rfl]
  | refine WP.bind (WP.callMC_ptrProject (projE hi) ?_)
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [show (bPtr.add 20).add 4 = WE.ptr from rfl]
  refine WP.bind (wp_mwait (.inr (.inl rfl)) (by decide) hi (fun G₁ m₁ hg₁ hi₁ hU => ?_)
    fun k hk G₁ m₁ hc₁ hi₁ => ?_)
  · -- it sleeps: `QOk` with `main` at the epoch
    intro w hw
    rcases Array.mem_push.mp hw with hw | rfl
    · exact hi₁.2.q w hw
    · exact .inr (.inl ⟨rfl, rfl, by rw [hg₁]; rfl, wt_sleep hi₁ hg₁ hU⟩)
  dsimp only
  -- Zig 0.17.0 forms the epoch pointer again before the load.
  try (refine WP.bind (WP.callMC_ptrProject (projE hi₁) ?_)
       simp only [StateT.run_bind, StateT.run_pure, pure_bind]
       rw [show (bPtr.add 20).add 4 = WE.ptr from rfl])
  refine WP.bind (WP.bind (wp_load (.inr (.inl rfl)) (g := gP { ph := .wt, cw := true }) hi₁
    (fun _ _ _ h => main_alive h) fun k₂ hk₂ G₂ m₂ m₃ v j hg₂ hi₂ hj hv hfl hacq hh hw' hop hL => ?_))
  have hcase := inv_seen (G := G₂) (by rw [upd_g hg₂]; exact hi₂) hw' hop (by rw [upd_g hg₂]; exact hL)
    hh hj hv (hacq rfl)
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  first
  | rw [show ((bPtr.add 20).add 0).add 0 = WS.ptr from rfl]
  | rw [show (bPtr.add 20 : Ptr) = WS.ptr from rfl]
  -- the state's load, then the inner loop
  obtain ⟨x, hx, hcwx, hvwx, hpx, hi₃⟩ : ∃ x : X, (x.ph = .wt ∧ v = 0 ∨ x.ph = .seen ∧ v = 1) ∧
      x.cw = true ∧ x.vw = false ∧ x.ph.post = false ∧ proto.inv (upd G₂ 0 (gP x)) m₃ := by
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨_, .inl ⟨rfl, rfl⟩, rfl, rfl, rfl, h⟩
    · exact ⟨_, .inr ⟨rfl, rfl⟩, rfl, rfl, rfl, h⟩
  refine WP.bind (WP.bind (WP.bind (wp_loadAs (.inl rfl) (g := gP x) hi₃
    (fun _ _ _ h => main_alive h) (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩)
    fun k₃ hk₃ G₃ m₄ m₅ b r j' hg₃ hi₄ hd hj' hv' hfl' hacq' hh' hw₅ hop₅ hL₅ => ?_)))
  have hi₅ := inv_mload (.inl rfl) (G := G₃) (by rw [upd_g hg₃]; exact hi₄) hw₅ hop₅
    (by rw [upd_g hg₃]; exact hL₅) hh'
  obtain ⟨hj2, hbj, hseen2⟩ := state_read (G := G₃) (by rw [upd_g hg₃]; exact hi₄) hcwx hpx hj' hv'
  have hr : r = Packed.ofBits b := by rw [ofBits_cst] at hd; cases hd; rfl
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv45 d) (fun _ => 0) (post45 d) (loop45_body d io) _ G₃
    m₅ k₃ ⟨by omega, hop₅.current, ?_⟩))
  · rintro ⟨e, s'⟩ G₄ m₆ d₄ ⟨hd₄, hc₆, ⟨rfl, hep, hi₆⟩ | ⟨rfl, hL₆, hi₆⟩⟩
    · simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' ?_)
      simp only [Io_Condition_waitUncancelable.again22, ↓reduceIte]
      exact ⟨⟨by omega, hc₆, hep, hi₆⟩, .inl (by omega)⟩
    · simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' ?_)
      simp only [Io_Condition_waitUncancelable.again22, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, rfl, hc₆, hL₆, hi₆⟩
  · rcases hx with ⟨hwt, rfl⟩ | ⟨hs, rfl⟩
    · have hx' : x = { ph := .wt, cw := true } := by
        cases x; simp only at hwt hcwx hvwx; subst hwt hcwx hvwx; rfl
      subst hx'
      exact .inl ⟨rfl, hi₅, j', by omega, by rw [hr, hbj]⟩
    · have hx' : x = { ph := .seen, cw := true } := by
        cases x; simp only at hs hcwx hvwx; subst hs hcwx hvwx; rfl
      subst hx'
      have := hseen2 rfl hfl'
      subst this
      exact .inr ⟨rfl, hi₅, by rw [hr, hbj]⟩

/-- `Condition.waitUncancelable` by `main`, which holds the mutex at `run` and read
`ready = false`: it holds the mutex again at `cons`. -/
theorem condWait_spec_v017 (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io) (hL : Heap)
    {Y : ThreadId → X} (hR : R Y hL) (hY : rdyOf (Y 1) = false)
    (hi : proto.inv (upd G 0 (gH { ph := .run } hL)) m) (hc : m.current = 0) :
    proto.WP 0 (Io_Condition_waitUncancelable (bPtr.add 20) io (bPtr.add 16)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = 0 ∧ ∃ hL', proto.inv (upd G' 0 (gH { ph := .cons, cw := true } hL')) m')
      G m d := by
  unfold Io_Condition_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  first
  | rw [show ((bPtr.add 20).add 4).add 0 = WE.ptr from rfl]
  | refine WP.bind (WP.callMC_ptrProject (projE hi) ?_)
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    rw [show (bPtr.add 20).add 4 = WE.ptr from rfl]
  refine WP.bind (WP.bind (wp_load (.inr (.inl rfl)) (g := gH { ph := .run } hL) hi
    (fun _ _ _ h => main_alive h) fun k₁ hk₁ G₁ m₁ m₂ v j hg₁ hi₁ hj hv _ _ hh hw' hop hL₁ => ?_))
  have hrd := rdy_now hi₁ hg₁ hR hY
  obtain ⟨rfl, hi₂⟩ := inv_ep (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hrd hw' hop
    (by rw [upd_g hg₁]; exact hL₁) hh hj hv
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind, StateT.run_modify]
  simp only [pure_bind]
  first
  | rw [show ((bPtr.add 20).add 0).add 0 = WS.ptr from rfl]
  | rw [show (bPtr.add 20 : Ptr) = WS.ptr from rfl]
  refine WP.bind (WP.bind (WP.bind (wp_rmwAs (.inl rfl) (g := gH { ph := .ep } hL) hi₂
    (fun _ _ _ h => main_alive h) (fun _ _ _ _ b _ => ⟨_, ofBits_cst b⟩)
    fun k₂ hk₂ G₂ m₃ m₄ old r hg₂ hi₃ hd hv₂ _ hh₂ _ hw₂ hop₂ hL₂ => ?_)))
  have hrd₂ := rdy_now hi₃ hg₂ hR hY
  obtain ⟨rfl, hi₄⟩ := inv_reg (G := G₂) (by rw [upd_g hg₂]; exact hi₃) hrd₂ hw₂ hop₂
    (by rw [upd_g hg₂]; exact hL₂) hv₂ hh₂
  have hr : r = Packed.ofBits 0 := by rw [ofBits_cst] at hd; cases hd; rfl
  subst hr
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  rw [lt_w]
  refine WP.bind (WP.callRC_ok dbg_true ?_)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  simp only [StateT.run_bind]
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_spec fits mptr rfl 0
    (gH { ph := .reg, cw := true } hL) rfl _ G₂ m₄ k₂ hi₄)))
  rintro _ G₃ m₅ d₃ ⟨hd₃, hc₅, hi₅⟩
  have hi₅' : proto.inv (upd G₃ 0 (gP { ph := .reg, cw := true })) m₅ := hi₅
  have hfl := hi₅'.2.flags
  rw [upd_self, upd0_1] at hfl
  -- `main` goes to the wait loop (`wt`)
  have hi₆ : proto.inv (upd G₃ 0 (gP { ph := .wt, cw := true })) m₅ :=
    inv_mx hi₅' (by decide) rfl (by decide) (by simp [sN, gP, Ph.post]) (by simp [vL, gP])
      ⟨hfl.sig, ⟨fun _ => .inr (.inl rfl), fun _ => rfl⟩, (fun _ h => by cases h <;> contradiction),
        hfl.pcw, hfl.pcw', (fun h => by cases h), (fun h => by cases h), hfl.pvw,
        (fun h => by have := hfl.setw h; simp [gP] at this), hfl.late, hfl.pfin, hfl.sg1⟩
      (reg_x0 hi₅'.2.reg rfl) (fun h => by cases h) (fun h => by cases h)
      (qok_of (G := upd G₃ 0 (gP { ph := .reg, cw := true })) hi₅' (by rw [upd_self]; decide))
  refine WP.mono ?_ (WP.loop _ _ (inv22 d) (fun _ => 0) (post22 d) (loop22_body d io) _ G₃ m₅ d₃
    ⟨by omega, hc₅, rfl, hi₆⟩)
  rintro ⟨e, s'⟩ G₄ m₆ d₄ ⟨hd₄, rfl, hc₆, hL₆, hi₇⟩
  exact WP.pure' ⟨hd₄, hc₆, hL₆, hi₇⟩

end_when

theorem condWait_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io) (hL : Heap)
    {Y : ThreadId → X} (hR : R Y hL) (hY : rdyOf (Y 1) = false)
    (hi : proto.inv (upd G 0 (gH { ph := .run } hL)) m) (hc : m.current = 0) :
    proto.WP 0 (Io_Condition_waitUncancelable (bPtr.add 20) io (bPtr.add 16)) (fun _ G' m' d' =>
      d' < d ∧ m'.current = 0 ∧ ∃ hL', proto.inv (upd G' 0 (gH { ph := .cons, cw := true } hL')) m')
      G m d := by
  first
  | exact condWait_spec_v016 G m d io hL hR hY hi hc
  | exact condWait_spec_v017 G m d io hL hR hY hi hc

/-! ## `main`'s event wait -/

theorem ofBits_ev0 : (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 0)).run = some (.ok .unset) := rfl
theorem ofBits_ev1 : (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 1)).run = some (.ok .waiting) := rfl
theorem ofBits_ev2 : (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 2)).run = some (.ok .is_set) := rfl
theorem sN_cw {x0 x1 x1' : X} (h : x1'.cw = x1.cw) : sN x0 x1' = sN x0 x1 := by simp [sN, h]

theorem eN_eq {x x' : X} (h : x'.cw = x.cw) (h8 : 8 ≤ x.ph.rank) (h8' : 8 ≤ x'.ph.rank) :
    eN x' = eN x := by
  unfold eN; rw [h]
  have a : decide (8 ≤ x'.ph.rank) = true := by simp; omega
  have b : decide (8 ≤ x.ph.rank) = true := by simp; omega
  rw [a, b]

theorem vok_push {m m' : Mem} {vs : List Nat} {e : Word.Entry} (hv : VOk m vs)
    (hh : WV.hist m' = (WV.hist m).push e) (he : e.Val (BitVec.ofNat 32 2)) : VOk m' (vs ++ [2]) := by
  obtain ⟨hsz, hval⟩ := hv
  refine ⟨by rw [hh]; simp [hsz], fun k hk => ?_⟩
  simp only [List.length_append, List.length_singleton] at hk
  rw [hh]
  rcases (by omega : k < vs.length ∨ k = vs.length) with hlt | rfl
  · rw [get_push_lt (by omega)]
    have := hval k hlt
    rwa [getElem!_pos (vs ++ [2]) k (by simp; omega), List.getElem_append_left hlt,
      ← getElem!_pos vs k hlt]
  · rw [get_push_eq' hsz.symm]
    rw [getElem!_pos (vs ++ [2]) vs.length (by simp), List.getElem_append_right (Nat.le_refl _)]
    simpa using he


/-- The event's writes, for `main` before (`x.vw = false`) or after its `waiting`: write `j` has
the value `vL[j]`. -/
theorem ev_read {G : ThreadId → Gh} {m : Mem} {x : X} {j : Nat} {b : BitVec 32}
    (hi : proto.inv (upd G 0 (gP x)) m) (hj : j < (WV.hist m).size) (hv : (WV.hist m)[j]!.Val b) :
    j < (vL x (G 1).2).length ∧ b = BitVec.ofNat 32 (vL x (G 1).2)[j]! := by
  obtain ⟨hsz, hval⟩ := hi.2.vh
  rw [upd_self, upd0_1] at hsz hval
  simp only [gP] at hsz hval
  exact ⟨by omega, val_eq hv (hval j (by omega))⟩

/-- `main`'s `cmpxchg(unset → waiting)` (acquire) succeeded at `ev0`: it goes to `ev1`. -/
theorem inv_ev1 {G : ThreadId → Gh} {m₁ m' : Mem} {c : Bool}
    (hi : proto.inv (upd G 0 (gP { ph := .ev0, cw := c })) m₁) (hw' : WV.Ok m') (hop : WV.Op 0 m₁ m')
    (hL : L.Inv (upd G 0 (gP { ph := .ev0, cw := c })) m') (hv : (last (WV.hist m₁)).Val (0 : BitVec 32))
    (hh : WV.hist m' = (WV.hist m₁).push (Word.rmwEnt m' 0 .acquire (last (WV.hist m₁)) (1 : BitVec 32))) :
    proto.inv (upd G 0 (gP { ph := .ev1, cw := c, vw := true })) m' := by
  have hu := hi.2
  have hfl := hu.flags
  rw [upd_self, upd0_1] at hfl
  obtain ⟨hsz, hval⟩ := hu.vh
  rw [upd_self, upd0_1] at hsz hval
  -- the newest write is `unset`: the producer did not write `is_set`
  have hv1 : (G 1).2.vw = false := by
    cases e : (G 1).2.vw
    · rfl
    · exfalso
      have hs2 : (WV.hist m₁).size = 2 := by simpa [vL, gP, e] using hsz
      have := val_eq hv (by
        rw [show last (WV.hist m₁) = (WV.hist m₁)[1]! by simp [last, hs2]]
        have := hval 1 (by simp [vL, gP, e])
        simpa [vL, gP, e] using this)
      revert this; decide
  have hs1 : (WV.hist m₁).size = 1 := by simpa [vL, gP, hv1] using hsz
  have hS := hist_op (.inr (.inr rfl)) (.inl rfl) (by decide) hu hop
  have hE := hist_op (.inr (.inr rfl)) (.inr (.inl rfl)) (by decide) hu hop
  have h1 : (WV.hist m')[1]! = Word.rmwEnt m' 0 .acquire (last (WV.hist m₁)) (1 : BitVec 32) := by
    rw [hh, get_push_eq' hs1.symm]
  refine inv_mstep (.inr (.inr rfl)) hi hw' hop hL rfl (by simp) rfl (by simp) ?_ ?_
    ⟨?_, fun k hk => ?_⟩ ?_ ?_ ?_ (fun h => by cases h) (fun _ => ?_)
    (fun w hw => .inl (qok_out hi (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.away)) w
      (hop.waiters ▸ hw))) ?_
  · rw [sok_congr hS]; have := hu.sh; rw [upd_self, upd0_1] at this
    have e : sN { ph := .ev1, cw := c, vw := true } (G 1).2 = sN (gP { ph := .ev0, cw := c }).2 (G 1).2 :=
      by cases c <;> rfl
    rw [e]; exact this
  · rw [eok_congr hE]; have := hu.eh; rw [upd0_1] at this; exact this
  · rw [hh]; simp [vL, gP, hv1, hs1]
  · have hk2 : k < 2 := by simpa [vL, gP, hv1] using hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [hh, get_push_lt (by omega)]
      have := hval 0 (by simp [vL, gP, hv1]); simpa [vL, gP, hv1] using this
    · rw [h1]
      have e : BitVec.ofNat 32 (vL { ph := .ev1, cw := c, vw := true } (G 1).2)[1]! = 1 := by
        simp [vL, hv1]
      rw [e]; exact rmwEnt_val
  · exact ⟨hfl.sig, by simpa [gP, Ph.post] using hfl.mcw, by simpa [gP, Ph.post] using hfl.cons,
      hfl.pcw, hfl.pcw', (fun _ => .inl rfl), (fun _ => rfl), hfl.pvw,
      (fun h => absurd (hfl.pvw.mpr (.inl h)) (by rw [hv1]; decide)), hfl.late, hfl.pfin,
      (fun h => by simpa [gP] using hfl.sg1 h)⟩
  · exact (reg_x0 hu.reg rfl).mono (by rw [hS]) hop.clocks (fun _ h => before_op hop apV h)
  · intro h; rw [hS, hE]; exact hu.sig (by rw [upd0_1]; exact h)
  · rw [h1]; exact VClock.le_refl _
  · intro h; rw [hS]; exact VClock.le_trans (by have := hu.pc; rw [upd0_1] at this; exact this h) (hop.clocks 1)

theorem vL_vals (x0 x1 : X) (j : Nat) (hj : j < (vL x0 x1).length) :
    (vL x0 x1)[j]! = 0 ∨ (vL x0 x1)[j]! = 1 ∨ (vL x0 x1)[j]! = 2 := by
  have hm : (vL x0 x1)[j]! ∈ vL x0 x1 := by
    rw [getElem!_pos (vL x0 x1) j hj]; exact List.getElem_mem hj
  have hall : ∀ v ∈ vL x0 x1, v = 0 ∨ v = 1 ∨ v = 2 := by
    unfold vL; cases x0.vw <;> cases x1.vw <;> simp
  exact hall _ hm

theorem ev_dec {x0 x1 : X} {j : Nat} (hj : j < (vL x0 x1).length) :
    ∃ r, (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 (vL x0 x1)[j]!)).run = some (.ok r) := by
  rcases vL_vals x0 x1 j hj with h | h | h <;> rw [h]
  · exact ⟨_, ofBits_ev0⟩
  · exact ⟨_, ofBits_ev1⟩
  · exact ⟨_, ofBits_ev2⟩

/-- `main` at `evd`: the event wait ended. -/
theorem inv_evd {G : ThreadId → Gh} {m : Mem} {c w : Bool} {x : X}
    (hi : proto.inv (upd G 0 (gP x)) m) (hx : x = { ph := .ev0, cw := c } ∨ x = { ph := .ev1, cw := c, vw := true })
    (hw : w = x.vw) : proto.inv (upd G 0 (gP { ph := .evd, cw := c, vw := w })) m := by
  have hfl := hi.2.flags
  rw [upd_self, upd0_1] at hfl
  have hp : x.ph ≠ .pre := by rcases hx with rfl | rfl <;> simp
  refine inv_mx hi hp rfl (by simp) (by rcases hx with rfl | rfl <;> cases c <;> rfl)
    (by rcases hx with rfl | rfl <;> subst hw <;> rfl) ?_ (reg_x0 hi.2.reg (by rcases hx with rfl | rfl <;> rfl))
    (fun h => by cases h) (fun h => ?_) (qok_of hi (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.away)))
  · rcases hx with rfl | rfl <;> subst hw <;>
      exact ⟨hfl.sig, by simpa [gP, Ph.post] using hfl.mcw, by simpa [gP, Ph.post] using hfl.cons,
        hfl.pcw, hfl.pcw', (fun _ => .inr (.inl rfl)), (fun h => by cases h), hfl.pvw,
        (fun h => by simpa [gP] using hfl.setw h), hfl.late, hfl.pfin,
        (fun h => by simpa [gP] using hfl.sg1 h)⟩
  · rcases hx with rfl | rfl <;> subst hw
    · cases h
    · have := hi.2.vclk; rw [upd_self] at this; exact this rfl

/-- The event loop's invariant: `main` at `ev1`. -/
def inv17 (c : Bool) (D : Nat) (_ : Io_Event_waitUncancelableLocals) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) : Prop :=
  d < D ∧ m.current = 0 ∧ proto.inv (upd G 0 (gP { ph := .ev1, cw := c, vw := true })) m

def post17 (c : Bool) (D : Nat) (r : Io_Event_waitUncancelableExit × Io_Event_waitUncancelableLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) : Prop :=
  d < D ∧ r.1 = .ret ∧ m.current = 0 ∧ proto.inv (upd G 0 (gP { ph := .evd, cw := c, vw := true })) m

theorem loop17_body (c : Bool) (D : Nat) (io : Io) (s : Io_Event_waitUncancelableLocals)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (h : inv17 c D s G m d) :
    proto.WP 0 ((Io_Event_waitUncancelable.loop17 (bPtr.add 28) io).run s) (fun r G' m' d' =>
      if Io_Event_waitUncancelable.again17 r.1 then inv17 c D r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Event_waitUncancelableLocals) => 0) s)
      else post17 c D r G' m' d') G m d := by
  obtain ⟨hD, hc, hi⟩ := h
  unfold Io_Event_waitUncancelable.loop17
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  rw [show bPtr.add 28 = WV.ptr from rfl]
  refine WP.bind (WP.bind (wp_mwait (.inr (.inr rfl)) (by decide) hi (fun G₁ m₁ hg₁ hi₁ hU => ?_)
    fun k hk G₁ m₁ hc₁ hi₁ => ?_))
  · intro w hw
    rcases Array.mem_push.mp hw with hw | rfl
    · exact hi₁.2.q w hw
    refine .inr (.inr ⟨rfl, rfl, by rw [hg₁]; rfl, fun hf => ?_⟩)
    have hv := (hi₁.2.wv.holds_last).mp hU
    obtain ⟨hsz, hval⟩ := hi₁.2.vh
    rw [hg₁] at hsz hval
    have hfl := hi₁.2.flags
    have h1 := hfl.pfin hf
    simp only [vL, gA, h1] at hsz hval
    have := val_eq hv (by rw [hsz]; exact hval 2 (by simp))
    revert this; decide
  simp only [StateT.run_bind]
  refine WP.bind (wp_loadAs (.inr (.inr rfl)) (g := gP { ph := .ev1, cw := c, vw := true }) hi₁
    (fun _ _ _ h => main_alive h) (fun G₂ m₂ hg₂ hi₂ j hj b hv => by
      obtain ⟨hj', rfl⟩ := ev_read (G := G₂) (by rw [upd_g hg₂]; exact hi₂) hj hv
      exact ev_dec hj')
    fun k₂ hk₂ G₂ m₂ m₃ b r j hg₂ hi₂ hd hj hv hfl hacq hh hw' hop hL => ?_)
  have hi₃ := inv_mload (.inr (.inr rfl)) (G := G₂) (by rw [upd_g hg₂]; exact hi₂) hw' hop
    (by rw [upd_g hg₂]; exact hL) hh
  obtain ⟨hj', rfl⟩ := ev_read (G := G₂) (by rw [upd_g hg₂]; exact hi₂) hj hv
  -- `main`'s `waiting` happened before it: it reads `waiting` or `is_set`
  have hj1 : 1 ≤ j := by
    have hvc := hi₂.2.vclk (by rw [hg₂]; rfl)
    obtain ⟨hsz, -⟩ := hi₂.2.vh
    rw [hg₂] at hsz
    have h2 : 1 < (WV.hist m₂).size := by
      rw [hsz]; simp only [vL, gP]; cases (G₂ 1).2.vw <;> simp
    exact hfl 1 h2 hvc
  have hlen := hj'
  simp only [vL] at hlen
  rcases (by cases e : (G₂ 1).2.vw <;> simp [e] at hlen <;> omega : j = 1 ∨ j = 2) with rfl | rfl
  · -- `waiting`: the loop goes on
    have hr : r = .waiting := by
      have : (vL { ph := .ev1, cw := c, vw := true } (G₂ 1).2)[1]! = 1 := by
        simp only [vL]; cases (G₂ 1).2.vw <;> rfl
      rw [this] at hd; rw [ofBits_ev1] at hd; cases hd; rfl
    subst hr
    refine WP.pure' ?_
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Io_Event_waitUncancelable.again17, ↓reduceIte]
    exact ⟨⟨by omega, hop.current, hi₃⟩, .inl (by omega)⟩
  · -- `is_set`: the event wait ends
    have hr : r = .is_set := by
      have h2 : (G₂ 1).2.vw = true := by cases e : (G₂ 1).2.vw <;> simp [e] at hlen; rfl
      have : (vL { ph := .ev1, cw := c, vw := true } (G₂ 1).2)[2]! = 2 := by simp [vL, h2]
      rw [this] at hd; rw [ofBits_ev2] at hd; cases hd; rfl
    subst hr
    refine WP.pure' ?_
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Io_Event_waitUncancelable.again17, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by omega, rfl, hop.current, inv_evd hi₃ (.inr rfl) rfl⟩

/-- `Event.waitUncancelable` by `main` at `ev0`: it ends at `evd`. -/
theorem event_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io) (c : Bool)
    (hi : proto.inv (upd G 0 (gP { ph := .ev0, cw := c })) m) (hc : m.current = 0) :
    proto.WP 0 (Io_Event_waitUncancelable (bPtr.add 28) io) (fun _ G' m' _ => m'.current = 0 ∧
      ∃ w, proto.inv (upd G' 0 (gP { ph := .evd, cw := c, vw := w })) m') G m d := by
  unfold Io_Event_waitUncancelable
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  rw [show bPtr.add 28 = WV.ptr from rfl]
  refine WP.bind (WP.bind (wp_casAs (.inr (.inr rfl)) (g := gP { ph := .ev0, cw := c }) hi
    (fun _ _ _ h => main_alive h) (fun G₁ m₁ hg₁ hi₁ j hj b hv => by
      obtain ⟨hj', rfl⟩ := ev_read (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hj hv
      exact ev_dec hj') fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL =>
        ⟨fun hv hU hh hacq => ?_, fun j b r hne hd hj hv hfl hacq hh => ?_⟩))
  · -- success: `main` wrote `waiting`; the loop
    have hi₂ := inv_ev1 (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop (by rw [upd_g hg₁]; exact hL)
      hv hh
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    refine WP.pure' ?_
    dsimp only
    refine WP.mono ?_ (WP.loop _ _ (inv17 c d) (fun _ => 0) (post17 c d) (loop17_body c d io) _ G₁
      m' k ⟨by omega, hop.current, hi₂⟩)
    rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨-, rfl, hc₂, hi₃⟩
    exact WP.pure' ⟨hc₂, true, hi₃⟩
  · -- failure: the event was set
    have hi₂ := inv_mload (.inr (.inr rfl)) (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop
      (by rw [upd_g hg₁]; exact hL) hh
    obtain ⟨hj', rfl⟩ := ev_read (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hj hv
    have hj2 : (vL { ph := .ev0, cw := c } (G₁ 1).2)[j]! = 2 := by
      rcases vL_vals _ _ j hj' with h | h | h
      · exact absurd (by rw [h]; rfl) hne
      · exfalso; have hlen := hj'
        simp only [vL] at hlen h
        cases e : (G₁ 1).2.vw <;> simp [e] at hlen h
        · subst hlen; simp at h
        · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp at h
      · exact h
    rw [hj2, ofBits_ev2] at hd
    cases hd
    simp only [StateT.run_pure]
    refine WP.pure' ?_
    simp only [Option.isSome_some, ↓reduceIte]
    repeat (first | exact ⟨hop.current, false, inv_evd hi₂ (.inl rfl) rfl⟩ | refine WP.pure' ?_ |
      simp only [StateT.run_pure])

/-! ## `main`'s body -/

/-- A step of `main` on the resource `hL` that it holds (`TTriple Pa x Qa`), with the same place:
after it `main` holds `hQ`. -/
theorem wp_mres {α σ : Type} {x : MemM α} {s : σ} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {x0 : X} {hL : Heap} {Pa : Assn} {Qa : α → Assn} (ht : TTriple Pa x Qa)
    (hi : proto.inv (upd G 0 (gH x0 hL)) m) (hc : m.current = 0)
    (hp : R (fun u => (upd G 0 (gH x0 hL) u).2) hL → Pa hL)
    (hq : ∀ a hQ, Qa a hQ → R (fun u => (upd G 0 (gH x0 hQ) u).2) hQ)
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ a m' hQ, m'.current = 0 → m'.threads = m.threads → Qa a hQ →
      proto.inv (upd G 0 (gH x0 hQ)) m' → Q (a, s) G m' d) :
    proto.WP 0 ((liftM x : CM Tgt σ α).run s) Q G m d := by
  have hh : L.ph (upd G 0 (gH x0 hL) 0) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht0, hjt⟩ := hi.1.live 0 (by rw [hh]; decide)
  have hres : R (fun u => (upd G 0 (gH x0 hL) u).2) hL := by
    have := hi.1.res 0 hh
    rwa [show L.held (upd G 0 (gH x0 hL) 0) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G 0 (gH x0 hL)) m 0 = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned ht hi.1.own hc ht0 (by rw [hown]; exact hp hres)
    fun a m' hQ hr ho' hq₀ hs hm' hd => ?_
  have hQe : L.part (gH x0 hQ) ∪ L.held (gH x0 hQ) = hQ := Heap.empty_union hQ
  rw [hown] at hs hm' hd
  have hl := hi.1.stepIn (g := gH x0 hQ) hc hjt (by rw [hQe]; exact ho')
    (by rw [hown]; exact hs) (by rw [hown, hQe]; exact hm') (by rw [hown, hQe]; exact hd)
    (by rw [upd_self]; rfl) (Heap.disjoint_empty _ |>.symm) (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G 0 (gH x0 hL)) 0 (gH x0 hQ) u).2) hQ
      rw [upd_upd]; exact hq a hQ hq₀)
  rw [upd_upd] at hl
  have hu := U_stepIn hi (by rw [hown]; exact hs) (by rw [hown]; exact hm') (by rw [hown]; exact hd)
  exact h a m' hQ (hs.current.trans hc) hs.threads hq₀ ⟨hl, U_lock0 hu rfl (fun _ => rfl)⟩

/-- `main`'s place while it holds the mutex in its `ready` loop: `run`, or `cons` after the
condition wait. -/
def RunX (x : X) : Prop := x = { ph := .run } ∨ x = { ph := .cons, cw := true }

/-- The `ready` loop's invariant: `main` holds the mutex. -/
def inv24 (s : handoffLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  s.b = bPtr ∧ m.current = 0 ∧ ∃ x hL, RunX x ∧ proto.inv (upd G 0 (gH x hL)) m

/-- The `ready` loop ends: `main` read `ready = true`. -/
def post24 (r : handoffExit × handoffLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  r.1 = .br23 ∧ r.2.b = bPtr ∧ m.current = 0 ∧ ∃ x hL, RunX x ∧
    proto.inv (upd G 0 (gH x hL)) m ∧ ∃ Y, R Y hL ∧ rdyOf (Y 1) = true

theorem loop24_body (io : Io) (s : handoffLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv24 s G m d) :
    proto.WP 0 ((handoff.loop24 io bPtr).run s) (fun r G' m' d' =>
      if handoff.again24 r.1 then inv24 r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : handoffLocals) => 0) s)
      else post24 r G' m' d') G m d := by
  obtain ⟨hb, hc, x, hL, hx, hi⟩ := h
  unfold handoff.loop24
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  refine WP.bind (WP.bind (WP.callMC_ptrProject (projB hi (k := 36) (by decide)) ?_))
  dsimp only
  refine WP.bind (wp_mres (Qa := fun r => ⌜r = rdyOf ((upd G 0 (gH x hL)) 1).2⌝ ∗ R
      (fun u => (upd G 0 (gH x hL) u).2))
    (((TTriple.load (p := bPtr.add 36) (a := 1) (v := rdyOf ((upd G 0 (gH x hL)) 1).2)
      (by decide)).frameL_eq (R := pts (bPtr.add 32) 4
        (BitVec.ofNat 32 (vOf ((upd G 0 (gH x hL)) 1).2)))))
    hi hc (fun h => h) (fun a hQ h => by
      obtain ⟨-, hR⟩ := sep_lift.mp h
      exact (R_congr (by simp only [upd0_1]) (by simp only [upd0_1]) hQ).mpr hR)
    fun a m' hQ hc' ht' hq hi' => ?_)
  obtain ⟨rfl, hR⟩ := sep_lift.mp hq
  cases hr : rdyOf (upd G 0 (gH x hL) 1).2
  · -- `ready = false`: `main` is at `run`; the condition wait
    have hxr : x = { ph := .run } := by
      rcases hx with rfl | rfl
      · rfl
      · exfalso
        have hf := hi.2.flags
        rw [upd_self, upd0_1] at hf
        have hc1 := hf.cons rfl (.inl rfl)
        have h7 := hf.pcw hc1
        obtain ⟨-, hsh⟩ := hi.2.shape
        rw [upd0_1] at hr
        rcases hsh with ⟨-, h0, -⟩ | ⟨-, -, -, -, hp, -⟩
        · simp only [upd_self] at h0; cases h0
        · simp only [upd0_1] at hp; unfold rdyOf at hr; rw [hp] at hr; simp at hr; omega
    subst hxr
    simp only [Bool.not_false, ↓reduceIte, StateT.run_bind]
    refine WP.bind (WP.callMC_ptrProject (projB hi' (k := 20) (by decide)) ?_)
    refine WP.bind (WP.callMC_ptrProject (projB hi' (k := 16) (by decide)) ?_)
    dsimp only
    refine WP.bind (WP.callC (WP.mono ?_ (condWait_spec G m' d io hQ hR hr hi' hc')))
    rintro _ G₁ m₁ d₁ ⟨hd₁, hc₁, hL₁, hi₁⟩
    simp only [StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [handoff.again24, ↓reduceIte]
    exact ⟨⟨hb, hc₁, _, hL₁, .inr rfl, hi₁⟩, .inl hd₁⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    refine WP.pure' (WP.pure' ?_)
    simp only [handoff.again24, Bool.false_eq_true, ↓reduceIte]
    exact ⟨rfl, hb, hc', x, hQ, hx, hi', _, hR, hr⟩

/-! ## The producer -/


theorem live1 {G : ThreadId → Gh} {m : Mem} {g : Gh} (hi : proto.inv (upd G 1 g) m)
    (hg : g.1.ph ≠ .gone) : 1 < m.threads.size :=
  (hi.1.live 1 (by rw [upd_self]; exact hg)).1

/-- The places and the writes agree, after a change of the producer's place before its signal. -/
theorem Flags.early {x0 x1 x1' : X} (h : Flags x0 x1) (hc : x1.cw = false) (hc' : x1'.cw = false)
    (hv' : x1'.vw = false) (hp : x1'.ph ≠ .sgp ∧ x1'.ph ≠ .wk ∧ x1'.ph ≠ .setw ∧ x1'.ph ≠ .fin)
    (hr7 : x1'.ph.rank < 6) :
    Flags x0 x1' := by
  refine ⟨fun hx => ?_, h.mcw, fun h1 h2 => ?_, fun hx => ?_, fun hx => ?_, h.mvw, h.mvw', ?_,
    fun hx => absurd hx hp.2.2.1, fun h1 h2 => ?_, fun hx => ?_, fun hx => ?_⟩
  · rw [hc'] at hx; cases hx
  · have := h.cons h1 h2; rw [hc] at this; cases this
  · rw [hc'] at hx; cases hx
  · rcases hx with hx | hx
    · exact absurd hx hp.1
    · exact absurd hx hp.2.1
  · rw [hv']
    simp only [Bool.false_eq_true, false_iff, not_or, and_false, not_false_eq_true, and_true]
    exact hp.2.2.1
  · exact absurd h2 (by have := hr7; omega)
  · exact absurd hx hp.2.2.2
  · rw [hx] at hr7; simp [Ph.rank] at hr7

/-- `RegHB` after a change of the producer's place before its `ready = true`. -/
theorem RegHB.early {G : ThreadId → Gh} {m : Mem} {g g' : Gh} (h : RegHB (upd G 1 g) m)
    (hr : g.2.ph.rank ≤ 3) (hr' : g'.2.ph.rank ≤ 3) : RegHB (upd G 1 g') m := by
  intro hcw
  rw [upd1_0] at hcw
  obtain ⟨h1, -⟩ := h (by rw [upd1_0]; exact hcw)
  have hr'' : ¬ (g'.2.ph = .rdy ∨ g'.2.ph = .sg1) := by
    rintro (h | h) <;> rw [h] at hr' <;> simp [Ph.rank] at hr'
  refine ⟨fun _ => ?_, fun hx => absurd (by rw [upd_self] at hx; exact hx) hr''⟩
  have := h1 (by rw [upd_self]; exact hr)
  rw [upd1_0] at this ⊢; exact this

/-- `QOk` after a change of the producer's place. -/
theorem QOk.p {G : ThreadId → Gh} {m : Mem} {g g' : Gh} (h : QOk (upd G 1 g) m)
    (hr : g.2.ph.rank < 9 → g'.2.ph.rank < 9) (hf : g'.2.ph = .fin → g.2.ph = .fin) :
    QOk (upd G 1 g') m := by
  intro w hw
  rcases h w hw with h' | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact .inl h'
  · rw [upd1_0] at h3; rw [upd_self] at h4
    exact .inr (.inl ⟨h1, h2, by rw [upd1_0]; exact h3, by rw [upd_self]; exact hr h4⟩)
  · rw [upd1_0] at h3; rw [upd_self] at h4
    exact .inr (.inr ⟨h1, h2, by rw [upd1_0]; exact h3, by
      rw [upd_self]; exact fun hx => h4 (hf hx)⟩)

/-- A step of the producer on the resource `hL` that it holds (`TTriple Pa x Qa`): after it the
producer is at `xb` and holds `hQ`. -/
theorem wp_pstep {α σ : Type} {x : MemM α} {s : σ} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {xa xb : X} {hL : Heap} {Pa : Assn} {Qa : α → Assn} (ht : TTriple Pa x Qa)
    (hi : proto.inv (upd G 1 (gH xa hL)) m) (hc : m.current = 1)
    (hp : R (fun u => (upd G 1 (gH xa hL) u).2) hL → Pa hL)
    (hq : ∀ a hQ, Qa a hQ → R (fun u => (upd G 1 (gH xb hQ) u).2) hQ)
    (hpa : xa.ph.isProd) (hpr : xb.ph.isProd) (hcw : xb.cw = xa.cw) (hvw : xb.vw = xa.vw)
    (heN : eN xb = eN xa) (hfl : Flags (G 0).2 xb)
    (hreg : ∀ m' hQ, L.Inv (upd G 1 (gH xb hQ)) m' → RegHB (upd G 1 (gH xa hL)) m' →
      RegHB (upd G 1 (gH xb hQ)) m')
    (hqk : ∀ m' hQ, QOk (upd G 1 (gH xa hL)) m' → QOk (upd G 1 (gH xb hQ)) m')
    (hxb : xb.ph ≠ .sgp)
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ a m' hQ, m'.current = 1 → m'.threads = m.threads → Qa a hQ →
      proto.inv (upd G 1 (gH xb hQ)) m' → Q (a, s) G m' d) :
    proto.WP 1 ((liftM x : CM Tgt σ α).run s) Q G m d := by
  have hh : L.ph (upd G 1 (gH xa hL) 1) = .holds := by rw [upd_self]; rfl
  obtain ⟨ht1, hjt⟩ := hi.1.live 1 (by rw [hh]; decide)
  have hres : R (fun u => (upd G 1 (gH xa hL) u).2) hL := by
    have := hi.1.res 1 hh
    rwa [show L.held (upd G 1 (gH xa hL) 1) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G 1 (gH xa hL)) m 1 = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned ht hi.1.own hc ht1 (by rw [hown]; exact hp hres)
    fun a m' hQ hr ho' hq₀ hs hm' hd => ?_
  have hQe : L.part (gH xb hQ) ∪ L.held (gH xb hQ) = hQ := Heap.empty_union hQ
  rw [hown] at hs hm' hd
  have hl := hi.1.stepIn (g := gH xb hQ) hc hjt (by rw [hQe]; exact ho')
    (by rw [hown]; exact hs) (by rw [hown, hQe]; exact hm') (by rw [hown, hQe]; exact hd)
    (by rw [upd_self]; rfl) (Heap.disjoint_empty _ |>.symm) (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G 1 (gH xa hL)) 1 (gH xb hQ) u).2) hQ
      rw [upd_upd]; exact hq a hQ hq₀)
  rw [upd_upd] at hl
  have hu := U_stepIn hi (by rw [hown]; exact hs) (by rw [hown]; exact hm') (by rw [hown]; exact hd)
  refine h a m' hQ (hs.current.trans hc) hs.threads hq₀ ⟨hl, U_upd hu
    (shape_p hu.shape hpa hpr) (parts_p hu.parts rfl) ?_ ?_ ?_
    (by rw [upd1_0, upd_self]; exact hfl) (hreg m' hQ hl hu.reg)
    (fun h => hu.seen (by rw [upd1_0] at h ⊢; exact h))
    (fun h => hu.vclk (by rw [upd1_0] at h ⊢; exact h)) (hqk m' hQ hu.q)
    (fun h => absurd (by rw [upd_self] at h; exact h) hxb)⟩
  · simp only [upd1_0, upd_self, sN, gH, hcw]
  · simp only [upd_self, gH, heN]
  · simp only [upd1_0, upd_self, vL, gH, hvw]

/-- The state `(waiters, signals)`. -/
def cst (w s : Nat) : Io_Condition_State := ⟨BitVec.ofNat 16 w, BitVec.ofNat 16 s⟩

/-- A thread's lock part with the same `v` and `ready`: the lock's invariant stays. -/
theorem linv_x {G : ThreadId → Gh} {m : Mem} {a : LG} {x x' : X} (hL : L.Inv (upd G 1 (a, x)) m)
    (hv : vOf x' = vOf x) (hr : rdyOf x' = rdyOf x) : L.Inv (upd G 1 (a, x')) m :=
  hL.congr (fun u => by unfold upd; split <;> rfl) (fun u => by unfold upd; split <;> rfl)
    (fun u => by unfold upd; split <;> rfl) fun h => by
      change R (fun u => (upd G 1 (a, x') u).2) h ↔ R (fun u => (upd G 1 (a, x) u).2) h
      exact R_congr (by simp only [upd_self]; exact hv) (by simp only [upd_self]; exact hr) h


theorem ht1 {g : Gh} (hg : g.1.ph ≠ .gone) :
    ∀ G₁ m₁, G₁ 1 = g → proto.inv G₁ m₁ → 1 < m₁.threads.size := fun G₁ m₁ hg₁ hi₁ =>
  live1 (G := G₁) (g := g) (by rw [upd_g hg₁]; exact hi₁) hg

/-- The producer's `cmpxchg` (`(1, 0) → (1, 1)`, release): it goes to `sgp`. -/
theorem inv_sgp {G : ThreadId → Gh} {m₁ m' : Mem}
    (hi : proto.inv (upd G 1 (gP { ph := .sg1 })) m₁) (hw' : WS.Ok m') (hop : WS.Op 1 m₁ m')
    (hL : L.Inv (upd G 1 (gP { ph := .sg1 })) m')
    (hh : WS.hist m' = (WS.hist m₁).push (Word.rmwEnt m' 1 .release (last (WS.hist m₁)) (sv 2))) :
    proto.inv (upd G 1 (gP { ph := .sgp, cw := true })) m' := by
  have hu := hi.2
  have hfl := hu.flags
  rw [upd1_0, upd_self] at hfl
  have hcw : (G 0).2.cw := hfl.sg1 rfl
  have hnp : (G 0).2.ph.post = false := by
    cases e : (G 0).2.ph.post
    · rfl
    · have := hfl.cons hcw (.inl e); simp [gP] at this
  have hS := hu.sh
  rw [upd1_0, upd_self] at hS
  obtain ⟨hsz, hval⟩ := hS
  have hN : sN (G 0).2 (gP { ph := .sg1 }).2 = 1 := by simp [sN, gP, hcw, hnp]
  rw [hN] at hsz hval
  refine ⟨linv_x hL rfl rfl, U_op (.inl rfl) hu hop hw' (shape_p hu.shape rfl rfl)
    (parts_p hu.parts rfl) ⟨?_, fun k hk => ?_⟩ ?_ ?_ ?_ ?_ (fun h => ?_) (fun h => ?_)
    (fun h => ?_) ?_ ?_⟩
  · rw [hh]; simp [upd1_0, sN, gP, hcw, hnp, hsz]
  · rw [hh]
    have hN2 : sN (upd G 1 (gP { ph := .sgp, cw := true }) 0).2
        (upd G 1 (gP { ph := .sgp, cw := true }) 1).2 = 2 := by
      simp [upd1_0, sN, gP, hcw, hnp]
    rw [hN2] at hk
    rcases (by omega : k < 2 ∨ k = 2) with hk' | rfl
    · rw [get_push_lt (by omega)]; exact hval k (by omega)
    · rw [get_push_eq' (by omega)]; exact rmwEnt_val
  · rw [eok_congr (hist_op (.inl rfl) (.inr (.inl rfl)) (by decide) hu hop)]
    have := hu.eh; rw [upd_self] at this ⊢; simpa [eN, gP, Ph.rank] using this
  · rw [vok_congr (hist_op (.inl rfl) (.inr (.inr rfl)) (by decide) hu hop)]
    have := hu.vh; rw [upd1_0, upd_self] at this ⊢; simpa [vL, gP] using this
  · rw [upd1_0, upd_self]
    exact ⟨fun _ => hcw, hfl.mcw, fun _ _ => rfl, fun _ => by simp [gP, Ph.rank],
      fun _ => rfl, hfl.mvw, hfl.mvw', by simp [gP], (fun h => by cases h),
      fun _ _ => rfl, (fun h => by cases h), (fun h => by cases h)⟩
  · intro hc0
    refine ⟨fun hr => ?_, fun hr => ?_⟩ <;> rw [upd_self] at hr <;> simp [gP, Ph.rank] at hr
  · rw [upd_self] at h; simp [eN, gP, Ph.rank] at h
  · rw [upd1_0] at h; have := hfl.cons hcw (.inr h); simp [gP] at this
  · rw [upd1_0] at h
    rw [hist_op (.inl rfl) (.inr (.inr rfl)) (by decide) hu hop]
    exact VClock.le_trans (by have := hu.vclk; rw [upd1_0] at this; exact this h) (hop.clocks 0)
  · intro w hw
    rw [hop.waiters] at hw
    rcases hu.q w hw with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact .inl h
    · rw [upd1_0] at h3; rw [upd_self] at h4
      exact .inr (.inl ⟨h1, h2, by rw [upd1_0]; exact h3, by rw [upd_self]; simp [gP, Ph.rank]⟩)
    · rw [upd1_0] at h3
      exact .inr (.inr ⟨h1, h2, by rw [upd1_0]; exact h3, by rw [upd_self]; simp [gP]⟩)
  · intro _
    have hsz2 : (WS.hist m₁).size = 2 := by omega
    rw [hh, get_push_eq' (by omega)]; exact VClock.le_refl _

/-- The producer's `epoch += 1` (release): it goes to `wk`. -/
theorem inv_wk {G : ThreadId → Gh} {m₁ m' : Mem} {old : BitVec 32}
    (hi : proto.inv (upd G 1 (gP { ph := .sgp, cw := true })) m₁) (hw' : WE.Ok m') (hop : WE.Op 1 m₁ m')
    (hL : L.Inv (upd G 1 (gP { ph := .sgp, cw := true })) m') (hv : (last (WE.hist m₁)).Val old)
    (hh : WE.hist m' = (WE.hist m₁).push
      (Word.rmwEnt m' 1 .release (last (WE.hist m₁)) (RmwOp.add.apply false old 1))) :
    proto.inv (upd G 1 (gP { ph := .wk, cw := true })) m' := by
  have hu := hi.2
  have hfl := hu.flags
  rw [upd1_0, upd_self] at hfl
  obtain ⟨hsz, hval⟩ := hu.eh
  have hN : eN (upd G 1 (gP { ph := .sgp, cw := true }) 1).2 = 0 := by
    simp [upd_self, eN, gP, Ph.rank]
  rw [hN] at hsz hval
  have hlast : last (WE.hist m₁) = (WE.hist m₁)[0]! := by simp [last, hsz]
  have h0 : old = 0 := by rw [hlast] at hv; exact val_eq hv (hval 0 (Nat.le_refl _))
  subst h0
  have hS := hist_op (.inr (.inl rfl)) (.inl rfl) (by decide) hu hop
  refine ⟨linv_x hL rfl rfl, U_op (.inr (.inl rfl)) hu hop hw' (shape_p hu.shape rfl rfl)
    (parts_p hu.parts rfl) ?_ ⟨?_, fun k hk => ?_⟩ ?_ ?_ ?_ (fun h => ?_) (fun h => ?_)
    (fun h => ?_) ?_ ?_⟩
  · rw [sok_congr hS]; have := hu.sh; rw [upd1_0, upd_self] at this ⊢; simpa [sN, gP] using this
  · rw [hh]; simp [upd_self, eN, gP, Ph.rank, hsz]
  · rw [hh]
    have hN1 : eN (upd G 1 (gP { ph := .wk, cw := true }) 1).2 = 1 := by
      simp [upd_self, eN, gP, Ph.rank]
    rw [hN1] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [get_push_lt (by omega)]; exact hval 0 (Nat.le_refl _)
    · rw [get_push_eq' (by omega), show BitVec.ofNat 32 1 = RmwOp.add.apply false (0 : BitVec 32) 1
        by decide]; exact rmwEnt_val
  · rw [vok_congr (hist_op (.inr (.inl rfl)) (.inr (.inr rfl)) (by decide) hu hop)]
    have := hu.vh; rw [upd1_0, upd_self] at this ⊢; simpa [vL, gP] using this
  · rw [upd1_0, upd_self]
    exact ⟨fun _ => hfl.sig rfl, hfl.mcw, fun h1 h2 => rfl, fun _ => by simp [gP, Ph.rank],
      fun _ => rfl, hfl.mvw, hfl.mvw', by simp [gP], (fun h => by cases h),
      fun _ _ => rfl, (fun h => by cases h), (fun h => by cases h)⟩
  · intro hc0
    refine ⟨fun hr => ?_, fun hr => ?_⟩ <;> rw [upd_self] at hr <;> simp [gP, Ph.rank] at hr
  · -- the signal happened before the new epoch's release clock
    rw [hS, hh, get_push_eq' (by omega)]
    have hpc := hu.pc (by rw [upd_self]; rfl)
    simp only [Word.rmwEnt, AtomicOrder.isRel, ↓reduceIte]
    exact VClock.le_trans hpc (VClock.le_trans (hop.clocks 1) (VClock.le_merge_right _ _))
  · rw [hS]; rw [upd1_0] at h
    exact VClock.le_trans (by have := hu.seen; rw [upd1_0] at this; exact this h) (hop.clocks 0)
  · rw [upd1_0] at h
    rw [hist_op (.inr (.inl rfl)) (.inr (.inr rfl)) (by decide) hu hop]
    exact VClock.le_trans (by have := hu.vclk; rw [upd1_0] at this; exact this h) (hop.clocks 0)
  · intro w hw
    rw [hop.waiters] at hw
    rcases hu.q w hw with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact .inl h
    · rw [upd1_0] at h3
      exact .inr (.inl ⟨h1, h2, by rw [upd1_0]; exact h3, by rw [upd_self]; simp [gP, Ph.rank]⟩)
    · rw [upd1_0] at h3
      exact .inr (.inr ⟨h1, h2, by rw [upd1_0]; exact h3, by rw [upd_self]; simp [gP]⟩)
  · intro h; rw [upd_self] at h; cases h

/-- After a futex wake of `n ≥ 1` at a shared word, no thread waits at it. -/
theorem wake_w {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {W : Word 32 4} {n : Nat} (hq : QOk G m)
    (hW : W.ptr ≠ L.ptr) (hn : 1 ≤ n)
    (h : ((Thread.futexWake W.ptr n).run { m with current := t }).run = some (.ok ((), m'))) :
    m'.current = t ∧ m'.threads = m.threads ∧ (∀ w ∈ m'.waiters, w ∈ m.waiters ∧ w.2 ≠ W.ptr) ∧
      m' = { m with current := t, waiters := m'.waiters, woken := m'.woken } := by
  have hm' := Proto.modify_ok h
  generalize hwk : ((m.waiters.filter (·.2 == W.ptr)).extract 0 n).map (·.1) = woke at hm'
  subst hm'
  refine ⟨rfl, rfl, fun w hw => ?_, rfl⟩
  have hw' := Array.mem_filter.mp hw
  refine ⟨hw'.1, fun he => ?_⟩
  have hw0 : w.1 = 0 := qok_main hq hw'.1 (by rw [he]; exact hW)
  have hmem : w ∈ m.waiters.filter (·.2 == W.ptr) := Array.mem_filter.mpr ⟨hw'.1, by simp [he]⟩
  have hpos : 0 < (m.waiters.filter (·.2 == W.ptr)).size := Array.size_pos_of_mem hmem
  obtain ⟨w0, hw0f, hin⟩ : ∃ w0, w0 ∈ m.waiters.filter (·.2 == W.ptr) ∧ w0.1 ∈ woke :=
    ⟨_, Array.getElem_mem hpos, by
      rw [← hwk]
      exact Array.mem_map.mpr ⟨_, Array.mem_extract_iff_getElem.mpr ⟨0, by simp; omega, rfl⟩, rfl⟩⟩
  have hw0m := Array.mem_filter.mp hw0f
  have hw00 : w0.1 = 0 := qok_main hq hw0m.1 (by
    have : w0.2 = W.ptr := by simpa using hw0m.2
    rw [this]; exact hW)
  have := hw'.2
  simp only [Bool.not_eq_true'] at this
  rw [hw0, ← hw00, Array.contains_iff_mem.mpr hin] at this
  cases this

/-- The producer's futex wake at the epoch: it goes to `set`. -/
theorem inv_set {G : ThreadId → Gh} {m₁ m' : Mem}
    (hi : proto.inv (upd G 1 (gP { ph := .wk, cw := true })) m₁)
    (h : ((Thread.futexWake WE.ptr 1).run { m₁ with current := 1 }).run = some (.ok ((), m'))) :
    proto.inv (upd G 1 (gP { ph := .set, cw := true })) m' := by
  have hu := hi.2
  obtain ⟨hc', ht', hws, hm'⟩ := wake_w hu.q (by decide) (Nat.le_refl _) h
  have hL := hi.1.wakeOff (by decide) h
  have hk : ∀ W : Word 32 4, W.Keep m₁ m' := fun W => by
    rw [hm']; exact Word.keep_same m₁ 1 m₁.seen m₁.nextMsg _ _ m₁.groups
  have hfl := hu.flags
  rw [upd1_0, upd_self] at hfl
  have hcl : ∀ u : Nat, VClock.le (m₁.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hm']; exact VClock.le_refl _
  have hu' : U (upd G 1 (gP { ph := .wk, cw := true })) m' :=
    U_keep hu (hk WS) (hk WE) (hk WV) ht' (fun w hw => by
      obtain ⟨hw', -⟩ := hws w hw; exact hu.q w hw') hcl
      (fun _ h => before_same (by rw [hm']) h) (by rw [hm']; exact hu.io) (by rw [hm']; exact hu.blk)
  refine ⟨linv_x hL rfl rfl, U_upd hu' (shape_p hu'.shape rfl rfl) (parts_p hu'.parts rfl)
    (by simp [upd1_0, upd_self, sN, gP]) (by simp [upd_self, eN, gP, Ph.rank])
    (by simp [upd1_0, upd_self, vL, gP]) ?_ ?_ (fun h => hu'.seen (by rw [upd1_0] at h ⊢; exact h))
    (fun h => hu'.vclk (by rw [upd1_0] at h ⊢; exact h)) (fun w hw => ?_)
    (fun h => by rw [upd_self] at h; cases h)⟩
  · rw [upd1_0, upd_self]
    exact ⟨fun _ => hfl.sig rfl, hfl.mcw, fun _ _ => rfl, fun _ => by simp [gP, Ph.rank],
      (fun h => by rcases h with h | h <;> cases h), hfl.mvw, hfl.mvw', by simp [gP],
      (fun h => by cases h), fun _ _ => rfl, (fun h => by cases h), (fun h => by cases h)⟩
  · intro hc0
    refine ⟨fun hr => ?_, fun hr => ?_⟩ <;> rw [upd_self] at hr <;> simp [gP, Ph.rank] at hr
  · obtain ⟨hw', hne⟩ := hws w hw
    rcases hu.q w hw' with h | ⟨-, h2, -⟩ | ⟨h1, h2, h3, -⟩
    · exact .inl h
    · exact absurd h2 hne
    · rw [upd1_0] at h3
      exact .inr (.inr ⟨h1, h2, by rw [upd1_0]; exact h3, by rw [upd_self]; simp [gP]⟩)

/-- The producer's load of the state at `rdy` (write `j`, the value `b`): it read `(1, 0)` and
goes to `sg1`, or it read `(0, 0)` (`main` did not register) and goes to `set`. -/
theorem inv_sload {G : ThreadId → Gh} {m₁ m' : Mem} {j : Nat} {b : BitVec 32}
    (hi : proto.inv (upd G 1 (gP { ph := .rdy })) m₁) (hw' : WS.Ok m') (hop : WS.Op 1 m₁ m')
    (hL : L.Inv (upd G 1 (gP { ph := .rdy })) m') (hh : WS.hist m' = WS.hist m₁)
    (hj : j < (WS.hist m₁).size) (hv : (WS.hist m₁)[j]!.Val b)
    (hfl : Word.Floor (WS.hist m₁) (m₁.clocks[1]!) j) :
    (b = sv 1 ∧ proto.inv (upd G 1 (gP { ph := .sg1 })) m') ∨
      (b = sv 0 ∧ proto.inv (upd G 1 (gP { ph := .set })) m') := by
  have hu := hi.2
  have hfl0 := hu.flags
  rw [upd1_0, upd_self] at hfl0
  have hnp : (G 0).2.cw → (G 0).2.ph.post = false := fun hcw => by
    cases e : (G 0).2.ph.post
    · rfl
    · have := hfl0.cons hcw (.inl e); simp [gP] at this
  obtain ⟨hsz, hval⟩ := hu.sh
  rw [upd1_0, upd_self] at hsz hval
  have hE := hist_op (.inl rfl) (.inr (.inl rfl)) (by decide) hu hop
  have hV := hist_op (.inl rfl) (.inr (.inr rfl)) (by decide) hu hop
  -- the new place `x'`, with the same `cw`, `vw`
  have key : ∀ x' : X, x'.ph.isProd → 4 ≤ x'.ph.rank → x'.cw = false → x'.vw = false →
      x'.ph ≠ .sgp → x'.ph ≠ .fin → Flags (G 0).2 x' →
      (x'.ph = .rdy ∨ x'.ph = .sg1 ∨ (G 0).2.cw = false) →
      (9 ≤ x'.ph.rank → (G 0).2.ph ≠ .wt) → proto.inv (upd G 1 (gP x')) m' := by
    intro x' hp h4 hc hvw hs hnf hfx hreg' hwt
    refine ⟨linv_x hL ?_ ?_, U_op (.inl rfl) hu hop hw' (shape_p hu.shape rfl hp)
      (parts_p hu.parts rfl) ?_ ?_ ?_ (by rw [upd1_0, upd_self]; exact hfx) ?_ (fun h => ?_)
      (fun h => ?_) (fun h => ?_) ?_ (fun h => ?_)⟩
    · show vOf x' = vOf { ph := .rdy }
      unfold vOf; rw [if_pos ⟨hp, by omega⟩]; rfl
    · show rdyOf x' = rdyOf { ph := .rdy }
      rw [show rdyOf { ph := .rdy } = true from rfl]; unfold rdyOf; simp [hp]; omega
    · rw [sok_congr hh, upd1_0, upd_self]
      have := hu.sh; rw [upd1_0, upd_self] at this; simpa [sN, gP, hc] using this
    · rw [eok_congr hE, upd_self]; have := hu.eh; rw [upd_self] at this
      simpa [eN, gP, hc] using this
    · rw [vok_congr hV, upd1_0, upd_self]; have := hu.vh; rw [upd1_0, upd_self] at this
      simpa [vL, gP, hvw] using this
    · intro hcw
      rw [upd1_0] at hcw
      rw [upd_self, hh]
      have h2 := (hu.reg (by rw [upd1_0]; exact hcw)).2 (by rw [upd_self]; exact .inl rfl)
      refine ⟨fun hr => by simp [gP] at hr; omega, fun _ => VClock.le_trans h2 (hop.clocks 1)⟩
    · rw [upd_self] at h; simp [eN, gP, hc] at h
    · rw [upd1_0] at h; rw [hh]
      exact VClock.le_trans (by have := hu.seen; rw [upd1_0] at this; exact this h) (hop.clocks 0)
    · rw [upd1_0] at h; rw [hV]
      exact VClock.le_trans (by have := hu.vclk; rw [upd1_0] at this; exact this h) (hop.clocks 0)
    · intro w hw
      rw [hop.waiters] at hw
      rcases hu.q w hw with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact .inl h
      · rw [upd1_0] at h3
        refine .inr (.inl ⟨h1, h2, by rw [upd1_0]; exact h3, by
          rw [upd_self]; simp only [gP]
          exact Nat.lt_of_not_le fun h9 => hwt h9 h3⟩)
      · rw [upd1_0] at h3
        exact .inr (.inr ⟨h1, h2, by rw [upd1_0]; exact h3, by
          rw [upd_self]; exact hnf⟩)
    · rw [upd_self] at h; exact absurd h hs
  by_cases hcw : (G 0).2.cw
  · -- `main` registered: the producer reads write 1
    have hN : sN (G 0).2 (gP { ph := .rdy }).2 = 1 := by simp [sN, gP, hcw, hnp hcw]
    rw [hN] at hsz hval
    have h2 := (hu.reg (by rw [upd1_0]; exact hcw)).2 (by rw [upd_self]; exact .inl rfl)
    have hj1 : j = 1 := by have := hfl 1 (by omega) h2; omega
    subst hj1
    refine .inl ⟨val_eq hv (hval 1 (Nat.le_refl _)), key { ph := .sg1 } rfl (by decide) rfl rfl
      (by decide) (by decide) ?_ (.inr (.inl rfl)) (fun h => by simp [Ph.rank] at h)⟩
    exact ⟨(fun h => by cases h), hfl0.mcw,
      (fun h1 h2 => by have := hfl0.cons h1 h2; simp [gP] at this),
      (fun h => by cases h), (fun h => by rcases h with h | h <;> cases h), hfl0.mvw, hfl0.mvw',
      (by simp), (fun h => by cases h), (fun _ h => by simp [Ph.rank] at h),
      (fun h => by cases h), fun _ => hcw⟩
  · -- it did not: the producer reads write 0
    have hcw' : (G 0).2.cw = false := by simpa using hcw
    have hN : sN (G 0).2 (gP { ph := .rdy }).2 = 0 := by simp [sN, gP, hcw']
    rw [hN] at hsz hval
    have hj0 : j = 0 := by omega
    subst hj0
    refine .inr ⟨val_eq hv (hval 0 (Nat.le_refl _)), key { ph := .set } rfl (by decide) rfl rfl
      (by decide) (by decide) ?_ (.inr (.inr hcw')) (fun _ hw => ?_)⟩
    · exact ⟨(fun h => by cases h), hfl0.mcw, (fun h1 => by rw [hcw'] at h1; cases h1),
        (fun h => by cases h), (fun h => by rcases h with h | h <;> cases h), hfl0.mvw, hfl0.mvw',
        (by simp), (fun h => by cases h), (fun h1 => by rw [hcw'] at h1; cases h1),
        (fun h => by cases h), (fun h => by cases h)⟩
    · have := hfl0.mcw.mpr (.inr (.inl hw)); rw [hcw'] at this; cases this

/-- `signal`'s loop invariant: the producer read `(1, 0)` (at `sg1`) or `(0, 0)` (it does not
signal: at `set`). -/
def sInv (s : Io_Condition_signalLocals) (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  m.current = 1 ∧ ((s.prev_state = cst 1 0 ∧ proto.inv (upd G 1 (gP { ph := .sg1 })) m) ∨
    (s.prev_state = cst 0 0 ∧ proto.inv (upd G 1 (gP { ph := .set })) m))

/-- `signal`'s loop ends with the producer at `set`. -/
def sPost (r : Io_Condition_signalExit × Io_Condition_signalLocals) (G : ThreadId → Gh) (m : Mem)
    (_ : Nat) : Prop :=
  (r.1 = .ret ∨ r.1 = .br10) ∧ m.current = 1 ∧ ∃ b, proto.inv (upd G 1 (gP { ph := .set, cw := b })) m

theorem add16 : (add false (cst 1 0).signals (1 : BitVec 16)).run = some (.ok 1) := by
  cases h : (add false (cst 1 0).signals (1 : BitVec 16)).run with
  | none =>
    exact absurd h (by
      simp [add]; split <;> simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure,
        ExceptT.pure, ExceptT.run])
  | some r =>
    cases r with
    | error e => exact absurd h (add_one_noErr (by decide) e)
    | ok v =>
      have := add_one_ok h (by decide)
      rw [show v = 1 from BitVec.eq_of_toNat_eq (by rw [this]; decide)]

/-- The producer at `sg1`: the state has the writes 0 and 1, and write 1 happened before it. -/
theorem sg1_hist {G : ThreadId → Gh} {m : Mem} (hi : proto.inv (upd G 1 (gP { ph := .sg1 })) m) :
    (WS.hist m).size = 2 ∧ (WS.hist m)[1]!.Val (sv 1) ∧
      VClock.le (WS.hist m)[1]!.clock (m.clocks[1]!) = true := by
  have hu := hi.2
  have hfl := hu.flags
  rw [upd1_0, upd_self] at hfl
  have hcw : (G 0).2.cw := hfl.sg1 rfl
  have hnp : (G 0).2.ph.post = false := by
    cases e : (G 0).2.ph.post
    · rfl
    · have := hfl.cons hcw (.inl e); simp [gP] at this
  obtain ⟨hsz, hval⟩ := hu.sh
  rw [upd1_0, upd_self] at hsz hval
  have hN : sN (G 0).2 (gP { ph := .sg1 }).2 = 1 := by simp [sN, gP, hcw, hnp]
  rw [hN] at hsz hval
  refine ⟨hsz, hval 1 (Nat.le_refl _), ?_⟩
  have := (hu.reg (by rw [upd1_0]; exact hcw)).2 (by rw [upd_self]; exact .inr rfl)
  exact this

theorem bits10 : Packed.toBits (cst 1 0) = sv 1 := by decide +kernel
theorem bits11 : Packed.toBits ({ waiters := (cst 1 0).waiters, signals := 1 } : Io_Condition_State) =
    sv 2 := by decide +kernel

/-- The producer's `cmpxchg` at `sg1` does not fail. -/
theorem sg1_noFail {G : ThreadId → Gh} {m : Mem} {j : Nat} {b : BitVec 32}
    (hi : proto.inv (upd G 1 (gP { ph := .sg1 })) m) (hne : b ≠ sv 1) (hj : j < (WS.hist m).size)
    (hv : (WS.hist m)[j]!.Val b) (hfl : Word.Floor (WS.hist m) (m.clocks[1]!) j) : False := by
  obtain ⟨hsz, h1, hle⟩ := sg1_hist hi
  have := hfl 1 (by omega) hle
  have hj1 : j = 1 := by omega
  subst hj1
  exact hne (val_eq hv h1)

theorem gt10 : gt false (cst 1 0).waiters (cst 1 0).signals = true := rfl
theorem gt00 : ¬ gt false (cst 0 0).waiters (cst 0 0).signals = true := by
  rw [show gt false (cst 0 0).waiters (cst 0 0).signals = false from rfl]; simp

theorem sig_body (io : Io) (s : Io_Condition_signalLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : sInv s G m d) :
    proto.WP 1 ((Io_Condition_signal.loop11 (bPtr.add 20) io).run s) (fun r G' m' d' =>
      if Io_Condition_signal.again11 r.1 then sInv r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 < (fun (_ : Io_Condition_signalLocals) => 0) s)
      else sPost r G' m' d') G m d := by
  obtain ⟨ps⟩ := s
  obtain ⟨hc, ⟨hs, hi⟩ | ⟨hs, hi⟩⟩ := h
  · simp only at hs
    unfold Io_Condition_signal.loop11
    simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    refine WP.bind ?_
    have hg : gt false ps.waiters ps.signals = true := by rw [hs]; exact gt10
    rw [if_pos hg]
    simp only [StateT.run_bind, StateT.run_get]
    simp only [pure_bind]
    refine WP.bind (WP.callRC (fun e he => by
      rw [hs] at he; change (add false (cst 1 0).signals 1).run = _ at he
      rw [add16] at he; cases he) fun v hv => ?_)
    have hv1 : v = 1 := by
      rw [hs] at hv; change (add false (cst 1 0).signals 1).run = _ at hv
      rw [add16] at hv; cases hv; rfl
    subst hv1 hs
    rw [show bPtr.add 20 = WS.ptr from rfl]
    refine WP.bind (wp_weakCasAs (.inl rfl) (g := gP { ph := .sg1 }) hi (ht1 (by simp [gP]))
      (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL =>
        ⟨fun hv hU hh hacq => ?_, fun j b r hd hj hv hfl hacq hh => ?_⟩)
    · have hi₂ := inv_sgp (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop
        (by rw [upd_g hg₁]; exact hL) (by rw [hh, bits11])
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      refine WP.bind (WP.bind (WP.callMC_ptrProject (projWE hi₂) ?_))
      dsimp only
      rw [show WS.ptr.add 4 = WE.ptr from rfl]
      refine WP.bind (wp_rmw (.inr (.inl rfl)) (g := gP { ph := .sgp, cw := true }) hi₂
        (ht1 (by simp [gP])) fun k₂ hk₂ G₂ m₂ m₃ old hg₂ hi₃ hv₃ hU₃ hh₃ hacq₃ hw₃ hop₃ hL₃ => ?_)
      have hi₄ := inv_wk (G := G₂) (by rw [upd_g hg₂]; exact hi₃) hw₃ hop₃
        (by rw [upd_g hg₂]; exact hL₃) hv₃ hh₃
      refine WP.bind (WP.callMC_ptrProject (projWE hi₄) ?_)
      dsimp only
      rw [show WS.ptr.add 4 = WE.ptr from rfl]
      refine WP.bind (WP.futexWakeC fun k₃ hk₃ => ⟨_, hi₄, fun G₃ m₄ hg₃ hi₅ m₅ hw => ?_⟩)
      have hi₆ := inv_set (G := G₃) (by rw [upd_g hg₃]; exact hi₅) hw
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_signal.again11, Bool.false_eq_true, ↓reduceIte]
      exact ⟨.inl rfl, (wake_w hi₅.2.q (by decide) (Nat.le_refl _) hw).1, true, hi₆⟩
    · have hb : b = sv 1 := by
        apply Classical.byContradiction
        intro hne'
        exact sg1_noFail (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hne' hj hv hfl
      have hi₂ := inv_load (.inl rfl) (G := G₁) hi₁ hw' hop hL hh
      rw [← upd_g hg₁] at hi₂
      have hr : r = cst 1 0 := by
        rw [hb, ofBits_cst] at hd
        cases hd
        rfl
      subst hr
      simp only [Option.isSome_some, ↓reduceIte, StateT.run_bind]
      refine WP.bind (WP.bind (WP.callRC_ok
        (x := optPayload (some (cst 1 0))) (v := cst 1 0) rfl ?_))
      repeat (first
        | exact ⟨⟨hop.current, .inl ⟨rfl, hi₂⟩⟩, .inl (by omega)⟩
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind,
            Io_Condition_signal.again11, ↓reduceIte])
      done

  · simp only at hs; subst hs
    unfold Io_Condition_signal.loop11
    simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
    rw [if_neg gt00]
    simp only [StateT.run_pure, pure_bind]
    refine WP.pure' ?_
    simp only [Io_Condition_signal.again11, Bool.false_eq_true, ↓reduceIte]
    exact ⟨.inr rfl, hc, false, hi⟩

/-- `signal` by the producer after its `unlock`: it signals iff `main` did `waiters += 1`. -/
theorem signal_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io)
    (hi : proto.inv (upd G 1 (gP { ph := .rdy })) m) (hc : m.current = 1) :
    proto.WP 1 (Io_Condition_signal (bPtr.add 20) io) (fun _ G' m' _ => m'.current = 1 ∧
      ∃ b, proto.inv (upd G' 1 (gP { ph := .set, cw := b })) m') G m d := by
  unfold Io_Condition_signal
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind, bind_assoc]
  rw [show bPtr.add 20 = WS.ptr from rfl]
  refine WP.bind (wp_loadAs (.inl rfl) (g := gP { ph := .rdy }) hi (ht1 (by simp [gP]))
    (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩)
    fun k hk G₁ m₁ m' b r j hg₁ hi₁ hd hj hv hfl _ hh hw' hop hL => ?_)
  have hcur : m'.current = 1 := hop.current
  have hr : r = Packed.ofBits b := by
    rw [ofBits_cst] at hd; cases hd; rfl
  subst hr
  have hcase := inv_sload (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop
    (by rw [upd_g hg₁]; exact hL) hh hj hv hfl
  simp only [StateT.run_bind]
  simp only [StateT.run_modify, pure_bind]
  refine WP.bind (WP.mono ?_ (WP.loop _ _ sInv (fun _ => 0) sPost (sig_body io) _ G₁ m' k ?_))
  · rintro ⟨e, s'⟩ G₂ m₂ d₂ ⟨he, hc₂, b', hi₂⟩
    rcases he with rfl | rfl <;>
    · simp only [StateT.run_pure]
      exact WP.pure' (WP.pure' ⟨hc₂, b', hi₂⟩)
  · refine ⟨hcur, ?_⟩
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact .inl ⟨by decide, h⟩
    · exact .inr ⟨by decide, h⟩

/-- The event's newest write, while the producer is before its `xchg`: `waiting` iff `main`
wrote it. -/
theorem ev_last {G : ThreadId → Gh} {m : Mem} {b : Bool}
    (hi : proto.inv (upd G 1 (gP { ph := .set, cw := b })) m) :
    (last (WV.hist m)).Val (if (G 0).2.vw then (1 : BitVec 32) else 0) := by
  obtain ⟨hsz, hval⟩ := hi.2.vh
  rw [upd1_0, upd_self] at hsz hval
  cases e : (G 0).2.vw
  · have hs : (WV.hist m).size = 1 := by simpa [vL, gP, e] using hsz
    have := hval 0 (by simp [vL, gP, e])
    rw [show last (WV.hist m) = (WV.hist m)[0]! by simp [last, hs]]
    simpa [vL, gP, e] using this
  · have hs : (WV.hist m).size = 2 := by simpa [vL, gP, e] using hsz
    have := hval 1 (by simp [vL, gP, e])
    rw [show last (WV.hist m) = (WV.hist m)[1]! by simp [last, hs]]
    simpa [vL, gP, e] using this

/-- The producer's `xchg(is_set)` (release) at the event, which read the value `old`: it goes to
`setw` (`old = waiting`) or to its end. -/
theorem inv_xset {G : ThreadId → Gh} {m₁ m' : Mem} {b : Bool} {old : BitVec 32}
    (hi : proto.inv (upd G 1 (gP { ph := .set, cw := b })) m₁) (hw' : WV.Ok m') (hop : WV.Op 1 m₁ m')
    (hL : L.Inv (upd G 1 (gP { ph := .set, cw := b })) m') (hv : (last (WV.hist m₁)).Val old)
    (hh : WV.hist m' = (WV.hist m₁).push (Word.rmwEnt m' 1 .release (last (WV.hist m₁))
      (RmwOp.xchg.apply false old (Packed.toBits Io_Event.is_set)))) :
    ((G 0).2.vw ∧ old = BitVec.ofNat 32 1 ∧
      proto.inv (upd G 1 (gP { ph := .setw, cw := b, vw := true })) m') ∨
    ((G 0).2.vw = false ∧ old = BitVec.ofNat 32 0 ∧
      proto.inv (upd G 1 (gP { ph := .fin, cw := b, vw := true })) m') := by
  have hu := hi.2
  have hfl := hu.flags
  rw [upd1_0, upd_self] at hfl
  have hS := hist_op (.inr (.inr rfl)) (.inl rfl) (by decide) hu hop
  have hE := hist_op (.inr (.inr rfl)) (.inr (.inl rfl)) (by decide) hu hop
  have hV2 : (Word.rmwEnt m' 1 .release (last (WV.hist m₁))
      (RmwOp.xchg.apply false old (Packed.toBits Io_Event.is_set))).Val (BitVec.ofNat 32 2) :=
    rmwEnt_val
  have key : ∀ x' : X, x'.ph.isProd = true → 9 ≤ x'.ph.rank → x'.cw = b → x'.vw = true →
      x'.ph ≠ .sgp → Flags (G 0).2 x' → (x'.ph = .fin → (G 0).2.ph ≠ .ev1) →
      proto.inv (upd G 1 (gP x')) m' := by
    intro x' hp h9 hc hvw hs hfx hev
    refine ⟨linv_x hL ?_ ?_, U_op (.inr (.inr rfl)) hu hop hw' (shape_p hu.shape rfl hp)
      (parts_p hu.parts rfl) ?_ ?_ ?_ (by rw [upd1_0, upd_self]; exact hfx) ?_
      (fun h => ?_) (fun h => ?_) (fun h => ?_) ?_ (fun h => absurd (by rw [upd_self] at h; exact h) hs)⟩
    · show vOf x' = vOf { ph := .set, cw := b }
      unfold vOf; rw [if_pos ⟨hp, by omega⟩]; rfl
    · show rdyOf x' = rdyOf { ph := .set, cw := b }
      rw [show rdyOf { ph := .set, cw := b } = true from rfl]; unfold rdyOf; simp [hp]; omega
    · rw [sok_congr hS, upd1_0, upd_self]
      have := hu.sh; rw [upd1_0, upd_self] at this
      rw [sN_cw (x1 := (gP { ph := .set, cw := b }).2) (by simp [gP, hc])]; exact this
    · rw [eok_congr hE, upd_self]; have := hu.eh; rw [upd_self] at this
      rw [eN_eq (x := (gP { ph := .set, cw := b }).2) (by simp [gP, hc]) (by simp [gP, Ph.rank])
        (by simp [gP]; omega)]; exact this
    · rw [upd1_0, upd_self]
      have := vok_push hu.vh hh hV2
      rw [upd1_0, upd_self] at this
      have hvl : vL (G 0).2 (gP x').2 = vL (G 0).2 (gP { ph := .set, cw := b }).2 ++ [2] := by
        simp [vL, gP, hvw]
      rw [hvl]; exact this
    · intro hc0
      refine ⟨fun hr => ?_, fun hr => ?_⟩ <;> rw [upd_self] at hr
      · simp [gP] at hr; omega
      · exfalso; simp only [gP] at hr
        rcases hr with h | h <;> rw [h] at h9 <;> simp [Ph.rank] at h9
    · rw [upd_self] at h; rw [hS, hE]
      have e8 := eN_eq (x := (gP { ph := .set, cw := b }).2) (x' := (gP x').2) (by simp [gP, hc])
        (by simp [gP, Ph.rank]) (by simp [gP]; omega)
      exact hu.sig (by rw [upd_self, ← e8]; exact h)
    · rw [upd1_0] at h; rw [hS]
      exact VClock.le_trans (by have := hu.seen; rw [upd1_0] at this; exact this h) (hop.clocks 0)
    · rw [upd1_0] at h; rw [hh]
      have h2 : 1 < (WV.hist m₁).size := by
        obtain ⟨hsz, -⟩ := hu.vh; rw [upd1_0, upd_self] at hsz; rw [hsz]; simp [vL, gP, h]
      rw [get_push_lt h2]
      exact VClock.le_trans (by have := hu.vclk; rw [upd1_0] at this; exact this h) (hop.clocks 0)
    · intro w hw
      rw [hop.waiters] at hw
      rcases hu.q w hw with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact .inl h
      · rw [upd_self] at h4; simp [gP, Ph.rank] at h4
      · rw [upd1_0] at h3
        refine .inr (.inr ⟨h1, h2, by rw [upd1_0]; exact h3, by
          rw [upd_self]; intro hf; exact hev hf h3⟩)
  have hl := ev_last hi
  cases e : (G 0).2.vw
  · -- `main` did not write `waiting`: the producer reads `unset`
    rw [e] at hl
    refine .inr ⟨rfl, val_eq hv hl, key { ph := .fin, cw := b, vw := true } rfl
      (by simp [Ph.rank]) rfl rfl (by simp) ?_ (fun _ hev => by rw [hfl.mvw' hev] at e; cases e)⟩
    exact ⟨hfl.sig, hfl.mcw, hfl.cons, (fun _ => by simp [Ph.rank]), (fun h => by rcases h with h | h <;> cases h),
      hfl.mvw, hfl.mvw', by simp, (fun h => by cases h), (fun h1 h2 => hfl.late h1 (by simp [gP, Ph.rank])), (fun _ => rfl),
      (fun h => by cases h)⟩
  · -- the producer reads `waiting`
    rw [e] at hl
    refine .inl ⟨rfl, val_eq hv hl, key { ph := .setw, cw := b, vw := true } rfl
      (by simp [Ph.rank]) rfl rfl (by simp) ?_ (fun h => by cases h)⟩
    exact ⟨hfl.sig, hfl.mcw, hfl.cons, (fun _ => by simp [Ph.rank]), (fun h => by rcases h with h | h <;> cases h),
      hfl.mvw, hfl.mvw', by simp, (fun _ => e), (fun h1 h2 => hfl.late h1 (by simp [gP, Ph.rank])), (fun h => by cases h),
      (fun h => by cases h)⟩

theorem same_q {m m' : Mem} {c : ThreadId} {ws : Array (ThreadId × Ptr)} {wk : Array ThreadId}
    (h : m' = { m with current := c, waiters := ws, woken := wk }) :
    m'.blocks = m.blocks ∧ m'.atomics = m.atomics ∧ m'.footprint = m.footprint ∧
      m'.threads = m.threads ∧ m'.clocks = m.clocks := by
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The producer's futex wake at the event: it goes to its end. -/
theorem inv_fin {G : ThreadId → Gh} {m₁ m' : Mem} {b : Bool} {n : Nat} (hn : 1 ≤ n)
    (hi : proto.inv (upd G 1 (gP { ph := .setw, cw := b, vw := true })) m₁)
    (h : ((Thread.futexWake WV.ptr n).run { m₁ with current := 1 }).run = some (.ok ((), m'))) :
    proto.inv (upd G 1 (gP { ph := .fin, cw := b, vw := true })) m' := by
  have hu := hi.2
  obtain ⟨hc', ht', hws, hm'⟩ := wake_w hu.q (by decide) hn h
  have hL := hi.1.wakeOff (by decide) h
  obtain ⟨hb', ha', hf', ht'', hc''⟩ := same_q hm'
  have hcl : ∀ u : Nat, VClock.le (m₁.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hc'']; exact VClock.le_refl _
  have hk : ∀ W : Word 32 4, W.Keep m₁ m' := fun W => Word.keep_of hb' ha' hf' ht'' hcl
  have hfl := hu.flags
  rw [upd1_0, upd_self] at hfl
  have hu' : U (upd G 1 (gP { ph := .setw, cw := b, vw := true })) m' :=
    U_keep hu (hk WS) (hk WE) (hk WV) ht' (fun w hw => by
      obtain ⟨hw', -⟩ := hws w hw; exact hu.q w hw') hcl
      (fun _ h => before_same ha' h)
      (by unfold IoOk AllLe; rw [hf', ht'', hc'']; exact hu.io)
      (by unfold BlkOk; rw [hb']; exact hu.blk)
  refine ⟨linv_x hL rfl rfl, U_upd hu' (shape_p hu'.shape rfl rfl) (parts_p hu'.parts rfl)
    (by simp [upd1_0, upd_self, sN, gP]) (by simp [upd_self, eN, gP, Ph.rank])
    (by simp [upd1_0, upd_self, vL, gP]) ?_ ?_ (fun h => hu'.seen (by rw [upd1_0] at h ⊢; exact h))
    (fun h => hu'.vclk (by rw [upd1_0] at h ⊢; exact h)) (fun w hw => ?_)
    (fun h => by rw [upd_self] at h; cases h)⟩
  · rw [upd1_0, upd_self]
    exact ⟨hfl.sig, hfl.mcw, hfl.cons, (fun _ => by simp [gP, Ph.rank]),
      (fun h => by rcases h with h | h <;> cases h), hfl.mvw, hfl.mvw', by simp [gP],
      (fun h => by cases h), (fun h1 _ => hfl.late h1 (by simp [gP, Ph.rank])), (fun _ => rfl),
      (fun h => by cases h)⟩
  · intro hc0
    refine ⟨fun hr => ?_, fun hr => ?_⟩ <;> rw [upd_self] at hr <;> simp [gP, Ph.rank] at hr
  · obtain ⟨hw', hne⟩ := hws w hw
    rcases hu.q w hw' with h | ⟨-, -, -, h4⟩ | ⟨-, h2, -⟩
    · exact .inl h
    · rw [upd_self] at h4; simp [gP, Ph.rank] at h4
    · exact absurd h2 hne

/-- `Event.set` by the producer: it writes `is_set`, and wakes `main` if it wrote `waiting`. -/
theorem set_spec (G : ThreadId → Gh) (m : Mem) (d : Nat) (io : Io) (b : Bool)
    (hi : proto.inv (upd G 1 (gP { ph := .set, cw := b })) m) (hc : m.current = 1) :
    proto.WP 1 (Io_Event_set (bPtr.add 28) io) (fun _ G' m' _ => m'.current = 1 ∧
      proto.inv (upd G' 1 (gP { ph := .fin, cw := b, vw := true })) m') G m d := by
  unfold Io_Event_set
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind]
  rw [show bPtr.add 28 = WV.ptr from rfl]
  refine WP.bind (wp_rmwAs (.inr (.inr rfl)) (g := gP { ph := .set, cw := b }) hi
    (ht1 (by simp [gP])) (fun G₁ m₁ hg₁ hi₁ v hv => ?_)
    fun k hk G₁ m₁ m' old r hg₁ hi₁ hd hv hU hh hacq hw' hop hL => ?_)
  · have hl := ev_last (G := G₁) (by rw [upd_g hg₁]; exact hi₁)
    have := val_eq hv hl
    split at this <;> subst this
    · exact ⟨_, ofBits_ev1⟩
    · exact ⟨_, ofBits_ev0⟩
  rcases inv_xset (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop (by rw [upd_g hg₁]; exact hL) hv hh
    with ⟨-, rfl, hi₂⟩ | ⟨-, rfl, hi₂⟩
  · rw [ofBits_ev1] at hd; cases hd
    simp only [StateT.run_bind]
    simp only [StateT.run_pure, pure_bind]
    refine WP.bind (WP.bind (WP.futexWakeC fun k₂ hk₂ => ⟨_, hi₂, fun G₂ m₂ hg₂ hi₃ m₃ hw => ?_⟩))
    have hi₄ := inv_fin (G := G₂) (by decide) (by rw [upd_g hg₂]; exact hi₃) hw
    have hc₃ := (wake_w hi₃.2.q (by decide) (by decide) hw).1
    repeat (first | exact ⟨hc₃, hi₄⟩ | refine WP.pure' ?_ | simp only [StateT.run_pure])
  · rw [ofBits_ev0] at hd; cases hd
    repeat (first | exact ⟨hop.current, hi₂⟩ | refine WP.pure' ?_ |
      simp only [StateT.run_pure, pure_bind])

theorem producer_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 1 (gP { ph := .lk })) m) (hc : m.current = 1) :
    proto.WP 1 (producer bPtr) (fun _ G' m' _ => m'.current = 1 ∧
      ∃ x, x.ph = .fin ∧ proto.inv (upd G' 1 (gP x)) m') G m d := by
  unfold producer
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (WP.callMC_ptrProject (projB hi (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io hi hc (live1 hi (by decide)) fun m₁ hc₁ ht₁ hi₁ => ?_)
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_spec fits mptr rfl 1 (gP { ph := .lk }) rfl _ G
    m₁ d hi₁)))
  rintro _ G₂ m₂ d₂ ⟨hd₂, hc₂, hL, hi₂⟩
  have hi₂' : proto.inv (upd G₂ 1 (gH { ph := .hl } hL)) m₂ := by
    have hf := hi₂.2.flags
    rw [upd1_0, upd_self] at hf
    exact inv_p (a := ⟨.holds, Heap.empty, hL⟩) (x := { ph := .lk }) hi₂ rfl rfl rfl rfl rfl rfl rfl
      (hf.early rfl rfl rfl (by decide) (by decide))
      (hi₂.2.reg.early (by simp [Lock.prod, gP, Ph.rank]) (by simp [Ph.rank]))
      (hi₂.2.q.p (fun _ => by simp [Ph.rank]) (fun h => by cases h)) (by decide)
  -- `v = 7`
  refine WP.bind (WP.callMC_ptrProject (projB hi₂' (k := 32) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_pstep (xa := { ph := .hl }) (xb := { ph := .v7 })
    ((TTriple.store (p := bPtr.add 32) (a := 4) (v := BitVec.ofNat 32 0) (by decide)
      (7 : BitVec 32)).frame (R := pts (bPtr.add 36) 1 false))
    hi₂' hc₂ (fun h => by simpa [R, vOf, rdyOf, gH, Ph.isProd, Ph.rank] using h)
    (fun _ hQ h => by simpa [R, vOf, rdyOf, gH, Ph.isProd, Ph.rank] using h) rfl rfl rfl rfl rfl
    (by have hf := hi₂'.2.flags; rw [upd1_0, upd_self] at hf; exact hf.early rfl rfl rfl (by decide) (by decide))
    (fun _ _ _ hr => hr.early (by simp [gH, Ph.rank]) (by simp [gH, Ph.rank]))
    (fun _ _ hq => hq.p (fun _ => by simp [gH, Ph.rank]) (fun h => by cases h)) (by decide)
    fun _ m₃ hQ hc₃ ht₃ _ hi₃ => ?_)
  -- `ready = true`
  refine WP.bind (WP.callMC_ptrProject (projB hi₃ (k := 36) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_pstep (xa := { ph := .v7 }) (xb := { ph := .rdy })
    ((TTriple.store (p := bPtr.add 36) (a := 1) (v := false) (by decide) true).frameL
      (R := pts (bPtr.add 32) 4 (BitVec.ofNat 32 7)))
    hi₃ hc₃ (fun h => by simpa [R, vOf, rdyOf, gH, Ph.isProd, Ph.rank] using h)
    (fun _ hQ h => by simpa [R, vOf, rdyOf, gH, Ph.isProd, Ph.rank] using h) rfl rfl rfl rfl rfl
    (by have hf := hi₃.2.flags; rw [upd1_0, upd_self] at hf; exact hf.early rfl rfl rfl (by decide) (by decide))
    (fun m' hQ' hl hr => ?_) (fun _ _ hq => hq.p (fun _ => by simp [gH, Ph.rank])
      (fun h => by cases h)) (by decide) fun _ m₄ hQ' hc₄ ht₄ _ hi₄ => ?_)
  · -- `ready = true`: write 1 happened before the producer, which holds the mutex
    intro hcw
    rw [upd1_0] at hcw
    obtain ⟨h1, -⟩ := hr (by rw [upd1_0]; exact hcw)
    refine ⟨fun hx => by rw [upd_self] at hx; simp [gH, Ph.rank] at hx, fun _ => ?_⟩
    have hh1 : L.ph (upd G₂ 1 (gH { ph := .rdy } hQ') 1) = .holds := by rw [upd_self]; rfl
    rcases h1 (by rw [upd_self]; simp [gH, Ph.rank]) with ⟨hh0, -⟩ | ⟨i, l, hl', hle⟩ | hle
    · rw [upd1_0] at hh0
      have := hl.one 0 1 (by rw [upd1_0]; exact hh0) hh1
      cases this
    · exact VClock.le_trans hle ((hl.rel i l hl').2 1 hh1)
    · exact hle
  -- `unlock`
  refine WP.bind (WP.callMC_ptrProject (projB hi₄ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io hi₄ hc₄ (live1 hi₄ (by simp [gH])) fun m₅ hc₅ ht₅ hi₅ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_spec fits mptr rfl 1 (gH { ph := .rdy } hQ') rfl
    _ G₂ m₅ d₂ hi₅)))
  rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
  have hi₆' : proto.inv (upd G₃ 1 (gP { ph := .rdy })) m₆ := hi₆
  -- `signal`
  refine WP.bind (WP.callMC_ptrProject (projB hi₆' (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io hi₆' hc₆ (live1 hi₆' (by simp [gP])) fun m₇ hc₇ ht₇ hi₇ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (signal_spec G₃ m₇ d₃ _ hi₇ hc₇)))
  rintro _ G₄ m₈ d₄ ⟨hc₈, b, hi₈⟩
  -- `Event.set`
  refine WP.bind (WP.callMC_ptrProject (projB hi₈ (k := 28) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_io hi₈ hc₈ (live1 hi₈ (by simp [gP])) fun m₉ hc₉ ht₉ hi₉ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (set_spec G₄ m₉ d₄ _ b hi₉ hc₉)))
  rintro _ G₅ m₁₀ d₅ ⟨hc₁₀, hi₁₀⟩
  refine WP.pure' ?_
  exact WP.pure' ⟨hc₁₀, _, rfl, hi₁₀⟩

/-! ## The producer's end -/

/-- The producer at its end: it is `gone`. -/
theorem inv_end {G : ThreadId → Gh} {m : Mem} {x : X} (hx : x.ph = .fin)
    (hi : proto.inv (upd G 1 (gP x)) m) :
    proto.inv (upd G 1 (⟨.gone, Heap.empty, Heap.empty⟩, x)) m := by
  have hl := hi.1.ghost (t := 1) (g := (⟨.gone, Heap.empty, Heap.empty⟩, x))
    (by rw [upd_self]; rfl) (.inr (.inl rfl)) (by rw [upd_self]; rfl) rfl
    (fun h => absurd rfl h) (fun hL hR => by
      change R (fun u => (upd (upd G 1 (gP x)) 1 (⟨.gone, Heap.empty, Heap.empty⟩, x) u).2) hL
      rw [upd_upd]
      exact (R_congr (Y := fun u => (upd G 1 (gP x) u).2) (by simp [upd_self, gP])
        (by simp [upd_self, gP]) hL).mpr hR)
  rw [upd_upd] at hl
  have hu := hi.2
  have hX : (fun u => (upd G 1 (⟨.gone, Heap.empty, Heap.empty⟩, x) u).2) =
      fun u => (upd G 1 (gP x) u).2 := by funext u; unfold upd; split <;> rfl
  have h0 : upd G 1 (⟨.gone, Heap.empty, Heap.empty⟩, x) 0 = upd G 1 (gP x) 0 := by
    rw [upd1_0, upd1_0]
  have h1 : (upd G 1 (⟨.gone, Heap.empty, Heap.empty⟩, x) 1).2 = (upd G 1 (gP x) 1).2 := by
    simp [gP]
  refine ⟨hl, ⟨by rw [hX]; exact hu.shape, hu.io, parts_p hu.parts rfl, hu.blk, hu.ws, hu.we, hu.wv,
    by rw [h0, h1]; exact hu.sh, by rw [h1]; exact hu.eh, by rw [h0, h1]; exact hu.vh,
    by rw [h0, h1]; exact hu.flags, ?_, by rw [h1]; exact hu.sig, by rw [h0]; exact hu.seen,
    by rw [h0]; exact hu.vclk, ?_, by rw [h1]; exact hu.pc⟩⟩
  · intro hcw; rw [h0] at hcw ⊢; rw [h1]; exact hu.reg hcw
  · intro w hw
    rcases hu.q w hw with h | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact .inl h
    · exact .inr (.inl ⟨a1, a2, by rw [h0]; exact a3, by rw [h1]; exact a4⟩)
    · exact .inr (.inr ⟨a1, a2, by rw [h0]; exact a3, by rw [h1]; exact a4⟩)

/-- The producer spawned no thread. -/
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

/-- The producer: its code, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | producer p =>
    obtain ⟨rfl, rfl⟩ := hg
    -- the producer is thread 1
    have hu1 : u = 1 := by
      obtain ⟨-, hc⟩ := hi.2.shape
      have hlt := (hi.1.live u (by rw [hgu]; exact (by decide : LPh.out ≠ LPh.gone))).1
      rcases hc with ⟨hs, -, -⟩ | ⟨hs, -⟩ <;> unfold ThreadId at * <;> omega
    subst hu1
    show proto.WP 1 ((fun _ => ()) <$> producer bPtr) _ G _ d
    refine WP.map (WP.mono ?_ (producer_spec G _ d
      (by rw [show gP { ph := .lk } = G 1 from hgu.symm, upd_same]; exact inv_cur hi 1) rfl))
    rintro _ G' m' _ ⟨-, x, hx, hi'⟩
    exact ⟨_, inv_end hx hi', ⟨rfl, hx⟩, fun _ => joinedAll_kid hi' (by decide)⟩
  | work p => cases hg
  | writer p => cases hg
  | semWork p => cases hg

/-! ## `main`'s start -/

/-- The initial mutex, condition and event. -/
def mutex0 : Io_Mutex := { state := { raw := Io_Mutex_State.unlocked } }
def cond0 : Io_Condition :=
  { state := { raw := (Packed.ofBits (0 : BitVec 32) : Io_Condition_State) }, epoch := { raw := 0 } }

/-- The bytes of the three shared words after `main`'s stores (bytes 20..32 of the `Box`). -/
def wb : Array Byte :=
  writeBytes (writeBytes (Array.replicate 12 Byte.undef) 0 (Enc.encode cond0)) 8
    (Enc.encode Io_Event.unset)

/-- The bytes of `v` and `ready` after `main`'s stores (bytes 32..37). -/
def rb : Array Byte :=
  writeBytes (writeBytes (Array.replicate 5 Byte.undef) 4 (Enc.encode false)) 0
    (Enc.encode (0 : BitVec 32))

theorem wb_size : wb.size = 12 := by decide +kernel
theorem rb_size : rb.size = 5 := by decide +kernel
theorem wb_s : wb.extract 0 4 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem wb_e : wb.extract 4 8 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem wb_v : wb.extract 8 12 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem rb_v : rb.extract 0 4 = Enc.encode (0 : BitVec 32) := by decide +kernel
theorem rb_r : rb.extract 4 5 = Enc.encode false := by decide +kernel
theorem enc_mutex : Enc.encode mutex0 = Enc.encode (0 : BitVec 32) := by decide +kernel

/-- A shared word at the start: no atomic location, each access happened before every thread,
and the value 0. -/
theorem word_init {W : Word 32 4} {m : Mem} {blk : Block} (hW : W.b = 0) (h4 : W.o % 4 = 0)
    (hlo : 20 ≤ W.o) (hhi : W.o + 4 ≤ 32) (hb : m.blocks[0]? = some blk) (hl : blk.live = true)
    (hs : blk.bytes.size = 40) (ha : blk.addr % 8 = 0) (hk : blk.kind = .stack)
    (hat : m.atomics = #[])
    (hv : (intOfBytes 32 (blk.bytes.extract W.o (W.o + 4))).run = some (.ok 0))
    (hfp : ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock) :
    W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) := by
  have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hu : W.Holds m 0 := by unfold Word.Holds curBytes; rw [hW, hb]; exact hv
  refine ⟨⟨⟨blk, by rw [hW]; exact hb, hl, by omega, by omega, by rw [hk]; decide⟩,
    fun l hl' => by rw [hat] at hl'; simp at hl', fun i l h => absurd h (hno i l),
    fun e he hh => .inr (hfp e he hh), ⟨0, hu⟩, fun i l h => absurd h (hno i l)⟩, ?_, ?_⟩
  · rw [Word.hist_none hno]; rfl
  · rw [Word.hist_none hno]; exact hu

theorem enc_io (io : Io) : (Enc.encode io).size = 16 := by
  show (Array.replicate 16 _).size = 16; simp

/-- Before the spawn: `main` owns the `Box`'s bytes, `io` first. A pointer into the `Box` is
formed (`ptrProject`, MM-3): the owned cells record the block's 40 bytes. -/
theorem projF {m : Mem} {h : Heap} {P : Assn} {A : Nat} {bs : Array Byte}
    (F : (bytesAt bPtr A 40 .stack bs ∗ P) h) (hs : h.Sub m.heap) (hpos : 0 < bs.size) {k : Nat}
    (hk : k ≤ 40) : (ptrProject bPtr (·.add k)).run m = pure (bPtr.add k, m) := by
  obtain ⟨hx, hy, -, rfl, hbx, -⟩ := F
  have hsx := Heap.sub_union_left.trans hs
  exact ptrProject_add_run (bytesAt_inBounds_block hbx hsx hpos rfl (by decide) (by decide))
    (bytesAt_inBounds_block hbx hsx hpos rfl (by simp [bPtr, Ptr.add]) (by simp [bPtr, Ptr.add]; omega))

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, {})

/-- `main` before its spawn. -/
def gPre : Gh := gP { ph := .pre }

/-- The `Box` in five parts, after `main`'s stores: `io`, the mutex, the three shared words, `v`
and `ready`, the padding. -/
def Parts (io : Io) (A : Nat) (pb : Array Byte) : Assn :=
  bytesAt bPtr A 40 .stack (Enc.encode io) ∗ (bytesAt (bPtr.add 16) A 40 .stack (Enc.encode mutex0) ∗
    (bytesAt (bPtr.add 20) A 40 .stack wb ∗ (bytesAt (bPtr.add 32) A 40 .stack rb ∗
      bytesAt (bPtr.add 37) A 40 .stack pb)))

theorem allLe_one {m : Mem} {c : VClock} (h1 : m.threads.size = 1)
    (h : VClock.le c (m.clocks[0]!) = true) : AllLe m c := fun u hu => by
  rw [h1] at hu
  have : u = 0 := by omega
  subst this; exact h

/-- Before the spawn: `main` alone owns the `Box`. The mutex starts: it owns `v` and `ready`; the
rest belongs to no thread. -/
theorem inv_start {m : Mem} {io : Io} {A : Nat} {pb : Array Byte} {h : Heap}
    (ho : Owned (upd (fun _ => Heap.empty) 0 h) m) (hp : Parts io A pb h) (hA : A % 8 = 0)
    (hth : m.threads = #[{ spawner := 0, joined := true }]) (hat : m.atomics = #[])
    (hq : m.waiters = #[]) : proto.inv (upd G0 0 gPre) m := by
  obtain ⟨hI, h2, dI, rfl, hio, hW, h3, dW, rfl, hw, hS, h4, dS, rfl, hs, hR, hP, dR, rfl, hr, -⟩ := hp
  have hsub := ho.sub 0; rw [upd_self] at hsub
  have s2 : (hW ∪ (hS ∪ (hR ∪ hP))).Sub (hI ∪ (hW ∪ (hS ∪ (hR ∪ hP)))) := Heap.sub_union_right dI
  have sI : hI.Sub m.heap := Heap.sub_union_left.trans hsub
  have sW : hW.Sub m.heap := (Heap.sub_union_left.trans s2).trans hsub
  have s3 : (hS ∪ (hR ∪ hP)).Sub m.heap := ((Heap.sub_union_right dW).trans s2).trans hsub
  have sS : hS.Sub m.heap := Heap.sub_union_left.trans s3
  have s4 : (hR ∪ hP).Sub m.heap := (Heap.sub_union_right dS).trans s3
  have sR : hR.Sub m.heap := Heap.sub_union_left.trans s4
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  -- block 0 and its bytes
  obtain ⟨blk, hblk, hl, hA', hS', hK', -⟩ := bytesAt_blk (m := m) hio sI rfl
    (by rw [enc_io]; decide)
  obtain ⟨blk₂, hblk₂, -, -, -, -, hxw⟩ := bytesAt_blk (m := m) hw sW rfl
    (by rw [enc_mutex, LawfulEnc.size_encode]; decide)
  rw [hblk] at hblk₂; cases hblk₂
  obtain ⟨blk₃, hblk₃, -, -, -, -, hxs⟩ := bytesAt_blk (m := m) hs sS rfl (by rw [wb_size]; decide)
  rw [hblk] at hblk₃; cases hblk₃
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have hword : ∀ o, 20 ≤ o → o + 4 ≤ 32 → blk.bytes.extract o (o + 4) = wb.extract (o - 20) (o - 16) := by
    intro o h1 h2
    have := congrArg (fun a => Array.extract a (o - 20) (o - 16)) hxs
    simp only [Array.extract_extract] at this
    rw [← this]
    simp only [show (bPtr.add 20).off.toNat = 20 from rfl, wb_size]
    congr 1 <;> omega
  -- each access to a byte of `main`'s part happened before `main`
  have hown : ∀ e ∈ m.footprint, e.Touches (hI ∪ (hW ∪ (hS ∪ (hR ∪ hP)))) → AllLe m e.clock :=
    fun e he ht => allLe_one h1 (by
      have := ho.owns 0 (by rw [h1]; decide) e he (.inl (by rw [upd_self]; exact ht)); exact this)
  have sS' : hS.Sub (hI ∪ (hW ∪ (hS ∪ (hR ∪ hP)))) :=
    Heap.sub_union_left.trans ((Heap.sub_union_right dW).trans s2)
  have hcellS : ∀ x, 20 ≤ x → x < 32 → (hI ∪ (hW ∪ (hS ∪ (hR ∪ hP)))) (0, x) ≠ none := fun x a b =>
    sS'.ne (bytesAt_in hs rfl (by simp [bPtr, Ptr.add]; omega) (by simp [bPtr, Ptr.add, wb_size]; omega))
  have hwi : ∀ W : Word 32 4, W.b = 0 → W.o % 4 = 0 → 20 ≤ W.o → W.o + 4 ≤ 32 →
      wb.extract (W.o - 20) (W.o - 16) = Enc.encode (0 : BitVec 32) →
      W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec 32) := fun W hb h4 h1' h2' he =>
    word_init hb h4 h1' h2' hblk hl hS' (by rw [hA']; exact hA) hK' hat
      (by rw [hword W.o h1' h2', he]; exact intOfBytes_rmw 0)
      (fun e he' hh => hown e he' (Word.touches_of hh fun x a b => by
        rw [hb]; exact hcellS x (by omega) (by omega)))
  obtain ⟨hwsOk, hwsz, hwsv⟩ := hwi WS rfl (by decide) (by decide) (by decide) wb_s
  obtain ⟨hweOk, hwez, hwev⟩ := hwi WE rfl (by decide) (by decide) (by decide) wb_e
  obtain ⟨hwvOk, hwvz, hwvv⟩ := hwi WV rfl (by decide) (by decide) (by decide) wb_v
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 16 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    have := hxw
    rw [enc_mutex, LawfulEnc.size_encode] at this
    rw [show (16 : Nat) = (bPtr.add 16).off.toNat from rfl, show 4 = Enc.size (BitVec 32) from rfl, this]
    exact intOfBytes_rmw 0
  -- the resource: `v = 0`, `ready = false`
  obtain ⟨hv', hr', dvr, rfl, hbv, hbr⟩ := bytesAt_split hr (k := 4) (by rw [rb_size]; decide)
  rw [rb_size] at hbr
  have hR' : L.R (upd G0 0 gPre) (hv' ∪ hr') := by
    show R (fun u => (upd G0 0 gPre u).2) (hv' ∪ hr')
    unfold R
    rw [show vOf ((fun u => (upd G0 0 gPre u).2) 1) = 0 from rfl,
      show rdyOf ((fun u => (upd G0 0 gPre u).2) 1) = false from rfl]
    refine ⟨hv', hr', dvr, rfl, ⟨A, 40, .stack, _, ?_, (by rw [rb_v]; exact LawfulEnc.size_encode _),
      (by rw [rb_v]; exact LawfulEnc.decode_encode _), hbv, (by decide)⟩,
      ⟨A, 40, .stack, _, ?_, (by rw [rb_r]; exact LawfulEnc.size_encode _),
      (by rw [rb_r]; exact LawfulEnc.decode_encode _), hbr, (by decide)⟩⟩
    · show (A + 32) % 4 = 0; omega
    · show (A + 36) % 1 = 0; omega
  -- `main` keeps nothing; the lock gets the mutex and the resource
  have hRsub : (hv' ∪ hr').Sub (hI ∪ (hW ∪ (hS ∪ ((hv' ∪ hr') ∪ hP)))) :=
    Heap.sub_union_left.trans ((Heap.sub_union_right dS).trans ((Heap.sub_union_right dW).trans s2))
  have hWsub : hW.Sub (hI ∪ (hW ∪ (hS ∪ ((hv' ∪ hr') ∪ hP)))) := Heap.sub_union_left.trans s2
  have dRW : Heap.Disjoint (hv' ∪ hr') hW :=
    (Heap.disjoint_sub dW (Heap.sub_union_left.trans (Heap.sub_union_right dS))).symm
  have ho' := ho.shrink (t := 0) (h := Heap.empty ∪ ((hv' ∪ hr') ∪ hW)) (by
    rw [upd_self, Heap.empty_union]; exact Heap.union_sub hRsub hWsub)
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 gPre u = G0 u := fun u h => upd_ne _ _ h
  have hcellW : ∀ x, 16 ≤ x → x < 16 + 4 → hW (0, x) ≠ none := fun x a b =>
    bytesAt_in hw rfl (by simp [bPtr, Ptr.add]; omega)
      (by rw [enc_mutex, LawfulEnc.size_encode, show Enc.size (BitVec 32) = 4 from rfl]
          simp [bPtr, Ptr.add]; omega)
  have hL := Inv.make (L := L) (G := upd G0 0 gPre) (t := 0) (hL := hv' ∪ hr') (hW := hW) ho' rfl
    (fun u hu => by rw [upd_ne _ _ hu]; unfold Lock.own; rw [hGu u hu]; split <;> rfl)
    (by rw [upd_self]; rfl) (by rw [upd_self]; exact fun _ => .inl rfl) dRW
    (fun u => by
      by_cases hu : u = 0
      · subst hu; rw [upd_self]; exact .inl ⟨rfl, by rw [h1]; decide, rfl⟩
      · rw [hGu u hu]; exact .inr rfl)
    (fun u => by
      by_cases hu : u = 0
      · subst hu; rw [upd_self]; rfl
      · rw [hGu u hu]; rfl)
    hR' hcellW ⟨blk, hblk, hl, by rw [hS']; decide, by show (blk.addr + 16) % 4 = 0; rw [hA']; omega,
      by rw [hK']; decide⟩ h0 (by rw [hat]; simp) hq (allLe_one h1 (VClock.le_refl _)) (by rw [h1]; decide)
  have hX0 : (upd G0 0 gPre 0).2 = { ph := .pre } := by rw [upd_self]; rfl
  have hX1 : (upd G0 0 gPre 1).2 = {} := rfl
  have hcellI : ∀ x, x < 16 → (hI ∪ (hW ∪ (hS ∪ ((hv' ∪ hr') ∪ hP)))) (0, x) ≠ none := fun x hx =>
    (Heap.sub_union_left).ne (bytesAt_in hio rfl (by simp [bPtr]) (by simp [bPtr, enc_io]; omega))
  refine ⟨hL, ⟨⟨by rw [hth]; rfl, .inl ⟨h1, hX0, fun u hu => ?_⟩⟩, fun e he hb ho16 => .inr ?_,
    fun u => ?_, hbk, hwsOk, hweOk, hwvOk, ?_, ?_, ?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun w hw => ?_, fun h => ?_⟩⟩
  · show (upd G0 0 gPre u).2 = {}
    rw [upd_ne _ _ (by unfold ThreadId at *; omega)]; rfl
  · exact hown e he ⟨e.off, Nat.le_refl _, .inr rfl, by rw [hb]; exact hcellI _ ho16⟩
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; rfl
    · rw [hGu u hu]; rfl
  · rw [hX0, hX1]; exact ⟨hwsz, fun k hk => by simp [sN] at hk; subst hk; exact hwsv⟩
  · rw [hX1]; exact ⟨hwez, fun k hk => by simp [eN] at hk; subst hk; exact hwev⟩
  · rw [hX0, hX1]; exact ⟨hwvz, fun k hk => by simp [vL] at hk; subst hk; exact hwvv⟩
  · rw [hX0, hX1]; constructor <;> simp [Ph.rank, Ph.post]
  · rw [hX0] at h; cases h
  · rw [hX1] at h; simp [eN] at h
  · rw [hX0] at h; cases h
  · rw [hX0] at h; cases h
  · rw [hq] at hw; simp at hw
  · rw [hX1] at h; cases h

/-- The spawn of the producer by `main` (at `pre`): the producer is thread 1, at `lk`; `main` goes
to `run`. -/
theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} (hi : proto.inv G m)
    (hg : G 0 = gPre)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = 1 ∧ proto.inv (upd (upd G 1 (gP { ph := .lk })) 0 (gP { ph := .run })) m' := by
  have hu := hi.2
  obtain ⟨h00, ⟨hs1, -, hnone⟩ | ⟨-, -, -, h0, -⟩⟩ := hu.shape
  rotate_left
  · exfalso; change (G 0).2.ph ≠ _ at h0; rw [hg] at h0; exact h0 rfl
  have hcs : m.clocks.size = 1 := by rw [hi.1.own.csize, hs1]
  have hjb := joinedB_fork hf
  obtain ⟨hch, hm'⟩ := Lock.fork_eq hf
  rw [hs1] at hch
  subst hch
  have hL := hi.1.fork (t := 0) (g₁ := gP { ph := .run }) (g₀ := gP { ph := .lk })
    (by rw [hg]; rfl) hf (by rw [hg]; rfl) (fun _ => .inl rfl) rfl rfl rfl rfl (fun hL hR => by
      change R (fun u => (upd (upd G 1 (gP { ph := .lk })) 0 (gP { ph := .run }) u).2) hL
      have e : (upd (upd G 1 (gP { ph := .lk })) 0 (gP { ph := .run }) 1).2 = { ph := .lk } := by
        simp [upd, gP]
      have e1 : (G 1).2 = {} := hnone 1 (Nat.le_refl _)
      exact (R_congr (Y := fun u => (G u).2) (by simp only [e, e1]; rfl)
        (by simp only [e, e1]; rfl) hL).mpr hR)
  subst hm'
  have hk : ∀ W : Word 32 4, W.Keep m _ := fun W =>
    Word.keep_fork (by rw [hs1]; decide) (by rw [hcs, hs1]) hf
  have h0' : (upd (upd G 1 (gP { ph := .lk })) 0 (gP { ph := .run }) 0).2 = { ph := .run } := by simp [gP]
  have h1' : (upd (upd G 1 (gP { ph := .lk })) 0 (gP { ph := .run }) 1).2 = { ph := .lk } := by
    simp [upd, gP]
  have hG0 : (G 0).2 = { ph := .pre } := by rw [hg]; rfl
  have hG1 : (G 1).2 = {} := hnone 1 (Nat.le_refl _)
  have hhS := Word.hist_keep hu.ws (hk WS)
  have hhE := Word.hist_keep hu.we (hk WE)
  have hhV := Word.hist_keep hu.wv (hk WV)
  obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m.clocks) (t := 0) (by rw [hcs]; decide)
  refine ⟨rfl, hL, ⟨⟨?_, .inr ⟨by simp [hs1], ?_, by simp only [h0']; rfl, by simp only [h0']; decide,
    by simp only [h1']; rfl, fun u hu => ?_⟩⟩, fun e he hb ho16 => ?_, fun u => ?_, hu.blk,
    hu.ws.keep (hk WS), hu.we.keep (hk WE), hu.wv.keep (hk WV), ?_, ?_, ?_, ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun w hw => ?_, fun h => ?_⟩⟩
  · simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00
  · simp only [Array.getElem?_push, hs1, ↓reduceIte]
  · show (upd (upd G 1 (gP { ph := .lk })) 0 (gP { ph := .run }) u).2 = {}
    rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
    exact hnone u (by unfold ThreadId at *; omega)
  · rcases hu.io e he hb ho16 with h | h
    · exact .inl h
    · refine .inr fun u hu' => ?_
      simp only [Array.size_push, hs1] at hu'
      rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
      · exact VClock.le_trans (h 0 (by rw [hs1]; decide)) (hcl 0 (by rw [hcs]; decide))
      · rw [← hcs]; exact VClock.le_trans (h 0 (by rw [hs1]; decide)) hcn
  · unfold upd; split
    · rfl
    · split
      · rfl
      · exact hu.parts u
  · rw [sok_congr hhS, h0', h1']; have := hu.sh; rw [hG0, hG1] at this; exact this
  · rw [eok_congr hhE, h1']; have := hu.eh; rw [hG1] at this; exact this
  · rw [vok_congr hhV, h0', h1']; have := hu.vh; rw [hG0, hG1] at this; exact this
  · rw [h0', h1']; constructor <;> simp [Ph.rank, Ph.post]
  · rw [h0'] at h; cases h
  · rw [h1'] at h; simp [eN] at h
  · rw [h0'] at h; cases h
  · rw [h0'] at h; cases h
  · exact .inl (qok_out hi (by rw [hg]; exact (by decide : LPh.out ≠ LPh.away)) w hw)
  · rw [h1'] at h; cases h

/-- `main` after its `unlock`: it goes to the event wait (`ev0`). -/
theorem inv_ev0 {G : ThreadId → Gh} {m : Mem} {x : X} (hx : RunX x)
    (hi : proto.inv (upd G 0 (gP x)) m) : proto.inv (upd G 0 (gP { ph := .ev0, cw := x.cw })) m := by
  have hfl := hi.2.flags
  rw [upd_self, upd0_1] at hfl
  have hp : x.ph ≠ .pre := by rcases hx with rfl | rfl <;> simp
  refine inv_mx hi hp rfl (by simp) (by rcases hx with rfl | rfl <;> rfl)
    (by rcases hx with rfl | rfl <;> rfl) ?_ (reg_x0 hi.2.reg rfl) (fun h => by cases h)
    (fun h => by cases h) (qok_of hi (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.away)))
  rcases hx with rfl | rfl
  · exact ⟨hfl.sig, (by simp [Ph.post]), (fun h => by cases h), hfl.pcw, hfl.pcw', (fun h => by cases h),
      (fun h => by cases h), hfl.pvw, (fun h => by simpa [gP] using hfl.setw h), (fun h => by cases h),
      hfl.pfin, (fun h => by simpa [gP] using hfl.sg1 h)⟩
  · exact ⟨hfl.sig, (by simp [Ph.post]), (fun _ _ => hfl.cons rfl (.inl rfl)), hfl.pcw, hfl.pcw',
      (fun h => by cases h), (fun h => by cases h), hfl.pvw, (fun h => by simpa [gP] using hfl.setw h),
      hfl.late, hfl.pfin, (fun h => by simpa [gP] using hfl.sg1 h)⟩

/-- `main` at its join. -/
theorem inv_joins {G : ThreadId → Gh} {m : Mem} {c w : Bool}
    (hi : proto.inv (upd G 0 (gP { ph := .evd, cw := c, vw := w })) m) :
    proto.inv (upd G 0 (gP { ph := .joins, cw := c, vw := w })) m := by
  have hfl := hi.2.flags
  rw [upd_self, upd0_1] at hfl
  refine inv_mx hi (by simp) rfl (by simp) (by cases c <;> rfl) rfl ?_ (reg_x0 hi.2.reg rfl)
    (fun h => by cases h) (fun h => ?_) (qok_of hi (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.away)))
  · exact ⟨hfl.sig, (by simpa [gP, Ph.post] using hfl.mcw), (by simpa [gP, Ph.post] using hfl.cons), hfl.pcw,
      hfl.pcw', (fun _ => .inr (.inr rfl)), (fun h => by cases h), hfl.pvw,
      (fun h => by simpa [gP] using hfl.setw h), hfl.late, hfl.pfin, (fun h => by simpa [gP] using hfl.sg1 h)⟩
  · have := hi.2.vclk; rw [upd_self] at this; exact this h

theorem vOf_of_rdy {x : X} (h : rdyOf x = true) : vOf x = 7 := by
  unfold rdyOf at h; unfold vOf
  simp at h
  rw [if_pos ⟨h.1, by omega⟩]

theorem main_spec (io : Io) (d : Nat) :
    proto.WP 0 (handoff io) QM G0 { mem0 with current := 0 } d := by
  unfold handoff
  -- the `Box`: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 40 8 (by decide))
    (Owned.start rfl rfl) rfl (by decide) rfl fun s1 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = bPtr from rfl] at hb₁ ⊢
  -- its five parts
  obtain ⟨hI, hR₁, dI, rfl, hI₁, hR₁'⟩ := bytesAt_split hb₁ (k := 16) (by simp)
  obtain ⟨hW, hR₂, dW, rfl, hW₁, hR₂'⟩ := bytesAt_split hR₁' (k := 4) (by simp)
  obtain ⟨hS, hR₃, dS, rfl, hS₁, hR₃'⟩ := bytesAt_split hR₂' (k := 12) (by simp)
  obtain ⟨hR, hP, dR, rfl, hRr, hP₁⟩ := bytesAt_split hR₃' (k := 5) (by simp)
  simp only [Array.extract_replicate, Array.size_replicate] at hI₁ hW₁ hS₁ hRr hP₁
  change bytesAt bPtr A 40 .stack (Array.replicate 16 .undef) hI at hI₁
  change bytesAt (bPtr.add 16) A 40 .stack (Array.replicate 4 .undef) hW at hW₁
  change bytesAt (bPtr.add 20) A 40 .stack (Array.replicate 12 .undef) hS at hS₁
  change bytesAt (bPtr.add 32) A 40 .stack (Array.replicate 5 .undef) hR at hRr
  change bytesAt (bPtr.add 37) A 40 .stack (Array.replicate 3 .undef) hP at hP₁
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  simp only [StateT.run_pure]
  simp only [pure_bind]
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 (hI ∪ (hW ∪ (hS ∪ (hR ∪ hP))))) m₁ := ho₁
  have hth₁ : 0 < m₁.threads.size := by rw [hs₁.threads]; decide
  have F₁ : (bytesAt bPtr A 40 .stack (Array.replicate 16 .undef) ∗
      (bytesAt (bPtr.add 16) A 40 .stack (Array.replicate 4 .undef) ∗
      (bytesAt (bPtr.add 20) A 40 .stack (Array.replicate 12 .undef) ∗
      (bytesAt (bPtr.add 32) A 40 .stack (Array.replicate 5 .undef) ∗
      bytesAt (bPtr.add 37) A 40 .stack (Array.replicate 3 .undef)))))
      (hI ∪ (hW ∪ (hS ∪ (hR ∪ hP)))) :=
    ⟨hI, _, dI, rfl, hI₁, hW, _, dW, rfl, hW₁, hS, _, dS, rfl, hS₁, hR, hP, dR, rfl, hRr, hP₁⟩
  -- `io`
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := bPtr) (A := A) (S := 40) (K := .stack)
    (bs := Array.replicate 16 .undef) (k := 0) (a := 8) io rfl (by decide)
    (by simp [show Enc.size Io = 16 from rfl]) (by simp [bPtr]; omega) (by decide)).frame)
    ho₁' hc₁ hth₁ (by rw [upd_self]; exact F₁) fun _ m₂ h₂ _ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  have hwI : 0 < (writeBytes (Array.replicate 16 Byte.undef) 0 (Enc.encode io)).size := by
    rw [writeBytes_size _ _ _ (by simp [enc_io])]; simp
  -- the mutex
  refine WP.bind (WP.callMC_ptrProject (projF F₂ (by simpa [upd_self] using ho₂.sub 0) hwI
    (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := bPtr.add 16) (A := A) (S := 40)
    (K := .stack) (bs := Array.replicate 4 .undef) (k := 0) (a := 4) mutex0
    (by rw [enc_mutex]; exact LawfulEnc.size_encode _) rfl (by decide) (by decide)
    (by simp [bPtr, Ptr.add]; omega)
    (by decide)).frame.frameL) ho₂ hc₂ (by rw [hs₂.threads]; exact hth₁) (by rw [upd_self]; exact F₂)
    fun _ m₃ h₃ _ ho₃ F₃ hs₃ _ _ => ?_)
  rw [upd_upd] at ho₃
  have hc₃ : m₃.current = 0 := hs₃.current.trans hc₂
  -- the condition
  refine WP.bind (WP.callMC_ptrProject (projF F₃ (by simpa [upd_self] using ho₃.sub 0) hwI
    (k := 20) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := bPtr.add 20) (A := A) (S := 40)
    (K := .stack) (bs := Array.replicate 12 .undef) (k := 0) (a := 4) cond0
    (by decide +kernel) rfl (by decide) (by decide) (by simp [bPtr, Ptr.add]; omega)
    (by decide)).frame.frameL.frameL) ho₃ hc₃ (by rw [hs₃.threads, hs₂.threads]; exact hth₁)
    (by rw [upd_self]; exact F₃) fun _ m₄ h₄ _ ho₄ F₄ hs₄ _ _ => ?_)
  rw [upd_upd] at ho₄
  have hc₄ : m₄.current = 0 := hs₄.current.trans hc₃
  -- `ready`
  refine WP.bind (WP.callMC_ptrProject (projF F₄ (by simpa [upd_self] using ho₄.sub 0) hwI
    (k := 36) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := bPtr.add 32) (A := A) (S := 40)
    (K := .stack) (bs := Array.replicate 5 .undef) (k := 4) (a := 1) false rfl (by decide)
    (by decide) (Nat.mod_one _) (by decide)).frame.frameL.frameL.frameL) ho₄ hc₄
    (by rw [hs₄.threads, hs₃.threads, hs₂.threads]; exact hth₁) (by rw [upd_self]; exact F₄)
    fun _ m₅ h₅ _ ho₅ F₅ hs₅ _ _ => ?_)
  rw [upd_upd] at ho₅
  have hc₅ : m₅.current = 0 := hs₅.current.trans hc₄
  -- the event
  refine WP.bind (WP.callMC_ptrProject (projF F₅ (by simpa [upd_self] using ho₅.sub 0) hwI
    (k := 28) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt' (p := bPtr.add 20) (A := A) (S := 40)
    (K := .stack) (bs := writeBytes (Array.replicate 12 .undef) 0 (Enc.encode cond0)) (k := 8) (a := 4)
    Io_Event.unset (by decide +kernel) rfl (by decide)
    (by decide +kernel) (by simp [bPtr, Ptr.add]; omega) (by decide)).frame.frameL.frameL) ho₅ hc₅
    (by rw [hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads]; exact hth₁)
    (by rw [upd_self]; exact F₅) fun _ m₆ h₆ _ ho₆ F₆ hs₆ _ _ => ?_)
  rw [upd_upd] at ho₆
  have hc₆ : m₆.current = 0 := hs₆.current.trans hc₅
  -- `v`
  refine WP.bind (WP.callMC_ptrProject (projF F₆ (by simpa [upd_self] using ho₆.sub 0) hwI
    (k := 32) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.liftM_owned ((TTriple.storeAt (p := bPtr.add 32) (A := A) (S := 40)
    (K := .stack) (bs := writeBytes (Array.replicate 5 .undef) 4 (Enc.encode false)) (k := 0) (a := 4)
    (0 : BitVec 32) rfl (by decide) (by decide +kernel)
    (by simp [bPtr, Ptr.add]; omega) (by decide)).frame.frameL.frameL.frameL) ho₆ hc₆
    (by rw [hs₆.threads, hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads]; exact hth₁)
    (by rw [upd_self]; exact F₆) fun _ m₇ h₇ _ ho₇ F₇ hs₇ _ _ => ?_)
  rw [upd_upd] at ho₇
  have hc₇ : m₇.current = 0 := hs₇.current.trans hc₆
  have hth₇ : m₇.threads = #[{ spawner := 0, joined := true }] := by
    rw [hs₇.threads, hs₆.threads, hs₅.threads, hs₄.threads, hs₃.threads, hs₂.threads, hs₁.threads]; rfl
  have hat₇ : m₇.atomics = #[] := by
    rw [hs₇.atomics, hs₆.atomics, hs₅.atomics, hs₄.atomics, hs₃.atomics, hs₂.atomics, hs₁.atomics]; rfl
  have hq₇ : m₇.waiters = #[] := by
    rw [hs₇.waiters, hs₆.waiters, hs₅.waiters, hs₄.waiters, hs₃.waiters, hs₂.waiters, hs₁.waiters]; rfl
  have hP : Parts io A (Array.replicate 3 .undef) h₇ := by
    rw [writeBytes_all (by rw [enc_io]; rfl),
      writeBytes_all (by rw [enc_mutex, LawfulEnc.size_encode]; rfl)] at F₇
    exact F₇
  -- the spawn
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨gPre, inv_start ho₇ hP hA8 hth₇ hat₇ hq₇, fun G₁ m₈ hg₁ hi₈ =>
    ⟨gP { ph := .lk }, ⟨rfl, rfl⟩, fun child m₉ hf => ?_⟩⟩)
  obtain ⟨rfl, hi₉⟩ := inv_spawn hi₈ hg₁ hf
  dsimp only
  simp only [StateT.run_bind]
  -- `lock`
  refine WP.bind (WP.callMC_ptrProject (projB hi₉ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_spec fits mptr rfl 0 (gP { ph := .run }) rfl io _ _ k
    hi₉)))
  rintro _ G₂ m₁₀ d₂ ⟨-, hc₁₀, hL₂, hi₁₀⟩
  -- the `ready` loop
  refine WP.bind (WP.mono ?_ (WP.loop _ _ inv24 (fun _ => 0) post24 (loop24_body io) _ G₂ m₁₀ d₂
    ⟨rfl, hc₁₀, _, hL₂, .inl rfl, hi₁₀⟩))
  rintro ⟨e, s'⟩ G₃ m₁₁ d₃ ⟨rfl, -, hc₁₁, x, hL, hx, hi₁₁, Y, hRY, hYr⟩
  dsimp only
  simp only [StateT.run_bind]
  -- `v`: the producer stored 7
  have hres := hi₁₁.1.res 0 (by rw [upd_self]; rfl)
  rw [show L.held (upd G₃ 0 (gH x hL) 0) = hL by rw [upd_self]; rfl] at hres
  have hrd : rdyOf ((upd G₃ 0 (gH x hL)) 1).2 = true := by
    rw [← hYr]; exact R_rdy (Y := fun u => (upd G₃ 0 (gH x hL) u).2) hres hRY
  refine WP.bind (WP.callMC_ptrProject (projB hi₁₁ (k := 32) (by decide)) ?_)
  dsimp only
  refine WP.bind (wp_mres (Qa := fun r => ⌜r = BitVec.ofNat 32 (vOf ((upd G₃ 0 (gH x hL)) 1).2)⌝ ∗
      R (fun u => (upd G₃ 0 (gH x hL) u).2))
    ((TTriple.load (p := bPtr.add 32) (a := 4)
      (v := BitVec.ofNat 32 (vOf ((upd G₃ 0 (gH x hL)) 1).2)) (by decide)).frame_eq
      (R := pts (bPtr.add 36) 1 (rdyOf ((upd G₃ 0 (gH x hL)) 1).2)))
    hi₁₁ hc₁₁ (fun h => h) (fun a hQ h => by
      obtain ⟨-, hR⟩ := sep_lift.mp h
      exact (R_congr (by simp only [upd0_1]) (by simp only [upd0_1]) hQ).mpr hR)
    fun a m₁₂ hQ hc₁₂ _ hq hi₁₂ => ?_)
  obtain ⟨rfl, -⟩ := sep_lift.mp hq
  rw [vOf_of_rdy hrd]
  -- `unlock`
  refine WP.bind (WP.callMC_ptrProject (projB hi₁₂ (k := 16) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_spec fits mptr rfl 0 (gH x hQ) rfl io _ _ d₃ hi₁₂)))
  rintro _ G₄ m₁₃ d₄ ⟨-, hc₁₃, hi₁₃⟩
  have hi₁₃' : proto.inv (upd G₄ 0 (gP x)) m₁₃ := hi₁₃
  -- the event wait
  refine WP.bind (WP.callMC_ptrProject (projB hi₁₃' (k := 28) (by decide)) ?_)
  dsimp only
  refine WP.bind (WP.callC (WP.mono ?_ (event_spec G₄ m₁₃ d₄ io x.cw (inv_ev0 hx hi₁₃') hc₁₃)))
  rintro _ G₅ m₁₄ d₅ ⟨hc₁₄, w, hi₁₄⟩
  have hiJ := inv_joins hi₁₄
  -- the join of the producer
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨_, hiJ, fun G₆ m₁₅ hg₆ hi₁₅ => ?_⟩)
  obtain ⟨h00, ⟨-, h0, -⟩ | ⟨hs2, hr1, -⟩⟩ := hi₁₅.2.shape
  · exfalso; change (G₆ 0).2 = _ at h0; rw [hg₆] at h0; cases h0
  refine ⟨fun _ => ⟨by decide, by rw [hs2]; decide, ⟨rfl, rfl⟩, by simp [Thread.joinValid, hr1]⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₁₅ with current := 0 }) hr1 rfl rfl, fun m₁₆ hj => ?_⟩⟩
  obtain ⟨rec, hrec, -, hm₁₆⟩ := join_eq hj
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  dsimp only
  -- the free of the `Box`
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hi₁₅.2.blk
  have hb₁₆ : m₁₆.blocks = m₁₅.blocks := by rw [hm₁₆]
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (by rw [hb₁₆]; exact hblk₀) hl₀ e he).elim)
    fun _ m₁₇ hfr => ?_)
  obtain ⟨b', blk', -, -, rfl⟩ := free_ok hfr
  refine ⟨rfl, WP.pure' ⟨rfl, fun r hr hsp => ?_⟩⟩
  -- every thread is joined
  have hth₁₆ : m₁₆.threads = m₁₅.threads.set! 1 { rec with joined := true } := by rw [hm₁₆]
  simp only [hth₁₆] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · rename_i hne
    have : i = 0 := by omega
    subst this
    rw [Array.getElem?_eq_getElem (by omega)] at h00
    rw [Option.some.inj h00]

/-! ## The results -/

/-- **`handoff` gives 7 under every schedule** (every oracle `o`, every `fuel`). -/
theorem handoff_spec {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (io : Io) (h : (Sched.run dispatch fuel o (handoff io) mem0).run = some (.ok (v, m))) :
    v = .ok 7 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec io) h
  exact hv

/-- **No run of `handoff` gives an error**: no data race, no deadlock at a futex, no
`unreachable`, under every schedule. -/
theorem handoff_safe {fuel : Nat} {o : Nat → Nat} {e : Error} (io : Io) :
    (Sched.run dispatch fuel o (handoff io) mem0).run ≠ some (.error e) :=
  proto.run_safe dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec io)

end Sync.Handoff
