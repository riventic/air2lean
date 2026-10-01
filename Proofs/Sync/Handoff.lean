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
  the mutex's release (`RegHB`); a reader of epoch 1 then reads the producer's signal (`sig`,
  `seen`); `main` reads its own `waiting` or a newer write (`vclk`).
- **The futex queue** (`QOk`): only `main` sleeps at the epoch or the event, and only while the
  producer has not woken it. So a thread that sleeps there is not the last one.
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Sync Assn

namespace Sync.Handoff

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
  /-- The producer stored `ready = true`. -/
  | rdy
  /-- The producer in `signal`, before its load of the state. -/
  | sg0
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
  | .seen | .sg0 => 5
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
  | .lk | .hl | .v7 | .rdy | .sg0 | .sg1 | .sgp | .wk | .set | .setw | .fin => true
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
def WS : Word := ⟨0, 20⟩
def WE : Word := ⟨0, 24⟩
def WV : Word := ⟨0, 28⟩

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
    ((G 1).2.ph = .rdy ∨ (G 1).2.ph = .sg0 ∨ (G 1).2.ph = .sg1 →
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
theorem mptr : ((bPtr.add 16).add 0).add 0 = L.ptr := rfl

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
theorem off_own {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {W : Word} (hb : W.b = 0)
    (ho : W.o + 4 ≤ 32) (u : ThreadId) : W.Off (L.own G m u) := fun x _ h2 => by
  rw [hb]; exact own_none hi u (by omega)

theorem off_R {W : Word} (hb : W.b = 0) (ho : W.o + 4 ≤ 32) :
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
def Wd (W : Word) : Prop := W = WS ∨ W = WE ∨ W = WV

theorem Wd.ok {W : Word} (hW : Wd W) {G : ThreadId → Gh} {m : Mem} (hu : U G m) : W.Ok m := by
  rcases hW with rfl | rfl | rfl
  · exact hu.ws
  · exact hu.we
  · exact hu.wv

theorem Wd.ap {W : Word} (hW : Wd W) : Word.Apart L W := by
  rcases hW with rfl | rfl | rfl
  · exact apS
  · exact apE
  · exact apV

theorem Wd.blk {W : Word} (hW : Wd W) : W.b = 0 ∧ W.o + 4 ≤ 32 := by
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
theorem linv_op {W : Word} (hW : Wd W) {G : ThreadId → Gh} {t : ThreadId} {m m' : Mem}
    (hi : proto.inv G m) (hop : W.Op t m m') : L.Inv G m' :=
  hi.1.wordOp (hW.ok hi.2) hop hW.ap (fun u => off_own hi (hW.blk).1 (hW.blk).2 u)
    (off_R (hW.blk).1 (hW.blk).2 G)

theorem op_of_cur {W : Word} {t : ThreadId} {m₁ m' : Mem}
    (hop : W.Op t { m₁ with current := t } m') : W.Op t m₁ m' :=
  ⟨hop.current, hop.threads, hop.waiters, hop.woken, hop.groups, hop.csize, hop.others,
    hop.mine, hop.bsize, hop.cells, hop.fp, ⟨hop.locs.new, hop.locs.same⟩⟩

/-- An atomic load at a shared word, with a decode (`atomicLoadAsC`), by thread `t` (`g`). -/
theorem wp_loadAs {α : Type} [Packed α 32] {σ : Type} {s : σ} {t : ThreadId} {G : ThreadId → Gh}
    {m : Mem} {n : Nat} {g : Gh} {W : Word} (hW : Wd W) {ord : AtomicOrder}
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
    {W : Word} (hW : Wd W) {ord : AtomicOrder} (hi : proto.inv (upd G t g) m)
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
    {W : Word} (hW : Wd W) {op : RmwOp} {signed : Bool} {ord : AtomicOrder} {v : BitVec 32}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    {Q : BitVec 32 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' old, G₁ t = g → proto.inv G₁ m₁ →
      (last (W.hist m₁)).Val old → W.U32 m' (op.apply signed old v) →
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
    {m : Mem} {n : Nat} {g : Gh} {W : Word} (hW : Wd W) {op : RmwOp} {ord : AtomicOrder} {v : α}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    (hdec : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → ∀ b, (last (W.hist m₁)).Val b →
      ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m' old r, G₁ t = g → proto.inv G₁ m₁ →
      (Packed.ofBits? (α := α) old).run = some (.ok r) →
      (last (W.hist m₁)).Val old → W.U32 m' (op.apply false old (Packed.toBits v)) →
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
    {m : Mem} {n : Nat} {g : Gh} {W : Word} (hW : Wd W) {succ fail : AtomicOrder} {exp new : α}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size)
    (hdec : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → ∀ j < (W.hist m₁).size, ∀ b,
      (W.hist m₁)[j]!.Val b → ∃ r, (Packed.ofBits? (α := α) b).run = some (.ok r))
    {Q : Option α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∀ G₁ m₁ m', G₁ t = g → proto.inv G₁ m₁ → W.Ok m' → W.Op t m₁ m' →
      L.Inv G₁ m' →
      ((last (W.hist m₁)).Val (Packed.toBits exp) → W.U32 m' (Packed.toBits new) →
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

/-! ## `U` after an op at a shared word -/

theorem Wd.lo {W : Word} (hW : Wd W) : 20 ≤ W.o := by
  rcases hW with rfl | rfl | rfl <;> decide

/-- Two shared words do not overlap. -/
theorem Wd.apart {W W' : Word} (hW : Wd W) (hW' : Wd W') (hne : W' ≠ W) :
    W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o := by
  rcases hW with rfl | rfl | rfl <;> rcases hW' with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | decide

/-- An op at `W` keeps the writes of another shared word. -/
theorem hist_op {W W' : Word} (hW : Wd W) (hW' : Wd W') (hne : W' ≠ W) {G : ThreadId → Gh}
    {t : ThreadId} {m₁ m' : Mem} (hu : U G m₁) (hop : W.Op t m₁ m') : W'.hist m' = W'.hist m₁ :=
  Word.hist_keep (hW'.ok hu) (Word.keep_op hop (hW.apart hW' hne))

/-- `U` after an op at a shared word, from the facts that depend on the ghost values and the
writes. -/
theorem U_op {W : Word} (hW : Wd W) {G G' : ThreadId → Gh} {t : ThreadId} {m₁ m' : Mem}
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

/-! ## The producer -/

/-- The producer's ghost value outside the lock's code. -/
def gP (x : X) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, x)

/-- The producer's ghost value while it holds the mutex and the resource `h`. -/
def gH (x : X) (h : Heap) : Gh := (⟨.holds, Heap.empty, h⟩, x)

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
  have hr'' : ¬ (g'.2.ph = .rdy ∨ g'.2.ph = .sg0 ∨ g'.2.ph = .sg1) := by
    rintro (h | h | h) <;> rw [h] at hr' <;> simp [Ph.rank] at hr'
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

/-- A thread's lock part with the same `v` and `ready`: the lock's invariant stays. -/
theorem linv_x {G : ThreadId → Gh} {m : Mem} {a : LG} {x x' : X} (hL : L.Inv (upd G 1 (a, x)) m)
    (hv : vOf x' = vOf x) (hr : rdyOf x' = rdyOf x) : L.Inv (upd G 1 (a, x')) m :=
  hL.congr (fun u => by unfold upd; split <;> rfl) (fun u => by unfold upd; split <;> rfl)
    (fun u => by unfold upd; split <;> rfl) fun h => by
      change R (fun u => (upd G 1 (a, x') u).2) h ↔ R (fun u => (upd G 1 (a, x) u).2) h
      exact R_congr (by simp only [upd_self]; exact hv) (by simp only [upd_self]; exact hr) h

theorem upd_g {G : ThreadId → Gh} {t : ThreadId} {g : Gh} (hg : G t = g) : upd G t g = G := by
  rw [← hg]; exact upd_same G t

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

theorem val_eq {x : Word.Entry} {a b : BitVec 32} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

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

/-- A thread at another futex than the mutex is `main`. -/
theorem qok_main {G : ThreadId → Gh} {m : Mem} (hq : QOk G m) {w : ThreadId × Ptr}
    (hw : w ∈ m.waiters) (hl : w.2 ≠ L.ptr) : w.1 = 0 := by
  rcases hq w hw with h | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h hl
  · exact h1
  · exact h1

/-- After a futex wake of `n ≥ 1` at a shared word, no thread waits at it. -/
theorem wake_w {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {W : Word} {n : Nat} (hq : QOk G m)
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
  have hk : ∀ W : Word, W.Keep m₁ m' := fun W => by
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
      (x'.ph = .rdy ∨ x'.ph = .sg0 ∨ x'.ph = .sg1 ∨ (G 0).2.cw = false) →
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
      (by decide) (by decide) ?_ (.inr (.inr (.inl rfl))) (fun h => by simp [Ph.rank] at h)⟩
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
      (by decide) (by decide) ?_ (.inr (.inr (.inr hcw'))) (fun _ hw => ?_)⟩
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

theorem liftM_res {α σ : Type} (x : Result α) : (liftM x : CM Tgt σ α) = callRC x := rfl

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
  have := (hu.reg (by rw [upd1_0]; exact hcw)).2 (by rw [upd_self]; exact .inr (.inr rfl))
  exact this

theorem bits10 : Packed.toBits (cst 1 0) = sv 1 := by decide
theorem bits11 : Packed.toBits ({ waiters := (cst 1 0).waiters, signals := 1 } : Io_Condition_State) =
    sv 2 := by decide

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
    rw [show ((bPtr.add 20).add 0).add 0 = WS.ptr from rfl]
    refine WP.bind (wp_casAs (.inl rfl) (g := gP { ph := .sg1 }) hi (ht1 (by simp [gP]))
      (fun _ _ _ _ _ _ b _ => ⟨_, ofBits_cst b⟩) fun k hk G₁ m₁ m' hg₁ hi₁ hw' hop hL =>
        ⟨fun hv hU hh hacq => ?_, fun j b r hne hd hj hv hfl hacq hh => ?_⟩)
    · have hi₂ := inv_sgp (G := G₁) (by rw [upd_g hg₁]; exact hi₁) hw' hop
        (by rw [upd_g hg₁]; exact hL) (by rw [hh, bits11])
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      simp only [StateT.run_bind]
      rw [show ((bPtr.add 20).add 4).add 0 = WE.ptr from rfl]
      refine WP.bind (WP.bind (wp_rmw (.inr (.inl rfl)) (g := gP { ph := .sgp, cw := true }) hi₂
        (ht1 (by simp [gP])) fun k₂ hk₂ G₂ m₂ m₃ old hg₂ hi₃ hv₃ hU₃ hh₃ hacq₃ hw₃ hop₃ hL₃ => ?_))
      have hi₄ := inv_wk (G := G₂) (by rw [upd_g hg₂]; exact hi₃) hw₃ hop₃
        (by rw [upd_g hg₂]; exact hL₃) hv₃ hh₃
      refine WP.bind (WP.futexWakeC fun k₃ hk₃ => ⟨_, hi₄, fun G₃ m₄ hg₃ hi₅ m₅ hw => ?_⟩)
      have hi₆ := inv_set (G := G₃) (by rw [upd_g hg₃]; exact hi₅) hw
      simp only [StateT.run_pure]
      refine WP.pure' (WP.pure' (WP.pure' ?_))
      simp only [Io_Condition_signal.again11, Bool.false_eq_true, ↓reduceIte]
      exact ⟨.inl rfl, (wake_w hi₅.2.q (by decide) (Nat.le_refl _) hw).1, true, hi₆⟩
    · exact (sg1_noFail (G := G₁) (by rw [upd_g hg₁]; exact hi₁) (by rw [← bits10]; exact hne)
        hj hv hfl).elim
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
  rw [show ((bPtr.add 20).add 0).add 0 = WS.ptr from rfl]
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

theorem ofBits_ev0 : (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 0)).run = some (.ok .unset) := rfl
theorem ofBits_ev1 : (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 1)).run = some (.ok .waiting) := rfl
theorem ofBits_ev2 : (Packed.ofBits? (α := Io_Event) (BitVec.ofNat 32 2)).run = some (.ok .is_set) := rfl
theorem bits_set : RmwOp.xchg.apply false (0 : BitVec 32) (Packed.toBits Io_Event.is_set) =
    BitVec.ofNat 32 2 := rfl

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

/-- The event's newest write, while the producer is before its `xchg`: `waiting` iff `main`
wrote it. -/
theorem ev_last {G : ThreadId → Gh} {m : Mem} {b : Bool}
    (hi : proto.inv (upd G 1 (gP { ph := .set, cw := b })) m) :
    (last (WV.hist m)).Val (if (G 0).2.vw then 1 else 0) := by
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
        rcases hr with h | h | h <;> rw [h] at h9 <;> simp [Ph.rank] at h9
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
  have hk : ∀ W : Word, W.Keep m₁ m' := fun W => Word.keep_of hb' ha' hf' ht'' hcl
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
  rw [ptr_add_zero]
  refine WP.bind (wp_io hi hc (live1 hi (by decide)) fun m₁ hc₁ ht₁ hi₁ => ?_)
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.lock_spec fits mptr 1 (gP { ph := .lk }) rfl _ G
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
  refine WP.bind (wp_io hi₄ hc₄ (live1 hi₄ (by simp [gH])) fun m₅ hc₅ ht₅ hi₅ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (MutexOps.unlock_spec fits mptr 1 (gH { ph := .rdy } hQ') rfl
    _ G₂ m₅ d₂ hi₅)))
  rintro _ G₃ m₆ d₃ ⟨hd₃, hc₆, hi₆⟩
  have hi₆' : proto.inv (upd G₃ 1 (gP { ph := .rdy })) m₆ := hi₆
  -- `signal`
  refine WP.bind (wp_io hi₆' hc₆ (live1 hi₆' (by simp [gP])) fun m₇ hc₇ ht₇ hi₇ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (signal_spec G₃ m₇ d₃ _ hi₇ hc₇)))
  rintro _ G₄ m₈ d₄ ⟨hc₈, b, hi₈⟩
  -- `Event.set`
  refine WP.bind (wp_io hi₈ hc₈ (live1 hi₈ (by simp [gP])) fun m₉ hc₉ ht₉ hi₉ => ?_)
  refine WP.bind (WP.callC (WP.mono ?_ (set_spec G₄ m₉ d₄ _ b hi₉ hc₉)))
  rintro _ G₅ m₁₀ d₅ ⟨hc₁₀, hi₁₀⟩
  refine WP.pure' ?_
  exact WP.pure' ⟨hc₁₀, _, rfl, hi₁₀⟩

end Sync.Handoff
