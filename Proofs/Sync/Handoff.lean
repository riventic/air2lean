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
  obtain ⟨hsh, hio, hpart, hblk, hws, hwe, hwv, hS, hE, hV, hfl, hreg, hsig, hseen, hvclk, hq⟩ := hu
  refine ⟨?_, fun e he hb ho => ?_, fun u => ?_, ?_, hws.keep hkS, hwe.keep hkE, hwv.keep hkV,
    by rw [hX0, hX1, sok_congr hhS]; exact hS, by rw [hX1, eok_congr hhE]; exact hE,
    by rw [hX0, hX1, vok_congr hhV]; exact hV,
    by rw [hX0, hX1]; exact hfl, ?_, by rw [hX1, hhS, hhE]; exact hsig,
    fun h0 => ?_, fun h0 => ?_, fun w hw => ?_⟩
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
    (hw : m'.waiters = m.waiters) (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hbef : ∀ c, L.Before m c → L.Before m' c) (hio : IoOk m') (hblk : BlkOk m') : U G m' := by
  have hhS := Word.hist_keep hu.ws hkS
  have hhE := Word.hist_keep hu.we hkE
  have hhV := Word.hist_keep hu.wv hkV
  obtain ⟨hsh, -, hpart, -, hws, hwe, hwv, hS, hE, hV, hfl, hreg, hsig, hseen, hvclk, hq⟩ := hu
  refine ⟨by unfold Shape at hsh ⊢; rw [ht]; exact hsh, hio, hpart, hblk, hws.keep hkS,
    hwe.keep hkE, hwv.keep hkV, (sok_congr hhS).mpr hS, (eok_congr hhE).mpr hE,
    (vok_congr hhV).mpr hV, hfl, fun hcw => ?_, by rw [hhS, hhE]; exact hsig,
    fun h0 => by rw [hhS]; exact VClock.le_trans (hseen h0) (hcl 0),
    fun h0 => by rw [hhV]; exact VClock.le_trans (hvclk h0) (hcl 0), by
      intro w hw'; rw [hw] at hw'; exact hq w hw'⟩
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
      (Word.keep_read m (by decide) (.inr (.inl (by decide)))) rfl rfl
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

end Sync.Handoff
