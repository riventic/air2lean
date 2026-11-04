import Proofs.Threadsync.Variant
import ZigLean.Sep.Full.Mutex
import ZigLean.Sep.Full.Event
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Conc.Share

/-!
# The protocol of `threadsync.waitGroup` (full-state logic)

`waitGroup` (`Proofs/Threadsync/WaitGroup.lean`): `main` stores a `Tally` (block 0: the group's
state, a `u64` at 0, the group's `Thread.ResetEvent` at 8, the `Thread.Mutex` at 16, the counter
at 20), runs `startMany(2)`, spawns two tasks and waits on the group; it then reads the whole
`Tally` and joins the tasks. A task adds 1 to the counter under the mutex and finishes the group
(`fetchSub(2, acqRel)`); the one whose `fetchSub` reads 3 (`main` waits, the other task finished)
sets the event. This file is the protocol, as a client of the generic contracts of the mutex
(`MutexImpl`) and the event (`EventImpl`).

- **Ghost values** (`Gh = FLG × X`): the lock's part, and `X`: the thread's place (`Ph`), its place
  in the event's code (`e`), a task's clock after its finish (`fc`) and whether it read 3 (`sx`:
  the event's setter role, `FEvent.sx`; `main` from its `add(1)` on has the waiter role).
- **The lock** (`L`, `FLock.prod`): the mutex at 16 owns the counter at 20, whose value is the
  number of tasks that stored it.
- **The group's state** `WG` and **the event** `EV` are shared words in the protocol's rest
  (`Rest`, `Word.InRest`). The state's newest write is `wgv` (`gv`), and its release clock is
  above each finish (`gw`): each `fetchSub` is `acqRel`, and the RMWs of `main` continue the
  release sequence.
- **The set**: the setter read 3, so `main` added and both tasks finished, and both finish clocks
  are below the setter's clock (`sto`); each `is_set` write is the setter's and above both finish
  clocks (`isw`).
- **`main`'s read of the whole `Tally`** (`FLock.Fits.wp_readAll`): every write access to block 0
  is below `main`'s clock, a task's bound (`bnd`: its clock, its finish clock once it finished) or
  an `is_set` write (`attr`; an event step's write access is a write of the word:
  `FEvent.MStep.fpNew`). After `main`'s wait both tasks finished below `main`'s clock and each
  `is_set` write happened before it (`done`, from the wait's `FEvent.Synced` and
  `FEvent.Inv.synced_first`), so the read races with no write; the tasks are lock-`gone` after
  their finish (`lg`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Full Zig.Full.FAssn

namespace Threadsync.WG

/-- Where a thread is in the program. -/
inductive Ph where
  | none
  /-- `main` before `startMany`. -/
  | pre
  /-- `main` after `startMany`. -/
  | sm
  /-- `main` after the first spawn. -/
  | sp1
  /-- `main` after the second spawn, before its `add(1)`. -/
  | run
  /-- `main` after an `add(1)` that read a pending task: in the event's `wait`. -/
  | ev
  /-- `main` after its wait (or an `add(1)` that read none pending), before its read. -/
  | rd
  /-- `main` read the `Tally` (at its first join). -/
  | rdd
  /-- `main` at its second join. -/
  | j1
  /-- A task before (or in) `lock`. -/
  | lk
  /-- A task that holds the mutex, before its store of the counter. -/
  | hl
  /-- A task that holds the mutex, after its store. -/
  | inc
  /-- A task after `unlock`, before its finish. -/
  | un
  /-- The setter: its finish read 3, before the end of its `set`. -/
  | st
  /-- A task after its finish (the setter after its `set`). -/
  | fin
  deriving DecidableEq

namespace Ph

def rank : Ph → Nat
  | .none => 0
  | .pre => 0 | .sm => 1 | .sp1 => 2 | .run => 3 | .ev => 4 | .rd => 6 | .rdd => 7 | .j1 => 8
  | .lk => 0 | .hl => 1 | .inc => 2 | .un => 3 | .st => 4 | .fin => 5

def isMain : Ph → Bool
  | .pre | .sm | .sp1 | .run | .ev | .rd | .rdd | .j1 => true
  | _ => false

def isTask : Ph → Bool
  | .lk | .hl | .inc | .un | .st | .fin => true
  | _ => false

/-- `main` did its `add(1)`. -/
def wa : Ph → Bool
  | .ev | .rd | .rdd | .j1 => true
  | _ => false

/-- A task stored the counter. -/
def stored : Ph → Bool
  | .inc | .un | .st | .fin => true
  | _ => false

/-- A task did its finish. -/
def fd : Ph → Bool
  | .st | .fin => true
  | _ => false

end Ph

/-- A thread's ghost value outside the lock (module doc). -/
structure X where
  ph : Ph := .none
  e : EPh := .out
  fc : VClock := #[]
  sx : Bool := false

abbrev Gh := FLG × X

/-- The `Tally` (block 0). -/
def bPtr : Ptr := ⟨some 0, 0⟩

/-- A task's store of the counter. -/
def X.cnt (x : X) : Nat := if x.ph.stored then 1 else 0

/-- A task's finish. -/
def X.fdn (x : X) : Nat := if x.ph.fd then 1 else 0

/-- The counter holds the stores of both tasks. -/
def R (Y : ThreadId → X) : FAssn :=
  up (pts (bPtr.add 20) 4 (BitVec.ofNat 32 ((Y 1).cnt + (Y 2).cnt)))

/-- The `Thread.Mutex`: bytes 16..20 of the `Tally`, the OS's contended value. -/
abbrev L : FLock Gh := FLock.prod 0 16 R mutexC (by decide)

/-- The group's state (bytes 0..8) and the event's state (bytes 8..12). -/
def WG : Word 64 8 := { b := 0, o := 0 }
def EV : Word 32 4 := { b := 0, o := 8 }

/-- The event: its place is `X.e`; `main` waits from its `add(1)` on, the task that read 3 sets. -/
def E : FEvent Gh where
  W := EV
  ph g := g.2.e
  set g p := (g.1, { g.2 with e := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  wx g := g.2.ph.wa = true
  wx_set _ _ := Iff.rfl
  sx g := g.2.sx = true
  sx_set _ _ := Iff.rfl

/-- The threads that run the lock's code: out of the event's code, and not a task while it holds
the mutex for its own steps. -/
def ok (g : Gh) : Prop := g.2.e = .out ∧ g.2.ph ≠ .hl ∧ g.2.ph ≠ .inc

/-- The group's state: 0 before `startMany`, then 4, `+ 1` after `main`'s `add`, `- 2` per
finish. -/
def wgv (x0 x1 x2 : X) : Nat :=
  if x0.ph = .pre then 0 else 4 + (if x0.ph.wa then 1 else 0) - 2 * (x1.fdn + x2.fdn)

/-- A task's bound for its accesses: its clock, or its finish clock once it finished. -/
def bnd (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : VClock :=
  if (G u).2.ph.fd then (G u).2.fc else m.clocks[u]!

/-- The write `j` of the event is `is_set`. -/
def IsSetW (m : Mem) (j : Nat) : Prop := (EV.hist m)[j]!.Val (2 : BitVec 32)

/-- The bytes of the two shared words: the group's state and the event's. -/
def BoxW (l : Zig.Loc) : Prop := l.1 = 0 ∧ l.2 < 12

instance (l : Zig.Loc) : Decidable (BoxW l) := by unfold BoxW; infer_instance

/-- The protocol's rest `rX`: the cells of the two words, and the `Tally`'s extent (it pins the
block for every thread's step). -/
def Rest (rX : Res) (m : Mem) : Prop :=
  ∃ rB, bext 0 24 .stack rB ∧ (∀ l, BoxW l → rB.heap l = none) ∧ rX = rsum (cellsAt BoxW m) rB

/-- Block 0 is the live `Tally`, 24 bytes on the stack. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 24 ∧ blk.kind = .stack

/-- The threads: `main` alone before its spawns; then the tasks, which `main` spawned. -/
def Shape (Y : ThreadId → X) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧ (Y 0).ph.isMain ∧ (∀ u, 3 ≤ u → Y u = {}) ∧
  ((m.threads.size = 1 ∧ (Y 0).ph.rank ≤ 1 ∧ Y 1 = {} ∧ Y 2 = {}) ∨
   (m.threads.size = 2 ∧ (Y 0).ph = .sp1 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
     (Y 1).ph.isTask ∧ Y 2 = {}) ∨
   (m.threads.size = 3 ∧ 3 ≤ (Y 0).ph.rank ∧ (Y 1).ph.isTask ∧ (Y 2).ph.isTask ∧
     m.threads[1]? = some { spawner := 0, joined := decide ((Y 0).ph = .j1) } ∧
     m.threads[2]? = some { spawner := 0, joined := false }))

/-- The newest write of a word. -/
abbrev newest {n nb : Nat} (W : Word n nb) (m : Mem) : Word.Entry := (W.hist m)[(W.hist m).size - 1]!

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  rest : Rest rX m
  blk : BlkOk m
  wg : WG.Ok m
  ev : EV.Ok m
  einv : E.Inv L G m
  /-- The group's newest write. -/
  gv : (newest WG m).Val (BitVec.ofNat 64 (wgv (G 0).2 (G 1).2 (G 2).2))
  /-- Its release clock is above each finish. -/
  gw : ∀ u, (G u).2.ph.fd = true → VClock.le (G u).2.fc (newest WG m).relClock = true
  /-- The setter read 3: `main` added, both tasks finished, and both finish clocks are below the
  setter's clock until its `is_set` write. -/
  sto : ∀ u, (G u).2.sx = true → (u = 1 ∨ u = 2) ∧ (G 0).2.ph.wa = true ∧
    (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
    ((G u).2.e = .out → VClock.le (G 1).2.fc (m.clocks[u]!) = true ∧
      VClock.le (G 2).2.fc (m.clocks[u]!) = true)
  /-- After `main`'s `add`, the last finish read 3. -/
  last3 : (G 0).2.ph.wa = true → (G 1).2.ph.fd = true → (G 2).2.ph.fd = true →
    ∃ u, (G u).2.sx = true
  /-- Each `is_set` write is the setter's (in or after its set), above both finish clocks. -/
  isw : ∀ j < (EV.hist m).size, IsSetW m j →
    (∃ u, (G u).2.sx = true ∧ ((G u).2.e.Setting ∨ (G u).2.ph = .fin)) ∧
    VClock.le (G 1).2.fc (EV.hist m)[j]!.clock = true ∧
    VClock.le (G 2).2.fc (EV.hist m)[j]!.clock = true
  /-- The setter at its end: the event is set. -/
  sfin : ∀ u, (G u).2.sx = true → (G u).2.ph = .fin → E.IsSet m
  /-- A finished task is `gone` for the lock. -/
  lg : ∀ u, (G u).2.ph.fd = true → (G u).1.ph = .gone
  /-- Every write to the `Tally` is below `main`'s clock, a task's bound or an `is_set` write. -/
  attr : ∀ e ∈ m.footprint, e.block = 0 → e.kind.isWrite = true →
    VClock.le e.clock (m.clocks[0]!) = true ∨
    (∃ u, (u = 1 ∨ u = 2) ∧ VClock.le e.clock (bnd G m u) = true) ∨
    ∃ j < (EV.hist m).size, IsSetW m j ∧ VClock.le e.clock (EV.hist m)[j]!.clock = true
  /-- After its wait, `main` is after both finishes and each `is_set` write. -/
  done : 6 ≤ (G 0).2.ph.rank → (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
    VClock.le (G 1).2.fc (m.clocks[0]!) = true ∧ VClock.le (G 2).2.fc (m.clocks[0]!) = true ∧
    ∀ j < (EV.hist m).size, IsSetW m j → VClock.le (EV.hist m)[j]!.clock (m.clocks[0]!) = true
  /-- A thread waits only at the mutex or the event. -/
  q : ∀ w ∈ m.waiters, w.2 = L.ptr ∨ w.2 = EV.ptr

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := ∃ rX, L.Inv G rX m ∧ U G rX m
  init tgt g := match tgt with
    | .task p => p = bPtr ∧ ∃ rp, plain rp ∧ g = (⟨.out, rp, rnil⟩, { ph := .lk })
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.ph = .fin ∧ g.2.e = .out
  strict := true
  joins g := g.1.ph = .out ∧ (g.2.ph = .rdd ∨ g.2.ph = .j1) ∧ g.2.e = .out

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 2 ∧ joinedAll 0 m

/-! ## The rest: the shared words' cells -/

theorem res_eq {a b : Res} (hh : a.heap = b.heap) (hk : a.know = b.know) (hg : a.gh = b.gh) :
    a = b := by
  cases a; cases b; simp only at hh hk hg; subst hh hk hg; rfl

theorem wg_box {l : Zig.Loc} (h : WG.In l) : BoxW l := by
  obtain ⟨h1, -, h3⟩ := h; exact ⟨h1, by simp [WG] at h3; omega⟩

theorem ev_box {l : Zig.Loc} (h : EV.In l) : BoxW l := by
  obtain ⟨h1, -, h3⟩ := h; exact ⟨h1, by simp [EV] at h3; omega⟩

/-- A word of the two in the rest: its cells and the others. -/
theorem Rest.split {n nb : Nat} {rX : Res} {m : Mem} {W : Word n nb} (hW : ∀ l, W.In l → BoxW l)
    (h : Rest rX m) : ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none := by
  obtain ⟨rB, -, hB, rfl⟩ := h
  refine ⟨rsum (cellsAt (fun l => BoxW l ∧ ¬ W.In l) m) rB, res_eq ?_ ?_ ?_, fun l hl => ?_⟩
  · funext l
    simp only [FHeap.union_apply, Word.cellsR]
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), cellsAt_none (fun h => h.2 hw), hB l (hW l hw)]
      simp
    · rw [cellsAt_none hw]
      by_cases hb : BoxW l
      · rw [cellsAt_of hb, cellsAt_of (W := fun l => BoxW l ∧ ¬ W.In l) ⟨hb, hw⟩]; simp
      · rw [cellsAt_none hb, cellsAt_none (W := fun l => BoxW l ∧ ¬ W.In l) (fun h => hb h.1)]
        simp
  · simp [cellsAt, Word.cellsR, Know.none_union]
  · simp [cellsAt, Word.cellsR]
  · simp only [FHeap.union_apply]
    rw [cellsAt_none (W := fun l => BoxW l ∧ ¬ W.In l) (fun h => h.2 hl), hB l (hW l hl)]; rfl

/-- After a step that changes only the bytes of the word `W` among the two (the other's cells
stay), the rest has `W`'s new cells. -/
theorem Rest.step {n nb : Nat} {rX rY : Res} {m m' : Mem} {W : Word n nb}
    (hW : ∀ l, W.In l → BoxW l) (h : Rest rX m) (hX : rX = rsum (W.cellsR m) rY)
    (hY : ∀ l, W.In l → rY.heap l = none) (hm : ∀ l, BoxW l → ¬ W.In l → m'.heap l = m.heap l) :
    Rest (rsum (W.cellsR m') rY) m' := by
  obtain ⟨rB, hR, hB, rfl⟩ := h
  have hk : rY.know = rB.know := by
    have := congrArg Res.know hX; simpa [cellsAt, Word.cellsR, Know.none_union] using this.symm
  have hg : rY.gh = rB.gh := by
    have := congrArg Res.gh hX; simpa [cellsAt, Word.cellsR] using this.symm
  refine ⟨rB, hR, hB, res_eq ?_ ?_ ?_⟩
  · funext l
    have hl := congrFun (congrArg Res.heap hX) l
    simp only [FHeap.union_apply, Word.cellsR] at hl ⊢
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), hY l hw, hB l (hW l hw)]
    · rw [cellsAt_none hw, Option.none_or] at hl ⊢
      rw [← hl]
      by_cases hb : BoxW l
      · rw [cellsAt_of hb, cellsAt_of hb, hm l hb hw]
      · rw [cellsAt_none hb, cellsAt_none hb]
  · simp [cellsAt, Word.cellsR, Know.none_union, hk]
  · simp [cellsAt, Word.cellsR, hg]

/-- A step that keeps the cells of the two words keeps the rest. -/
theorem Rest.congr {rX : Res} {m m' : Mem} (h : Rest rX m)
    (hm : ∀ l, BoxW l → m'.heap l = m.heap l) : Rest rX m' := by
  obtain ⟨rB, hR, hB, rfl⟩ := h
  refine ⟨rB, hR, hB, res_eq ?_ rfl rfl⟩
  funext l
  simp only [FHeap.union_apply]
  by_cases hb : BoxW l
  · rw [cellsAt_of hb, cellsAt_of hb, hm l hb]
  · rw [cellsAt_none hb, cellsAt_none hb]

/-- The words are in the protocol's rest (`Word.InRest`). -/
theorem wg_inRest : WG.InRest U := fun _ _ _ hu => ⟨hu.wg, Rest.split (fun _ => wg_box) hu.rest⟩

theorem ev_inRest : EV.InRest U := fun _ _ _ hu => ⟨hu.ev, Rest.split (fun _ => ev_box) hu.rest⟩

/-- The words are apart from the mutex's word. -/
theorem apG : WG.ApartL L.toLockWord := .inr (.inl (by simp [WG, L, FLock.prod]))
theorem apE : EV.ApartL L.toLockWord := .inr (.inl (by simp [EV, L, FLock.prod]))

/-! ## The stop -/

/-- A stop keeps `U`: it reads no current thread. -/
theorem atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : U G rX m) :
    U G rX { m with current := t } :=
  have wordOk : ∀ {n nb : Nat} (W : Word n nb), W.Ok m → W.Ok { m with current := t } :=
    fun _ hw => (hw.fields_native (m' := { m with current := t })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)).1
  ⟨hu.shape, hu.rest, hu.blk, wordOk _ hu.wg, wordOk _ hu.ev,
    hu.einv.frame (t := t) (fun _ _ => rfl) rfl rfl rfl rfl (fun _ => VClock.le_refl _)
      (Nat.le_refl _) id id hu.einv.fresh,
    hu.gv, hu.gw, hu.sto, hu.last3, hu.isw, hu.sfin, hu.lg, hu.attr, hu.done, hu.q⟩

end Threadsync.WG
