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
  /-- A task after its store (holding the mutex until its `unlock`), before its finish. -/
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
  | .lk => 0 | .hl => 1 | .un => 2 | .st => 3 | .fin => 4

def isMain : Ph → Bool
  | .pre | .sm | .sp1 | .run | .ev | .rd | .rdd | .j1 => true
  | _ => false

def isTask : Ph → Bool
  | .lk | .hl | .un | .st | .fin => true
  | _ => false

/-- `main` did its `add(1)`. -/
def wa : Ph → Bool
  | .ev | .rd | .rdd | .j1 => true
  | _ => false

/-- A task stored the counter. -/
def stored : Ph → Bool
  | .un | .st | .fin => true
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
  sx g := g.2.sx = true ∧ g.2.ph = .st
  sx_set _ _ := Iff.rfl

/-- **The group's state's live set** (`Word.Ok`): the threads that may still access it, `main` and
each task before its finish. A task does not access the `Tally` after its finish, so `main`'s whole
read after its wait need be below `main` alone. -/
def WLive (g : Gh) : Prop := g.2.ph.fd = false

/-- **The event's word's live set**: `main` (from its `add(1)` on the waiter; its store of the
`Tally` and its whole read are its own accesses) and the event's own live set (`FEvent.Live`: the
setter until its `is_set` write). -/
def ELive (g : Gh) : Prop := g.2.ph.isMain = true ∨ E.Live g

/-- The live sets read only the places outside the lock. -/
theorem WLive_snd {g g' : Gh} (h : g'.2 = g.2) : WLive g' ↔ WLive g := by
  unfold WLive; rw [h]

theorem ELive_snd {g g' : Gh} (h : g'.2 = g.2) : ELive g' ↔ ELive g := by
  show (_ ∨ (g'.2.ph.wa = true ∨ (g'.2.sx = true ∧ g'.2.ph = .st)) ∧ ¬ g'.2.e.Setting) ↔
    (_ ∨ (g.2.ph.wa = true ∨ (g.2.sx = true ∧ g.2.ph = .st)) ∧ ¬ g.2.e.Setting)
  rw [h]

/-- The threads that run the lock's code: out of the event's code, and not a task while it holds
the mutex for its own steps. -/
def ok (g : Gh) : Prop := g.2.e = .out ∧ g.2.ph ≠ .hl

/-- The group's state: 0 before `startMany`, then 4, `+ 1` after `main`'s `add`, `- 2` per
finish. -/
def wgv (x0 x1 x2 : X) : Nat :=
  if x0.ph = .pre then 0 else 4 + (if x0.ph.wa then 1 else 0) - 2 * (x1.fdn + x2.fdn)

/-- A task's bound for its accesses: its clock, or its finish clock once it finished. -/
def bnd (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : VClock :=
  if (G u).2.ph.fd then (G u).2.fc else m.clocks[u]!

/-- The write `j` of the event is `is_set`. -/
def IsSetW (m : Mem) (j : Nat) : Prop := (EV.hist m)[j]!.Val (2 : BitVec 32)

/-- The bytes of the two shared words (the group's state and the event's) and the group's
padding: the `Tally` below the mutex. -/
def BoxW (l : Zig.Loc) : Prop := l.1 = 0 ∧ l.2 < 16

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
  /-- The words, for their live sets. -/
  wg : WG.Ok m (fun u => WLive (G u))
  ev : EV.Ok m (fun u => ELive (G u))
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
  /-- If `main`'s `add` read a pending task (it waits at the event), the last finish read 3. -/
  last3 : (G 0).2.ph = .ev → (G 1).2.ph.fd = true → (G 2).2.ph.fd = true →
    ∃ u, (G u).2.sx = true
  /-- Each `is_set` write is the setter's (in or after its set), above both finish clocks. -/
  isw : ∀ j < (EV.hist m).size, IsSetW m j →
    (∃ u, (G u).2.sx = true ∧ ((G u).2.e.Setting ∨ (G u).2.ph = .fin)) ∧
    VClock.le (G 1).2.fc (EV.hist m)[j]!.clock = true ∧
    VClock.le (G 2).2.fc (EV.hist m)[j]!.clock = true
  /-- At most one `is_set` write: the setter writes it once, from `out` at `st`. -/
  one : ∀ i < (EV.hist m).size, ∀ j < (EV.hist m).size, IsSetW m i → IsSetW m j → i = j
  /-- The setter at its end: the event is set. -/
  sfin : ∀ u, (G u).2.sx = true → (G u).2.ph = .fin → E.IsSet m
  /-- A finished task is `gone` for the lock. -/
  lg : ∀ u, (G u).2.ph.fd = true → (G u).1.ph = .gone
  /-- No thread above the tasks. -/
  out3 : ∀ u, 3 ≤ u → (G u).1.ph = .gone
  /-- Only `main` has the waiter's role; only one task reads 3. -/
  wa0 : ∀ u, (G u).2.ph.wa = true → u = 0
  sx1 : ∀ u v, (G u).2.sx = true → (G v).2.sx = true → u = v
  /-- Every write to the `Tally`'s bytes is below `main`'s clock, a task's bound or an `is_set`
  write (the accesses `NoRace` asks for: nonempty, in its 24 bytes). -/
  attr : ∀ e ∈ m.footprint, e.block = 0 → e.kind.isWrite = true → 0 < e.len → e.off < 24 →
    VClock.le e.clock (m.clocks[0]!) = true ∨
    (∃ u, (u = 1 ∨ u = 2) ∧ VClock.le e.clock (bnd G m u) = true) ∨
    ∃ j < (EV.hist m).size, IsSetW m j ∧ VClock.le e.clock (EV.hist m)[j]!.clock = true
  /-- After its wait, `main` is after both finishes and each `is_set` write. -/
  done : 6 ≤ (G 0).2.ph.rank → (G 1).2.ph.fd = true ∧ (G 2).2.ph.fd = true ∧
    VClock.le (G 1).2.fc (m.clocks[0]!) = true ∧ VClock.le (G 2).2.fc (m.clocks[0]!) = true ∧
    (∀ j < (EV.hist m).size, IsSetW m j → VClock.le (EV.hist m)[j]!.clock (m.clocks[0]!) = true) ∧
    ∀ u, (G u).2.sx = true → (G u).2.e.Setting ∨ (G u).2.ph = .fin
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

/-- A thread out of the lock's code with the part `r` at the places `x`. -/
def gO (r : Res) (x : X) : Gh := (⟨.out, r, rnil⟩, x)

/-- A thread with the part `r` at the places `x` that holds the mutex and its resource `rL`. -/
def gH (r rL : Res) (x : X) : Gh := (⟨.holds, r, rL⟩, x)

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
theorem wg_inRest : WG.InRest U WLive :=
  fun _ _ _ hu => ⟨hu.wg, Rest.split (fun _ => wg_box) hu.rest⟩

theorem ev_inRest : EV.InRest U ELive :=
  fun _ _ _ hu => ⟨hu.ev, Rest.split (fun _ => ev_box) hu.rest⟩

/-- The words are apart from the mutex's word. -/
theorem apG : WG.ApartL L.toLockWord := .inr (.inr (by simp [WG, L, FLock.prod]))
theorem apE : EV.ApartL L.toLockWord := .inr (.inr (by simp [EV, L, FLock.prod]))

/-! ## The stop -/

/-- A stop keeps `U`: it reads no current thread. -/
theorem atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : U G rX m) :
    U G rX { m with current := t } :=
  have wordOk : ∀ {n nb : Nat} {A : ThreadId → Prop} (W : Word n nb), W.Ok m A →
      W.Ok { m with current := t } A :=
    fun _ hw => (hw.fields_native (m' := { m with current := t })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)).1
  ⟨hu.shape, hu.rest, hu.blk, wordOk _ hu.wg, wordOk _ hu.ev,
    hu.einv.frame (t := t) (fun _ _ => rfl) rfl rfl rfl rfl (fun _ => VClock.le_refl _)
      (Nat.le_refl _) id id hu.einv.fresh,
    hu.gv, hu.gw, hu.sto, hu.last3, hu.isw, hu.one, hu.sfin, hu.lg, hu.out3, hu.wa0, hu.sx1, hu.attr,
    hu.done, hu.q⟩

/-! ## Steps that keep the threads' places -/

/-- `omega` does not see through `ThreadId`: the two thread facts it is needed for, over `Nat`. -/
theorem lt3 {u : Nat} (h : u < 3) : u = 0 ∨ u = 1 ∨ u = 2 := by omega
theorem ne_of_lt3 {u t : Nat} (h : 3 ≤ u) (ht : t < 3) : u ≠ t := by omega

/-- An access that narrows another: the other is nonempty and starts in the `Tally` too. -/
theorem narrows_box {e e₀ : FootprintEntry} (hn : e.Narrows e₀) (hl : 0 < e.len)
    (ho : e.off < 24) : 0 < e₀.len ∧ e₀.off < 24 := by
  obtain ⟨-, -, -, h1, h2, -⟩ := hn; omega

/-- The group's value reads only the places. -/
theorem wgv_congr {a b c a' b' c' : X} (ha : a'.ph = a.ph) (hb : b'.ph = b.ph) (hc : c'.ph = c.ph) :
    wgv a' b' c' = wgv a b c := by
  unfold wgv X.fdn; rw [ha, hb, hc]

/-- A task's bound grows with the clocks, at the same places. -/
theorem bnd_mono {G G' : ThreadId → Gh} {m m' : Mem} (hX : ∀ u, (G' u).2 = (G u).2)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) (u : ThreadId) :
    VClock.le (bnd G m u) (bnd G' m' u) = true := by
  unfold bnd; rw [hX u]
  split
  · exact VClock.le_refl _
  · exact hclk u

/-- **`attr` after a step at the same places** whose new write accesses to the `Tally` narrow old
ones or are below the clock of `main` or of a task that did not finish. -/
theorem attr_step {G G' : ThreadId → Gh} {rX : Res} {m m' : Mem} (hu : U G rX m)
    (hX : ∀ u, (G' u).2 = (G u).2)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hhE : EV.hist m' = EV.hist m)
    (hnew : ∀ e ∈ m'.footprint, e.block = 0 → e.kind.isWrite = true →
      (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨
      (∃ u, u < 3 ∧ (G u).2.ph.fd = false ∧ VClock.le e.clock (m'.clocks[u]!) = true)) :
    ∀ e ∈ m'.footprint, e.block = 0 → e.kind.isWrite = true → 0 < e.len → e.off < 24 →
      VClock.le e.clock (m'.clocks[0]!) = true ∨
      (∃ u, (u = 1 ∨ u = 2) ∧ VClock.le e.clock (bnd G' m' u) = true) ∨
      ∃ j < (EV.hist m').size, IsSetW m' j ∧ VClock.le e.clock (EV.hist m')[j]!.clock = true := by
  intro e he hb hk hl ho
  rcases hnew e he hb hk with ⟨e₀, he₀, hn⟩ | ⟨u, hu3, hfd, hle⟩
  · have hp := narrows_box hn hl ho
    obtain ⟨-, hb₀, hk₀, -, -, hc⟩ := hn
    rcases hu.attr e₀ he₀ (hb₀ ▸ hb) (hk₀ ▸ hk) hp.1 hp.2 with h | ⟨u, hu12, h⟩ | ⟨j, hj, hs, h⟩
    · exact .inl (VClock.le_trans hc (VClock.le_trans h (hclk 0)))
    · exact .inr (.inl ⟨u, hu12, VClock.le_trans hc (VClock.le_trans h (bnd_mono hX hclk u))⟩)
    · refine .inr (.inr ⟨j, by rw [hhE]; exact hj, ?_, ?_⟩)
      · unfold IsSetW; rw [hhE]; exact hs
      · rw [hhE]; exact VClock.le_trans hc h
  · rcases lt3 hu3 with rfl | rfl | rfl
    · exact .inl hle
    · exact .inr (.inl ⟨1, .inl rfl, by unfold bnd; rw [hX, hfd]; exact hle⟩)
    · exact .inr (.inl ⟨2, .inr rfl, by unfold bnd; rw [hX, hfd]; exact hle⟩)

/-- **`U` after a step that keeps the threads' places and the words' histories**, given the
fields that read the memory (the step's facts) and the new write accesses (`attr_step`). -/
theorem U.congrX {G G' : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} (hu : U G rX m)
    (hX : ∀ u, (G' u).2 = (G u).2) (hhW : WG.hist m' = WG.hist m) (hhE : EV.hist m' = EV.hist m)
    (hclk : ∀ u : ThreadId, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hth : m'.threads = m.threads) (rest : Rest rX' m') (blk : BlkOk m')
    (wg : WG.Ok m' (fun u => WLive (G u))) (ev : EV.Ok m' (fun u => ELive (G u)))
    (einv : E.Inv L G' m')
    (hlg : ∀ u, (G u).2.ph.fd = true → (G' u).1.ph = .gone)
    (hout3 : ∀ u, 3 ≤ u → (G' u).1.ph = .gone)
    (hnew : ∀ e ∈ m'.footprint, e.block = 0 → e.kind.isWrite = true →
      (∃ e₀ ∈ m.footprint, e.Narrows e₀) ∨
      (∃ u, u < 3 ∧ (G u).2.ph.fd = false ∧ VClock.le e.clock (m'.clocks[u]!) = true))
    (q : ∀ w ∈ m'.waiters, w.2 = L.ptr ∨ w.2 = EV.ptr) : U G' rX' m' := by
  have hY : (fun u => (G' u).2) = fun u => (G u).2 := funext hX
  refine ⟨?_, rest, blk, wg.anti fun u h => (WLive_snd (hX u)).mp h,
    ev.anti fun u h => (ELive_snd (hX u)).mp h, einv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    attr_step hu hX hclk hhE hnew, ?_, q⟩
  · rw [hY]; unfold Shape at *; rw [hth]; exact hu.shape
  · show (newest WG m').Val _; unfold newest; rw [hhW, hX 0, hX 1, hX 2]; exact hu.gv
  · intro u h; unfold newest; rw [hhW, hX u]; rw [hX u] at h; exact hu.gw u h
  · intro u h; rw [hX u] at h; rw [hX 0, hX 1, hX 2, hX u]
    obtain ⟨a, b, c, d, f⟩ := hu.sto u h
    exact ⟨a, b, c, d, fun he => let ⟨x, y⟩ := f he; ⟨VClock.le_trans x (hclk u),
      VClock.le_trans y (hclk u)⟩⟩
  · intro h0 h1 h2; rw [hX 0] at h0; rw [hX 1] at h1; rw [hX 2] at h2
    obtain ⟨u, hu'⟩ := hu.last3 h0 h1 h2; exact ⟨u, by rw [hX u]; exact hu'⟩
  · intro j hj hs; unfold IsSetW at hs; rw [hhE] at hj hs ⊢; rw [hX 1, hX 2]
    obtain ⟨⟨u, h1, h2⟩, h3, h4⟩ := hu.isw j hj hs
    exact ⟨⟨u, by rw [hX u]; exact h1, by rw [hX u]; exact h2⟩, h3, h4⟩
  · intro i hi j hj h1 h2; unfold IsSetW at h1 h2; rw [hhE] at hi hj h1 h2
    exact hu.one i hi j hj h1 h2
  · intro u h1 h2; rw [hX u] at h1 h2; exact E.IsSet_of_hist_eq hhE (hu.sfin u h1 h2)
  · intro u h; rw [hX u] at h; exact hlg u h
  · exact hout3
  · intro u h; rw [hX u] at h; exact hu.wa0 u h
  · intro u v h1 h2; rw [hX u] at h1; rw [hX v] at h2; exact hu.sx1 u v h1 h2
  · intro h; rw [hX 0] at h; rw [hX 1, hX 2]
    obtain ⟨a, b, c, d, f, k⟩ := hu.done h
    refine ⟨a, b, VClock.le_trans c (hclk 0), VClock.le_trans d (hclk 0), fun j hj hs => ?_,
      fun u hs => by rw [hX u] at hs ⊢; exact k u hs⟩
    unfold IsSetW at hs; rw [hhE] at hj hs ⊢
    exact VClock.le_trans (f j hj hs) (hclk 0)

/-- A thread that runs code out of the lock's `gone` is `main` or a task that did not finish. -/
theorem live3 {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m) {t : ThreadId}
    (hng : (G t).1.ph ≠ .gone) : t < 3 ∧ (G t).2.ph.fd = false := by
  refine ⟨Nat.lt_of_not_le fun h3 => hng (hu.out3 t h3), ?_⟩
  cases hf : (G t).2.ph.fd
  · rfl
  · exact absurd (hu.lg t hf) hng

/-! ## The lock's steps -/

theorem box_notL {l : Zig.Loc} (h : BoxW l) : ¬ L.In l := fun ⟨_, h2, _⟩ => by
  have h2' : 16 ≤ l.2 := h2
  have := h.2
  omega

theorem BlkOk.lstep {t : ThreadId} {m m' : Mem} (hb : BlkOk m) (hs : L.Step t m m') :
    BlkOk m' := by
  obtain ⟨blk, hb, hl, hsz, hk⟩ := hb
  rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
  · exact ⟨blk, by rw [e]; exact hb, hl, hsz, hk⟩
  · have h1' : m.blocks[0]? = some blk' := h1
    rw [hb] at h1'; cases h1'
    refine ⟨{ blk with bytes := writeBytes blk.bytes 16 bs }, ?_, hl, ?_, hk⟩
    · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hb).1]; rfl
    · show (writeBytes blk.bytes 16 bs).size = 24
      rw [writeBytes_size _ _ _ (by rw [h3]; exact h4), hsz]

/-- **A step of the lock's code keeps `U`** (`FLock.Fits.stable`). -/
theorem stable (G : ThreadId → Gh) (rX : Res) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Res)
    (hok : ok (G t)) (hng : L.ph (G t) ≠ .gone) (_ : L.ph (G t) ≠ .away)
    (hu : U G rX m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) rX m' := by
  have hX : ∀ u, (upd G t (L.set (G t) p h) u).2 = (G u).2 := fun u =>
    congrFun (FLock.snd_set G t p h) u
  obtain ⟨hwG, hhG⟩ := hu.wg.lockStep hs apG
  obtain ⟨hwE, hhE⟩ := hu.ev.lockStep hs apE
  obtain ⟨ht3, htf⟩ := live3 hu hng
  refine hu.congrX hX hhG hhE hs.clocks hs.threads
    (hu.rest.congr fun l hl => hs.heap (box_notL hl)) (hu.blk.lstep hs) hwG hwE
    (hu.einv.lstep hu.ev apE hok.1 (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl)
      (fun _ _ _ => Iff.rfl) hs)
    (fun u hfd => ?_) (fun u h3 => ?_) (fun e he _ _ => ?_) (fun w hw => ?_)
  · by_cases e : u = t
    · subst e; rw [htf] at hfd; cases hfd
    · rw [upd_ne _ _ e]; exact hu.lg u hfd
  · rw [upd_ne _ _ (ne_of_lt3 h3 ht3)]; exact hu.out3 u h3
  · rcases hs.fpt e he with h' | ⟨-, hle⟩
    · exact .inl ⟨e, h', .refl e⟩
    · exact .inr ⟨t, ht3, htf, hle⟩
  · by_cases hl : w.2 = L.ptr
    · exact .inl hl
    · exact hu.q w ((hs.waiters_mem w hl).mp hw)

/-- **A native framed step of thread `t` on its own part** (a tick, a step of a sync object's code
on its own stack block) keeps `U`, with the words' validity and histories and the rest. -/
theorem U_own {G : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} {t : ThreadId} {g : Gh}
    {hF : Heap} (hu : U G rX m) (hs : FStepIn hF m m') (hc : m.current = t)
    (hng : (G t).1.ph ≠ .gone) (hrest : Rest rX' m') (hbk : BlkOk m')
    (hwG : WG.Ok m' (fun u => WLive (G u))) (hwE : EV.Ok m' (fun u => ELive (G u)))
    (hhG : WG.hist m' = WG.hist m) (hhE : EV.hist m' = EV.hist m)
    (hfr : EV.Fresh m') (hX : g.2 = (G t).2) (hph : g.1.ph = (G t).1.ph) :
    U (upd G t g) rX' m' := by
  have hX' : ∀ u, (upd G t g u).2 = (G u).2 := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hX]
    · rw [upd_ne _ _ e]
  have hP' : ∀ u, (upd G t g u).1.ph = (G u).1.ph := fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self, hph]
    · rw [upd_ne _ _ e]
  obtain ⟨ht3, htf⟩ := live3 hu hng
  refine hu.congrX hX' hhG hhE hs.clock hs.threads hrest hbk hwG hwE
    (hu.einv.frame (fun u hu => upd_ne _ _ hu) (by rw [upd_self]; exact congrArg (·.e) hX)
      (by rw [upd_self]; exact hph) hhE hs.waiters hs.clock (Nat.le_of_eq (by rw [hs.threads]))
      (fun h => by rw [upd_self]; show g.2.ph.wa = true; rw [hX]; exact h)
      (fun h => by rw [upd_self]; show g.2.sx = true ∧ g.2.ph = .st; rw [hX]; exact h) hfr)
    (fun u hfd => by rw [hP']; exact hu.lg u hfd) (fun u h3 => by rw [hP']; exact hu.out3 u h3)
    (fun e he _ _ => ?_) (fun w hw => by rw [hs.waiters] at hw; exact hu.q w hw)
  rcases hs.fp e he with h' | ⟨-, -⟩
  · exact .inl h'
  rcases hs.fpc e he with h' | hle
  · exact .inl h'
  · exact .inr ⟨t, ht3, htf, by rw [← hc]; exact hle⟩

/-- The composite tick obligation: a native framed step on the caller's part. -/
theorem tickStable (t : ThreadId) (G : ThreadId → Gh) (rX : Res) (m : Mem)
    (G' : ThreadId → Gh) (rX' : Res) (m' : Mem)
    (hs : L.PartTick t G rX m G' rX' m') (hu : U G rX m) : U G' rX' m' := by
  obtain ⟨hc, hng, -, r, -, rfl, rfl, rfl, -⟩ := hs
  exact U_own hu (FStepIn.ticked m (fun _ => none)) hc hng (hu.rest.congr fun _ _ => rfl) hu.blk
    hu.wg.ticked hu.ev.ticked rfl rfl hu.einv.fresh rfl rfl

/-! ## A step of the event's code -/

theorem BlkOk.of_block {m m' : Mem} (h : BlkOk m)
    (hb : ∀ (b : BlockId) (blk : Block), m.blocks[b]? = some blk → ∃ blk', m'.blocks[b]? = some blk' ∧
      blk'.live = blk.live ∧ blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) :
    BlkOk m' := by
  obtain ⟨blk, h1, h2, h3, h4⟩ := h
  obtain ⟨blk', e1, e2, e3, e4⟩ := hb _ _ h1
  exact ⟨blk', e1, by rw [e2]; exact h2, by rw [e3]; exact h3, by rw [e4]; exact h4⟩

theorem Shape.congr {Y Y' : ThreadId → X} {m m' : Mem} (h : Shape Y m)
    (hth : m'.threads = m.threads) (hp : ∀ u, (Y' u).ph = (Y u).ph)
    (he : ∀ u, Y u = {} → Y' u = {}) : Shape Y' m' := by
  obtain ⟨h0, hm, h3, hc⟩ := h
  refine ⟨by rw [hth]; exact h0, by rw [hp]; exact hm, fun u hu => he u (h3 u hu), ?_⟩
  rw [hth, hp 0, hp 1, hp 2]
  rcases hc with ⟨a, b, c, d⟩ | ⟨a, b, c, d, f⟩ | ⟨a, b, c, d, f, g⟩
  · exact .inl ⟨a, b, he 1 c, he 2 d⟩
  · exact .inr (.inl ⟨a, b, c, d, he 2 f⟩)
  · exact .inr (.inr ⟨a, b, c, d, f, g⟩)

/-- **A step of the event's code keeps `U`** (`FLock.Fits.kstep` of `FEvent.prim`): the stepping
thread's place in the event's code moves (`FEvent.Next`); a new write of the word is `main`'s
`waiting` or the setter's `is_set`, above both finish clocks (`sto`); a new write access is that
write (`FEvent.MStep.fpNew`). -/
theorem estep (G : ThreadId → Gh) (rY : Res) (m m' : Mem) (t : ThreadId) (p : EPh) (q : LPh)
    (hlq : ((L.ph (G t) = .out ∨ (L.ph (G t) = .away ∧ E.ph (G t) = .w1)) ∧
      (q = .out ∨ (q = .away ∧ p = .w1))) ∨ (L.ph (G t) = .gone ∧ q = .gone))
    (hu : U G (rsum (EV.cellsR m) rY) m) (hY : ∀ l, EV.In l → rY.heap l = none)
    (hs : E.MStep t m m') (hN : E.Next t (G t) p m m') (hwL : L.WInv (L.pl G) m)
    (hI : E.Inv L (upd G t (L.set (E.set (G t) p) q rnil)) m') :
    U (upd G t (L.set (E.set (G t) p) q rnil)) (rsum (EV.cellsR m') rY) m' := by
  have hG : ∀ u, u ≠ t → upd G t (L.set (E.set (G t) p) q rnil) u = G u := fun u h => upd_ne _ _ h
  have hXt : (upd G t (L.set (E.set (G t) p) q rnil) t).2 = { (G t).2 with e := p } := by
    rw [upd_self]; rfl
  have hph : ∀ u, (upd G t (L.set (E.set (G t) p) q rnil) u).2.ph = (G u).2.ph ∧
      (upd G t (L.set (E.set (G t) p) q rnil) u).2.fc = (G u).2.fc ∧
      (upd G t (L.set (E.set (G t) p) q rnil) u).2.sx = (G u).2.sx := fun u => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact ⟨rfl, rfl, rfl⟩
    · rw [hG u e]; exact ⟨rfl, rfl, rfl⟩
  have he : ∀ u, u ≠ t → (upd G t (L.set (E.set (G t) p) q rnil) u).2.e = (G u).2.e :=
    fun u h => by rw [hG u h]
  have hclk := hs.clocks
  have hcs : m.clocks.size = m.threads.size := hwL.csize
  obtain ⟨hwG, hhG⟩ := hs.wordApart hu.wg (.inr (.inr (by decide)))
  obtain ⟨hwE, hhE⟩ := hs.word hu.ev (.inl rfl)
  -- the stepping thread's roles
  have hEt : E.ph (upd G t (L.set (E.set (G t) p) q rnil) t) = p := by rw [upd_self]; rfl
  have hwx : p.Waiting → (G t).2.ph.wa = true := fun hp => by
    have := hI.wx t (by rw [hEt]; exact hp)
    have h2 : (upd G t (L.set (E.set (G t) p) q rnil) t).2.ph.wa = true := this
    rwa [(hph t).1] at h2
  have hsx : p.Setting → (G t).2.sx = true := fun hp => by
    have := (hI.sx t (by rw [hEt]; exact hp)).1
    have h2 : (upd G t (L.set (E.set (G t) p) q rnil) t).2.sx = true := this
    rwa [(hph t).2.2] at h2
  have hpo : (G t).2.ph.wa = false → (G t).2.sx = false → p = .out := fun h1 h2 => by
    cases p with
    | out => rfl
    | w0 => rw [hwx (.inl rfl)] at h1; cases h1
    | w1 => rw [hwx (.inr rfl)] at h1; cases h1
    | sw => rw [hsx (.inl rfl)] at h2; cases h2
    | sd => rw [hsx (.inr rfl)] at h2; cases h2
  -- a setter stays a setter; `out` is reached only from a waiter's place
  have hsetT : (G t).2.e.Setting → p.Setting := fun hS => by
    rcases hN with ⟨-, hn⟩ | ⟨_, _, -, ⟨-, -, h0, -⟩ | ⟨-, -, -, h0, -⟩⟩
    · have hn' : EPh.Next (G t).2.e p (E.IsSet m) := hn
      rcases hS with h | h <;> rw [h] at hn' <;> simp only [EPh.Next] at hn'
      · rcases hn' with h' | h' <;> rw [h'] <;> simp [EPh.Setting]
      · rw [hn']; simp [EPh.Setting]
    · have h0' : (G t).2.e = .w0 := h0
      rcases hS with h | h <;> rw [h] at h0' <;> cases h0'
    · have h0' : (G t).2.e = .out := h0
      rcases hS with h | h <;> rw [h] at h0' <;> cases h0'
  have hset : ∀ u, (G u).2.sx = true → (G u).2.e.Setting →
      (upd G t (L.set (E.set (G t) p) q rnil) u).2.e.Setting := fun u _ hS => by
    by_cases e : u = t
    · subst e; rw [hXt]; exact hsetT hS
    · rw [he u e]; exact hS
  -- the live sets: the places stay, and a thread in the event's code enters none of them
  have hwG' : WG.Ok m' (fun u => WLive (upd G t (L.set (E.set (G t) p) q rnil) u)) :=
    hwG.anti fun u h => by unfold WLive at h ⊢; rw [← (hph u).1]; exact h
  have hwE' : EV.Ok m' (fun u => ELive (upd G t (L.set (E.set (G t) p) q rnil) u)) :=
    hwE.anti fun u h => by
      by_cases e : u = t
      · subst e
        rw [upd_self] at h
        rcases h with h | ⟨hr, hn⟩
        · exact .inl h
        · exact .inr ⟨hr, fun hS => hn (hsetT hS)⟩
      · rwa [hG u e] at h
  have hto : (G t).2.sx = true → p = .out → (G t).2.e = .out := fun hx hp => by
    subst hp
    rcases hN with ⟨-, hn⟩ | ⟨_, _, -, ⟨-, -, -, h⟩ | ⟨-, -, -, h, -⟩⟩
    · have hn' : EPh.Next (G t).2.e .out (E.IsSet m) := hn
      cases h' : (G t).2.e <;> rw [h'] at hn' <;>
        simp only [EPh.Next, reduceCtorEq, or_self] at hn' <;> try rfl
      all_goals
        have hw := hu.einv.wx t (by show (G t).2.e.Waiting; rw [h']; simp [EPh.Waiting])
        have h0 := hu.wa0 t hw
        subst h0
        exact absurd (hu.sto 0 hx).1 (by decide)
    · cases h
    · exact h
  -- the new writes of the event's word
  have hpush : ∀ x, EV.hist m' = (EV.hist m).push x →
      (t = 0 ∧ ¬ x.Val (2 : BitVec 32)) ∨
      ((G t).2.sx = true ∧ (G t).2.ph = .st ∧ (G t).2.e = .out ∧ p.Setting ∧
        x.Val (2 : BitVec 32) ∧ x.clock = m'.clocks[t]!) := fun x hx => by
    rcases hN with ⟨hh, -⟩ | ⟨ord, v, hh, ⟨rfl, hw, -, -⟩ | ⟨rfl, ⟨hx', hst⟩, -, h0, hS⟩⟩
    · have h2 : (EV.hist m).push x = EV.hist m := hx.symm.trans hh
      have := congrArg Array.size h2; simp at this
    · have hx2 := Array.push_inj_right.mp (hx.symm.trans hh)
      refine .inl ⟨hu.wa0 t hw, fun h2 => ?_⟩
      rw [hx2] at h2
      exact absurd (FEvent.val_eq h2 FEvent.rmwEnt_val) (by decide)
    · have hx2 := Array.push_inj_right.mp (hx.symm.trans hh)
      exact .inr ⟨hx', hst, h0, hS, by rw [hx2]; exact FEvent.rmwEnt_val, by rw [hx2]; rfl⟩
  -- old writes stay
  have hold : ∀ j < (EV.hist m).size, j < (EV.hist m').size ∧ (EV.hist m')[j]! = (EV.hist m)[j]! :=
    fun j hj => by
      rcases hhE with e | ⟨-, x, e⟩
      · rw [e]; exact ⟨hj, rfl⟩
      · rw [e]; exact ⟨by simp; omega, Word.get_push_lt hj⟩
  have hsetS : (EV.hist m').size = (EV.hist m).size ∨ ∃ x, EV.hist m' = (EV.hist m).push x :=
    hhE.imp (fun e => by rw [e]) fun ⟨_, x, e⟩ => ⟨x, e⟩
  have hnewj : ∀ j < (EV.hist m').size, (EV.hist m).size ≤ j → ∃ x,
      EV.hist m' = (EV.hist m).push x ∧ j = (EV.hist m).size ∧ (EV.hist m')[j]! = x := fun j hj hle => by
    rcases hhE with e | ⟨-, x, e⟩
    · rw [e] at hj; omega
    · rw [e] at hj; simp at hj
      refine ⟨x, e, by omega, ?_⟩
      rw [e, show j = (EV.hist m).size by omega, Word.get_push_eq]
  refine ⟨Shape.congr hu.shape hs.threads (fun u => (hph u).1) fun u hu0 => ?_,
    Rest.step (fun _ => ev_box) hu.rest rfl hY (fun l _ hw => hs.cells hw),
    hu.blk.of_block fun _ _ hb => hs.block hb, hwG', hwE', hI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- shape: a thread without a role stays out of the event's code
    by_cases e : u = t
    · subst e
      rw [hXt, hu0, hpo (by rw [hu0]; rfl) (by rw [hu0])]
    · rw [hG u e]; exact hu0
  · -- gv
    show (newest WG m').Val _; unfold newest
    rw [hhG, wgv_congr (hph 0).1 (hph 1).1 (hph 2).1]; exact hu.gv
  · -- gw
    intro u h; unfold newest; rw [hhG, (hph u).2.1]; rw [(hph u).1] at h; exact hu.gw u h
  · -- sto
    intro u h; rw [(hph u).2.2] at h; rw [(hph 0).1, (hph 1).1, (hph 2).1, (hph 1).2.1, (hph 2).2.1]
    obtain ⟨a, b, c, d, f⟩ := hu.sto u h
    refine ⟨a, b, c, d, fun hout => ?_⟩
    have hout' : (G u).2.e = .out := by
      by_cases e : u = t
      · subst e; rw [hXt] at hout; exact hto h hout
      · rw [he u e] at hout; exact hout
    obtain ⟨x, y⟩ := f hout'
    exact ⟨VClock.le_trans x (hclk u), VClock.le_trans y (hclk u)⟩
  · -- last3
    intro h0 h1 h2; rw [(hph 0).1] at h0; rw [(hph 1).1] at h1; rw [(hph 2).1] at h2
    obtain ⟨u, hu'⟩ := hu.last3 h0 h1 h2; exact ⟨u, by rw [(hph u).2.2]; exact hu'⟩
  · -- isw
    intro j hj hsj
    rw [(hph 1).2.1, (hph 2).2.1]
    by_cases hlt : j < (EV.hist m).size
    · obtain ⟨-, hgj⟩ := hold j hlt
      unfold IsSetW at hsj; rw [hgj] at hsj ⊢
      obtain ⟨⟨u, h1, h2⟩, h3, h4⟩ := hu.isw j hlt hsj
      refine ⟨⟨u, by rw [(hph u).2.2]; exact h1, ?_⟩, h3, h4⟩
      rcases h2 with h2 | h2
      · exact .inl (hset u h1 h2)
      · exact .inr (by rw [(hph u).1]; exact h2)
    · obtain ⟨x, hx, rfl, hgx⟩ := hnewj j hj (by omega)
      unfold IsSetW at hsj; rw [hgx] at hsj ⊢
      rcases hpush x hx with ⟨-, hn⟩ | ⟨hx', -, ho, hS, -, hc⟩
      · exact absurd hsj hn
      · obtain ⟨-, -, -, -, f⟩ := hu.sto t hx'
        obtain ⟨a, b⟩ := f ho
        refine ⟨⟨t, by rw [(hph t).2.2]; exact hx', .inl (by rw [hXt]; exact hS)⟩, ?_, ?_⟩
        · rw [hc]; exact VClock.le_trans a (hclk t)
        · rw [hc]; exact VClock.le_trans b (hclk t)
  · -- one: a new `is_set` write is the setter's from `out` at `st`, which wrote none before
    intro i hi j hj hsi hsj
    have key : ∀ k < (EV.hist m').size, IsSetW m' k → k < (EV.hist m).size ∨
        ((G t).2.sx = true ∧ (G t).2.ph = .st ∧ (G t).2.e = .out ∧ k = (EV.hist m).size) :=
      fun k hk hsk => by
        by_cases hlt : k < (EV.hist m).size
        · exact .inl hlt
        · obtain ⟨x, hx, rfl, hgx⟩ := hnewj k hk (by omega)
          unfold IsSetW at hsk; rw [hgx] at hsk
          rcases hpush x hx with ⟨-, hn⟩ | ⟨hx', hst, ho, -, -, -⟩
          · exact absurd hsk hn
          · exact .inr ⟨hx', hst, ho, rfl⟩
    have oldS : ∀ k < (EV.hist m).size, IsSetW m' k → IsSetW m k := fun k hk hsk => by
      unfold IsSetW at hsk ⊢; rw [(hold k hk).2] at hsk; exact hsk
    have noOld : (G t).2.sx = true → (G t).2.ph = .st → (G t).2.e = .out →
        ∀ k < (EV.hist m).size, ¬ IsSetW m k := fun hx hst ho k hk hsk => by
      obtain ⟨⟨u, h1, h2⟩, -, -⟩ := hu.isw k hk hsk
      obtain rfl := hu.sx1 u t h1 hx
      rcases h2 with h2 | h2
      · rw [ho] at h2; rcases h2 with h2 | h2 <;> cases h2
      · rw [hst] at h2; cases h2
    rcases key i hi hsi with hi' | ⟨hx, hst, ho, hi'⟩
    · rcases key j hj hsj with hj' | ⟨hx, hst, ho, -⟩
      · exact hu.one i hi' j hj' (oldS i hi' hsi) (oldS j hj' hsj)
      · exact absurd (oldS i hi' hsi) (noOld hx hst ho i hi')
    · rcases key j hj hsj with hj' | ⟨-, -, -, hj'⟩
      · exact absurd (oldS j hj' hsj) (noOld hx hst ho j hj')
      · rw [hi', hj']
  · -- sfin: the event stays set
    intro u h1 h2; rw [(hph u).2.2] at h1; rw [(hph u).1] at h2
    have hS := hu.sfin u h1 h2
    have hpos := FEvent.hist_pos hu.ev
    rcases hhE with e | ⟨-, x, e⟩
    · exact E.IsSet_of_hist_eq e hS
    · refine hI.isSet_of (j := (EV.hist m).size - 1) ?_ ?_
      · show _ < (EV.hist m').size; rw [e, Array.size_push]; omega
      · show ((EV.hist m')[(EV.hist m).size - 1]!).Val _
        rw [e, Word.get_push_lt (by omega)]; exact hS
  · -- lg
    intro u h; rw [(hph u).1] at h
    by_cases e : u = t
    · subst e
      have hg := hu.lg u h
      rw [upd_self]; show q = .gone
      rcases hlq with ⟨h' | ⟨h', -⟩, -⟩ | ⟨-, hq⟩
      · exact absurd (h'.symm.trans hg) (by decide)
      · exact absurd (h'.symm.trans hg) (by decide)
      · exact hq
    · rw [hG u e]; exact hu.lg u h
  · -- out3
    intro u h3
    by_cases e : u = t
    · subst e
      have hg := hu.out3 u h3
      rw [upd_self]; show q = .gone
      rcases hlq with ⟨h' | ⟨h', -⟩, -⟩ | ⟨-, hq⟩
      · exact absurd (h'.symm.trans hg) (by decide)
      · exact absurd (h'.symm.trans hg) (by decide)
      · exact hq
    · rw [hG u e]; exact hu.out3 u h3
  · intro u h; rw [(hph u).1] at h; exact hu.wa0 u h
  · intro u v h1 h2; rw [(hph u).2.2] at h1; rw [(hph v).2.2] at h2; exact hu.sx1 u v h1 h2
  · -- attr
    have hbnd : ∀ u, VClock.le (bnd G m u) (bnd (upd G t (L.set (E.set (G t) p) q rnil)) m' u) = true :=
      fun u => by unfold bnd; rw [(hph u).1, (hph u).2.1]; split
                  · exact VClock.le_refl _
                  · exact hclk u
    intro e hfe hb hk hl ho
    rcases hs.fpNew hfe with ⟨e₀, he₀, hn⟩ | ⟨htid, hle, hw⟩
    · have hp := narrows_box hn hl ho
      obtain ⟨-, hb₀, hk₀, -, -, hc⟩ := hn
      rcases hu.attr e₀ he₀ (hb₀ ▸ hb) (hk₀ ▸ hk) hp.1 hp.2 with h | ⟨u, hu12, h⟩ | ⟨j, hj, hsj, h⟩
      · exact .inl (VClock.le_trans hc (VClock.le_trans h (hclk 0)))
      · exact .inr (.inl ⟨u, hu12, VClock.le_trans hc (VClock.le_trans h (hbnd u))⟩)
      · obtain ⟨hj', hgj⟩ := hold j hj
        refine .inr (.inr ⟨j, hj', ?_, ?_⟩)
        · unfold IsSetW at hsj ⊢; rw [hgj]; exact hsj
        · rw [hgj]; exact VClock.le_trans hc h
    · obtain ⟨x, hx⟩ := hw hk
      replace hx : EV.hist m' = (EV.hist m).push x := hx
      rcases hpush x hx with ⟨rfl, -⟩ | ⟨-, -, -, -, hv, hc⟩
      · exact .inl hle
      · refine .inr (.inr ⟨(EV.hist m).size, by rw [hx]; simp, ?_, ?_⟩)
        · unfold IsSetW; rw [hx, Word.get_push_eq]; exact hv
        · rw [hx, Word.get_push_eq, hc]; exact hle
  · -- done: no new `is_set` write after `main`'s wait
    intro h; rw [(hph 0).1] at h; rw [(hph 1).1, (hph 2).1, (hph 1).2.1, (hph 2).2.1]
    obtain ⟨a, b, c, d, f, k⟩ := hu.done h
    refine ⟨a, b, VClock.le_trans c (hclk 0), VClock.le_trans d (hclk 0), fun j hj hsj => ?_,
      fun u hx => ?_⟩
    · by_cases hlt : j < (EV.hist m).size
      · obtain ⟨-, hgj⟩ := hold j hlt
        unfold IsSetW at hsj; rw [hgj] at hsj ⊢
        exact VClock.le_trans (f j hlt hsj) (hclk 0)
      · obtain ⟨x, hx, rfl, hgx⟩ := hnewj j hj (by omega)
        unfold IsSetW at hsj; rw [hgx] at hsj
        rcases hpush x hx with ⟨-, hn⟩ | ⟨hx', hst, ho, -, -, -⟩
        · exact absurd hsj hn
        · -- after `main`'s wait the setter is past its write (or ended): no new `is_set`
          rcases k t hx' with hS | hS
          · rcases hS with h' | h' <;> rw [h'] at ho <;> cases ho
          · rw [hst] at hS; cases hS
    · rw [(hph u).2.2] at hx
      rcases k u hx with hS | hS
      · exact .inl (hset u hx hS)
      · exact .inr (by rw [(hph u).1]; exact hS)
  · -- q
    intro w hw
    rcases hs.waiters hw with h' | rfl
    · exact hu.q w h'
    · exact .inr rfl

/-- **The protocol has the lock**, for the threads that run its code (`ok`). -/
theorem fitsL : L.Fits (FPrim.empty Gh) proto U ok :=
  .ofLock (fun _ _ => Iff.rfl) (fun _ h => h.1) (fun _ h => h.1) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) stable (fun _ _ _ t _ hu => atStop t hu) tickStable

/-- The frame of a native step on the caller's part covers the event's cells. -/
theorem frame_ev {G : ThreadId → Gh} {rY : Res} {m : Mem}
    (hu : U G (rsum (EV.cellsR m) rY) m) {x : Nat} (h1 : EV.o ≤ x) (h2 : x < EV.o + 4) :
    (rsum (L.wordR m) (rsum (EV.cellsR m) rY)).heap.erase (EV.b, x) ≠ none := by
  have hc := hu.ev.cellIn (l := (EV.b, x)) ⟨rfl, h1, h2⟩
  simp only [FHeap.erase, FHeap.union_apply, Word.cellsR, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and]
  intro _
  rw [cellsAt_of (W := EV.In) ⟨rfl, h1, h2⟩]
  intro h; exact absurd (Option.map_eq_none_iff.mp h) hc

/-! ## A native step on the caller's part, next to the event -/

theorem wg_ev {l : Zig.Loc} (h : WG.In l) : ¬ EV.In l := fun h' => by
  obtain ⟨-, -, h3⟩ := h; obtain ⟨-, h2, -⟩ := h'; simp [WG, EV] at h2 h3; omega

theorem heap_blk {m : Mem} {blk : Block} (hb : m.blocks[0]? = some blk) (hl : blk.live = true)
    (hk : blk.kind = .stack) {x : Nat} (hx : x < blk.bytes.size) :
    m.heap (0, x) = some ⟨blk.bytes[x], blk.addr, blk.bytes.size, blk.kind⟩ := by
  simp [Mem.heap, hb, hl, hx, hk, BlockKind.mappedLo]

/-- The bytes of the `Tally` below the mutex are live. -/
theorem box_live {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : U G rX m) {l : Zig.Loc}
    (hl : BoxW l) : m.heap l ≠ none := by
  obtain ⟨b, x⟩ := l
  obtain ⟨h1, h2⟩ := hl
  simp only at h1 h2; subst h1
  obtain ⟨blk, hb, hlv, hs, hk⟩ := hu.blk
  rw [heap_blk hb hlv hk (by omega)]; nofun

/-- The frame of a step on a part with the mutex's word and the rest has the words' bytes. -/
theorem frame_box {rX : Res} {m : Mem} (hr : Rest rX m) {l : Zig.Loc} (hl : BoxW l)
    (hw : m.heap l ≠ none) : (rsum (L.wordR m) rX).heap.erase l ≠ none := by
  obtain ⟨rB, -, -, rfl⟩ := hr
  have := cellsAt_some hl hw (m := m)
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff, Option.or_eq_none_iff,
    not_and]
  intro _ h; exact absurd h this

/-- **The `Tally` is block 0**: live, 24 bytes on the stack (the extent in the rest). -/
theorem blk_of {G : ThreadId → Gh} {c rY rB : Res} {m : Mem} (hi : L.Inv G (rsum c rY) m)
    (hB : bext 0 24 .stack rB) (hg : rY.gh = rB.gh) : BlkOk m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  simp only at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [hg, bauth_eq hB] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 24 .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

/-- A byte of the `Tally` that the rest after a step holds with its cell before it: the same
cell (the block is pinned). -/
theorem cell_eq {G' : ThreadId → Gh} {rX' : Res} {m m' : Mem} (hbk : BlkOk m)
    (hbk' : BlkOk m') (hi' : L.Inv G' rX' m') {x : Nat} (hx : x < 24)
    (hr : rX'.heap (0, x) = (m.heap (0, x)).map fun c => ⟨c, none⟩) :
    m'.heap (0, x) = m.heap (0, x) := by
  obtain ⟨blk, hb, hlv, hs, hk⟩ := hbk
  obtain ⟨blk', hb', hlv', hs', hk'⟩ := hbk'
  have e := heap_blk hb hlv hk (by omega : x < blk.bytes.size)
  have e' := heap_blk hb' hlv' hk' (by omega : x < blk'.bytes.size)
  rw [e] at hr
  have hrc := hi'.restCell (l := (0, x)) hr
  rw [e', e]
  rw [e'] at hrc
  simp only [Option.map_some, Option.some.injEq, Cell.norm, Cell.mk.injEq] at hrc
  obtain ⟨hby, had, -⟩ := hrc
  simp only [Option.some.injEq, Cell.mk.injEq]
  exact ⟨hby, had, by omega, by rw [hk, hk']⟩

/-- **A native step of `t` on its own part, out of the lock** (the second step of
`FPrim.ofWords`) keeps `U`: the lock's invariant after it pins the block and the cells of the
group's word (`cell_eq`); the event's word is the step's. -/
theorem U_own_native {G : ThreadId → Gh} {rY : Res} {m m' : Mem} {t : ThreadId} {r : Res}
    (hu : U G (rsum (EV.cellsR m) rY) m) (hY : ∀ l, EV.In l → rY.heap l = none)
    (hng : (G t).1.ph ≠ .gone) (hc : m.current = t)
    (hs : FStepIn (rsum (L.wordR m) (rsum (EV.cellsR m) rY)).heap.erase m m')
    (hcW : ∀ l, EV.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm)
    (hh : EV.hist m' = EV.hist m)
    (hL : L.Inv (upd G t (L.setPart (G t) r)) (rsum (EV.cellsR m') rY) m') :
    U (upd G t (L.setPart (G t) r)) (rsum (EV.cellsR m') rY) m' := by
  obtain ⟨rB, hB, hBoff, hrX⟩ := hu.rest
  have hg : rY.gh = rB.gh := by
    have := congrArg Res.gh hrX; simpa [cellsAt, Word.cellsR] using this
  have hbk' := blk_of hL hB hg
  have hcs : ∀ l, BoxW l → ¬ EV.In l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ ⟨h0, h1⟩ hw
    simp only at h0 h1; subst h0
    refine cell_eq hu.blk hbk' hL (by omega) ?_
    have := congrFun (congrArg Res.heap hrX) (0, x)
    simp only [FHeap.union_apply] at this ⊢
    rw [cellsAt_none hw, Option.none_or] at this ⊢
    rw [this, cellsAt_of (W := BoxW) ⟨rfl, h1⟩, hBoff _ ⟨rfl, h1⟩, Option.or_none]
  have hcov : ∀ l, BoxW l → (rsum (L.wordR m) (rsum (EV.cellsR m) rY)).heap.erase l ≠ none :=
    fun l hl => frame_box hu.rest hl (box_live hu hl)
  have hnG : ∀ l, WG.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm :=
    fun l hl => by rw [hcs l (wg_box hl) (wg_ev hl)]
  exact U_own hu hs hc hng (Rest.step (fun _ => ev_box) hu.rest rfl hY hcs) hbk'
    (hu.wg.fstep hs (fun l hl => hcov l (wg_box hl)) hnG)
    (hu.ev.fstep hs (fun l hl => hcov l (ev_box hl)) hcW)
    (Word.hist_fstep hu.wg hs (fun l hl => hcov l (wg_box hl)) hnG) hh
    (hu.einv.fresh.fstep hs (fun x h1 h2 => hcov _ (ev_box ⟨rfl, h1, h2⟩))
      (fun i l hl => (hu.ev.loc i l hl).1)) rfl rfl

/-- **The protocol has the event** (the lock's laws as for `fitsL`). -/
theorem fitsE : L.Fits (E.prim L) proto U ok := { fitsL with
  kfin g h := by show g.2.e = _; rw [h.2.2]
  kjoins g h := by show g.2.e = _; rw [h.2.2]
  sub _ _ _ hu := ⟨hu.einv, fun _ hW => by
    subst hW; exact ⟨hu.ev.anti fun _ h => .inr h, Rest.split (fun _ => ev_box) hu.rest⟩⟩
  apart _ hW := hW ▸ apE
  lph _ _ := rfl
  lpart _ _ := rfl
  lheld _ _ := rfl
  lR G t p r hr := by
    change R (fun u => (upd G t (E.set (G t) p) u).2) r
    have : (fun u => (upd G t (E.set (G t) p) u).2) = fun u => { (G u).2 with e := (if u = t then p else (G u).2.e) } := by
      funext u; unfold upd; split
      · rename_i e; subst e; rfl
      · rfl
    rw [this]; exact hr
  ph_l _ _ _ := rfl
  set_l _ _ _ _ := rfl
  ph_part _ _ := rfl
  set_part _ _ _ := rfl
  role_l _ _ _ _ := Iff.rfl
  role_part _ _ _ := Iff.rfl
  ok_calm _ _ _ h := h.elim
  kstep := by
    intro t G rX m G' rX' m' hs hu
    rcases hs with hs | hs
    · rcases hs with ⟨W, rY, rfl, rfl, rfl, hY, hI,
        ⟨p, q, h, ⟨hlq, rfl, hs, hN⟩, hwL, rfl⟩ | ⟨r, hout, hi, hc, hs, hcW, -, hh, hL, rfl⟩⟩
      · exact estep G rY m m' t p q hlq hu hY hs hN hwL hI
      · exact U_own_native hu hY
          (fun h => absurd ((show L.ph (G t) = .gone from h).symm.trans hout) (by decide))
          hc hs hcW hh hL
    · exact tickStable t G rX m G' rX' m' hs hu }

end Threadsync.WG
