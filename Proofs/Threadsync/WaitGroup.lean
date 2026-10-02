import Proofs.Threadsync.Lock
import ZigLean.Conc.Word

/-!
# `threadsync.waitGroup` over all schedules

`waitGroup` starts a `Thread.WaitGroup` with 2, spawns two tasks and waits on the group. Each
task adds 1 to a counter under a `Thread.Mutex` and finishes the group; the last one to finish
after `main` began to wait sets the group's `Thread.ResetEvent`. Then `main` reads the counter
(0.15.2 reads the whole `Tally` struct) and joins the tasks. All sync objects are translated from
Zig 0.15.2's std code (Linux); the futex under them is the model. The result is 2 under every
schedule (`waitGroup_spec`), and no schedule gives an error (`waitGroup_safe`).

The mutex (bytes 16..20 of the `Tally`, block 0) is a lock that owns the counter (bytes 20..24,
`R`; contended value 3). The group's state (a `u64`, bytes 0..8) and the event's state (bytes
8..12) are shared atomic words. This file proves the rest:

- **Ghost values** (`Gh = LG × X`): the lock's part, the thread's place (`Ph`), and for a task its
  clock after its finish (`fc`), its clock after its last access to the `Tally` (`fz`, when it is
  `frozen`) and whether it set the event (`sx`).
- **The writes**: the group's state is `4 + 1 (main waits) - 2 (each finish)`, and its newest
  write's release clock is above each finish (`gw`). The event's writes are `0`, `1` (`main`) and
  `2` (the setter, `ev`); the set happened after the clocks of both tasks (`setc`).
- **`main`'s read**: when `main` stops waiting, both tasks are `frozen` and their clocks are below
  `main`'s (`done`). Each access to the `Tally` is by a thread and below its clock, or its frozen
  clock (`attr`). So `main`'s read of the whole `Tally` does not race. The tasks are `gone` for the
  lock after their finish, so the read keeps the lock's invariant (`Lock.Inv.readAll`).
-/

open Zig Zig.Conc Zig.Conc.Proto Zig.Conc.Lock Assn

namespace Threadsync.WG

open Threadsync.ThreadMutexOps

/-- Where a thread is, outside the lock's code. -/
inductive Ph where
  | none
  /-- `main`, before `startMany`. -/
  | pre
  /-- `main`, after `startMany`. -/
  | sm
  /-- `main`, after the first spawn. -/
  | sp1
  /-- `main`, after the second spawn, before its `add(1)`. -/
  | run
  /-- `main` in the event's `wait`, before it wrote `1`. -/
  | ev0
  /-- `main` wrote `1` to the event (it waits at the futex). -/
  | ev1
  /-- `main` read `2` from the event. -/
  | evd
  /-- `main` stopped waiting, before its read of the `Tally`. -/
  | rd
  /-- `main` read the `Tally` (at its first join). -/
  | rdd
  /-- `main` at its second join. -/
  | j1
  /-- A task before `lock`. -/
  | lk
  /-- A task that holds the mutex, before its store of the counter. -/
  | hl
  /-- A task that holds the mutex, after its store. -/
  | inc
  /-- A task after `unlock`, before its finish. -/
  | un
  /-- The setter after its finish (it read `3`), before its load of the event. -/
  | s0
  /-- The setter after its load of the event. -/
  | s1
  /-- The setter after its `xchg(2)`, which read `1`: before its futex wake. -/
  | wk
  /-- A task after its last access to the `Tally`. -/
  | dn
  /-- The task has ended. -/
  | fin
  deriving DecidableEq

def Ph.rank : Ph → Nat
  | .none => 0
  | .pre => 0 | .sm => 1 | .sp1 => 2 | .run => 3 | .ev0 => 4 | .ev1 => 5 | .evd => 6
  | .rd => 7 | .rdd => 8 | .j1 => 9
  | .lk => 0 | .hl => 1 | .inc => 2 | .un => 3 | .s0 => 4 | .s1 => 5 | .wk => 6 | .dn => 7
  | .fin => 8

def Ph.isMain : Ph → Bool
  | .pre | .sm | .sp1 | .run | .ev0 | .ev1 | .evd | .rd | .rdd | .j1 => true
  | _ => false

def Ph.isTask : Ph → Bool
  | .lk | .hl | .inc | .un | .s0 | .s1 | .wk | .dn | .fin => true
  | _ => false

/-- The ghost value of a thread outside the lock. -/
structure X where
  ph : Ph := .none
  /-- `main` wrote `1` to the event. -/
  e1 : Bool := false
  /-- A task: its clock after its finish. -/
  fc : VClock := #[]
  /-- A task: its clock after its last access to the `Tally`. -/
  fz : VClock := #[]
  /-- A task: it wrote `2` to the event. -/
  sx : Bool := false

abbrev Gh := LG × X

/-- A task did its store of the counter. -/
def X.cnt (x : X) : Nat := if x.ph.isTask ∧ 2 ≤ x.ph.rank then 1 else 0

/-- A task did its finish. -/
def X.fd (x : X) : Bool := x.ph.isTask && decide (4 ≤ x.ph.rank)

/-- A task did its last access to the `Tally`. -/
def X.frozen (x : X) : Bool := x.ph.isTask && decide (6 ≤ x.ph.rank)

/-- `main` did its `add(1)`. -/
def X.wa (x : X) : Bool := x.ph.isMain && decide (4 ≤ x.ph.rank)

/-- The `Tally` (block 0). -/
def bPtr : Ptr := ⟨some 0, 0⟩

/-- The counter holds the stores of both tasks. -/
def R (X : ThreadId → X) : Assn := pts (bPtr.add 20) 4 (BitVec.ofNat 32 ((X 1).cnt + (X 2).cnt))

/-- The `Thread.Mutex`: bytes 16..20 of the `Tally`, contended value `3`. -/
abbrev L : Lock Gh := Lock.prod 0 16 R 3 (.inr rfl)

/-- The group's state (bytes 0..8) and the event's state (bytes 8..12). -/
def WG : Word 64 8 := { b := 0, o := 0 }
def EV : Word 32 4 := { b := 0, o := 8 }

/-- The newest write of a word. -/
abbrev last (h : Array Word.Entry) : Word.Entry := h[h.size - 1]!

/-- `main` before `startMany`. -/
def X.isPre (x : X) : Bool := x.ph == .pre

/-- The setter, between its finish and its `xchg(2)`. -/
def X.st (x : X) : Bool := x.ph == .s0 || x.ph == .s1

/-- `main` in the event's `wait`, before it read `2`. -/
def X.e01 (x : X) : Bool := x.ph == .ev0 || x.ph == .ev1

def X.isEv1 (x : X) : Bool := x.ph == .ev1
def X.isEvd (x : X) : Bool := x.ph == .evd

/-- The group's state: `4` after `startMany`, `+ 1` after `main`'s `add`, `- 2` per finish. -/
def wgv (x0 x1 x2 : X) : Nat :=
  if x0.isPre then 0 else
    4 + (if x0.wa then 1 else 0) - 2 * ((if x1.fd then 1 else 0) + (if x2.fd then 1 else 0))

/-- The event's writes: `0`, then `1` by `main`, then `2` by the setter. -/
def evL (x0 x1 x2 : X) : List Nat :=
  [0] ++ (if x0.e1 then [1] else []) ++ (if x1.sx || x2.sx then [2] else [])

def EVOk (m : Mem) (vs : List Nat) : Prop :=
  (EV.hist m).size = vs.length ∧ ∀ j (h : j < vs.length), (EV.hist m)[j]!.Val (BitVec.ofNat 32 vs[j])

/-- Thread `u`'s clock, or its frozen clock. -/
def ac (G : ThreadId → Gh) (m : Mem) (u : ThreadId) : VClock :=
  if (G u).2.frozen then (G u).2.fz else m.clocks[u]!

/-- The threads: `main` alone before its spawns; then the tasks, which `main` spawned. -/
def Shape (X : ThreadId → X) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧ (X 0).ph.isMain ∧ (∀ u, 3 ≤ u → X u = {}) ∧
  ((m.threads.size = 1 ∧ (X 0).ph.rank ≤ 1 ∧ X 1 = {} ∧ X 2 = {}) ∨
   (m.threads.size = 2 ∧ (X 0).ph = .sp1 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
     (X 1).ph.isTask ∧ X 2 = {}) ∨
   (m.threads.size = 3 ∧ 3 ≤ (X 0).ph.rank ∧ (X 1).ph.isTask ∧ (X 2).ph.isTask ∧
     m.threads[1]? = some { spawner := 0, joined := (X 0).ph = .j1 } ∧
     m.threads[2]? = some { spawner := 0, joined := false }))

/-- Block 0 is the live `Tally`: 24 bytes on the stack, at an address that is a multiple of 8. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 24 ∧ blk.addr % 8 = 0 ∧
    blk.kind = .stack

/-- The futex queue: a thread at another futex than the mutex is `main` at the event, while no
task set it or the setter has not woken it yet. -/
def QOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  ∀ w ∈ m.waiters, w.2 = L.ptr ∨
    (w.1 = 0 ∧ w.2 = EV.ptr ∧ (G 0).2.ph = .ev1 ∧
      ((!(G 1).2.sx && !(G 2).2.sx) = true ∨ (G 1).2.ph = .wk ∨ (G 2).2.ph = .wk))

/-- Two ghost values that agree on what `Pre` reads. -/
structure XEq (x x' : X) : Prop where
  isPre : x'.isPre = x.isPre
  wa : x'.wa = x.wa
  fd : x'.fd = x.fd
  frozen : x'.frozen = x.frozen
  sx : x'.sx = x.sx
  e1 : x'.e1 = x.e1
  st : x'.st = x.st
  e01 : x'.e01 = x.e01
  isEv1 : x'.isEv1 = x.isEv1
  isEvd : x'.isEvd = x.isEvd
  fc : x'.fc = x.fc
  fz : x'.fz = x.fz

theorem XEq.refl (x : X) : XEq x x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem XEq.symm {x y : X} (h : XEq x y) : XEq y x :=
  ⟨h.isPre.symm, h.wa.symm, h.fd.symm, h.frozen.symm, h.sx.symm, h.e1.symm, h.st.symm,
    h.e01.symm, h.isEv1.symm, h.isEvd.symm, h.fc.symm, h.fz.symm⟩

theorem XEq.trans {x y z : X} (h : XEq x y) (h' : XEq y z) : XEq x z :=
  ⟨h'.isPre.trans h.isPre, h'.wa.trans h.wa, h'.fd.trans h.fd, h'.frozen.trans h.frozen,
    h'.sx.trans h.sx, h'.e1.trans h.e1, h'.st.trans h.st, h'.e01.trans h.e01,
    h'.isEv1.trans h.isEv1, h'.isEvd.trans h.isEvd, h'.fc.trans h.fc, h'.fz.trans h.fz⟩

/-- The two tasks. -/
def Pair (u v : ThreadId) : Prop := u = 1 ∧ v = 2 ∨ u = 2 ∧ v = 1

/-- The facts before `main`'s read of the `Tally` (module doc). -/
structure Pre (G : ThreadId → Gh) (m : Mem) : Prop where
  wg : WG.Ok m
  ev : EV.Ok m
  gv : (last (WG.hist m)).Val (BitVec.ofNat 64 (wgv (G 0).2 (G 1).2 (G 2).2))
  /-- The newest write of the group's state happened after each finish. -/
  gw : ∀ u, u = 1 ∨ u = 2 → (G u).2.fd → VClock.le (G u).2.fc (last (WG.hist m)).relClock = true
  evh : EVOk m (evL (G 0).2 (G 1).2 (G 2).2)
  /-- The set happened after both tasks' frozen clocks. -/
  setc : ((G 1).2.sx || (G 2).2.sx) = true →
    VClock.le (G 1).2.fz (last (EV.hist m)).relClock = true ∧
    VClock.le (G 2).2.fz (last (EV.hist m)).relClock = true
  /-- The setter read `3`: the other task finished before it, is frozen and did not set. -/
  sto : ∀ u v, Pair u v → (G u).2.st → (G v).2.frozen ∧ VClock.le (G v).2.fz (m.clocks[u]!) = true
  sfd : ∀ u v, Pair u v → ((G u).2.st || (G u).2.sx) →
    (G v).2.fd ∧ (G v).2.sx = false ∧ (G v).2.st = false
  /-- A setter read `3`, after `main`'s `add`. -/
  swa : ∀ u, u = 1 ∨ u = 2 → ((G u).2.st || (G u).2.sx) → (G 0).2.wa
  /-- After `main`'s `add`, the last finish reads `3`. -/
  last3 : (G 0).2.e01 → (G 1).2.fd → (G 2).2.fd →
    ((G 1).2.st || (G 1).2.sx || (G 2).2.st || (G 2).2.sx) = true
  /-- `main` wrote `1` exactly at `ev1` (and after it, at `evd`). -/
  e1m : (G 0).2.e1 → ((G 0).2.isEv1 || (G 0).2.isEvd) = true
  m1e : (G 0).2.isEv1 → (G 0).2.e1
  /-- Each access to the `Tally` is by a thread, and below its clock (or its frozen clock). -/
  attr : ∀ e ∈ m.footprint, e.block = 0 → e.tid < 3 ∧ VClock.le e.clock (ac G m e.tid) = true

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  parts : ∀ u, u ≠ 0 → (G u).1.part = Heap.empty
  part0 : ∀ x, (G 0).1.part (0, x) = none
  /-- No thread above the tasks. -/
  out3 : ∀ u, 3 ≤ u → (G u).1.ph = .gone
  blk : BlkOk m
  q : QOk G m
  /-- A task's flags. -/
  sx1 : ∀ u, (G u).2.sx → (G u).2.ph = .wk ∨ (G u).2.ph = .dn ∨ (G u).2.ph = .fin
  wks : ∀ u, (G u).2.ph = .wk → (G u).2.sx
  /-- A frozen task that did not set: its frozen clock is its finish clock. -/
  fzc : ∀ u, (G u).2.frozen → (G u).2.sx = false → (G u).2.fz = (G u).2.fc
  /-- A task after its finish is `gone` for the lock. -/
  lg : ∀ u, (G u).2.fd → (G u).1.ph = .gone
  pre : (G 0).2.ph.rank ≤ 7 → Pre G m
  /-- `main` stopped waiting: both tasks are frozen, below `main`'s clock. -/
  done : 6 ≤ (G 0).2.ph.rank → (G 1).2.frozen ∧ (G 2).2.frozen ∧
    VClock.le (G 1).2.fz (m.clocks[0]!) = true ∧ VClock.le (G 2).2.fz (m.clocks[0]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv G m := L.Inv G m ∧ U G m
  init tgt g := match tgt with
    | .task p => p = bPtr ∧ g = (⟨.out, Heap.empty, Heap.empty⟩, { ph := .lk })
    | _ => False
  fin g := g.1.ph = .gone ∧ g.2.ph = .fin
  strict := true
  joins g := g.1.ph = .out ∧ (g.2.ph = .rdd ∨ g.2.ph = .j1)

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 2 ∧ joinedAll 0 m

/-! ## The protocol has the lock -/

theorem apG : Word.Apart L WG := .inr (.inr (by decide))
theorem apE : Word.Apart L EV := .inr (.inr (by decide))

theorem shape_size {X : ThreadId → X} {m : Mem} (h : Shape X m) : m.threads.size ≤ 3 := by
  obtain ⟨-, -, -, ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩⟩ := h <;> omega

/-- `ac` with the same ghost values and clocks that are not smaller. -/
theorem ac_mono {G G' : ThreadId → Gh} {m m' : Mem} (hX : ∀ u, (G' u).2 = (G u).2)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) (u : ThreadId) :
    VClock.le (ac G m u) (ac G' m' u) = true := by
  unfold ac; rw [hX u]; split
  · exact VClock.le_refl _
  · exact hcl u

/-- `Pre` with ghost values that agree on what it reads (`XEq`), the same writes and clocks that
are not smaller; the new accesses to the `Tally` are by `t`, which is not frozen. -/
theorem Pre.keep {G G' : ThreadId → Gh} {m m' : Mem} {t : ThreadId} (hp : Pre G m)
    (hX : ∀ u, XEq (G u).2 (G' u).2) (hwg : WG.Ok m') (hev : EV.Ok m')
    (hhg : WG.hist m' = WG.hist m) (hhe : EV.hist m' = EV.hist m)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) (ht : t < 3)
    (hft : (G' t).2.frozen = false)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
      (e.tid = t ∧ VClock.le e.clock (m'.clocks[t]!) = true)) : Pre G' m' := by
  have hwgv : wgv (G' 0).2 (G' 1).2 (G' 2).2 = wgv (G 0).2 (G 1).2 (G 2).2 := by
    unfold wgv; rw [(hX 0).isPre, (hX 0).wa, (hX 1).fd, (hX 2).fd]
  have hevL : evL (G' 0).2 (G' 1).2 (G' 2).2 = evL (G 0).2 (G 1).2 (G 2).2 := by
    unfold evL; rw [(hX 0).e1, (hX 1).sx, (hX 2).sx]
  have hac : ∀ u, VClock.le (ac G m u) (ac G' m' u) = true := fun u => by
    unfold ac; rw [(hX u).frozen, (hX u).fz]; split
    · exact VClock.le_refl _
    · exact hcl u
  refine ⟨hwg, hev, by rw [hhg, hwgv]; exact hp.gv, fun u hu hf => ?_,
    by unfold EVOk; rw [hhe, hevL]; exact hp.evh, fun h => ?_, fun u v huv hu => ?_,
    fun u v huv hu => ?_, fun u hu hs => ?_, fun h0 h1 h2 => ?_, fun h => ?_, fun h => ?_,
    fun e he hb => ?_⟩
  · rw [(hX u).fd] at hf; rw [hhg, (hX u).fc]; exact hp.gw u hu hf
  · rw [(hX 1).sx, (hX 2).sx] at h; rw [hhe, (hX 1).fz, (hX 2).fz]; exact hp.setc h
  · rw [(hX u).st] at hu; rw [(hX v).frozen, (hX v).fz]
    obtain ⟨a, b⟩ := hp.sto u v huv hu
    exact ⟨a, VClock.le_trans b (hcl u)⟩
  · rw [(hX u).st, (hX u).sx] at hu; rw [(hX v).fd, (hX v).sx, (hX v).st]
    exact hp.sfd u v huv hu
  · rw [(hX u).st, (hX u).sx] at hs; rw [(hX 0).wa]; exact hp.swa u hu hs
  · rw [(hX 0).e01] at h0; rw [(hX 1).fd] at h1; rw [(hX 2).fd] at h2
    rw [(hX 1).st, (hX 1).sx, (hX 2).st, (hX 2).sx]; exact hp.last3 h0 h1 h2
  · rw [(hX 0).e1] at h; rw [(hX 0).isEv1, (hX 0).isEvd]; exact hp.e1m h
  · rw [(hX 0).isEv1] at h; rw [(hX 0).e1]; exact hp.m1e h
  · rcases hfp e he with h' | ⟨het, hle⟩
    · obtain ⟨a, b⟩ := hp.attr e h' hb
      exact ⟨a, VClock.le_trans b (hac _)⟩
    · refine ⟨het ▸ ht, ?_⟩
      unfold ac; rw [het, hft]; exact hle

theorem stable (G : ThreadId → Gh) (m m' : Mem) (t : ThreadId) (p : LPh) (h : Heap)
    (hg : L.ph (G t) ≠ .gone) (hu : U G m) (hs : L.Step t m m')
    (_ : L.ph (G t) = .holds → p ≠ .holds → L.Before m' (m.clocks[t]!)) :
    U (upd G t (L.set (G t) p h)) m' := by
  have hX : ∀ u, (upd G t (L.set (G t) p h) u).2 = (G u).2 := fun u => congrFun (snd_set G t p h) u
  have hX' : (fun u => (upd G t (L.set (G t) p h) u).2) = fun u => (G u).2 := snd_set G t p h
  have hft : (G t).2.fd = false := by
    cases e : (G t).2.fd
    · rfl
    · exact absurd (hu.lg t e) hg
  have hfz : (G t).2.frozen = false := by
    unfold X.frozen; unfold X.fd at hft
    cases h' : (G t).2.ph.isTask <;> simp_all; omega
  have hpart : ∀ u, (upd G t (L.set (G t) p h) u).1.part = (G u).1.part := fun u => by
    unfold upd; split
    · rename_i e; subst e; rfl
    · rfl
  have hsh := hu.shape
  refine ⟨by rw [hX']; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh,
    fun u hu' => by rw [hpart]; exact hu.parts u hu', fun x => by rw [hpart]; exact hu.part0 x,
    fun u h3 => ?_, ?_, fun w hw => ?_, fun u => by rw [hX]; exact hu.sx1 u, fun u => by rw [hX]; exact hu.wks u,
    fun u => by rw [hX]; exact hu.fzc u,
    fun u hf => ?_, fun hr => ?_, fun hr => ?_⟩
  · have ht3 : t < 3 := Nat.lt_of_not_le fun h3 => hg (hu.out3 t h3)
    unfold upd; split
    · rename_i e; subst e; exact absurd h3 (by unfold ThreadId at *; omega)
    · exact hu.out3 u h3
  · obtain ⟨blk, hb, hl, hsz, ha, hk⟩ := hu.blk
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
  · by_cases hl : w.2 = L.ptr
    · exact .inl hl
    · have := hu.q w ((hs.waiters w hl).mp hw)
      rw [hX 0, hX 1, hX 2]; exact this
  · rw [hX] at hf
    unfold upd; split
    · rename_i e; subst e; rw [hft] at hf; cases hf
    · exact hu.lg u hf
  · rw [hX 0] at hr
    have hp := hu.pre hr
    have hkG := Word.keep_lockStep hs apG
    have hkE := Word.keep_lockStep hs apE
    have ht3 : t < 3 := Nat.lt_of_not_le fun h3 => hg (hu.out3 t h3)
    exact Pre.keep hp (fun u => by rw [hX u]; exact XEq.refl _) (hp.wg.keep hkG) (hp.ev.keep hkE) (Word.hist_keep hp.wg hkG)
      (Word.hist_keep hp.ev hkE) hs.clocks ht3 (by rw [hX]; exact hfz) hs.fpt
  · rw [hX 0, hX 1, hX 2] at *
    obtain ⟨a, b, c, d⟩ := hu.done hr
    exact ⟨a, b, VClock.le_trans c (hs.clocks 0), VClock.le_trans d (hs.clocks 0)⟩

theorem fits : L.Fits proto U :=
  ⟨fun _ _ => Iff.rfl, fun _ h => h.1, fun _ h => h.1, stable⟩

/-- The mutex word: `L.ptr`. -/
theorem mptr : bPtr.add 16 = L.ptr := rfl

/-! ## The heap -/

/-- The counter's bytes: none before byte 20. -/
theorem R_none {X : ThreadId → X} {h : Heap} (hR : R X h) {x : Nat} (hx : x < 20) :
    h (0, x) = none := by
  obtain ⟨A, S, K, bs, -, -, -, ⟨b, hb, -, hl⟩, -⟩ := hR
  cases hb
  rw [hl, if_neg]
  simp only [bPtr, Ptr.add, not_and, Nat.not_lt]
  intro _ h; simp at h; omega

/-- No thread owns a byte before the counter. -/
theorem own_none {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (u : ThreadId) {x : Nat}
    (hx : x < 20) : L.own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    have hp : (G u).1.part (0, x) = none := by
      by_cases hu : u = 0
      · subst hu; exact hi.2.part0 x
      · rw [hi.2.parts u hu]; rfl
    rw [Heap.union_apply, hp, Option.none_or]
    by_cases hh : L.ph (G u) = .holds
    · exact R_none (X := fun u => (G u).2) (hi.1.res u hh) hx
    · rw [show (G u).1.held = L.held (G u) from rfl, hi.1.idle u hh]; rfl

/-- If no thread holds the mutex, no thread owns a byte of the `Tally`. -/
theorem own_free {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (hF : L.Free G) (u : ThreadId)
    (x : Nat) : L.own G m u (0, x) = none := by
  unfold Lock.own; split
  · rfl
  · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
    have hp : (G u).1.part (0, x) = none := by
      by_cases hu : u = 0
      · subst hu; exact hi.2.part0 x
      · rw [hi.2.parts u hu]; rfl
    rw [Heap.union_apply, hp, Option.none_or,
      show (G u).1.held = L.held (G u) from rfl, hi.1.idle u (hF u)]; rfl

theorem off_own {n nb : Nat} {W : Word n nb} {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m)
    (hb : W.b = 0) (ho : W.o + nb ≤ 16) (u : ThreadId) : W.Off (L.own G m u) := fun x _ h2 => by
  rw [hb]; exact own_none hi u (by omega)

theorem off_R {n nb : Nat} {W : Word n nb} (hb : W.b = 0) (ho : W.o + nb ≤ 16) :
    ∀ G hL, L.R G hL → W.Off hL := fun G _ hR x _ h2 => by
  rw [hb]; exact R_none (X := fun u => (G u).2) hR (by omega)

/-- The cell of byte `x < 24` of the `Tally`. -/
theorem blk_heap {m : Mem} (hb : BlkOk m) {x : Nat} (hx : x < 24) : m.heap (0, x) ≠ none := by
  obtain ⟨blk, hblk, hl, hs, -⟩ := hb
  simp only [Mem.heap, hblk]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  simp

/-- The same cell at byte 12 (padding): the same block 0. -/
theorem blk_keep {m m' : Mem} (hb : BlkOk m) (h : m'.heap (0, 12) = m.heap (0, 12)) : BlkOk m' := by
  obtain ⟨blk, hblk, hl, hs, ha, hk⟩ := hb
  have hc : m.heap (0, 12) = some ⟨blk.bytes[12]'(by omega), blk.addr, blk.bytes.size, blk.kind⟩ := by
    simp only [Mem.heap, hblk]; rw [dite_eq_left_of_eq_true (eq_true ⟨hl, by omega⟩)]
  rw [hc] at h
  obtain ⟨blk', hblk', hl', ho', he⟩ := Mem.heap_some h
  simp only [Cell.mk.injEq] at he
  obtain ⟨-, hA, hS, hK⟩ := he
  exact ⟨blk', hblk', by simpa using hl', by rw [← hS, hs], by rw [← hA, ha], by rw [← hK, hk]⟩

theorem hcs_of {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) :
    m.clocks.size = m.threads.size := hi.1.own.csize

/-- A memory with the same blocks, atomic locations, footprint, threads and clocks, and a futex
queue that keeps `QOk`. -/
theorem U_mem {G : ThreadId → Gh} {m m' : Mem} (hu : U G m) (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hf : m'.footprint = m.footprint) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hq : QOk G m') : U G m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hc]; exact VClock.le_refl _
  have hsh := hu.shape
  refine ⟨by unfold Shape at hsh ⊢; rw [ht]; exact hsh, hu.parts, hu.part0, hu.out3,
    by obtain ⟨blk, h1, h2, h3, h4, h5⟩ := hu.blk; exact ⟨blk, by rw [hb]; exact h1, h2, h3, h4, h5⟩,
    hq, hu.sx1, hu.wks, hu.fzc, hu.lg, fun hr => ?_, fun hr => ?_⟩
  · have hp := hu.pre hr
    have hkG : WG.Keep m m' := Word.keep_of hb ha hf ht hcl
    have hkE : EV.Keep m m' := Word.keep_of hb ha hf ht hcl
    exact ⟨hp.wg.keep hkG, hp.ev.keep hkE, by rw [Word.hist_keep hp.wg hkG]; exact hp.gv,
      fun u h1 h2 => by rw [Word.hist_keep hp.wg hkG]; exact hp.gw u h1 h2,
      by unfold EVOk; rw [Word.hist_keep hp.ev hkE]; exact hp.evh,
      fun h => by rw [Word.hist_keep hp.ev hkE]; exact hp.setc h,
      fun u v h1 h2 => by rw [hc]; exact hp.sto u v h1 h2, hp.sfd, hp.swa, hp.last3, hp.e1m, hp.m1e,
      fun e he hb' => by rw [hf] at he; unfold ac; rw [hc]; exact hp.attr e he hb'⟩
  · rw [hc]; exact hu.done hr

/-- The invariant at a stop of thread `t`: the same, with `current := t`. -/
theorem inv_cur {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (t : ThreadId) :
    proto.inv G { m with current := t } :=
  ⟨hi.1.current t, U_mem hi.2 rfl rfl rfl rfl rfl hi.2.q⟩

theorem upd_g {G : ThreadId → Gh} {t : ThreadId} {g : Gh} (hg : G t = g) : upd G t g = G := by
  rw [← hg]; exact upd_same G t

/-! ## The ops at a shared word -/

theorem op_of_cur {n nb : Nat} {W : Word n nb} {t : ThreadId} {m₁ m' : Mem}
    (hop : W.Op t { m₁ with current := t } m') : W.Op t m₁ m' :=
  ⟨hop.current, hop.threads, hop.waiters, hop.woken, hop.groups, hop.csize, hop.others,
    hop.mine, hop.bsize, hop.cells, hop.fp, ⟨hop.locs.new, hop.locs.same⟩, hop.fpt⟩

/-- A shared word of the `Tally`, before the mutex. -/
structure Sh {n nb : Nat} (W : Word n nb) : Prop where
  b : W.b = 0
  o : W.o + nb ≤ 16
  ap : Word.Apart L W
  ok : ∀ G m, proto.inv G m → (G 0).2.ph.rank ≤ 7 → W.Ok m

theorem shG : Sh WG := ⟨rfl, by decide, apG, fun _ _ hi hr => (hi.2.pre hr).wg⟩
theorem shE : Sh EV := ⟨rfl, by decide, apE, fun _ _ hi hr => (hi.2.pre hr).ev⟩

/-- An op at a shared word keeps the lock's invariant. -/
theorem linv_op {n nb : Nat} {W : Word n nb} (hW : Sh W) {G : ThreadId → Gh} {t : ThreadId}
    {m m' : Mem} (hi : proto.inv G m) (hr : (G 0).2.ph.rank ≤ 7) (hop : W.Op t m m') : L.Inv G m' :=
  hi.1.wordOp (hW.ok G m hi hr) hop hW.ap (fun u => off_own hi hW.b hW.o u) (off_R hW.b hW.o G)

/-- An RMW at a shared word (`atomicRmwC`), by thread `t` (`g`). -/
theorem wp_rmw {n nb : Nat} {W : Word n nb} (hW : Sh W) {σ : Type} {s : σ} {t : ThreadId}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh} {op : RmwOp} {signed : Bool}
    {ord : AtomicOrder} {v : BitVec n} (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size ∧ (G₁ 0).2.ph.rank ≤ 7)
    {Q : BitVec n × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m' old, G₁ t = g → proto.inv G₁ m₁ → (G₁ 0).2.ph.rank ≤ 7 →
      (last (W.hist m₁)).Val old → W.Holds m' (op.apply signed old v) →
      W.hist m' = (W.hist m₁).push
        (Word.rmwEnt m' t ord (last (W.hist m₁)) (op.apply signed old v)) →
      (ord.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
      W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' → Q (old, s) G₁ m' k) :
    proto.WP t ((atomicRmwC op signed ord nb W.ptr v : CM Tgt σ (BitVec n)).run s) Q G m d := by
  unfold atomicRmwC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  obtain ⟨htl, hr⟩ := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok _ _ hic hr
  refine WP.callMC (fun e he => (hwc.rmw_noErr htl (hcs_of hic) hcr e he).elim)
    fun old m' hr' => ?_
  obtain ⟨hv, hw', hop, hU, hh, hacq⟩ := hwc.rmw rfl htl (hcs_of hic) hr'
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hv hh hacq
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' old hg₁ hi₁ hr hv hU hh hacq hw' (op_of_cur hop)
    (linv_op hW hic hr hop)⟩

/-- An atomic load at a shared word (`atomicLoadC`), by thread `t` (`g`). -/
theorem wp_load {n nb : Nat} {W : Word n nb} (hW : Sh W) {σ : Type} {s : σ} {t : ThreadId}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh} {ord : AtomicOrder}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size ∧ (G₁ 0).2.ph.rank ≤ 7)
    {Q : BitVec n × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m' v j, G₁ t = g → proto.inv G₁ m₁ → (G₁ 0).2.ph.rank ≤ 7 →
      j < (W.hist m₁).size → (W.hist m₁)[j]!.Val v → Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
      (ord.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
      W.hist m' = W.hist m₁ → W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' → Q (v, s) G₁ m' k) :
    proto.WP t ((atomicLoadC (n := n) ord nb W.ptr : CM Tgt σ (BitVec n)).run s) Q G m d := by
  unfold atomicLoadC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  obtain ⟨htl, hr⟩ := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok _ _ hic hr
  refine WP.callMC (fun e he => (hwc.load_noErr htl (hcs_of hic) hcr e he).elim) fun v m' hr' => ?_
  obtain ⟨j, hj, hv, hfl, hacq, hh, hw', hop⟩ := hwc.load rfl htl (hcs_of hic) hr'
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  rw [hh₁] at hj hv hfl hacq hh
  exact ⟨by rw [hop.threads], h k hk G₁ m₁ m' v j hg₁ hi₁ hr hj hv hfl hacq hh hw' (op_of_cur hop)
    (linv_op hW hic hr hop)⟩

/-- A `cmpxchg` at a shared word (`cmpxchgC`), by thread `t` (`g`): on success an RMW of the
newest write, which holds `exp`; on failure a read of write `j`. -/
theorem wp_cas {n nb : Nat} {W : Word n nb} (hW : Sh W) {σ : Type} {s : σ} {t : ThreadId}
    {G : ThreadId → Gh} {m : Mem} {d : Nat} {g : Gh} {succ fail : AtomicOrder} {exp new : BitVec n}
    (hi : proto.inv (upd G t g) m)
    (ht : ∀ G₁ m₁, G₁ t = g → proto.inv G₁ m₁ → t < m₁.threads.size ∧ (G₁ 0).2.ph.rank ≤ 7)
    {Q : Option (BitVec n) × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ k, d = k + 1 → ∀ G₁ m₁ m', G₁ t = g → proto.inv G₁ m₁ → (G₁ 0).2.ph.rank ≤ 7 →
      W.Ok m' → W.Op t m₁ m' → L.Inv G₁ m' →
      ((last (W.hist m₁)).Val exp → W.Holds m' new →
        W.hist m' = (W.hist m₁).push (Word.rmwEnt m' t succ (last (W.hist m₁)) new) →
        (succ.isAcq = true → VClock.le (last (W.hist m₁)).relClock (m'.clocks[t]!) = true) →
        Q (none, s) G₁ m' k) ∧
      (∀ j b, b ≠ exp → j < (W.hist m₁).size → (W.hist m₁)[j]!.Val b →
        Word.Floor (W.hist m₁) (m₁.clocks[t]!) j →
        (fail.isAcq = true → VClock.le (W.hist m₁)[j]!.relClock (m'.clocks[t]!) = true) →
        W.hist m' = W.hist m₁ → Q (some b, s) G₁ m' k)) :
    proto.WP t ((cmpxchgC succ fail nb W.ptr exp new : CM Tgt σ (Option (BitVec n))).run s) Q G m d := by
  unfold cmpxchgC
  simp only [StateT.run_bind]
  refine WP.bind (WP.pickC fun k hk => ⟨g, hi, fun G₁ m₁ hg₁ hi₁ c hcr => ?_⟩)
  have hic := inv_cur hi₁ t
  obtain ⟨htl, hr⟩ := ht G₁ m₁ hg₁ hi₁
  have hwc := hW.ok _ _ hic hr
  have hh₁ : W.hist { m₁ with current := t } = W.hist m₁ := Word.hist_congr rfl rfl
  refine WP.callMC (fun e he => (hwc.cas_noErr (fail := fail) (new := new) htl (hcs_of hic) hcr
    e he).elim) fun r m' hr' => ?_
  obtain ⟨hw', hop, hcase⟩ := hwc.cas rfl htl (hcs_of hic) hr'
  have hH := h k hk G₁ m₁ m' hg₁ hi₁ hr hw' (op_of_cur hop) (linv_op hW hic hr hop)
  refine ⟨by rw [hop.threads], ?_⟩
  rcases hcase with ⟨rfl, hv, hU, hh, hacq⟩ | ⟨j, old, rfl, hne, hj, hv, hfl, hacq, hh⟩
  · rw [hh₁] at hv hh hacq; exact hH.1 hv hU hh hacq
  · rw [hh₁] at hj hv hfl hacq hh; exact hH.2 j old hne hj hv hfl hacq hh

/-! ## A step of a thread on its own part -/

/-- A step of thread `t` on its own part (`WP.liftM_owned`) keeps `U`, with `t`'s new ghost value
`g`: the same for `Pre` (`XEq`), and the facts of `U` that read the ghost values. -/
theorem U_stepIn {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g : Gh} {hQ : Heap}
    (hi : proto.inv G m) (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own G m t))) (hc : m.current = t) (ht : t < 3)
    (hX : XEq (G t).2 g.2) (hfz : g.2.frozen = false)
    (hsh : Shape (upd (fun u => (G u).2) t g.2) m)
    (hpart : t ≠ 0 → g.1.part = Heap.empty) (hpart0 : t = 0 → ∀ x, g.1.part (0, x) = none)
    (hq : QOk (upd G t g) m') (hsx1 : g.2.sx → g.2.ph = .wk ∨ g.2.ph = .dn ∨ g.2.ph = .fin)
    (hwks : g.2.ph = .wk → g.2.sx) (hlg : g.2.fd → g.1.ph = .gone)
    (hdone : 6 ≤ (upd G t g 0).2.ph.rank → (upd G t g 1).2.frozen ∧ (upd G t g 2).2.frozen ∧
      VClock.le (upd G t g 1).2.fz (m'.clocks[0]!) = true ∧
      VClock.le (upd G t g 2).2.fz (m'.clocks[0]!) = true)
    (hpre : (upd G t g 0).2.ph.rank ≤ 7 → (G 0).2.ph.rank ≤ 7) :
    U (upd G t g) m' := by
  have hrest : ∀ x, x < 20 → m.heap.diff (L.own G m t) (0, x) = m.heap (0, x) := fun x hx => by
    simp [Heap.diff, own_none hi t hx]
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hs.clock
  have hXu : ∀ u, XEq (G u).2 (upd G t g u).2 := fun u => by
    unfold upd; split
    · rename_i e; subst e; exact hX
    · exact XEq.refl _
  refine ⟨by rw [snd_upd]; unfold Shape at hsh ⊢; rw [hs.threads]; exact hsh, fun u hu => ?_,
    fun x => ?_, fun u h3 => ?_, blk_keep hi.2.blk ?_, hq, fun u => ?_, fun u => ?_, fun u => ?_,
    fun u => ?_, fun hr => ?_, hdone⟩
  · unfold upd; split
    · rename_i e; subst e; exact hpart hu
    · exact hi.2.parts u hu
  · unfold upd; split
    · rename_i e; exact hpart0 e.symm x
    · exact hi.2.part0 x
  · unfold upd; split
    · rename_i e; subst e; exact absurd h3 (by unfold ThreadId at *; omega)
    · exact hi.2.out3 u h3
  · rw [hm', Heap.union_of_right ((hd (0, 12)).resolve_right (by
      rw [hrest 12 (by decide)]; exact blk_heap hi.2.blk (by decide))), hrest 12 (by decide)]
  · unfold upd; split
    · exact hsx1
    · exact hi.2.sx1 u
  · unfold upd; split
    · exact hwks
    · exact hi.2.wks u
  · unfold upd; split
    · rename_i e; subst e
      intro hf; rw [hfz] at hf; cases hf
    · exact hi.2.fzc u
  · unfold upd; split
    · exact hlg
    · exact hi.2.lg u
  · have hp := hi.2.pre (hpre hr)
    have hoff : ∀ {n nb : Nat} (W : Word n nb), W.b = 0 → W.o + nb ≤ 16 →
        W.Off (L.own G m t) := fun W hb ho => off_own hi hb ho t
    have hkG := Word.keep_stepIn hp.wg (hoff WG rfl (by decide)) hs hm' hd
    have hkE := Word.keep_stepIn hp.ev (hoff EV rfl (by decide)) hs hm' hd
    refine Pre.keep hp hXu (hp.wg.keep hkG) (hp.ev.keep hkE) (Word.hist_keep hp.wg hkG)
      (Word.hist_keep hp.ev hkE) hcl ht (by rw [upd_self]; exact hfz) fun e he => ?_
    rcases hs.fp e he with h' | ⟨het, -, -⟩
    · exact .inl h'
    · rcases hs.fpc e he with h'' | hle
      · exact .inl h''
      · rw [hc] at het hle; exact .inr ⟨het, hle⟩

/-! ## A task's counter -/

/-- A task at `out`, at the place `ph`. -/
def gT (ph : Ph) : Gh := (⟨.out, Heap.empty, Heap.empty⟩, { ph := ph })

/-- A task that holds the mutex and the counter `h`, at the place `ph`. -/
def gH (ph : Ph) (h : Heap) : Gh := (⟨.holds, Heap.empty, h⟩, { ph := ph })

/-- The stores of both tasks. -/
def cnt (X : ThreadId → X) : Nat := (X 1).cnt + (X 2).cnt

theorem task_ne {t : ThreadId} (ht : t = 1 ∨ t = 2) : t ≠ 0 := by
  rcases ht with rfl | rfl <;> decide

theorem task_lt {t : ThreadId} (ht : t = 1 ∨ t = 2) : t < 3 := by
  rcases ht with rfl | rfl <;> decide

theorem shape_task {Y : ThreadId → X} {m : Mem} {t : ThreadId} {x x' : X} (ht : t = 1 ∨ t = 2)
    (h : Shape (upd Y t x) m) (hx : x.ph.isTask) (hx' : x'.ph.isTask) : Shape (upd Y t x') m := by
  have h0 := task_ne ht
  obtain ⟨a, b, c, d⟩ := h
  have hne3 : ∀ u, 3 ≤ u → u ≠ t := fun u hu e => by
    subst e; rcases ht with rfl | rfl <;> unfold ThreadId at * <;> omega
  refine ⟨a, by rw [upd_ne _ _ (Ne.symm h0)] at b ⊢; exact b,
    fun u hu => by have := c u hu; rw [upd_ne _ _ (hne3 u hu)] at this ⊢; exact this, ?_⟩
  rcases d with ⟨d1, d2, d3, d4⟩ | ⟨d1, d2, d3, d4, d5⟩ | ⟨d1, d2, d3, d4, d5, d6⟩
  · exfalso; rcases ht with rfl | rfl
    · rw [upd_self] at d3; rw [d3] at hx; cases hx
    · rw [upd_self] at d4; rw [d4] at hx; cases hx
  · rcases ht with rfl | rfl
    · exact .inr (.inl ⟨d1, by rw [upd_ne _ _ (by decide)] at d2 ⊢; exact d2, d3,
        by rw [upd_self]; exact hx', by rw [upd_ne _ _ (by decide)] at d5 ⊢; exact d5⟩)
    · exfalso; rw [upd_self] at d5; rw [d5] at hx; cases hx
  · refine .inr (.inr ⟨d1, by rw [upd_ne _ _ (Ne.symm h0)] at d2 ⊢; exact d2, ?_, ?_,
      by rw [upd_ne _ _ (Ne.symm h0)] at d5 ⊢; exact d5, d6⟩)
    · rcases ht with rfl | rfl
      · rw [upd_self]; exact hx'
      · rw [upd_ne _ _ (by decide)] at d3 ⊢; exact d3
    · rcases ht with rfl | rfl
      · rw [upd_ne _ _ (by decide)] at d4 ⊢; exact d4
      · rw [upd_self]; exact hx'

/-- A holder's step on the counter: `U` with the ghost value `g'` (a holder at `lk` or `inc`). -/
theorem U_hold {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g' : Gh} {hQ : Heap}
    (ht : t = 1 ∨ t = 2) (hi : proto.inv G m)
    (hs : StepIn (m.heap.diff (L.own G m t)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own G m t))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own G m t))) (hc : m.current = t)
    (hg : (G t).2 = { ph := .lk } ∨ (G t).2 = { ph := .inc })
    (hg' : g'.2 = { ph := .lk } ∨ g'.2 = { ph := .inc })
    (hp : g'.1.part = Heap.empty) (hlg : g'.1.ph = .holds) :
    U (upd G t g') m' := by
  have h0 := task_ne ht
  have hrk : ∀ x : X, x = { ph := .lk } ∨ x = { ph := .inc } → XEq x { ph := .lk } := by
    rintro x (rfl | rfl)
    · exact XEq.refl _
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hT : ∀ x : X, x = { ph := .lk } ∨ x = { ph := .inc } → x.ph.isTask := by
    rintro x (rfl | rfl) <;> rfl
  have hG : upd G t (G t) = G := upd_same G t
  have hi' : proto.inv (upd G t (G t)) m := by rw [hG]; exact hi
  have hU := U_stepIn (g := g') hi hs hm' hd hc (task_lt ht) ((hrk _ hg).trans (hrk _ hg').symm)
    (by rcases hg' with h | h <;> rw [h] <;> rfl)
    (by
      have hsh := hi.2.shape
      rw [← hG, snd_upd] at hsh
      exact shape_task ht hsh (hT _ hg) (hT _ hg'))
    (fun _ => hp) (fun e => absurd e h0)
    (fun w hw => by
      rw [hs.waiters] at hw
      rcases hi.2.q w hw with h | ⟨a, b, c, d⟩
      · exact .inl h
      · have hsx : (G t).2.sx = false := by rcases hg with h | h <;> rw [h]
        have hsx' : g'.2.sx = false := by rcases hg' with h | h <;> rw [h]
        have hwk : (G t).2.ph ≠ .wk := by rcases hg with h | h <;> rw [h] <;> decide
        have hwk' : g'.2.ph ≠ .wk := by rcases hg' with h | h <;> rw [h] <;> decide
        refine .inr ⟨a, b, by rw [upd_ne _ _ (Ne.symm h0)]; exact c, ?_⟩
        rcases ht with rfl | rfl
        · rw [upd_self, upd_ne _ _ (by decide), hsx']
          rcases d with d | d | d
          · left; rw [hsx] at d; exact d
          · exact absurd d hwk
          · exact .inr (.inr d)
        · rw [upd_self, upd_ne _ _ (by decide), hsx']
          rcases d with d | d | d
          · left; rw [hsx] at d; simpa using d
          · exact .inr (.inl d)
          · exact absurd d hwk)
    (fun h => by rcases hg' with h' | h' <;> rw [h'] at h <;> cases h)
    (fun h => by rcases hg' with h' | h' <;> rw [h'] at h <;> cases h)
    (fun h => by rcases hg' with h' | h' <;> rw [h'] at h <;> cases h)
    (fun hr => by
      have hr' : 6 ≤ (G 0).2.ph.rank := by rwa [upd_ne _ _ (Ne.symm h0)] at hr
      obtain ⟨a, b, -⟩ := hi.2.done hr'
      exfalso
      rcases ht with rfl | rfl
      · rcases hg with h | h <;> rw [h] at a <;> cases a
      · rcases hg with h | h <;> rw [h] at b <;> cases b)
    (fun hr => by rwa [upd_ne _ _ (Ne.symm h0)] at hr)
  exact hU

/-- The holder's load of the counter: the stores of both tasks. -/
theorem wp_cntLoad {σ : Type} {s : σ} {t : ThreadId} {hL : Heap} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} (ht : t = 1 ∨ t = 2) (hi : proto.inv (upd G t (gH .lk hL)) m)
    (hc : m.current = t)
    {Q : BitVec 32 × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gH .lk hQ)) m' →
      Q (BitVec.ofNat 32 (cnt fun u => (upd G t (gH .lk hL) u).2), s) G m' d) :
    proto.WP t ((liftM (load (BitVec 32) 4 (bPtr.add 20)) : CM Tgt σ (BitVec 32)).run s) Q G m d := by
  have hh : L.ph (upd G t (gH .lk hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨htl, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gH .lk hL) u).2) hL := by
    have := hi.1.res t hh
    rwa [show L.held (upd G t (gH .lk hL) t) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G t (gH .lk hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned (TTriple.load (by decide)) hi.1.own hc htl (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  obtain ⟨rfl, hq'⟩ := sep_lift.mp hq
  have hQe : L.part (gH .lk hQ) ∪ L.held (gH .lk hQ) = hQ := Heap.empty_union hQ
  have hl := hi.1.stepIn (g := gH .lk hQ) hc hjt (by rw [hQe]; exact ho') hs (by rw [hQe]; exact hm')
    (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl) (fun h => absurd rfl h)
    (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gH .lk hL)) t (gH .lk hQ) u).2) hQ
      rw [snd_upd_upd G t (gH .lk hL) (gH .lk hQ) rfl]; exact hq')
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have := U_hold (g' := gH .lk hQ) ht hi hs hm' hd hc (by rw [upd_self]; exact .inl rfl) (.inl rfl)
    rfl rfl
  rwa [upd_upd] at this

/-- The holder's store of `w`, the stores of both tasks after its own. -/
theorem wp_cntStore {σ : Type} {s : σ} {t : ThreadId} {hL : Heap} {G : ThreadId → Gh}
    {m : Mem} {d : Nat} (w : BitVec 32) (ht : t = 1 ∨ t = 2) (hi : proto.inv (upd G t (gH .lk hL)) m)
    (hc : m.current = t)
    (hw : w = BitVec.ofNat 32 (cnt fun u => (upd G t (gH .inc hL) u).2))
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (h : ∀ m' hQ, m'.current = t → m'.threads = m.threads →
      proto.inv (upd G t (gH .inc hQ)) m' → Q ((), s) G m' d) :
    proto.WP t ((liftM (store (α := BitVec 32) 4 (bPtr.add 20) w) : CM Tgt σ Unit).run s) Q G m d := by
  have hh : L.ph (upd G t (gH .lk hL) t) = .holds := by rw [upd_self]; rfl
  obtain ⟨htl, hjt⟩ := hi.1.live t (by rw [hh]; decide)
  have hres : R (fun u => (upd G t (gH .lk hL) u).2) hL := by
    have := hi.1.res t hh
    rwa [show L.held (upd G t (gH .lk hL) t) = hL by rw [upd_self]; rfl] at this
  have hown : L.own (upd G t (gH .lk hL)) m t = hL := by
    rw [L.own_live hjt, upd_self]; exact Heap.empty_union hL
  refine WP.liftM_owned (TTriple.store (by decide) w) hi.1.own hc htl (by rw [hown]; exact hres)
    fun a m' hQ hr ho' hq hs hm' hd => ?_
  have hQe : L.part (gH .inc hQ) ∪ L.held (gH .inc hQ) = hQ := Heap.empty_union hQ
  have hX : (fun u => (upd (upd G t (gH .lk hL)) t (gH .inc hQ) u).2) =
      fun u => (upd G t (gH .inc hL) u).2 := by
    rw [upd_upd]; funext u; unfold upd; split <;> rfl
  have hl := hi.1.stepIn (g := gH .inc hQ) hc hjt (by rw [hQe]; exact ho') hs
    (by rw [hQe]; exact hm') (by rw [hQe]; exact hd) (by rw [upd_self]; rfl) (fun _ => .inl rfl)
    (fun h => absurd rfl h) (fun h => absurd hh h) (fun _ => by
      show R (fun u => (upd (upd G t (gH .lk hL)) t (gH .inc hQ) u).2) hQ
      rw [hX]; unfold R; exact hw ▸ hq)
  rw [upd_upd] at hl
  refine h m' hQ (hs.current.trans hc) hs.threads ⟨hl, ?_⟩
  have := U_hold (g' := gH .inc hQ) ht hi hs hm' hd hc (by rw [upd_self]; exact .inl rfl) (.inr rfl)
    rfl rfl
  rwa [upd_upd] at this

end Threadsync.WG
