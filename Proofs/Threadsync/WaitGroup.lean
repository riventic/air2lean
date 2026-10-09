import Proofs.Threadsync.Deadline
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
  | .pre => 0 | .sm => 1 | .sp1 => 2 | .run => 3 | .ev0 => 4 | .ev1 => 5
  | .rd => 7 | .rdd => 8 | .j1 => 9
  | .lk => 0 | .hl => 1 | .inc => 2 | .un => 3 | .s0 => 4 | .s1 => 5 | .wk => 6 | .dn => 7
  | .fin => 8

def Ph.isMain : Ph → Bool
  | .pre | .sm | .sp1 | .run | .ev0 | .ev1 | .rd | .rdd | .j1 => true
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
abbrev L : Lock Gh := Lock.prod 0 16 R mutexC (by decide)

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
  fc : x'.fc = x.fc
  fz : x'.fz = x.fz

theorem XEq.refl (x : X) : XEq x x := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem XEq.symm {x y : X} (h : XEq x y) : XEq y x :=
  ⟨h.isPre.symm, h.wa.symm, h.fd.symm, h.frozen.symm, h.sx.symm, h.e1.symm, h.st.symm,
    h.e01.symm, h.isEv1.symm, h.fc.symm, h.fz.symm⟩

theorem XEq.trans {x y z : X} (h : XEq x y) (h' : XEq y z) : XEq x z :=
  ⟨h'.isPre.trans h.isPre, h'.wa.trans h.wa, h'.fd.trans h.fd, h'.frozen.trans h.frozen,
    h'.sx.trans h.sx, h'.e1.trans h.e1, h'.st.trans h.st, h'.e01.trans h.e01,
    h'.isEv1.trans h.isEv1, h'.fc.trans h.fc, h'.fz.trans h.fz⟩

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
  /-- At `ev1`, `main` wrote `1`. -/
  m1e : (G 0).2.isEv1 → (G 0).2.e1
  /-- `main`'s write of `1` happened before it. -/
  e1c : (G 0).2.e1 → VClock.le (EV.hist m)[1]!.clock (m.clocks[0]!) = true
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

/-- `Pre` with ghost values that agree on what it reads (`XEq`), the same writes and clocks that
are not smaller; the new accesses to the `Tally` are by `t`, which is not frozen. -/
theorem Pre.keep {G G' : ThreadId → Gh} {m m' : Mem} {t : ThreadId} (hp : Pre G m)
    (hX : ∀ u, XEq (G u).2 (G' u).2) (hwg : WG.Ok m') (hev : EV.Ok m')
    (hhg : WG.hist m' = WG.hist m) (hhe : EV.hist m' = EV.hist m)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true) (ht : t < 3)
    (hft : (G' t).2.frozen = false ∨ ∀ e ∈ m'.footprint, e ∈ m.footprint)
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
    fun u v huv hu => ?_, fun u hu hs => ?_, fun h0 h1 h2 => ?_, fun h => ?_,
    fun h => ?_, fun e he hb => ?_⟩
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
  · rw [(hX 0).isEv1] at h; rw [(hX 0).e1]; exact hp.m1e h
  · rw [(hX 0).e1] at h; rw [hhe]; exact VClock.le_trans (hp.e1c h) (hcl 0)
  · have hold : e ∈ m.footprint → e.tid < 3 ∧ VClock.le e.clock (ac G' m' e.tid) = true :=
      fun h' => by obtain ⟨a, b⟩ := hp.attr e h' hb; exact ⟨a, VClock.le_trans b (hac _)⟩
    rcases hfp e he with h' | ⟨het, hle⟩
    · exact hold h'
    · rcases hft with hft | hft
      · refine ⟨het ▸ ht, ?_⟩
        unfold ac; rw [het, hft]; exact hle
      · exact hold (hft e he)

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
      (Word.hist_keep hp.ev hkE) hs.clocks ht3 (.inl (by rw [hX]; exact hfz)) hs.fpt
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
      fun u v h1 h2 => by rw [hc]; exact hp.sto u v h1 h2, hp.sfd, hp.swa, hp.last3, hp.m1e,
      fun h => by rw [Word.hist_keep hp.ev hkE, hc]; exact hp.e1c h,
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
      (Word.hist_keep hp.ev hkE) hcl ht (.inl (by rw [upd_self]; exact hfz)) fun e he => ?_
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
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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

/-! ## A task's finish -/

/-- The other task. -/
def oth (t : ThreadId) : ThreadId := 3 - t

theorem pair_oth {t : ThreadId} (ht : t = 1 ∨ t = 2) : Pair t (oth t) := by
  rcases ht with rfl | rfl
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem oth_ne {t : ThreadId} (ht : t = 1 ∨ t = 2) : oth t ≠ t ∧ oth t ≠ 0 ∧ (oth t = 1 ∨ oth t = 2) := by
  rcases ht with rfl | rfl <;> decide

/-- A task after its finish, which read `k`, with its clock `c`: the setter if `k = 3`. -/
def gF (k : Nat) (c : VClock) : Gh :=
  (⟨.gone, Heap.empty, Heap.empty⟩, { ph := if k = 3 then .s0 else .dn, fc := c, fz := c })

theorem wgv_le (x0 x1 x2 : X) : wgv x0 x1 x2 ≤ 5 := by
  unfold wgv; split
  · omega
  · split <;> omega

/-- The group's state, by the place of each task: `wgv` with task `t`'s finish is 2 less. -/
theorem wgv_fin {Y : ThreadId → X} {t : ThreadId} {x : X} (ht : t = 1 ∨ t = 2)
    (hf : (Y t).fd = false) (hx : x.fd = true) (hp : (Y 0).isPre = false) :
    2 ≤ wgv (Y 0) (Y 1) (Y 2) ∧
    wgv (upd Y t x 0) (upd Y t x 1) (upd Y t x 2) + 2 = wgv (Y 0) (Y 1) (Y 2) ∧
    (wgv (Y 0) (Y 1) (Y 2) = 3 ↔ (Y 0).wa ∧ (Y (oth t)).fd) := by
  have h0 := task_ne ht
  unfold wgv
  rw [upd_ne _ _ (Ne.symm h0), hp]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases ht with rfl | rfl
  · rw [upd_self, upd_ne _ _ (by decide), hx, hf]
    show _ ∧ _ ∧ (_ ↔ _ ∧ (Y 2).fd = true)
    cases (Y 0).wa <;> cases (Y 2).fd <;> simp
  · rw [upd_self, upd_ne _ _ (by decide), hx, hf]
    show _ ∧ _ ∧ (_ ↔ _ ∧ (Y 1).fd = true)
    cases (Y 0).wa <;> cases (Y 1).fd <;> simp

theorem val_eq {n : Nat} {x : Word.Entry} {a b : BitVec n} (ha : x.Val a) (hb : x.Val b) : a = b := by
  unfold Word.Entry.Val at ha hb; rw [ha] at hb; cases hb; rfl

theorem last_push (h : Array Word.Entry) (x : Word.Entry) : last (h.push x) = x := by
  simp [last]

theorem sub_two (k : Nat) (h2 : 2 ≤ k) (h5 : k ≤ 5) :
    RmwOp.sub.apply false (BitVec.ofNat 64 k) 2 = BitVec.ofNat 64 (k - 2) := by
  rcases (by omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl <;> rfl

/-- `R` reads only the tasks' stores. -/
theorem R_cnt {Y Y' : ThreadId → X} (h1 : (Y' 1).cnt = (Y 1).cnt) (h2 : (Y' 2).cnt = (Y 2).cnt)
    (h : Heap) : R Y' h ↔ R Y h := by
  unfold R; rw [h1, h2]

/-- A task exists: `main` is after `startMany`. -/
theorem isPre_of_task {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {t : ThreadId}
    (ht : t = 1 ∨ t = 2) (htk : (G t).2.ph.isTask) : (G 0).2.isPre = false := by
  obtain ⟨-, -, -, d⟩ := hi.2.shape
  rcases d with ⟨-, -, d3, d4⟩ | ⟨-, d2, -⟩ | ⟨-, d2, -⟩
  · exfalso; rcases ht with rfl | rfl
    · change (G 1).2 = {} at d3; rw [d3] at htk; cases htk
    · change (G 2).2 = {} at d4; rw [d4] at htk; cases htk
  · change (G 0).2.ph = .sp1 at d2; simp [X.isPre, d2]
  · change 3 ≤ (G 0).2.ph.rank at d2
    unfold X.isPre; cases h : (G 0).2.ph <;> simp_all [Ph.rank]

/-- Task `t`'s finish, `sub(2)` (acq-rel) at the group's state, which read `old` (the place `k`):
it goes to `gF k`, `gone` for the lock. -/
theorem inv_finish {G : ThreadId → Gh} {m₁ m' : Mem} {t : ThreadId} {old : BitVec 64}
    (ht : t = 1 ∨ t = 2) (hi : proto.inv G m₁) (hg : G t = gT .inc) (hr : (G 0).2.ph.rank ≤ 7)
    (hv : (last (WG.hist m₁)).Val old)
    (hh : WG.hist m' = (WG.hist m₁).push
      (Word.rmwEnt m' t .acqRel (last (WG.hist m₁)) (RmwOp.sub.apply false old 2)))
    (hacq : VClock.le (last (WG.hist m₁)).relClock (m'.clocks[t]!) = true)
    (hw' : WG.Ok m') (hop : WG.Op t m₁ m') (hL : L.Inv G m') :
    ∃ k, old = BitVec.ofNat 64 k ∧ 2 ≤ k ∧ k ≤ 5 ∧
      proto.inv (upd G t (gF k (m'.clocks[t]!))) m' := by
  have h0 := task_ne ht
  obtain ⟨hot, ho0, ho12⟩ := oth_ne ht
  have hp := hi.2.pre hr
  have hgt : (G t).2 = { ph := .inc } := by rw [hg]; rfl
  have hpre := isPre_of_task hi ht (by rw [hgt]; rfl)
  have hft : (G t).2.fd = false := by rw [hgt]; rfl
  obtain ⟨k, hk⟩ : ∃ k, wgv (G 0).2 (G 1).2 (G 2).2 = k := ⟨_, rfl⟩
  have hclt := hop.clocks t
  generalize hc : m'.clocks[t]! = c at hacq hclt ⊢
  obtain ⟨hk2, hk', hk3⟩ := wgv_fin (Y := fun u => (G u).2) (x := (gF k c).2) ht hft
    (by unfold gF X.fd; split <;> rfl) hpre
  simp only [hk] at hk2 hk' hk3
  have hk5 : k ≤ 5 := hk ▸ wgv_le _ _ _
  have hold : old = BitVec.ofNat 64 k := val_eq hv (by rw [← hk]; exact hp.gv)
  refine ⟨k, hold, hk2, hk5, ?_⟩
  subst hold
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t (gF k c) := ⟨_, rfl⟩
  rw [← hG']
  have hGo : ∀ u, u ≠ t → G' u = G u := fun u h => by rw [hG']; exact upd_ne _ _ h
  have hGt : G' t = gF k c := by rw [hG']; exact upd_self _ _ _
  -- the other task, if `k = 3`
  have hsx0 : ∀ u, u = 1 ∨ u = 2 → u ≠ t → ((G u).2.st || (G u).2.sx) = false := by
    intro u hu hut
    cases e : ((G u).2.st || (G u).2.sx)
    · rfl
    · have hpu : Pair u t := by
        rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
          first | exact absurd rfl hut | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩
      have := (hp.sfd u t hpu e).1; rw [hft] at this; cases this
  have hoth3 : k = 3 → (G (oth t)).2.fd ∧ (G (oth t)).2.st = false ∧ (G (oth t)).2.sx = false ∧
      (G (oth t)).2.frozen ∧ VClock.le (G (oth t)).2.fz c = true := by
    intro h3
    obtain ⟨-, hfo⟩ := hk3.mp h3
    have hs := hsx0 _ ho12 hot
    simp only [Bool.or_eq_false_iff] at hs
    obtain ⟨hst, hsx⟩ := hs
    have hfr : (G (oth t)).2.frozen := by
      unfold X.fd at hfo; unfold X.st at hst; unfold X.frozen
      have hwk : (G (oth t)).2.ph ≠ .wk := fun e => by rw [hi.2.wks _ e] at hsx; cases hsx
      cases e : (G (oth t)).2.ph <;> simp_all [Ph.isTask, Ph.rank]
    refine ⟨hfo, hst, hsx, hfr, ?_⟩
    rw [hi.2.fzc _ hfr hsx]
    exact VClock.le_trans (hp.gw _ ho12 hfo) hacq
  -- the lock: `t` goes from `out` to `gone`
  have hRk : ∀ hL, L.R G hL → L.R G' hL := fun hL hR => by
    show R (fun u => (G' u).2) hL
    refine (R_cnt (Y := fun u => (G u).2) ?_ ?_ hL).mpr hR <;>
    · show (G' _).2.cnt = (G _).2.cnt
      rw [hG']; unfold upd; split
      · rename_i e; subst e; rw [hgt]; unfold gF X.cnt; split <;> rfl
      · rfl
  have hl := hL.ghost (t := t) (g := gF k c) (by rw [hg]; rfl) (.inr (.inl rfl))
    (by rw [hg]; rfl) rfl (fun h => absurd rfl h) (by rw [← hG']; exact hRk)
  refine ⟨by rw [hG']; exact hl, ?_⟩
  have hsh := hi.2.shape
  have hfz' : (gF k c).2.frozen = !(decide (k = 3)) := by
    unfold gF X.frozen; split <;> simp_all [Ph.isTask, Ph.rank]
  refine ⟨?_, fun u hu => ?_, fun x => ?_, fun u h3 => ?_, blk_keep hi.2.blk (hop.cells _ ?_),
    fun w hw => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun hr' => ?_, fun hr' => ?_⟩
  · rw [hG', snd_upd]
    have := shape_task (Y := fun u => (G u).2) (x := (G t).2) (x' := (gF k c).2) ht
      (by rw [upd_same]; exact hsh) (by rw [hgt]; rfl) (by unfold gF; split <;> rfl)
    unfold Shape at this ⊢; rw [hop.threads]; exact this
  · rw [hG']; unfold upd; split
    · rfl
    · exact hi.2.parts u hu
  · rw [hGo 0 (Ne.symm h0)]; exact hi.2.part0 x
  · have hut : u ≠ t := fun e => by
      subst e; exact absurd h3 (by rcases ht with rfl | rfl <;> decide)
    rw [hGo u hut]; exact hi.2.out3 u h3
  · rintro ⟨-, -, h⟩; simp only [WG] at h; omega
  · rw [hop.waiters] at hw
    rcases hi.2.q w hw with h | ⟨a, b, c', d⟩
    · exact .inl h
    · refine .inr ⟨a, b, by rw [hGo 0 (Ne.symm h0)]; exact c', ?_⟩
      have hsxt : (gF k c).2.sx = false := rfl
      have hwkt : (gF k c).2.ph ≠ .wk := by unfold gF; split <;> simp
      rcases ht with rfl | rfl
      · rw [hGt, hGo 2 (by decide), hsxt]
        rcases d with d | d | d
        · left; rw [hgt] at d; exact d
        · rw [hgt] at d; cases d
        · exact .inr (.inr d)
      · rw [hGt, hGo 1 (by decide), hsxt]
        rcases d with d | d | d
        · left; rw [hgt] at d; simpa using d
        · exact .inr (.inl d)
        · rw [hgt] at d; cases d
  · rw [hG']; unfold upd; split
    · intro h; cases h
    · exact hi.2.sx1 u
  · rw [hG']; unfold upd; split
    · unfold gF; split <;> intro h <;> cases h
    · exact hi.2.wks u
  · rw [hG']; unfold upd; split
    · intro _ _; rfl
    · exact hi.2.fzc u
  · rw [hG']; unfold upd; split
    · intro _; rfl
    · exact hi.2.lg u
  · -- `Pre`
    rw [hGo 0 (Ne.symm h0)] at hr'
    have hkE := Word.keep_op hop (W' := EV) (.inr (.inl (by decide)))
    have hhE := Word.hist_keep hp.ev hkE
    have hX0 : (G' 0).2 = (G 0).2 := by rw [hGo 0 (Ne.symm h0)]
    have hXo : (G' (oth t)).2 = (G (oth t)).2 := by rw [hGo _ hot]
    have hlast : last (WG.hist m') = Word.rmwEnt m' t .acqRel (last (WG.hist m₁))
        (RmwOp.sub.apply false (BitVec.ofNat 64 k) 2) := by rw [hh, last_push]
    have hrel : (last (WG.hist m')).relClock = VClock.merge (last (WG.hist m₁)).relClock c := by
      rw [hlast]; simp only [Word.rmwEnt, AtomicOrder.isRel, ↓reduceIte, hc]
    have hsxG : ∀ u, (G' u).2.sx = (G u).2.sx := fun u => by
      rw [hG']; unfold upd; split
      · rename_i e; subst e; rw [hgt]; rfl
      · rfl
    refine ⟨hw', hp.ev.keep hkE, ?_, fun u hu hf => ?_, ?_, fun h => ?_, fun u v huv hu => ?_,
      fun u v huv hu => ?_, fun u hu hs => ?_, fun h0' h1 h2 => ?_, ?_, fun h => ?_, fun e he hb => ?_⟩
    · rw [hlast]
      have : wgv (G' 0).2 (G' 1).2 (G' 2).2 = k - 2 := by
        have e : ∀ u, (G' u).2 = upd (fun u => (G u).2) t (gF k c).2 u := fun u => by
          rw [hG']; unfold upd; split <;> rfl
        rw [e 0, e 1, e 2]; omega
      rw [this, ← sub_two k hk2 hk5]
      exact WG.enc_val _
    · rw [hrel]
      by_cases hut : u = t
      · subst hut; rw [hGt]; exact VClock.le_merge_right _ _
      · rw [hGo u hut] at hf ⊢
        exact VClock.le_trans (hp.gw u hu hf) (VClock.le_merge_left _ _)
    · unfold EVOk; rw [hhE]
      have : evL (G' 0).2 (G' 1).2 (G' 2).2 = evL (G 0).2 (G 1).2 (G 2).2 := by
        unfold evL; rw [hX0, hsxG 1, hsxG 2]
      rw [this]; exact hp.evh
    · exfalso
      rw [hsxG 1, hsxG 2] at h
      rcases ht with rfl | rfl
      · have := hsx0 2 (.inr rfl) (by decide)
        rw [hgt] at h; simp only [Bool.or_eq_false_iff] at this
        exact absurd h (by simp [this.2])
      · have := hsx0 1 (.inl rfl) (by decide)
        rw [hgt] at h; simp only [Bool.or_eq_false_iff] at this
        exact absurd h (by simp [this.2])
    · by_cases hut : u = t
      · subst hut
        rw [hGt] at hu
        have h3 : k = 3 := by unfold gF X.st at hu; split at hu <;> simp_all
        obtain ⟨-, -, -, hfr, hle⟩ := hoth3 h3
        have hv' : v = oth u := by
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        subst hv'
        rw [hGo _ hot, hc]; exact ⟨hfr, hle⟩
      · have hvt : v = t := by
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases ht with rfl | rfl <;>
            first | rfl | exact absurd rfl hut
        rw [hGo u hut] at hu
        have hu12 : u = 1 ∨ u = 2 := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
        have := hsx0 u hu12 hut
        rw [hu] at this; cases this
    · by_cases hut : u = t
      · subst hut
        rw [hGt] at hu
        have h3 : k = 3 := by unfold gF X.st X.sx at hu; split at hu <;> simp_all
        obtain ⟨hfo, hst, hsx, -⟩ := hoth3 h3
        have hv' : v = oth u := by
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        subst hv'
        rw [hGo _ hot]; exact ⟨hfo, hsx, hst⟩
      · rw [hGo u hut] at hu
        have hu12 : u = 1 ∨ u = 2 := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
        rw [hsx0 u hu12 hut] at hu; cases hu
    · rw [hX0]
      by_cases hut : u = t
      · subst hut
        rw [hGt] at hs
        have h3 : k = 3 := by unfold gF X.st X.sx at hs; split at hs <;> simp_all
        exact (hk3.mp h3).1
      · rw [hGo u hut, hsx0 u hu hut] at hs; cases hs
    · rw [hX0] at h0'
      have hwa : (G 0).2.wa := by
        unfold X.e01 at h0'; unfold X.wa
        cases e : (G 0).2.ph <;> simp_all [Ph.isMain, Ph.rank]
      have hfo : (G (oth t)).2.fd := by
        rcases ht with rfl | rfl
        · rw [← hXo]; exact h2
        · rw [← hXo]; exact h1
      have h3 := hk3.mpr ⟨hwa, hfo⟩
      have hst : (G' t).2.st = true := by rw [hGt]; unfold gF X.st; simp [h3]
      rcases ht with rfl | rfl <;> simp [hst]
    · rw [hX0]; exact hp.m1e
    · rw [hX0] at h; rw [hhE]; exact VClock.le_trans (hp.e1c h) (hop.clocks 0)
    · rcases hop.fpt e he with h' | ⟨het, hle⟩
      · obtain ⟨a, b⟩ := hp.attr e h' hb
        refine ⟨a, VClock.le_trans b ?_⟩
        unfold ac
        by_cases hut : e.tid = t
        · rw [hut, hGt, hgt]
          show VClock.le (m₁.clocks[t]!) _ = true
          rw [hfz', hc]; cases (decide (k = 3)) <;> exact hclt
        · rw [hGo _ hut]; split
          · exact VClock.le_refl _
          · exact hop.clocks _
      · refine ⟨het ▸ task_lt ht, ?_⟩
        unfold ac; rw [het, hGt, hfz', hc]; rw [hc] at hle
        cases (decide (k = 3)) <;> exact hle
  · exfalso
    rw [hGo 0 (Ne.symm h0)] at hr'
    obtain ⟨a, b, -⟩ := hi.2.done hr'
    rcases ht with rfl | rfl
    · rw [hgt] at a; cases a
    · rw [hgt] at b; cases b

/-! ## `U` after a step that changes one ghost value -/

/-- `U` after a step of thread `t` (`t ≠ 0`, a task) that keeps the threads, the blocks' sizes
and the cell at byte 12, with `t`'s new ghost value `g`. -/
theorem U_task {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {g : Gh} (ht : t = 1 ∨ t = 2)
    (hi : proto.inv G m) (hth : m'.threads = m.threads)
    (hcell : m'.heap (0, 12) = m.heap (0, 12))
    (htk : (G t).2.ph.isTask) (htk' : g.2.ph.isTask) (hp : g.1.part = Heap.empty)
    (hq : QOk (upd G t g) m') (hsx1 : g.2.sx → g.2.ph = .wk ∨ g.2.ph = .dn ∨ g.2.ph = .fin)
    (hwks : g.2.ph = .wk → g.2.sx) (hfzc : g.2.frozen → g.2.sx = false → g.2.fz = g.2.fc)
    (hlg : g.2.fd → g.1.ph = .gone)
    (hpre : (G 0).2.ph.rank ≤ 7 → Pre (upd G t g) m')
    (hdone : 6 ≤ (G 0).2.ph.rank → (upd G t g 1).2.frozen ∧ (upd G t g 2).2.frozen ∧
      VClock.le (upd G t g 1).2.fz (m'.clocks[0]!) = true ∧
      VClock.le (upd G t g 2).2.fz (m'.clocks[0]!) = true) :
    U (upd G t g) m' := by
  have h0 := task_ne ht
  have hG0 : upd G t g 0 = G 0 := upd_ne _ _ (Ne.symm h0)
  have hsh := hi.2.shape
  rw [← upd_same G t, snd_upd] at hsh
  have hsh' := shape_task ht hsh htk htk'
  refine ⟨by rw [snd_upd]; unfold Shape at hsh' ⊢; rw [hth]; exact hsh', fun u hu => ?_,
    fun x => by rw [hG0]; exact hi.2.part0 x, fun u h3 => ?_, blk_keep hi.2.blk hcell, hq,
    fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun hr => ?_, fun hr => ?_⟩
  · unfold upd; split
    · exact hp
    · exact hi.2.parts u hu
  · have hut : u ≠ t := fun e => by
      subst e; exact absurd h3 (by rcases ht with rfl | rfl <;> decide)
    rw [upd_ne _ _ hut]; exact hi.2.out3 u h3
  · unfold upd; split
    · exact hsx1
    · exact hi.2.sx1 u
  · unfold upd; split
    · exact hwks
    · exact hi.2.wks u
  · unfold upd; split
    · exact hfzc
    · exact hi.2.fzc u
  · unfold upd; split
    · exact hlg
    · exact hi.2.lg u
  · rw [hG0] at hr; exact hpre hr
  · rw [hG0] at hr; exact hdone hr

/-- A task's step that is not in `U`'s view of the lock: the lock's invariant with `t`'s new
ghost value `g`, with the same lock part and the same store. -/
theorem linv_task {G : ThreadId → Gh} {m : Mem} {t : ThreadId} {g : Gh} (hL : L.Inv G m)
    (h1 : g.1 = (G t).1) (hc : g.2.cnt = (G t).2.cnt) : L.Inv (upd G t g) m :=
  hL.congr (fun u => by unfold upd; split <;> simp_all [L, Lock.prod])
    (fun u => by unfold upd; split <;> simp_all [L, Lock.prod])
    (fun u => by unfold upd; split <;> simp_all [L, Lock.prod]) fun h => by
      show R (fun u => (upd G t g u).2) h ↔ R (fun u => (G u).2) h
      refine R_cnt ?_ ?_ h <;>
      · show (upd G t g _).2.cnt = (G _).2.cnt
        unfold upd; split
        · rename_i e; subst e; exact hc
        · rfl

/-! ## The setter -/

/-- The event's writes: the value of write `j`. -/
theorem ev_val {m : Mem} {vs : List Nat} (h : EVOk m vs) {j : Nat} {v : BitVec 32}
    (hj : j < (EV.hist m).size) (hv : (EV.hist m)[j]!.Val v) :
    ∃ hj' : j < vs.length, v = BitVec.ofNat 32 vs[j] := by
  have hj' : j < vs.length := h.1 ▸ hj
  exact ⟨hj', val_eq hv (h.2 j hj')⟩

/-- A task after its finish, `gone` for the lock. -/
def gS (ph : Ph) (a b : VClock) (sx : Bool) : Gh :=
  (⟨.gone, Heap.empty, Heap.empty⟩, { ph := ph, fc := a, fz := b, sx := sx })

/-- The setter's relaxed load of the event (at `s0`): it read `0` or `1`, and goes to `s1`. -/
theorem inv_sload {G : ThreadId → Gh} {m₁ m' : Mem} {t : ThreadId} {a b : VClock} {j : Nat}
    {v : BitVec 32} (ht : t = 1 ∨ t = 2) (hi : proto.inv G m₁) (hg : G t = gS .s0 a b false)
    (hr : (G 0).2.ph.rank ≤ 7) (hj : j < (EV.hist m₁).size) (hv : (EV.hist m₁)[j]!.Val v)
    (hh : EV.hist m' = EV.hist m₁) (hw' : EV.Ok m') (hop : EV.Op t m₁ m') (hL : L.Inv G m') :
    (v = 0 ∨ v = 1) ∧ proto.inv (upd G t (gS .s1 a b false)) m' := by
  have hp := hi.2.pre hr
  obtain ⟨hot, ho0, ho12⟩ := oth_ne ht
  have hst : (G t).2.st := by rw [hg]; rfl
  obtain ⟨-, hsxo, -⟩ := hp.sfd t (oth t) (pair_oth ht) (by rw [hst]; rfl)
  have hsx : ((G 1).2.sx || (G 2).2.sx) = false := by
    have hsxt : (G t).2.sx = false := by rw [hg]; rfl
    rcases ht with rfl | rfl
    · simp [hsxt, show (G 2).2.sx = false from hsxo]
    · simp [hsxt, show (G 1).2.sx = false from hsxo]
  have hv01 : v = 0 ∨ v = 1 := by
    obtain ⟨hj', hve⟩ := ev_val hp.evh hj hv
    have hm := List.getElem_mem hj'
    generalize (evL (G 0).2 (G 1).2 (G 2).2)[j] = x at hm hve
    subst hve
    unfold evL at hm; rw [hsx] at hm
    have hx : x = 0 ∨ x = 1 := by
      by_cases he : (G 0).2.e1 = true <;> simp [he] at hm <;> omega
    rcases hx with rfl | rfl <;> simp
  refine ⟨hv01, linv_task hL (by rw [hg]; rfl) (by rw [hg]; rfl), ?_⟩
  have hX : XEq (G t).2 (gS .s1 a b false).2 := by
    rw [hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine U_task ht hi hop.threads (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [EV] at h; omega))
    (by rw [hg]; rfl) rfl rfl (fun w hw => ?_) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (fun _ => rfl) (fun _ => ?_) (fun hr' => ?_)
  · rw [hop.waiters] at hw
    rcases hi.2.q w hw with h | ⟨a', b', c', d⟩
    · exact .inl h
    · refine .inr ⟨a', b', by rw [upd_ne _ _ (Ne.symm (task_ne ht))]; exact c', ?_⟩
      rcases ht with rfl | rfl
      · rw [hg] at d; rw [upd_self, upd_ne _ _ (by decide)]; simpa [gS] using d
      · rw [hg] at d; rw [upd_self, upd_ne _ _ (by decide)]; simpa [gS] using d
  · have hkG := Word.keep_op hop (W' := WG) (.inr (.inr (by decide)))
    refine Pre.keep hp (fun u => ?_) (hp.wg.keep hkG) hw' (Word.hist_keep hp.wg hkG) hh hop.clocks
      (task_lt ht) (.inl (by rw [upd_self]; rfl)) hop.fpt
    unfold upd; split
    · rename_i e; subst e; exact hX
    · exact XEq.refl _
  · exfalso
    obtain ⟨a', b', -⟩ := hi.2.done hr'
    rcases ht with rfl | rfl
    · rw [hg] at a'; cases a'
    · rw [hg] at b'; cases b'

theorem push_get_lt {xs : Array Word.Entry} {x : Word.Entry} {j : Nat} (h : j < xs.size) :
    (xs.push x)[j]! = xs[j]! := by
  rw [getElem!_pos (xs.push x) j (by simp; omega), getElem!_pos xs j h, Array.getElem_push_lt]

theorem push_get_eq {xs : Array Word.Entry} {x : Word.Entry} : (xs.push x)[xs.size]! = x := by
  simp

theorem evOk_push {m m' : Mem} {vs : List Nat} {e : Word.Entry} (h : EVOk m vs)
    (hh : EV.hist m' = (EV.hist m).push e) (he : e.Val (BitVec.ofNat 32 2)) :
    EVOk m' (vs ++ [2]) := by
  refine ⟨by rw [hh, Array.size_push, h.1]; simp, fun j hj => ?_⟩
  rw [hh]
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j vs.length with hjl | hjl
  · rw [push_get_lt (by rw [h.1]; exact hjl), List.getElem_append_left hjl]
    exact h.2 j hjl
  · obtain rfl : j = vs.length := by omega
    have e1 : (vs ++ [2])[vs.length]'(by simp) = 2 := by simp
    rw [e1]
    have hs : vs.length = (EV.hist m).size := h.1.symm
    rw [hs, push_get_eq]; exact he

/-- The newest write of the event. -/
theorem ev_lastOf {m : Mem} {vs l : List Nat} {x : Nat} (h : EVOk m vs) (hv : vs = l ++ [x]) :
    (last (EV.hist m)).Val (BitVec.ofNat 32 x) := by
  subst hv
  have hl : l.length < (l ++ [x]).length := by simp
  have := h.2 _ hl
  unfold last; rw [h.1]
  simpa using this

/-- The setter's `xchg(2)` (release) at the event, which read `old` (at `s1`): it sets `sx` and
freezes, at `wk` if it read `1` (`main` waits), else at `dn`. -/
theorem inv_sxchg {G : ThreadId → Gh} {m₁ m' : Mem} {t : ThreadId} {a b : VClock}
    {old : BitVec 32} (ht : t = 1 ∨ t = 2) (hi : proto.inv G m₁) (hg : G t = gS .s1 a b false)
    (hr : (G 0).2.ph.rank ≤ 7) (hv : (last (EV.hist m₁)).Val old)
    (hh : EV.hist m' = (EV.hist m₁).push
      (Word.rmwEnt m' t .release (last (EV.hist m₁)) (RmwOp.xchg.apply false old 2)))
    (hw' : EV.Ok m') (hop : EV.Op t m₁ m') (hL : L.Inv G m') :
    (old = 0 ∨ old = 1) ∧
      proto.inv (upd G t (gS (if old = 1 then .wk else .dn) a (m'.clocks[t]!) true)) m' := by
  have hp := hi.2.pre hr
  have h0 := task_ne ht
  obtain ⟨hot, ho0, ho12⟩ := oth_ne ht
  have hst : (G t).2.st := by rw [hg]; rfl
  obtain ⟨hfo, hsxo, hsto⟩ := hp.sfd t (oth t) (pair_oth ht) (by rw [hst]; rfl)
  obtain ⟨hfro, hfzo⟩ := hp.sto t (oth t) (pair_oth ht) hst
  have hsxt : (G t).2.sx = false := by rw [hg]; rfl
  have hsx : ((G 1).2.sx || (G 2).2.sx) = false := by
    rcases ht with rfl | rfl
    · simp [hsxt, show (G 2).2.sx = false from hsxo]
    · simp [hsxt, show (G 1).2.sx = false from hsxo]
  -- the value read: the newest write, `0` or `1` (`1` iff `main` wrote it)
  have hold : old = BitVec.ofNat 32 (if (G 0).2.e1 then 1 else 0) := by
    refine val_eq hv (ev_lastOf hp.evh (l := if (G 0).2.e1 then [0] else []) ?_)
    unfold evL; rw [hsx]; cases (G 0).2.e1 <;> rfl
  have h01 : old = 0 ∨ old = 1 := by rw [hold]; split <;> simp
  refine ⟨h01, ?_⟩
  have hclt := hop.clocks t
  generalize hc : m'.clocks[t]! = c at hclt ⊢
  have hle_c : VClock.le (G (oth t)).2.fz c = true := VClock.le_trans hfzo hclt
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G t (gS (if old = 1 then .wk else .dn) a c true) := ⟨_, rfl⟩
  rw [← hG']
  have hGo : ∀ u, u ≠ t → G' u = G u := fun u h => by rw [hG']; exact upd_ne _ _ h
  have hGt : G' t = gS (if old = 1 then .wk else .dn) a c true := by rw [hG']; exact upd_self _ _ _
  have hlast : last (EV.hist m') = Word.rmwEnt m' t .release (last (EV.hist m₁))
      (RmwOp.xchg.apply false old 2) := by rw [hh, last_push]
  have hrel : (last (EV.hist m')).relClock = VClock.merge (last (EV.hist m₁)).relClock c := by
    rw [hlast]; simp only [Word.rmwEnt, AtomicOrder.isRel, ↓reduceIte, hc]
  have hgx : (gS (if old = 1 then .wk else .dn) a c true).2.frozen = true := by
    unfold gS X.frozen; split <;> rfl
  have hL' : L.Inv G' m' := by
    rw [hG']
    refine linv_task hL ?_ ?_
    · rw [hg]; rfl
    · rw [hg]; unfold gS X.cnt; split <;> rfl
  refine ⟨hL', ?_⟩
  rw [hG']
  refine U_task ht hi hop.threads (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [EV] at h; omega))
    (by rw [hg]; rfl) (by unfold gS; split <;> rfl) rfl (fun w hw => ?_)
    (fun _ => by unfold gS; split <;> simp) (fun _ => rfl) (fun _ h => by cases h)
    (fun _ => rfl) (fun _ => ?_) (fun hr' => ?_)
  · rw [hop.waiters] at hw
    rcases hi.2.q w hw with h | ⟨a', b', c', d⟩
    · exact .inl h
    · refine .inr ⟨a', b', by rw [upd_ne _ _ (Ne.symm h0)]; exact c', ?_⟩
      -- `main` waits: it wrote `1`, so the setter read `1`
      have he1 : (G 0).2.e1 := hp.m1e (by simp [X.isEv1, c'])
      have h1 : old = 1 := by rw [hold, he1]; rfl
      have hwk : (gS (if old = 1 then .wk else .dn) a c true).2.ph = .wk := by
        unfold gS; rw [if_pos h1]
      rcases ht with rfl | rfl
      · rw [upd_self]; exact .inr (.inl hwk)
      · rw [upd_self]; exact .inr (.inr hwk)
  · rw [← hG']
    have hkG := Word.keep_op hop (W' := WG) (.inr (.inr (by decide)))
    have hhG := Word.hist_keep hp.wg hkG
    have hX0 : (G' 0).2 = (G 0).2 := by rw [hGo 0 (Ne.symm h0)]
    have hXo : (G' (oth t)).2 = (G (oth t)).2 := by rw [hGo _ hot]
    have hfdG : ∀ u, (G' u).2.fd = (G u).2.fd := fun u => by
      by_cases hut : u = t
      · subst hut; rw [hGt, hg]; unfold gS X.fd; split <;> rfl
      · rw [hGo u hut]
    have hsxG' : ((G' 1).2.sx || (G' 2).2.sx) = true := by
      rcases ht with rfl | rfl <;> simp [hGt, gS]
    refine ⟨hp.wg.keep hkG, hw', ?_, fun u hu hf => ?_, ?_, fun _ => ?_, fun u v huv hu => ?_,
      fun u v huv hu => ?_, fun u hu hs => ?_, fun _ _ _ => ?_,
      by rw [hX0]; exact hp.m1e, fun h => ?_, fun e he hb => ?_⟩
    · rw [hhG]
      have : wgv (G' 0).2 (G' 1).2 (G' 2).2 = wgv (G 0).2 (G 1).2 (G 2).2 := by
        unfold wgv; rw [hX0, hfdG 1, hfdG 2]
      rw [this]; exact hp.gv
    · rw [hhG]
      by_cases hut : u = t
      · subst hut; rw [hGt]
        have := hp.gw u hu (by rw [hg]; rfl); rw [hg] at this; exact this
      · rw [hGo u hut] at hf ⊢; exact hp.gw u hu hf
    · have hev : evL (G' 0).2 (G' 1).2 (G' 2).2 = evL (G 0).2 (G 1).2 (G 2).2 ++ [2] := by
        unfold evL; rw [hX0, hsxG', hsx]; simp
      unfold EVOk; rw [hev]
      refine evOk_push hp.evh hh ?_
      exact EV.enc_val _
    · rw [hrel]
      have ht' : VClock.le c (VClock.merge (last (EV.hist m₁)).relClock c) = true :=
        VClock.le_merge_right _ _
      rcases ht with rfl | rfl
      · rw [hGt, hGo 2 (by decide)]
        exact ⟨ht', VClock.le_trans hle_c ht'⟩
      · rw [hGt, hGo 1 (by decide)]
        exact ⟨VClock.le_trans hle_c ht', ht'⟩
    · by_cases hut : u = t
      · subst hut; rw [hGt] at hu; unfold gS X.st at hu; split at hu <;> simp at hu
      · have hvt : v = t := by
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases ht with rfl | rfl <;>
            first | rfl | exact absurd rfl hut
        subst hvt
        have hu' : u = oth v := by rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        subst hu'
        rw [hGo _ hot, hsto] at hu; cases hu
    · by_cases hut : u = t
      · subst hut
        have hv' : v = oth u := by rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        subst hv'
        rw [hGo _ hot]; exact ⟨hfo, hsxo, hsto⟩
      · have hvt : v = t := by
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases ht with rfl | rfl <;>
            first | rfl | exact absurd rfl hut
        subst hvt
        have hu' : u = oth v := by rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        subst hu'
        rw [hGo _ hot, hsto, hsxo] at hu; cases hu
    · rw [hX0]; exact hp.swa t ht (by rw [hst]; rfl)
    · rcases ht with rfl | rfl <;> simp [hGt, gS]
    · rw [hX0] at h
      have hs2 : 1 < (EV.hist m₁).size := by rw [hp.evh.1]; unfold evL; simp [h]
      rw [hh, push_get_lt hs2]; exact VClock.le_trans (hp.e1c h) (hop.clocks 0)
    · rcases hop.fpt e he with h' | ⟨het, hle⟩
      · obtain ⟨a', b'⟩ := hp.attr e h' hb
        refine ⟨a', VClock.le_trans b' ?_⟩
        unfold ac
        by_cases hut : e.tid = t
        · rw [hut, hGt, hg, hgx]
          show VClock.le (m₁.clocks[t]!) c = true
          exact hclt
        · rw [hGo _ hut]; split
          · exact VClock.le_refl _
          · exact hop.clocks _
      · refine ⟨het ▸ task_lt ht, ?_⟩
        unfold ac; rw [het, hGt, hgx]; rw [hc] at hle; exact hle
  · exfalso
    obtain ⟨a', b', -⟩ := hi.2.done hr'
    rcases ht with rfl | rfl
    · rw [hg] at a'; cases a'
    · rw [hg] at b'; cases b'

/-- A step of a frozen task that changes only the futex queue (and `current`): its new place is
`ph'` (`dn` or `fin`), the same for `Pre`. -/
theorem inv_frozen {G : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {ph ph' : Ph} {a b : VClock}
    {sx : Bool} (ht : t = 1 ∨ t = 2) (hi : proto.inv G m) (hg : G t = gS ph a b sx)
    (hph : ph = .wk ∨ ph = .dn) (hph' : ph' = .dn ∨ ph' = .fin) (hwk : ph = .wk → sx)
    (hL : L.Inv G m') (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) (hth : m'.threads = m.threads) (hc : m'.clocks = m.clocks)
    (hq : QOk (upd G t (gS ph' a b sx)) m') :
    proto.inv (upd G t (gS ph' a b sx)) m' := by
  have hX : XEq (G t).2 (gS ph' a b sx).2 := by
    rw [hg]; rcases hph with rfl | rfl <;> rcases hph' with rfl | rfl <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := fun u => by
    rw [hc]; exact VClock.le_refl _
  refine ⟨linv_task hL (by rw [hg]; rfl) (by rw [hg]; rcases hph with rfl | rfl <;>
    rcases hph' with rfl | rfl <;> rfl), ?_⟩
  refine U_task ht hi hth (by simp only [Mem.heap, hb]) (by rw [hg]; rcases hph with rfl | rfl <;> rfl)
    (by rcases hph' with rfl | rfl <;> rfl) rfl hq
    (fun _ => by rcases hph' with rfl | rfl <;> simp [gS]) (fun h => by
      rcases hph' with rfl | rfl <;> cases h)
    (fun _ hs => by
      have := hi.2.fzc t (by rw [hg]; rcases hph with rfl | rfl <;> rfl) (by rw [hg]; exact hs)
      rw [hg] at this; exact this)
    (fun _ => rfl) (fun hr => ?_) (fun hr => ?_)
  · have hp := hi.2.pre hr
    have hkG : WG.Keep m m' := Word.keep_of hb ha hf hth hcl
    have hkE : EV.Keep m m' := Word.keep_of hb ha hf hth hcl
    refine Pre.keep hp (fun u => ?_) (hp.wg.keep hkG) (hp.ev.keep hkE) (Word.hist_keep hp.wg hkG)
      (Word.hist_keep hp.ev hkE) hcl (task_lt ht) (.inr fun e he => hf ▸ he)
      fun e he => .inl (hf ▸ he)
    · unfold upd; split
      · rename_i e; subst e; exact hX
      · exact XEq.refl _
  · obtain ⟨a', b', c', d'⟩ := hi.2.done hr
    rw [hc]
    rcases ht with rfl | rfl
    · rw [upd_self, upd_ne _ _ (by decide)]; rw [hg] at a' c'
      exact ⟨by rcases hph' with rfl | rfl <;> rfl, b', c', d'⟩
    · rw [upd_self, upd_ne _ _ (by decide)]; rw [hg] at b' d'
      exact ⟨a', by rcases hph' with rfl | rfl <;> rfl, c', d'⟩

/-! ## A task's facts at a stop -/

theorem task_size {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {t : ThreadId}
    (ht : t = 1 ∨ t = 2) (htk : (G t).2.ph.isTask) : t < m.threads.size := by
  obtain ⟨-, -, -, d⟩ := hi.2.shape
  rcases d with ⟨-, -, d3, d4⟩ | ⟨d1, -, -, -, d5⟩ | ⟨d1, -⟩
  · exfalso; rcases ht with rfl | rfl
    · change (G 1).2 = {} at d3; rw [d3] at htk; cases htk
    · change (G 2).2 = {} at d4; rw [d4] at htk; cases htk
  · rcases ht with rfl | rfl
    · rw [d1]; decide
    · exfalso; change (G 2).2 = {} at d5; rw [d5] at htk; cases htk
  · rcases ht with rfl | rfl <;> rw [d1] <;> decide

theorem task_rank {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {t : ThreadId}
    (ht : t = 1 ∨ t = 2) (hfz : (G t).2.frozen = false) : (G 0).2.ph.rank ≤ 7 := by
  by_cases h : 6 ≤ (G 0).2.ph.rank
  · obtain ⟨a, b, -⟩ := hi.2.done h
    rcases ht with rfl | rfl
    · rw [hfz] at a; cases a
    · rw [hfz] at b; cases b
  · omega

/-- The futex wake of the setter (`wk`) at the event: no thread waits at the event after it. -/
theorem wake_q {cs : List Nat} {G G' : ThreadId → Gh} {m m' : Mem} {t : ThreadId} {n : Nat} (hn : 1 ≤ n)
    (hq : QOk G m)
    (hw : ((Thread.futexWake EV.ptr n cs).run { m with current := t }).run = some (.ok ((), m'))) :
    QOk G' m' ∧ m'.blocks = m.blocks ∧ m'.atomics = m.atomics ∧ m'.footprint = m.footprint ∧
      m'.threads = m.threads ∧ m'.clocks = m.clocks := by
  have hm' := Proto.modify_ok hw
  subst hm'
  refine ⟨fun w hw' => .inl ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [Array.mem_filter] at hw'
  obtain ⟨hwm, hnot⟩ := hw'
  rcases hq w hwm with h | ⟨h1, h2, -⟩
  · exact h
  · exfalso
    -- every waiter at the event is `main`, so `main` is woken
    have hin : (0 : ThreadId) ∈ Thread.wakeSet m.waiters EV.ptr n cs := by
      refine Thread.mem_wakeSet_of_all (by omega) ⟨w, hwm, h2⟩ fun v hv hvp => ?_
      rcases hq v hv with h | ⟨a, -, -⟩
      · exfalso; rw [hvp] at h; exact absurd h (by decide)
      · exact a
    rw [h1] at hnot
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hnot
    rw [Array.contains_iff_mem.mpr hin] at hnot; cases hnot

/-! ## `set` -/

/- The rules need `WP` only as a name: unfolding it runs the program. -/
attribute [local irreducible] Proto.WP

theorem evptr : (((((bPtr.add 0).add 8).add 0).add 0).add 0) = EV.ptr := rfl
theorem evptr4 : ((((bPtr.add 0).add 8).add 0).add 0) = EV.ptr := rfl

theorem set_eq (p : Ptr) : Thread_ResetEvent_set p =
    (Thread_ResetEvent_FutexImpl_set (p.add 0) >>= fun _ => pure ()) := by
  unfold Thread_ResetEvent_set
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, pure_bind, callC, StateT.run_lift,
    bind_assoc, map_bind, map_pure]

/-- `ResetEvent.set` by the setter `t` (at `s0`): it ends at `dn`, having set the event. -/
theorem set_spec {t : ThreadId} (ht : t = 1 ∨ t = 2) (a b : VClock) (G : ThreadId → Gh) (m : Mem)
    (d : Nat) (hi : proto.inv (upd G t (gS .s0 a b false)) m) :
    proto.WP t (Thread_ResetEvent_set ((bPtr.add 0).add 8))
      (fun _ G' m' _ => ∃ c, proto.inv (upd G' t (gS .dn a c true)) m') G m d := by
  rw [set_eq]
  refine WP.bind ?_
  unfold Thread_ResetEvent_FutexImpl_set
  refine WP.bind ?_
  rw [StateT.run'_eq, map_eq_pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  rw [evptr]
  have hts : ∀ (g : Gh), g.2.ph.isTask → g.2.frozen = false → ∀ G₁ m₁, G₁ t = g →
      proto.inv G₁ m₁ → t < m₁.threads.size ∧ (G₁ 0).2.ph.rank ≤ 7 := fun g h1 h2 G₁ m₁ hg hi₁ =>
    ⟨task_size hi₁ ht (by rw [hg]; exact h1), task_rank hi₁ ht (by rw [hg]; exact h2)⟩
  refine WP.bind (wp_load shE hi (hts _ rfl rfl)
    fun k hk G₁ m₁ m' v j hg₁ hi₁ hr hj hv _ _ hh hw' hop hL => ?_)
  obtain ⟨hv01, hi'⟩ := inv_sload ht hi₁ hg₁ hr hj hv hh hw' hop hL
  have hv2 : (v == (2 : BitVec 32)) = false := by rcases hv01 with rfl | rfl <;> rfl
  simp only [StateT.run_pure, pure_bind, hv2, Bool.false_eq_true, ↓reduceIte]
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_rmw shE hi' (hts _ rfl rfl)
    fun k₂ hk₂ G₂ m₂ m'' old hg₂ hi₂ hr₂ hv' _ hh' _ hw'' hop' hL' => ?_)
  obtain ⟨h01, hi''⟩ := inv_sxchg ht hi₂ hg₂ hr₂ hv' hh' hw'' hop' hL'
  simp only [StateT.run_pure, pure_bind]
  by_cases h1 : old = 1
  · subst h1
    simp only [show ((1 : BitVec 32) == 1) = true from rfl, ↓reduceIte, StateT.run_bind, bind_assoc,
      pure_bind]
    rw [evptr4, threadFutexWakeC_eq]
    refine WP.bind (WP.futexWakeC fun k₃ hk₃ => ⟨_, hi'', fun G₃ m₃ hg₃ hi₃ cs m₄ hw => ?_⟩)
    simp only [if_pos rfl] at hg₃
    have hl := hi₃.1.wakeOff (by decide) hw
    obtain ⟨hq, hb, ha, hf, hth, hc⟩ := wake_q (G' := upd G₃ t (gS .dn a (m''.clocks[t]!) true))
      (by decide) hi₃.2.q hw
    have := inv_frozen (ph := .wk) (ph' := .dn) ht hi₃ hg₃ (.inl rfl) (.inl rfl) (fun _ => rfl) hl hb
      ha hf hth hc hq
    simp only [StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' (WP.pure' (WP.pure' ⟨_, this⟩)))
  · have h0 : old = 0 := h01.resolve_right h1
    subst h0
    simp only [show ((0 : BitVec 32) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, pure_bind] at hi'' ⊢
    simp only [show ((0 : BitVec 32) = 1) ↔ False by decide, ↓reduceIte] at hi''
    exact WP.pure' (WP.pure' (WP.pure' (WP.pure' ⟨_, hi''⟩)))

/-! ## `finish` -/

theorem dbg_true : (debug_assert true).run = some (.ok ()) := rfl

theorem div2 (k : Nat) (h2 : 2 ≤ k) (h5 : k ≤ 5) :
    (divTrunc false (BitVec.ofNat 64 k) 2).run = some (.ok (BitVec.ofNat 64 (k / 2))) ∧
      gt false (BitVec.ofNat 64 (k / 2)) 0 = true := by
  rcases (by omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem gF_dn {k : Nat} (h : k ≠ 3) (c : VClock) : gF k c = gS .dn c c false := by
  simp [gF, gS, h]

theorem gF_s0 (c : VClock) : gF 3 c = gS .s0 c c false := by simp [gF, gS]

/-- `WaitGroup.finish` by task `t` (at `inc`, `out`): it ends at `dn`. -/
theorem finish_spec {t : ThreadId} (ht : t = 1 ∨ t = 2) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G t (gT .inc)) m) :
    proto.WP t (Thread_WaitGroup_finish (bPtr.add 0))
      (fun _ G' m' _ => ∃ a c sx, proto.inv (upd G' t (gS .dn a c sx)) m') G m d := by
  unfold Thread_WaitGroup_finish
  refine WP.bind ?_
  rw [StateT.run'_eq, map_eq_pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_rmw shG hi (fun G₁ m₁ hg hi₁ =>
    ⟨task_size hi₁ ht (by rw [hg]; rfl), task_rank hi₁ ht (by rw [hg]; rfl)⟩)
    fun k hk G₁ m₁ m' old hg₁ hi₁ hr hv _ hh hacq hw' hop hL => ?_)
  obtain ⟨n, rfl, hn2, hn5, hi'⟩ := inv_finish ht hi₁ hg₁ hr hv hh (hacq rfl) hw' hop hL
  obtain ⟨hdiv, hgt⟩ := div2 n hn2 hn5
  simp only [StateT.run_pure, pure_bind]
  refine WP.bind (WP.callRC_ok hdiv ?_)
  simp only [StateT.run_pure, pure_bind, hgt]
  refine WP.bind (WP.callRC_ok dbg_true ?_)
  simp only [StateT.run_pure, pure_bind]
  by_cases h3 : n = 3
  · subst h3
    simp only [show (BitVec.ofNat 64 3 == 3) = true from rfl, ↓reduceIte, StateT.run_bind,
      bind_assoc, pure_bind]
    rw [gF_s0] at hi'
    refine WP.bind (WP.callC (WP.mono ?_ (set_spec ht _ _ G₁ m' k hi')))
    rintro _ G₂ m₂ d₂ ⟨c', hi₂⟩
    simp only [StateT.run_pure, pure_bind]
    exact WP.pure' (WP.pure' (WP.pure' ⟨_, _, _, hi₂⟩))
  · have hne : (BitVec.ofNat 64 n == 3) = false := by
      rcases (by omega : n = 2 ∨ n = 4 ∨ n = 5) with rfl | rfl | rfl <;> rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
    rw [gF_dn h3] at hi'
    exact WP.pure' (WP.pure' (WP.pure' ⟨_, _, _, hi'⟩))

/-! ## A task -/

theorem cnt_le {Y : ThreadId → X} {t : ThreadId} (ht : t = 1 ∨ t = 2) (hy : (Y t).cnt = 0) :
    cnt Y ≤ 1 := by
  unfold cnt
  have : ∀ x : X, x.cnt ≤ 1 := fun x => by unfold X.cnt; split <;> omega
  rcases ht with rfl | rfl
  · rw [hy]; exact Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) (this _)
  · rw [hy]; exact this _

theorem cnt_inc {G : ThreadId → Gh} {t : ThreadId} (ht : t = 1 ∨ t = 2) (hL hL' : Heap) :
    cnt (fun u => (upd G t (gH .inc hL') u).2) = cnt (fun u => (upd G t (gH .lk hL) u).2) + 1 := by
  unfold cnt
  rcases ht with rfl | rfl
  · simp only [upd_self, upd_ne _ _ (show (2 : ThreadId) ≠ 1 by decide)]
    simp [gH, X.cnt, Ph.isTask, Ph.rank]; omega
  · simp only [upd_self, upd_ne _ _ (show (1 : ThreadId) ≠ 2 by decide)]
    simp [gH, X.cnt, Ph.isTask, Ph.rank]

/-- A task: `lock`, the counter `+= 1`, `unlock`, `finish`; it ends at `dn`. -/
theorem task_spec {t : ThreadId} (ht : t = 1 ∨ t = 2) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G t (gT .lk)) m) (hc : m.current = t) :
    proto.WP t (task bPtr)
      (fun _ G' m' _ => ∃ a c sx, proto.inv (upd G' t (gS .dn a c sx)) m') G m d := by
  unfold task
  refine WP.bind ?_
  rw [StateT.run'_eq, map_eq_pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  -- `lock`
  refine WP.bind (WP.callC (WP.mono ?_ (lock_spec fits rfl mptr t (gT .lk) rfl G m d hi)))
  rintro _ G₂ m₂ d₂ ⟨-, hc₂, hL, hi₂⟩
  have hi₂' : proto.inv (upd G₂ t (gH .lk hL)) m₂ := hi₂
  -- the load of the counter
  refine WP.bind (wp_cntLoad ht hi₂' hc₂ fun m₃ hQ hc₃ ht₃ hi₃ => ?_)
  have hle := cnt_le (Y := fun u => (upd G₂ t (gH .lk hL) u).2) ht (by
    show (upd G₂ t (gH .lk hL) t).2.cnt = 0; rw [upd_self]; rfl)
  generalize hS : cnt (fun u => (upd G₂ t (gH .lk hL) u).2) = S at hle ⊢
  have hS3 : S + 1 < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega : S + 1 ≤ 2) (by decide)
  have hS32 : (BitVec.ofNat 32 S).toNat = S := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- the add
  refine WP.bind (WP.callRC (fun e he => (add_one_noErr (by rw [hS32]; exact hS3) e he).elim)
    fun v₃ hadd => ?_)
  have hv₃ := add_one_ok hadd (by rw [hS32]; exact hS3)
  rw [hS32] at hv₃
  -- the store
  refine WP.bind (wp_cntStore v₃ ht hi₃ hc₃ (by
    apply BitVec.eq_of_toNat_eq
    rw [hv₃, cnt_inc ht hL hQ, hS, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS3])
    fun m₄ hQ' hc₄ ht₄ hi₄ => ?_)
  -- `unlock`
  refine WP.bind (WP.callC (WP.mono ?_ (unlock_spec fits rfl mptr t (gH .inc hQ') rfl G₂ m₄ d₂ hi₄)))
  rintro _ G₃ m₅ d₃ ⟨-, -, hi₅⟩
  have hi₅' : proto.inv (upd G₃ t (gT .inc)) m₅ := hi₅
  -- `finish`
  refine WP.bind (WP.callC (WP.mono ?_ (finish_spec ht G₃ m₅ d₃ hi₅')))
  rintro _ G₄ m₆ d₄ ⟨a, c, sx, hi₆⟩
  simp only [StateT.run_pure, pure_bind]
  exact WP.pure' (WP.pure' (WP.pure' ⟨a, c, sx, hi₆⟩))

/-- The tasks spawned no thread. -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : proto.inv G m)
    (hu : 0 < u) : joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, -, -, h⟩ := hi.2.shape
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have hsp : ∀ j (hj : j < m.threads.size), (m.threads[j]'hj).spawner = 0 := by
    intro j hj
    rcases h with ⟨h1, -⟩ | ⟨h2, -, h1, -⟩ | ⟨h3, -, -, -, h1, h2⟩
    · obtain rfl : j = 0 := by omega
      rw [Array.getElem?_eq_getElem hj] at h0; rw [Option.some.inj h0]
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [Array.getElem?_eq_getElem hj] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hj] at h1; rw [Option.some.inj h1]
    · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [Array.getElem?_eq_getElem hj] at h0; rw [Option.some.inj h0]
      · rw [Array.getElem?_eq_getElem hj] at h1; rw [Option.some.inj h1]
      · rw [Array.getElem?_eq_getElem hj] at h2; rw [Option.some.inj h2]
  rw [hsp i hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)

theorem discard_eq (x : ConcM Tgt Unit) : discard x = (fun _ => ()) <$> x := rfl

theorem dispatch_task (p : Ptr) : dispatch (Tgt.task p) = (fun _ => ()) <$> task p := by
  rw [show dispatch (Tgt.task p) = discard (task p) from rfl]; exact discard_eq _

/-- A task: `task` on the `Tally`, then its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | task p =>
    obtain ⟨rfl, rfl⟩ := hg
    have hu12 : u = 1 ∨ u = 2 := by
      have := hi.2.out3 u
      by_cases h3 : 3 ≤ u
      · rw [hgu] at this; exact absurd (this h3) (by decide)
      · unfold ThreadId at *; omega
    rw [dispatch_task]
    refine WP.map (WP.mono ?_ (task_spec hu12 G _ d
      (by rw [show gT .lk = G u from hgu.symm, upd_same]; exact inv_cur hi u) rfl))
    rintro _ G' m' _ ⟨a, c, sx, hi'⟩
    have hq : QOk (upd G' u (gS .fin a c sx)) m' := by
      intro w hw
      rcases hi'.2.q w hw with h | ⟨a', b', c', d'⟩
      · exact .inl h
      · have hu0 : (0 : ThreadId) ≠ u := Nat.ne_of_lt hu
        refine .inr ⟨a', b', by rw [upd_ne _ _ hu0] at c' ⊢; exact c', ?_⟩
        rcases hu12 with rfl | rfl
        · simp only [upd_self, upd_ne _ _ (show (2 : ThreadId) ≠ 1 by decide)] at d' ⊢
          simpa [gS] using d'
        · simp only [upd_self, upd_ne _ _ (show (1 : ThreadId) ≠ 2 by decide)] at d' ⊢
          simpa [gS] using d'
    have hfin := inv_frozen (ph := .dn) (ph' := .fin) hu12 hi' (upd_self _ _ _) (.inr rfl) (.inr rfl)
      (fun h => by cases h) hi'.1 rfl rfl rfl rfl rfl (by rw [upd_upd]; exact hq)
    rw [upd_upd] at hfin
    exact ⟨_, hfin, ⟨rfl, rfl⟩, fun _ => joinedAll_kid hfin hu⟩
  | producer p => cases hg
  | work p => cases hg

/-! ## The start -/

/-- The `Tally` that `main` stores. -/
def tally0 : Tally :=
  { wg := { state := { raw := 0 }, event := { impl := { state := { raw := 0 } } } },
    m := mutexOf 0, n := 0 }

theorem enc_tally : (Enc.encode tally0).size = 24 ∧
    (Enc.encode tally0).extract 0 8 = Enc.encode (0 : BitVec 64) ∧
    (Enc.encode tally0).extract 8 12 = Enc.encode (0 : BitVec 32) ∧
    (Enc.encode tally0).extract 16 20 = Enc.encode (0 : BitVec 32) ∧
    (Enc.encode tally0).extract 20 24 = Enc.encode (0 : BitVec 32) := by decide +kernel

/-- No thread at the start. -/
def G0 : ThreadId → Gh := fun _ => (⟨.gone, Heap.empty, Heap.empty⟩, {})

/-- `main` before `startMany`. -/
def gM (h : Heap) (x : X) : Gh := (⟨.out, h, Heap.empty⟩, x)

/-- A shared word at the start: no atomic location, each access happened before every thread,
and the value 0. -/
theorem word_init {n nb : Nat} {W : Word n nb} {m : Mem} {blk : Block} (hW : W.b = 0)
    (hal : (blk.addr + W.o) % nb = 0) (hhi : W.o + nb ≤ 24) (hb : m.blocks[0]? = some blk)
    (hl : blk.live = true) (hs : blk.bytes.size = 24) (hk : blk.kind = .stack)
    (hat : m.atomics = #[])
    (hv : (intOfBytes n (blk.bytes.extract W.o (W.o + nb))).run = some (.ok 0))
    (hfp : ∀ e ∈ m.footprint, W.Hits e → AllLe m e.clock) :
    W.Ok m ∧ (W.hist m).size = 1 ∧ (W.hist m)[0]!.Val (0 : BitVec n) := by
  have hno : ∀ i l, ¬ W.Loc m i l := fun i l hl => by
    have := (Word.loc_get hl).1; rw [hat] at this; simp at this
  have hu : W.Holds m 0 := by unfold Word.Holds curBytes; rw [hW, hb]; exact hv
  refine ⟨⟨⟨blk, by rw [hW]; exact hb, hl, by omega, hal, by rw [hk]; decide⟩,
    fun l hl' => by rw [hat] at hl'; simp at hl', fun i l h => absurd h (hno i l),
    fun e he hh => .inr (hfp e he hh), ⟨0, hu⟩, fun i l h => absurd h (hno i l)⟩, ?_, ?_⟩
  · rw [Word.hist_none hno]; rfl
  · rw [Word.hist_none hno]; exact hu

theorem allLe_one {m : Mem} {c : VClock} (h1 : m.threads.size = 1)
    (h : VClock.le c (m.clocks[0]!) = true) : AllLe m c := fun u hu => by
  rw [h1] at hu
  have : u = 0 := by omega
  subst this; exact h

/-- Before `startMany`: `main` alone owns the `Tally`, with its bytes. The mutex starts: it owns the
counter; the two words belong to no thread. -/
theorem inv_start {m : Mem} {A : Nat} {h : Heap}
    (ho : Owned (upd (fun _ => Heap.empty) 0 h) m)
    (hb : bytesAt bPtr A 24 .stack (Enc.encode tally0) h) (hA : A % 8 = 0)
    (hth : m.threads = #[{ spawner := 0, joined := true }]) (hat : m.atomics = #[])
    (hq : m.waiters = #[])
    (hfp0 : ∀ e ∈ m.footprint, e.tid = 0 ∧ VClock.le e.clock (m.clocks[0]!) = true) :
    proto.inv (upd G0 0 (gM Heap.empty { ph := .pre })) m := by
  obtain ⟨hsz, he0, he8, he16, he20⟩ := enc_tally
  obtain ⟨hP, hWR, dP, rfl, hbP, hbWR⟩ := bytesAt_split hb (k := 16) (by rw [hsz]; decide)
  obtain ⟨hW, hR, dWR, rfl, hbW, hbR⟩ := bytesAt_split hbWR (k := 4) (by simp [hsz])
  have hsub := ho.sub 0; rw [upd_self] at hsub
  have sW : hW.Sub m.heap :=
    (Heap.sub_union_left.trans (Heap.sub_union_right dP)).trans hsub
  have sR : hR.Sub m.heap :=
    (Heap.sub_union_right dWR |>.trans (Heap.sub_union_right dP)).trans hsub
  have sH : (hP ∪ (hW ∪ hR)).Sub m.heap := hsub
  have h1 : m.threads.size = 1 := by rw [hth]; rfl
  obtain ⟨blk, hblk, hl, hA', hS', hK', hx⟩ := bytesAt_blk (m := m) hb sH rfl (by rw [hsz]; decide)
  have hbk : BlkOk m := ⟨blk, hblk, hl, hS', by rw [hA']; exact hA, hK'⟩
  have hext : ∀ a b, b ≤ 24 → blk.bytes.extract a b = (Enc.encode tally0).extract a b := by
    intro a b hb'
    rw [← hx]; simp only [Array.extract_extract, bPtr]
    simp [hsz]; congr 1 <;> omega
  have hall : ∀ e ∈ m.footprint, AllLe m e.clock := fun e he =>
    allLe_one h1 (by obtain ⟨-, hle⟩ := hfp0 e he; exact hle)
  obtain ⟨hwgOk, hwgz, hwgv⟩ := word_init (W := WG) rfl (by simp [WG]; rw [hA']; omega)
    (by decide) hblk hl hS' hK' hat (by
      rw [show WG.o = 0 from rfl, hext 0 8 (by decide), he0]
      exact LawfulEnc.decode_encode (α := BitVec 64) 0) (fun e he _ => hall e he)
  obtain ⟨hevOk, hevz, hevv⟩ := word_init (W := EV) rfl (by simp [EV]; rw [hA']; omega)
    (by decide) hblk hl hS' hK' hat (by
      rw [show EV.o = 8 from rfl, hext 8 12 (by decide), he8]
      exact LawfulEnc.decode_encode (α := BitVec 32) 0) (fun e he _ => hall e he)
  have h0 : L.U32 m 0 := by
    show (intOfBytes 32 (curBytes m 0 16 4)).run = _
    unfold curBytes; rw [hblk]
    simp only [Option.map_some, Option.getD_some]
    rw [hext 16 20 (by decide), he16]
    exact intOfBytes_rmw 0
  -- the resource: the counter is `0`
  have hR' : L.R (upd G0 0 (gM Heap.empty { ph := .pre })) hR := by
    show R (fun u => (upd G0 0 (gM Heap.empty { ph := .pre }) u).2) hR
    unfold R
    rw [show ((fun u => (upd G0 0 (gM Heap.empty { ph := .pre }) u).2) 1).cnt +
      ((fun u => (upd G0 0 (gM Heap.empty { ph := .pre }) u).2) 2).cnt = 0 from rfl]
    have hbR' : bytesAt (bPtr.add 20) A 24 .stack (Enc.encode (0 : BitVec 32)) hR := by
      have e : ((((Enc.encode tally0).extract 16 (Enc.encode tally0).size)).extract 4
          ((Enc.encode tally0).extract 16 (Enc.encode tally0).size).size) =
          Enc.encode (0 : BitVec 32) := by
        rw [hsz]; simp only [Array.extract_extract]; rw [← he20]; simp [hsz]
      rw [← e]
      exact hbR
    exact ⟨A, 24, .stack, _, by simp [bPtr, Ptr.add]; omega, LawfulEnc.size_encode _,
      LawfulEnc.decode_encode _, hbR', by decide⟩
  -- `main` keeps nothing; the lock gets the mutex and the counter
  have dRW : Heap.Disjoint hR hW := dWR.symm
  have ho' := ho.shrink (t := 0) (h := Heap.empty ∪ (hR ∪ hW)) (by
    rw [upd_self, Heap.empty_union, Heap.union_comm dRW]; exact Heap.sub_union_right dP)
  rw [upd_upd] at ho'
  have hGu : ∀ u, u ≠ 0 → upd G0 0 (gM Heap.empty { ph := .pre }) u = G0 u := fun u h => upd_ne _ _ h
  have hcellW : ∀ x, 16 ≤ x → x < 16 + 4 → hW (0, x) ≠ none := fun x a b =>
    bytesAt_in hbW rfl (by simp [bPtr, Ptr.add]; omega) (by simp [bPtr, Ptr.add, hsz]; omega)
  have hL := Inv.make (L := L) (G := upd G0 0 (gM Heap.empty { ph := .pre })) (t := 0) (hL := hR)
    (hW := hW) ho' rfl
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
  have hX0 : (upd G0 0 (gM Heap.empty { ph := .pre }) 0).2 = { ph := .pre } := by rw [upd_self]; rfl
  have hXu : ∀ u, u ≠ 0 → (upd G0 0 (gM Heap.empty { ph := .pre }) u).2 = {} := fun u hu => by
    rw [hGu u hu]; rfl
  have h3ne : ∀ u : ThreadId, 3 ≤ u → u ≠ 0 := fun u hu => Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu)
  refine ⟨hL, ⟨⟨by rw [hth]; rfl, by show (upd G0 0 (gM Heap.empty { ph := .pre }) 0).2.ph.isMain = true; rw [hX0]; rfl,
    fun u hu => hXu u (h3ne u hu),
    .inl ⟨h1, by show (upd G0 0 (gM Heap.empty { ph := .pre }) 0).2.ph.rank ≤ 1; rw [hX0]; decide, hXu 1 (by decide),
      hXu 2 (by decide)⟩⟩,
    fun u hu => by rw [hGu u hu]; rfl, fun x => by rw [upd_self]; rfl,
    fun u hu => by rw [hGu u (h3ne u hu)]; rfl, hbk, fun w hw => by rw [hq] at hw; simp at hw,
    fun u h => ?_, fun u h => ?_, fun u h => ?_, fun u h => ?_, fun _ => ?_, fun h => ?_⟩⟩
  · by_cases hu : u = 0
    · subst hu; rw [hX0] at h; cases h
    · rw [hXu u hu] at h; cases h
  · by_cases hu : u = 0
    · subst hu; rw [hX0] at h; cases h
    · rw [hXu u hu] at h; cases h
  · by_cases hu : u = 0
    · subst hu; rw [hX0] at h; cases h
    · rw [hXu u hu] at h; cases h
  · by_cases hu : u = 0
    · subst hu; rw [hX0] at h; cases h
    · rw [hXu u hu] at h; cases h
  · have hX1 := hXu 1 (by decide); have hX2 := hXu 2 (by decide)
    refine ⟨hwgOk, hevOk, ?_, fun u hu hf => ?_, ?_, fun h => ?_, fun u v huv hu => ?_,
      fun u v huv hu => ?_, fun u hu hs => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
      fun e he hb' => ?_⟩
    · rw [hX0, hX1, hX2]; unfold last; rw [hwgz]; exact hwgv
    · rcases hu with rfl | rfl
      · rw [hX1] at hf; cases hf
      · rw [hX2] at hf; cases hf
    · rw [hX0, hX1, hX2]; exact ⟨hevz, fun j hj => by simp [evL] at hj; subst hj; exact hevv⟩
    · rw [hX1, hX2] at h; cases h
    · rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [hX1] at hu; cases hu
      · rw [hX2] at hu; cases hu
    · rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [hX1] at hu; cases hu
      · rw [hX2] at hu; cases hu
    · rcases hu with rfl | rfl
      · rw [hX1] at hs; cases hs
      · rw [hX2] at hs; cases hs
    · rw [hX0] at h; cases h
    · rw [hX0] at h; cases h
    · rw [hX0] at h; cases h
    · obtain ⟨ht0, hle⟩ := hfp0 e he
      refine ⟨by rw [ht0]; decide, ?_⟩
      unfold ac; rw [ht0, hX0]; exact hle
  · rw [hX0] at *; exact absurd h (by decide)

/-! ## `main`'s steps -/

/-- `U` after a step of `main` with its new ghost value `g`: the facts of `U` that read it. -/
theorem U_main {G : ThreadId → Gh} {m m' : Mem} {g : Gh} (hi : proto.inv G m)
    (hsh : Shape (fun u => (upd G 0 g u).2) m') (hcell : m'.heap (0, 12) = m.heap (0, 12))
    (hp0 : ∀ x, g.1.part (0, x) = none) (hq : QOk (upd G 0 g) m')
    (hpre : (upd G 0 g 0).2.ph.rank ≤ 7 → Pre (upd G 0 g) m')
    (hdone : 6 ≤ (upd G 0 g 0).2.ph.rank → (G 1).2.frozen ∧ (G 2).2.frozen ∧
      VClock.le (G 1).2.fz (m'.clocks[0]!) = true ∧ VClock.le (G 2).2.fz (m'.clocks[0]!) = true)
    (hx : g.2.sx = false ∧ g.2.ph ≠ .wk ∧ g.2.frozen = false ∧ g.2.fd = false) :
    U (upd G 0 g) m' := by
  obtain ⟨hsx, hwk, hfz, hfd⟩ := hx
  have hGu : ∀ u, u ≠ 0 → upd G 0 g u = G u := fun u h => upd_ne _ _ h
  refine ⟨hsh, fun u hu => by rw [hGu u hu]; exact hi.2.parts u hu, fun x => by rw [upd_self]; exact hp0 x,
    fun u h3 => by rw [hGu u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h3))]; exact hi.2.out3 u h3,
    blk_keep hi.2.blk hcell, hq, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, hpre,
    fun hr => ?_⟩
  · by_cases hu : u = 0
    · subst hu; rw [upd_self, hsx]; intro h; cases h
    · rw [hGu u hu]; exact hi.2.sx1 u
  · by_cases hu : u = 0
    · subst hu; rw [upd_self]; intro h; exact absurd h hwk
    · rw [hGu u hu]; exact hi.2.wks u
  · by_cases hu : u = 0
    · subst hu; rw [upd_self, hfz]; intro h; cases h
    · rw [hGu u hu]; exact hi.2.fzc u
  · by_cases hu : u = 0
    · subst hu; rw [upd_self, hfd]; intro h; cases h
    · rw [hGu u hu]; exact hi.2.lg u
  · obtain ⟨a, b, c, d⟩ := hdone hr
    rw [hGu 1 (by decide), hGu 2 (by decide)]; exact ⟨a, b, c, d⟩

/-- `main`'s `startMany(2)`: a relaxed `add(4)` at the group's state, which read `0`. -/
theorem inv_sm {G : ThreadId → Gh} {m₁ m' : Mem} {old : BitVec 64} (hi : proto.inv G m₁)
    (hg : G 0 = gM Heap.empty { ph := .pre }) (hv : (last (WG.hist m₁)).Val old)
    (hh : WG.hist m' = (WG.hist m₁).push
      (Word.rmwEnt m' 0 .relaxed (last (WG.hist m₁)) (RmwOp.add.apply false old 4)))
    (hw' : WG.Ok m') (hop : WG.Op 0 m₁ m') (hL : L.Inv G m') :
    old = 0 ∧ proto.inv (upd G 0 (gM Heap.empty { ph := .sm })) m' := by
  have hp := hi.2.pre (by rw [hg]; decide)
  have hgx : (G 0).2 = { ph := .pre } := by rw [hg]; rfl
  have hold : old = 0 := val_eq hv (by
    have := hp.gv; unfold wgv at this; rw [hgx] at this; exact this)
  subst hold
  refine ⟨rfl, linv_task hL (by rw [hg]; rfl) (by rw [hg]; rfl), ?_⟩
  -- the tasks do not exist yet
  obtain ⟨h00, -, h3, d⟩ := hi.2.shape
  rcases d with ⟨d1, -, d3, d4⟩ | ⟨-, d2, -⟩ | ⟨-, d2, -⟩
  rotate_left
  · exfalso; change (G 0).2.ph = .sp1 at d2; rw [hgx] at d2; cases d2
  · exfalso; change 3 ≤ (G 0).2.ph.rank at d2; rw [hgx] at d2; simp [Ph.rank] at d2
  change (G 1).2 = {} at d3; change (G 2).2 = {} at d4
  have hGu : ∀ u, u ≠ 0 → upd G 0 (gM Heap.empty { ph := .sm }) u = G u := fun u h => upd_ne _ _ h
  have hX0 : (upd G 0 (gM Heap.empty { ph := .sm }) 0).2 = { ph := .sm } := by rw [upd_self]; rfl
  refine U_main hi ⟨by rw [hop.threads]; exact h00, by show (upd G 0 (gM Heap.empty { ph := .sm }) 0).2.ph.isMain = true; rw [hX0]; rfl,
      fun u hu => by show (upd G 0 (gM Heap.empty { ph := .sm }) u).2 = _; rw [hGu u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu))]; exact h3 u hu,
      .inl ⟨by rw [hop.threads]; exact d1, by show (upd G 0 (gM Heap.empty { ph := .sm }) 0).2.ph.rank ≤ 1; rw [hX0]; decide,
        by show (upd G 0 (gM Heap.empty { ph := .sm }) 1).2 = _; rw [hGu 1 (by decide)]; exact d3,
        by show (upd G 0 (gM Heap.empty { ph := .sm }) 2).2 = _; rw [hGu 2 (by decide)]; exact d4⟩⟩
    (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [WG] at h; omega)) (fun x => rfl)
    (fun w hw => ?_) (fun _ => ?_) (fun h => by rw [hX0] at h; simp [Ph.rank] at h) ⟨rfl, by decide, rfl, rfl⟩
  · rw [hop.waiters] at hw
    rcases hi.2.q w hw with h | ⟨-, -, c', -⟩
    · exact .inl h
    · rw [hgx] at c'; cases c'
  · have hkE := Word.keep_op hop (W' := EV) (.inr (.inl (by decide)))
    have hX1 : (upd G 0 (gM Heap.empty { ph := .sm }) 1).2 = {} := by rw [hGu 1 (by decide)]; exact d3
    have hX2 : (upd G 0 (gM Heap.empty { ph := .sm }) 2).2 = {} := by rw [hGu 2 (by decide)]; exact d4
    refine ⟨hw', hp.ev.keep hkE, ?_, fun u hu hf => ?_, ?_, fun h => ?_, fun u v huv hu => ?_,
      fun u v huv hu => ?_, fun u hu hs => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
      fun e he hb => ?_⟩
    · rw [hh, last_push, hX0, hX1, hX2]; exact WG.enc_val _
    · rcases hu with rfl | rfl
      · rw [hX1] at hf; cases hf
      · rw [hX2] at hf; cases hf
    · unfold EVOk; rw [Word.hist_keep hp.ev hkE, hX0, hX1, hX2]
      have := hp.evh; rw [hgx, d3, d4] at this; exact this
    · rw [hX1, hX2] at h; cases h
    · rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [hX1] at hu; cases hu
      · rw [hX2] at hu; cases hu
    · rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [hX1] at hu; cases hu
      · rw [hX2] at hu; cases hu
    · rcases hu with rfl | rfl
      · rw [hX1] at hs; cases hs
      · rw [hX2] at hs; cases hs
    · rw [hX0] at h; cases h
    · rw [hX0] at h; cases h
    · rw [hX0] at h; cases h
    · rcases hop.fpt e he with h' | ⟨het, hle⟩
      · obtain ⟨a, b⟩ := hp.attr e h' hb
        refine ⟨a, VClock.le_trans b ?_⟩
        unfold ac
        by_cases h0 : e.tid = 0
        · rw [h0, hX0, hgx]; exact hop.clocks 0
        · rw [show (upd G 0 (gM Heap.empty { ph := .sm }) e.tid) = G e.tid from upd_ne _ _ h0]
          split
          · exact VClock.le_refl _
          · exact hop.clocks _
      · refine ⟨by rw [het]; decide, ?_⟩
        unfold ac; rw [het, hX0]; exact hle

theorem nil_le (x : VClock) : VClock.le #[] x = true := by
  unfold VClock.le VClock.get
  rw [Array.all_eq_true]; intro i _; simp

/-- The spawn of task `k` (the thread count before it) by `main` (at `p`, which goes to `p'`). -/
theorem inv_spawn {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} {k : Nat} {p p' : Ph}
    (hi : proto.inv G m) (hg : G 0 = gM Heap.empty { ph := p })
    (hk : (k = 1 ∧ p = .sm ∧ p' = .sp1) ∨ (k = 2 ∧ p = .sp1 ∧ p' = .run))
    (hsz : m.threads.size = k)
    (hf : (Thread.fork.run { m with current := 0 }).run = some (.ok (c, m'))) :
    c = k ∧ proto.inv (upd (upd G k (gT .lk)) 0 (gM Heap.empty { ph := p' })) m' := by
  have hu := hi.2
  have hk12 : k = 1 ∨ k = 2 := by rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hk0 : (0 : ThreadId) ≠ k := by rcases hk12 with rfl | rfl <;> decide
  have hcs : m.clocks.size = k := by rw [hi.1.own.csize, hsz]
  have hjb := joinedB_fork hf
  obtain ⟨hch, hm'⟩ := Lock.fork_eq hf
  rw [hsz] at hch
  subst hch
  have hGk : (G c).2 = {} := by
    obtain ⟨-, -, -, d⟩ := hu.shape
    rcases hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases d with ⟨-, -, d3, -⟩ | ⟨d1, -⟩ | ⟨d1, -⟩
      · exact d3
      · omega
      · omega
    · rcases d with ⟨d1, -⟩ | ⟨-, -, -, -, d5⟩ | ⟨d1, -⟩
      · omega
      · exact d5
      · omega
  have hR : ∀ hL, L.R G hL → L.R (upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' })) hL := by
    intro hL hR
    show R (fun u => (upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' }) u).2) hL
    refine (R_cnt (Y := fun u => (G u).2) ?_ ?_ hL).mpr hR <;>
    · show (upd (upd G c (gT .lk)) 0 _ _).2.cnt = (G _).2.cnt
      rw [upd_ne _ _ (by decide)]
      unfold upd; split
      · rename_i e; subst e; rw [hGk]; rfl
      · rfl
  have hL := hi.1.fork (t := 0) (g₁ := gM Heap.empty { ph := p' }) (g₀ := gT .lk)
    (by rw [hg]; rfl) hf (by rw [hg]; rfl) (fun _ => .inl rfl) rfl rfl rfl rfl hR
  subst hm'
  have hth : ∀ u, u ≠ 0 → u ≠ c → upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' }) u = G u :=
    fun u h0 hc => by rw [upd_ne _ _ h0, upd_ne _ _ hc]
  have hX0 : (upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' }) 0).2 = { ph := p' } := by
    rw [upd_self]; rfl
  have hXc : (upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' }) c).2 = { ph := .lk } := by
    rw [upd_ne _ _ (Ne.symm hk0), upd_self]; rfl
  have hG0 : (G 0).2 = { ph := p } := by rw [hg]; rfl
  obtain ⟨hcl, hcn, -⟩ := Lock.fork_clocks (cs := m.clocks) (t := 0)
    (by rw [hcs]; rcases hk12 with rfl | rfl <;> decide)
  have hcl' : ∀ u : Nat, VClock.le (m.clocks[u]!) (((m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).push
      (VClock.bump (m.clocks[0]!) 0))[u]!) = true := fun u => by
    by_cases hu' : u < m.clocks.size
    · exact hcl u hu'
    · rw [getElem!_neg m.clocks u hu']; exact nil_le _
  have hXeq : ∀ u, XEq (G u).2 (upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' }) u).2 := by
    intro u
    by_cases h0 : u = 0
    · subst h0; rw [hX0, hG0]
      rcases hk with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · by_cases hc : u = c
      · subst hc; rw [hXc, hGk]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [hth u h0 hc]; exact XEq.refl _
  refine ⟨rfl, hL, ?_⟩
  obtain ⟨h00, -, h3, d⟩ := hu.shape
  generalize hG' : upd (upd G c (gT .lk)) 0 (gM Heap.empty { ph := p' }) = G' at hX0 hXc hth hXeq ⊢
  have hcne : ∀ u : ThreadId, 3 ≤ u → u ≠ c := fun u hu' e => by
    subst e; rcases hk12 with rfl | rfl <;> exact absurd hu' (by decide)
  have h3ne : ∀ u : ThreadId, 3 ≤ u → u ≠ 0 := fun u hu' =>
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu')
  have hsh' : Shape (fun u => (G' u).2)
      { m with
        current := 0
        clocks := (m.clocks.set! 0 (VClock.bump (m.clocks[0]!) 0)).push (VClock.bump (m.clocks[0]!) 0)
        threads := m.threads.push { spawner := 0, joined := false } } := by
    refine ⟨by simp only [Array.getElem?_push]; rw [if_neg (by omega)]; exact h00, ?_,
      fun u hu' => by show (G' u).2 = {}; rw [hth u (h3ne u hu') (hcne u hu')]; exact h3 u hu', ?_⟩
    · show (G' 0).2.ph.isMain = true; rw [hX0]; rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    · rcases hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rcases d with ⟨-, -, -, d4⟩ | ⟨d1, -⟩ | ⟨d1, -⟩
        · refine .inr (.inl ⟨by simp [hsz], by show (G' 0).2.ph = _; rw [hX0],
            by simp only [Array.getElem?_push, hsz, ↓reduceIte],
            by show (G' 1).2.ph.isTask = true; rw [hXc]; rfl,
            by show (G' 2).2 = _; rw [hth 2 (by decide) (by decide)]; exact d4⟩)
        · omega
        · omega
      · rcases d with ⟨d1, -⟩ | ⟨-, -, d3, d4, -⟩ | ⟨d1, -⟩
        · omega
        · refine .inr (.inr ⟨by simp [hsz], by show 3 ≤ (G' 0).2.ph.rank; rw [hX0]; decide,
            by show (G' 1).2.ph.isTask = true; rw [hth 1 (by decide) (by decide)]; exact d4,
            by show (G' 2).2.ph.isTask = true; rw [hXc]; rfl, ?_,
            by simp only [Array.getElem?_push, hsz, ↓reduceIte]⟩)
          simp only [Array.getElem?_push]; rw [if_neg (by omega), d3]; simp [hG0, hX0]
        · omega
  refine ⟨hsh', fun u hu' => ?_, fun x => ?_, fun u h3' => ?_,
    blk_keep hu.blk rfl, fun w hw => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_,
    fun hr => ?_, fun hr => ?_⟩
  · rw [← hG']; unfold upd; split
    · rename_i e; exact absurd e hu'
    · split
      · rfl
      · exact hu.parts u hu'
  · rw [← hG', upd_self]; rfl
  · rw [hth u (h3ne u h3') (hcne u h3')]; exact hu.out3 u h3'
  · rcases hu.q w hw with h | ⟨-, -, c', -⟩
    · exact .inl h
    · rw [hG0] at c'; rcases hk with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> cases c'
  · by_cases h0 : u = 0
    · subst h0; rw [← hG', upd_self]
      rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [gM, X.frozen, X.fd, Ph.isTask]
    · by_cases hc : u = c
      · subst hc; rw [← hG', upd_ne _ _ (Ne.symm hk0), upd_self]; simp [gT, X.frozen, X.fd, Ph.isTask]
      · rw [hth u h0 hc]; exact hu.sx1 u
  · by_cases h0 : u = 0
    · subst h0; rw [← hG', upd_self]
      rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [gM, X.frozen, X.fd, Ph.isTask]
    · by_cases hc : u = c
      · subst hc; rw [← hG', upd_ne _ _ (Ne.symm hk0), upd_self]; simp [gT, X.frozen, X.fd, Ph.isTask]
      · rw [hth u h0 hc]; exact hu.wks u
  · by_cases h0 : u = 0
    · subst h0; rw [← hG', upd_self]
      rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [gM, X.frozen, X.fd, Ph.isTask]
    · by_cases hc : u = c
      · subst hc; rw [← hG', upd_ne _ _ (Ne.symm hk0), upd_self]; simp [gT, X.frozen, X.fd, Ph.isTask]
      · rw [hth u h0 hc]; exact hu.fzc u
  · by_cases h0 : u = 0
    · subst h0; rw [← hG', upd_self]
      rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [gM, X.frozen, X.fd, Ph.isTask]
    · by_cases hc : u = c
      · subst hc; rw [← hG', upd_ne _ _ (Ne.symm hk0), upd_self]
        simp [gT, X.frozen, X.fd, Ph.isTask, Ph.rank]
      · rw [hth u h0 hc]; exact hu.lg u
  · have hp := hu.pre (by rw [hG0]; rcases hk with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> decide)
    have hkG : WG.Keep m _ := Word.keep_fork (by rw [hsz]; rcases hk12 with rfl | rfl <;> decide)
      (by rw [hcs, hsz]) hf
    have hkE : EV.Keep m _ := Word.keep_fork (by rw [hsz]; rcases hk12 with rfl | rfl <;> decide)
      (by rw [hcs, hsz]) hf
    exact Pre.keep (t := 0) hp hXeq (hp.wg.keep hkG) (hp.ev.keep hkE) (Word.hist_keep hp.wg hkG)
      (Word.hist_keep hp.ev hkE) hcl' (by decide) (.inr fun e he => he) fun e he => .inl he
  · exfalso; rw [hX0] at hr; rcases hk with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [Ph.rank] at hr

/-- `main`'s place after its `add(1)`, which read `w`: `rd` if both tasks finished, else `ev0`. -/
def phA (w : Nat) : Ph := if w = 0 then .rd else .ev0

/-- `main`'s `add(1)` (acquire) at the group's state, which read `old` (at `run`). -/
theorem inv_add {G : ThreadId → Gh} {m₁ m' : Mem} {old : BitVec 64} (hi : proto.inv G m₁)
    (hg : G 0 = gM Heap.empty { ph := .run }) (hv : (last (WG.hist m₁)).Val old)
    (hh : WG.hist m' = (WG.hist m₁).push
      (Word.rmwEnt m' 0 .acquire (last (WG.hist m₁)) (RmwOp.add.apply false old 1)))
    (hacq : VClock.le (last (WG.hist m₁)).relClock (m'.clocks[0]!) = true)
    (hw' : WG.Ok m') (hop : WG.Op 0 m₁ m') (hL : L.Inv G m') :
    ∃ w, old = BitVec.ofNat 64 w ∧ (w = 0 ∨ w = 2 ∨ w = 4) ∧
      proto.inv (upd G 0 (gM Heap.empty { ph := phA w })) m' := by
  have hp := hi.2.pre (by rw [hg]; decide)
  have hgx : (G 0).2 = { ph := .run } := by rw [hg]; rfl
  have hfd : ∀ u, u = 1 ∨ u = 2 → ((G u).2.st || (G u).2.sx) = false := fun u hu => by
    cases e : ((G u).2.st || (G u).2.sx)
    · rfl
    · have := hp.swa u hu e; rw [hgx] at this; cases this
  obtain ⟨w, hw⟩ : ∃ w, wgv (G 0).2 (G 1).2 (G 2).2 = w := ⟨_, rfl⟩
  have hw024 : w = 0 ∨ w = 2 ∨ w = 4 := by
    rw [← hw]; unfold wgv; rw [hgx]
    simp only [X.isPre, X.wa, Ph.isMain, Ph.rank]
    cases (G 1).2.fd <;> cases (G 2).2.fd <;> simp
  have hold : old = BitVec.ofNat 64 w := val_eq hv (by rw [← hw]; exact hp.gv)
  subst hold
  refine ⟨w, rfl, hw024, ?_⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G 0 (gM Heap.empty { ph := phA w }) := ⟨_, rfl⟩
  rw [← hG']
  have hGu : ∀ u, u ≠ 0 → G' u = G u := fun u h => by rw [hG']; exact upd_ne _ _ h
  have hX0 : (G' 0).2 = { ph := phA w } := by rw [hG', upd_self]; rfl
  have hrk : (phA w).rank = 4 ∨ (phA w).rank = 7 := by unfold phA; split <;> simp [Ph.rank]
  have hL' : L.Inv G' m' := by
    rw [hG']; refine linv_task hL (by rw [hg]; rfl) ?_
    rw [hg]; unfold gM X.cnt phA; split <;> rfl
  -- `w = 0`: both tasks finished before, and did not set
  have hboth : w = 0 → ∀ u, u = 1 ∨ u = 2 → (G u).2.frozen ∧
      VClock.le (G u).2.fz (m'.clocks[0]!) = true := by
    intro h0 u hu
    subst h0
    have hf : (G u).2.fd := by
      have := hw; unfold wgv at this; rw [hgx] at this
      simp only [X.isPre, X.wa, Ph.isMain, Ph.rank] at this
      rcases hu with rfl | rfl <;> cases e1 : (G 1).2.fd <;> cases e2 : (G 2).2.fd <;>
        simp_all
    have hs := hfd u hu
    simp only [Bool.or_eq_false_iff] at hs
    have hfr : (G u).2.frozen := by
      unfold X.fd at hf; unfold X.st at hs; unfold X.frozen
      have hwk : (G u).2.ph ≠ .wk := fun e => by rw [hi.2.wks _ e] at hs; simp at hs
      cases e : (G u).2.ph <;> simp_all [Ph.isTask, Ph.rank]
    refine ⟨hfr, ?_⟩
    rw [hi.2.fzc _ hfr hs.2]
    exact VClock.le_trans (hp.gw u hu hf) hacq
  refine ⟨hL', ?_⟩
  rw [hG']
  have hsh := hi.2.shape
  refine U_main hi ?_ (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [WG] at h; omega)) (fun x => rfl)
    (fun w' hw' => ?_) (fun _ => ?_) (fun hr => ?_) ⟨rfl, by unfold phA; split <;> decide, by unfold gM X.frozen phA; split <;> rfl,
      by unfold gM X.fd phA; split <;> rfl⟩
  · obtain ⟨h00, -, h3, d⟩ := hsh
    rw [← hG']
    refine ⟨by rw [hop.threads]; exact h00, by show (G' 0).2.ph.isMain = true; rw [hX0]; unfold phA; split <;> rfl,
      fun u hu => by show (G' u).2 = {}; rw [hGu u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu))]; exact h3 u hu, ?_⟩
    rcases d with ⟨-, d2, -⟩ | ⟨-, d2, -⟩ | ⟨d1, d2, d3, d4, d5, d6⟩
    · exfalso; change (G 0).2.ph.rank ≤ 1 at d2; rw [hgx] at d2; simp [Ph.rank] at d2
    · exfalso; change (G 0).2.ph = .sp1 at d2; rw [hgx] at d2; cases d2
    · refine .inr (.inr ⟨by rw [hop.threads]; exact d1, by show 3 ≤ (G' 0).2.ph.rank; rw [hX0]; show 3 ≤ (phA w).rank; omega,
        by show (G' 1).2.ph.isTask = true; rw [hGu 1 (by decide)]; exact d3,
        by show (G' 2).2.ph.isTask = true; rw [hGu 2 (by decide)]; exact d4, ?_,
        by rw [hop.threads]; exact d6⟩)
      rw [hop.threads, d5]; simp [hgx, hX0, phA]; split <;> simp
  · rw [hop.waiters] at hw'
    rcases hi.2.q w' hw' with h | ⟨-, -, c', -⟩
    · exact .inl h
    · rw [hgx] at c'; cases c'
  · rw [← hG']
    have hkE := Word.keep_op hop (W' := EV) (.inr (.inl (by decide)))
    have hhE := Word.hist_keep hp.ev hkE
    have hX1 : (G' 1).2 = (G 1).2 := by rw [hGu 1 (by decide)]
    have hX2 : (G' 2).2 = (G 2).2 := by rw [hGu 2 (by decide)]
    have hrel : (last (WG.hist m')).relClock = (last (WG.hist m₁)).relClock := by
      rw [hh, last_push]; rfl
    refine ⟨hw', hp.ev.keep hkE, ?_, fun u hu hf => ?_, ?_, fun h => ?_, fun u v huv hu => ?_,
      fun u v huv hu => ?_, fun u hu hs => ?_, fun h0 h1 h2 => ?_, fun h => ?_,
      fun h => ?_, fun e he hb => ?_⟩
    · rw [hh, last_push, hX0, hX1, hX2]
      have : wgv { ph := phA w } (G 1).2 (G 2).2 = w + 1 := by
        have := hw; unfold wgv at this ⊢; rw [hgx] at this
        unfold phA
        cases e1 : (G 1).2.fd <;> cases e2 : (G 2).2.fd <;> split <;>
          simp_all [X.isPre, X.wa, Ph.isMain, Ph.rank] <;> omega
      rw [this]
      have e : RmwOp.add.apply false (BitVec.ofNat 64 w) 1 = BitVec.ofNat 64 (w + 1) := by
        rcases hw024 with rfl | rfl | rfl <;> rfl
      rw [e]; exact WG.enc_val _
    · rw [hrel]
      have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> decide
      rw [hGu u hu0] at hf ⊢; exact hp.gw u hu hf
    · unfold EVOk; rw [hhE, hX0, hX1, hX2]
      have := hp.evh; rw [hgx] at this; exact this
    · rw [hX1, hX2] at h; rw [hhE, hX1, hX2]; exact hp.setc h
    · have hu0 : u ≠ 0 := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      have hv0 : v ≠ 0 := by rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
      rw [hGu u hu0] at hu; rw [hGu v hv0, hop.others u hu0]; exact hp.sto u v huv hu
    · have hu0 : u ≠ 0 := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      rw [hGu u hu0, hfd u (by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)] at hu; cases hu
    · have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> decide
      rw [hGu u hu0, hfd u hu] at hs; cases hs
    · exfalso
      rw [hX0] at h0; rw [hX1] at h1; rw [hX2] at h2
      have hw0 : w ≠ 0 := by intro e; rw [e] at h0; simp [phA, X.e01] at h0
      have := hw; unfold wgv at this; rw [hgx] at this
      simp only [X.isPre, X.wa, Ph.isMain, Ph.rank, h1, h2] at this
      simp at this; omega
    · rw [hX0] at h; simp [phA, X.isEv1] at h; split at h <;> cases h
    · rw [hX0] at h; cases h
    · rcases hop.fpt e he with h' | ⟨het, hle⟩
      · obtain ⟨a, b⟩ := hp.attr e h' hb
        refine ⟨a, VClock.le_trans b ?_⟩
        unfold ac
        by_cases h0 : e.tid = 0
        · have hfz0 : ({ ph := phA w } : X).frozen = false := by unfold X.frozen phA; split <;> rfl
          rw [h0, hX0, hgx, hfz0]; exact hop.clocks 0
        · rw [hGu _ h0]; split
          · exact VClock.le_refl _
          · exact hop.clocks _
      · refine ⟨by rw [het]; decide, ?_⟩
        have hfz0 : ({ ph := phA w } : X).frozen = false := by unfold X.frozen phA; split <;> rfl
        unfold ac; rw [het, hX0, hfz0]; exact hle
  · rw [upd_self] at hr; show _ ∧ _ ∧ _ ∧ _
    have h0 : w = 0 := by
      by_cases h : w = 0
      · exact h
      · have : (phA w).rank = 4 := by simp [phA, h, Ph.rank]
        rw [show (gM Heap.empty { ph := phA w }).2.ph = phA w from rfl, this] at hr; omega
    obtain ⟨a1, b1⟩ := hboth h0 1 (.inl rfl)
    obtain ⟨a2, b2⟩ := hboth h0 2 (.inr rfl)
    exact ⟨a1, a2, b1, b2⟩

/-! ## `main` at the event -/

/-- A running `main` (`out` for the lock) is not in the futex queue: the queue keeps `QOk` for
each ghost value. -/
theorem qok_run {G : ThreadId → Gh} {m m' : Mem} (hi : proto.inv G m) (h0 : L.ph (G 0) = .out)
    (hw : m'.waiters = m.waiters) (G' : ThreadId → Gh) : QOk G' m' := by
  intro w hw'
  rw [hw] at hw'
  rcases hi.2.q w hw' with h | ⟨h1, h2, -⟩
  · exact .inl h
  · exfalso
    rcases hi.1.fq w hw' with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h2] at h; exact absurd h (by decide)
    · rw [h1, h0] at h; cases h

/-- `main`'s ghost value: no task flags. -/
theorem main_x {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) :
    (G 0).2.sx = false ∧ (G 0).2.ph ≠ .wk ∧ (G 0).2.frozen = false ∧ (G 0).2.fd = false := by
  have hm : (G 0).2.ph.isMain = true := hi.2.shape.2.1
  have hs := hi.2.sx1 0
  unfold X.frozen X.fd
  cases e : (G 0).2.ph <;> rw [e] at hm hs <;> simp_all [Ph.isMain, Ph.isTask]

/-- `Pre` after a step of `main` to the ghost value `g`, with the same writes: `g` agrees on what
`Pre` reads, except `main`'s place in the event's `wait`. -/
theorem Pre.mx {G : ThreadId → Gh} {m m' : Mem} {g : Gh} (hp : Pre G m)
    (hpre : g.2.isPre = (G 0).2.isPre) (hwa : g.2.wa = (G 0).2.wa) (he1 : g.2.e1 = (G 0).2.e1)
    (hf0 : (G 0).2.frozen = false) (hf : g.2.frozen = false)
    (hwg : WG.Ok m') (hev : EV.Ok m') (hhg : WG.hist m' = WG.hist m) (hhe : EV.hist m' = EV.hist m)
    (hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true)
    (hfp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
      (e.tid = 0 ∧ VClock.le e.clock (m'.clocks[0]!) = true))
    (hlast3 : g.2.e01 → (G 1).2.fd → (G 2).2.fd →
      ((G 1).2.st || (G 1).2.sx || (G 2).2.st || (G 2).2.sx) = true)
    (hm1e : g.2.isEv1 → g.2.e1) : Pre (upd G 0 g) m' := by
  have hX : ∀ u, u ≠ 0 → (upd G 0 g u).2 = (G u).2 := fun u h => by rw [upd_ne _ _ h]
  have h0 : (upd G 0 g 0).2 = g.2 := by rw [upd_self]
  have h1 := hX 1 (by decide)
  have h2 := hX 2 (by decide)
  have hwgv : wgv (upd G 0 g 0).2 (upd G 0 g 1).2 (upd G 0 g 2).2 =
      wgv (G 0).2 (G 1).2 (G 2).2 := by
    unfold wgv; rw [h0, h1, h2, hpre, hwa]
  have hevL : evL (upd G 0 g 0).2 (upd G 0 g 1).2 (upd G 0 g 2).2 =
      evL (G 0).2 (G 1).2 (G 2).2 := by
    unfold evL; rw [h0, h1, h2, he1]
  have hac : ∀ u, VClock.le (ac G m u) (ac (upd G 0 g) m' u) = true := fun u => by
    by_cases hu : u = 0
    · subst hu; unfold ac; rw [h0, hf, hf0]; exact hcl 0
    · unfold ac; rw [hX u hu]; split
      · exact VClock.le_refl _
      · exact hcl u
  have hu12 : ∀ u : ThreadId, u = 1 ∨ u = 2 → u ≠ 0 := fun u h => by
    rcases h with rfl | rfl <;> decide
  have hpair : ∀ u v, Pair u v → u ≠ 0 ∧ v ≠ 0 := fun u v h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by decide⟩
  refine ⟨hwg, hev, by rw [hhg, hwgv]; exact hp.gv, fun u hu hf' => ?_,
    by unfold EVOk; rw [hhe, hevL]; exact hp.evh, fun h => ?_, fun u v huv hu => ?_,
    fun u v huv hu => ?_, fun u hu hs => ?_, fun h0' h1' h2' => ?_, fun h => ?_,
    fun h => ?_, fun e he hb => ?_⟩
  · rw [hX u (hu12 u hu)] at hf' ⊢; rw [hhg]; exact hp.gw u hu hf'
  · rw [h1, h2] at h ⊢; rw [hhe]; exact hp.setc h
  · obtain ⟨hu0, hv0⟩ := hpair u v huv
    rw [hX u hu0] at hu; rw [hX v hv0]
    obtain ⟨a, b⟩ := hp.sto u v huv hu
    exact ⟨a, VClock.le_trans b (hcl u)⟩
  · obtain ⟨hu0, hv0⟩ := hpair u v huv
    rw [hX u hu0] at hu; rw [hX v hv0]; exact hp.sfd u v huv hu
  · rw [hX u (hu12 u hu)] at hs; rw [h0, hwa]; exact hp.swa u hu hs
  · rw [h0] at h0'; rw [h1] at h1'; rw [h2] at h2'; rw [h1, h2]; exact hlast3 h0' h1' h2'
  · rw [h0] at h ⊢; exact hm1e h
  · rw [h0, he1] at h; rw [hhe]; exact VClock.le_trans (hp.e1c h) (hcl 0)
  · rcases hfp e he with h' | ⟨het, hle⟩
    · obtain ⟨a, b⟩ := hp.attr e h' hb
      exact ⟨a, VClock.le_trans b (hac _)⟩
    · refine ⟨by rw [het]; decide, ?_⟩
      unfold ac; rw [het, h0, hf]; exact hle

/-- After the set, both tasks are frozen, below the set's release clock. -/
theorem set_done {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (hp : Pre G m)
    (hs : ((G 1).2.sx || (G 2).2.sx) = true) :
    (G 1).2.frozen ∧ (G 2).2.frozen ∧
      VClock.le (G 1).2.fz (last (EV.hist m)).relClock = true ∧
      VClock.le (G 2).2.fz (last (EV.hist m)).relClock = true := by
  have hfr : ∀ u, (G u).2.sx → (G u).2.frozen := fun u h => by
    unfold X.frozen
    rcases hi.2.sx1 u h with e | e | e <;> rw [e] <;> rfl
  have hoth : ∀ u v, Pair u v → (G u).2.sx → (G v).2.frozen := fun u v huv h => by
    obtain ⟨hfd, hsx, hst⟩ := hp.sfd u v huv (by simp [h])
    have hwk : (G v).2.ph ≠ .wk := fun e => by rw [hi.2.wks v e] at hsx; cases hsx
    unfold X.fd at hfd; unfold X.st at hst; unfold X.frozen
    cases e : (G v).2.ph <;> simp_all [Ph.isTask, Ph.rank]
  obtain ⟨c1, c2⟩ := hp.setc hs
  refine ⟨?_, ?_, c1, c2⟩
  · cases e1 : (G 1).2.sx
    · rw [e1] at hs; simp at hs; exact hoth 2 1 (.inr ⟨rfl, rfl⟩) hs
    · exact hfr 1 e1
  · cases e2 : (G 2).2.sx
    · rw [e2] at hs; simp at hs; exact hoth 1 2 (.inl ⟨rfl, rfl⟩) hs
    · exact hfr 2 e2

/-- The value `2` is only the set, the last of the event's writes. -/
theorem evL_two (x0 x1 x2 : X) (j : Nat) (hj : j < (evL x0 x1 x2).length)
    (h : BitVec.ofNat 32 2 = BitVec.ofNat 32 (evL x0 x1 x2)[j]) :
    (x1.sx || x2.sx) = true ∧ j + 1 = (evL x0 x1 x2).length := by
  unfold evL at *
  cases e0 : x0.e1 <;> cases es : (x1.sx || x2.sx) <;> simp only [e0, es] at hj h ⊢ <;>
    rcases j with _ | _ | _ | j <;> simp_all
  all_goals omega

/-- A write of `2` at the event is the set, its newest write. -/
theorem ev2_last {G : ThreadId → Gh} {m : Mem} (hp : Pre G m) {j : Nat}
    (hj : j < (EV.hist m).size) (hv : (EV.hist m)[j]!.Val (BitVec.ofNat 32 2)) :
    ((G 1).2.sx || (G 2).2.sx) = true ∧ (EV.hist m)[j]! = last (EV.hist m) := by
  obtain ⟨hj', h2⟩ := ev_val hp.evh hj hv
  obtain ⟨hs, hl⟩ := evL_two _ _ _ j hj' h2
  refine ⟨hs, ?_⟩
  unfold last; rw [hp.evh.1, show (evL (G 0).2 (G 1).2 (G 2).2).length - 1 = j by omega]

/-- The threads after a step of `main` that keeps it at rank 3 or more (and not at `j1`). -/
theorem shape_m {Y : ThreadId → X} {m m' : Mem} {x : X} (h : Shape Y m)
    (ht : m'.threads = m.threads) (h3 : 3 ≤ (Y 0).ph.rank) (hj : (Y 0).ph ≠ .j1)
    (hm : x.ph.isMain) (h3' : 3 ≤ x.ph.rank) (hj' : x.ph ≠ .j1) : Shape (upd Y 0 x) m' := by
  obtain ⟨a, -, c, d⟩ := h
  rcases d with ⟨-, d2, -⟩ | ⟨-, d2, -⟩ | ⟨d1, -, d3, d4, d5, d6⟩
  · omega
  · rw [d2] at h3; simp [Ph.rank] at h3
  · refine ⟨by rw [ht]; exact a, by rw [upd_self]; exact hm,
      fun u hu => by rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu))]; exact c u hu,
      .inr (.inr ⟨by rw [ht]; exact d1, by rw [upd_self]; exact h3',
        by rw [upd_ne _ _ (by decide)]; exact d3, by rw [upd_ne _ _ (by decide)]; exact d4, ?_,
        by rw [ht]; exact d6⟩)⟩
    rw [ht, d5, upd_self]; simp [hj, hj']

/-- A value other than `2` at the event, at or after `main`'s write of `1` if there is one. -/
theorem evL_low (x0 x1 x2 : X) (j : Nat) (hj : j < (evL x0 x1 x2).length) {b : BitVec 32}
    (hb : b = BitVec.ofNat 32 (evL x0 x1 x2)[j]) (h1 : x0.e1 → 1 ≤ j) (h : b ≠ 2) :
    b = if x0.e1 then 1 else 0 := by
  subst hb
  revert h1 hj
  unfold evL
  cases x0.e1 <;> cases (x1.sx || x2.sx) <;> intro hj h1 h <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.nil_append, List.cons_append,
      List.length_cons, List.length_nil, forall_const] at hj h1 h ⊢ <;>
    rcases j with _ | _ | _ | j <;> simp_all
  all_goals omega

/-- `main` in the event's `wait`: `ev0` before its write of `1`, `ev1` after it. -/
def EvX (x : X) : Prop := x = { ph := .ev0 } ∨ x = { ph := .ev1, e1 := true }

/-- A step of `main` (part `h`, from `x` to `x'`) at the event that keeps the writes: an atomic
read, or a `cmpxchg` that failed. -/
theorem inv_mx {G : ThreadId → Gh} {m₁ m' : Mem} {h : Heap} {x x' : X}
    (hi : proto.inv G m₁) (hg : G 0 = gM h x) (h3 : 3 ≤ x.ph.rank) (hr : x.ph.rank ≤ 7)
    (hj1 : x.ph ≠ .j1) (hm' : x'.ph.isMain) (h3' : 3 ≤ x'.ph.rank) (hj1' : x'.ph ≠ .j1)
    (hpre : x'.isPre = x.isPre) (hwa : x'.wa = x.wa) (he1 : x'.e1 = x.e1)
    (hx' : x'.sx = false ∧ x'.ph ≠ .wk ∧ x'.frozen = false ∧ x'.fd = false)
    (hlast3 : x'.e01 → (G 1).2.fd → (G 2).2.fd →
      ((G 1).2.st || (G 1).2.sx || (G 2).2.st || (G 2).2.sx) = true)
    (hm1e : x'.isEv1 → x'.e1)
    (hdone : 6 ≤ x'.ph.rank → (G 1).2.frozen ∧ (G 2).2.frozen ∧
      VClock.le (G 1).2.fz (m'.clocks[0]!) = true ∧ VClock.le (G 2).2.fz (m'.clocks[0]!) = true)
    (hw' : EV.Ok m') (hop : EV.Op 0 m₁ m') (hh : EV.hist m' = EV.hist m₁) (hL : L.Inv G m') :
    proto.inv (upd G 0 (gM h x')) m' := by
  have hgx : (G 0).2 = x := by rw [hg]; rfl
  have hp := hi.2.pre (by rw [hgx]; exact hr)
  have hkG := Word.keep_op hop (W' := WG) (.inr (.inr (by decide)))
  refine ⟨linv_task hL (by rw [hg]; rfl) ?_, ?_⟩
  · rw [hg]; unfold gM X.cnt
    have hm := hi.2.shape.2.1; change (G 0).2.ph.isMain = true at hm; rw [hgx] at hm
    have nt : ∀ y : Ph, y.isMain = true → y.isTask = false := fun y hy => by cases y <;> simp_all [Ph.isMain, Ph.isTask]
    simp [nt _ hm, nt _ hm']
  refine U_main hi (by
      rw [show (fun u => (upd G 0 (gM h x') u).2) = upd (fun u => (G u).2) 0 x' by
        funext u; unfold upd; split <;> rfl]
      exact shape_m hi.2.shape hop.threads (by rw [hgx]; exact h3) (by rw [hgx]; exact hj1) hm' h3' hj1')
    (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [EV] at h; omega))
    (fun y => by have := hi.2.part0 y; rw [hg] at this; exact this)
    (qok_run hi (by rw [hg]; rfl) hop.waiters _) (fun _ => ?_) (fun hr' => ?_) hx'
  · have hf0 := (main_x hi).2.2.1
    refine Pre.mx hp (by rw [hgx]; exact hpre) (by rw [hgx]; exact hwa) (by rw [hgx]; exact he1) hf0
      hx'.2.2.1 (hp.wg.keep hkG) hw' (Word.hist_keep hp.wg hkG) hh hop.clocks hop.fpt hlast3 hm1e
  · rw [upd_self] at hr'; exact hdone hr'

/-- `main`'s read of the event (a load, or a `cmpxchg` that failed) at `ev0`/`ev1`, of write `j`
with the value `b`: `2` (the set) ends the wait at `rd`; else `b` is `main`'s own value. -/
theorem inv_mread {G : ThreadId → Gh} {m₁ m' : Mem} {h : Heap} {x : X} {j : Nat} {b : BitVec 32}
    (hi : proto.inv G m₁) (hg : G 0 = gM h x) (hx : EvX x)
    (hj : j < (EV.hist m₁).size) (hv : (EV.hist m₁)[j]!.Val b)
    (hfl : Word.Floor (EV.hist m₁) (m₁.clocks[0]!) j)
    (hacq : VClock.le (EV.hist m₁)[j]!.relClock (m'.clocks[0]!) = true)
    (hh : EV.hist m' = EV.hist m₁) (hw' : EV.Ok m') (hop : EV.Op 0 m₁ m') (hL : L.Inv G m') :
    (b = 2 ∧ proto.inv (upd G 0 (gM h { ph := .rd, e1 := x.e1 })) m') ∨
    (b = (if x.e1 then 1 else 0) ∧ proto.inv G m') := by
  have hgx : (G 0).2 = x := by rw [hg]; rfl
  have hr : x.ph.rank ≤ 7 := by rcases hx with rfl | rfl <;> decide
  have hp := hi.2.pre (by rw [hgx]; exact hr)
  have h3 : 3 ≤ x.ph.rank := by rcases hx with rfl | rfl <;> decide
  have hj1 : x.ph ≠ .j1 := by rcases hx with rfl | rfl <;> decide
  obtain ⟨hj', hb⟩ := ev_val hp.evh hj hv
  by_cases h2 : b = 2
  · subst h2
    left; refine ⟨rfl, ?_⟩
    obtain ⟨hs, hl⟩ := ev2_last hp hj hv
    obtain ⟨f1, f2, c1, c2⟩ := set_done hi hp hs
    rw [← hl] at c1 c2
    refine inv_mx hi hg h3 hr hj1 rfl (by show 3 ≤ Ph.rd.rank; decide) (by show Ph.rd ≠ .j1; decide)
      ?_ ?_ rfl ⟨rfl, by show Ph.rd ≠ .wk; decide, rfl, rfl⟩
      (fun h => by cases h) (fun h => by cases h)
      (fun _ => ⟨f1, f2, VClock.le_trans c1 hacq, VClock.le_trans c2 hacq⟩) hw' hop hh hL
    · rcases hx with rfl | rfl <;> rfl
    · rcases hx with rfl | rfl <;> rfl
  · right
    have h1 : (G 0).2.e1 → 1 ≤ j := fun he => by
      have hs1 : 1 < (EV.hist m₁).size := by
        rw [hp.evh.1]; unfold evL; simp [he]
      exact hfl 1 hs1 (hp.e1c he)
    have := evL_low _ _ _ j hj' hb h1 h2
    rw [hgx] at this
    refine ⟨this, ?_⟩
    have e : upd G 0 (gM h x) = G := upd_g hg
    rw [← e]
    exact inv_mx hi hg h3 hr hj1 (by rcases hx with rfl | rfl <;> rfl) h3 hj1 rfl rfl rfl
      (by rcases hx with rfl | rfl <;> exact ⟨rfl, by decide, rfl, rfl⟩)
      (fun h0 h1 h2 => by have := hp.last3; rw [hgx] at this; exact this h0 h1 h2)
      (fun h => by have := hp.m1e; rw [hgx] at this; exact this h)
      (fun h6 => by rcases hx with rfl | rfl <;> simp [Ph.rank] at h6) hw' hop hh hL

/-- `main`'s `cmpxchg(0 → 1)` (acquire) at `ev0` succeeded: it wrote `1`, and goes to `ev1`. -/
theorem inv_mev1 {G : ThreadId → Gh} {m₁ m' : Mem} {h : Heap}
    (hi : proto.inv G m₁) (hg : G 0 = gM h { ph := .ev0 })
    (hv : (last (EV.hist m₁)).Val (0 : BitVec 32))
    (hh : EV.hist m' = (EV.hist m₁).push
      (Word.rmwEnt m' 0 .acquire (last (EV.hist m₁)) (1 : BitVec 32)))
    (hw' : EV.Ok m') (hop : EV.Op 0 m₁ m') (hL : L.Inv G m') :
    proto.inv (upd G 0 (gM h { ph := .ev1, e1 := true })) m' := by
  have hgx : (G 0).2 = { ph := .ev0 } := by rw [hg]; rfl
  have hp := hi.2.pre (by rw [hgx]; decide)
  -- no set yet: the newest write is `0`
  have hsx : ((G 1).2.sx || (G 2).2.sx) = false := by
    cases e : ((G 1).2.sx || (G 2).2.sx)
    · rfl
    · exfalso
      have := ev_lastOf hp.evh (l := [0]) (x := 2) (by unfold evL; rw [hgx, e]; rfl)
      have := val_eq hv this
      revert this; decide
  have hs1 : (EV.hist m₁).size = 1 := by
    rw [hp.evh.1]; unfold evL; rw [hgx, hsx]; rfl
  have hkG := Word.keep_op hop (W' := WG) (.inr (.inr (by decide)))
  have hhG := Word.hist_keep hp.wg hkG
  obtain ⟨G', hG'⟩ : ∃ G', G' = upd G 0 (gM h { ph := .ev1, e1 := true }) := ⟨_, rfl⟩
  rw [← hG']
  have hGu : ∀ u, u ≠ 0 → G' u = G u := fun u hu => by rw [hG']; exact upd_ne _ _ hu
  have hX0 : (G' 0).2 = { ph := .ev1, e1 := true } := by rw [hG', upd_self]; rfl
  have hX1 : (G' 1).2 = (G 1).2 := by rw [hGu 1 (by decide)]
  have hX2 : (G' 2).2 = (G 2).2 := by rw [hGu 2 (by decide)]
  refine ⟨by rw [hG']; exact linv_task hL (by rw [hg]; rfl) (by rw [hg]; rfl), ?_⟩
  rw [hG']
  refine U_main hi (by
      rw [show (fun u => (upd G 0 (gM h { ph := .ev1, e1 := true }) u).2) =
        upd (fun u => (G u).2) 0 { ph := .ev1, e1 := true } by funext u; unfold upd; split <;> rfl]
      exact shape_m hi.2.shape hop.threads (by rw [hgx]; decide) (by rw [hgx]; decide) rfl
        (by decide) (by decide))
    (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [EV] at h; omega))
    (fun y => by have := hi.2.part0 y; rw [hg] at this; exact this)
    (qok_run hi (by rw [hg]; rfl) hop.waiters _) (fun _ => ?_)
    (fun hr => by rw [upd_self] at hr; exact absurd hr (by show ¬6 ≤ Ph.ev1.rank; decide))
    ⟨rfl, by show Ph.ev1 ≠ .wk; decide, rfl, rfl⟩
  rw [← hG']
  refine ⟨hp.wg.keep hkG, hw', ?_, fun u hu hf => ?_, ?_, fun h => ?_, fun u v huv hu => ?_,
    fun u v huv hu => ?_, fun u hu hs => ?_, fun h0 h1 h2 => ?_, fun _ => ?_, fun _ => ?_,
    fun e he hb => ?_⟩
  · rw [hhG, hX0, hX1, hX2]
    have := hp.gv; rw [hgx] at this
    have e : wgv { ph := .ev1, e1 := true } (G 1).2 (G 2).2 = wgv { ph := .ev0 } (G 1).2 (G 2).2 :=
      rfl
    rw [e]; exact this
  · have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> decide
    rw [hGu u hu0] at hf ⊢; rw [hhG]; exact hp.gw u hu hf
  · have e : evL (G' 0).2 (G' 1).2 (G' 2).2 = [0, 1] := by
      unfold evL; rw [hX0, hX1, hX2, hsx]; rfl
    rw [e]
    refine ⟨by rw [hh, Array.size_push, hs1]; rfl, fun j hj => ?_⟩
    rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [hh, push_get_lt (by rw [hs1]; decide)]
      have := hp.evh.2 0 (by rw [show evL (G 0).2 (G 1).2 (G 2).2 = [0] by
        unfold evL; rw [hgx, hsx]; rfl]; decide)
      simpa [evL, hgx, hsx] using this
    · have e : (EV.hist m')[1]! = Word.rmwEnt m' 0 .acquire (last (EV.hist m₁)) (1 : BitVec 32) := by
        rw [hh, show (1 : Nat) = (EV.hist m₁).size from hs1.symm, push_get_eq]
      rw [e]; exact EV.enc_val _
  · rw [hX1, hX2, hsx] at h; cases h
  · have hu0 : u ≠ 0 := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
    have hv0 : v ≠ 0 := by rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
    rw [hGu u hu0] at hu; rw [hGu v hv0, hop.others u hu0]; exact hp.sto u v huv hu
  · have hu0 : u ≠ 0 := by rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
    have hv0 : v ≠ 0 := by rcases huv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
    rw [hGu u hu0] at hu; rw [hGu v hv0]; exact hp.sfd u v huv hu
  · have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> decide
    rw [hGu u hu0] at hs; rw [hX0]; rfl
  · rw [hX1] at h1; rw [hX2] at h2; rw [hX1, hX2]
    exact hp.last3 (by rw [hgx]; rfl) h1 h2
  · rw [hX0]
  · have e : (EV.hist m')[1]! = Word.rmwEnt m' 0 .acquire (last (EV.hist m₁)) (1 : BitVec 32) := by
      rw [hh, show (1 : Nat) = (EV.hist m₁).size from hs1.symm, push_get_eq]
    rw [e]; exact VClock.le_refl _
  · rcases hop.fpt e he with h' | ⟨het, hle⟩
    · obtain ⟨a, b⟩ := hp.attr e h' hb
      refine ⟨a, VClock.le_trans b ?_⟩
      unfold ac
      by_cases h0 : e.tid = 0
      · rw [h0, hX0, hgx]; exact hop.clocks 0
      · rw [hGu _ h0]; split
        · exact VClock.le_refl _
        · exact hop.clocks _
    · refine ⟨by rw [het]; decide, ?_⟩
      unfold ac; rw [het, hX0]; exact hle

/-! ## `main`'s own part: the deadline -/

/-- A step of `main` (at `gM h x0`) on its own part `h`, which is `hQ` after it. -/
theorem inv_mown {G : ThreadId → Gh} {m m' : Mem} {x0 : X} {h hQ : Heap}
    (hi : proto.inv (upd G 0 (gM h x0)) m) (hc : m.current = 0)
    (ho' : Owned (upd (L.own (upd G 0 (gM h x0)) m) 0 hQ) m')
    (hs : StepIn (m.heap.diff (L.own (upd G 0 (gM h x0)) m 0)) m m')
    (hm' : m'.heap = hQ ∪ m.heap.diff (L.own (upd G 0 (gM h x0)) m 0))
    (hd : Heap.Disjoint hQ (m.heap.diff (L.own (upd G 0 (gM h x0)) m 0)))
    (hb0 : ∀ y, hQ (0, y) = none) :
    proto.inv (upd G 0 (gM hQ x0)) m' := by
  have hph : L.ph (upd G 0 (gM h x0) 0) = .out := by rw [upd_self]; rfl
  obtain ⟨-, hjt⟩ := hi.1.live 0 (by rw [hph]; decide)
  have hQe : L.part (gM hQ x0) ∪ L.held (gM hQ x0) = hQ := Heap.union_empty hQ
  have hl := hi.1.stepIn (g := gM hQ x0) hc hjt (by rw [hQe]; exact ho') hs
    (by rw [hQe]; exact hm') (by rw [hQe]; exact hd) (by rw [upd_self]; rfl)
    (Heap.disjoint_empty _) (fun _ => rfl)
    (fun _ hL hR => by
      show R (fun u => (upd (upd G 0 (gM h x0)) 0 (gM hQ x0) u).2) hL
      rw [snd_upd_upd G 0 (gM h x0) (gM hQ x0) rfl]; exact hR)
    (fun h' => absurd h' (by show ¬(LPh.out = LPh.holds); decide))
  rw [upd_upd] at hl
  refine ⟨hl, ?_⟩
  obtain ⟨hsx, hwk, hfz, hfd⟩ := main_x hi
  rw [upd_self] at hsx hwk hfz hfd
  change x0.sx = false at hsx; change x0.ph ≠ .wk at hwk
  change x0.frozen = false at hfz; change x0.fd = false at hfd
  have hU := U_stepIn (g := gM hQ x0) hi hs hm' hd hc (by decide)
    (by rw [upd_self]; exact XEq.refl _) hfz
    (by
      rw [show (gM hQ x0).2 = (fun u => (upd G 0 (gM h x0) u).2) 0 by
        show x0 = (upd G 0 (gM h x0) 0).2; rw [upd_self]; rfl, upd_same]
      exact hi.2.shape)
    (fun h0 => absurd rfl h0) (fun _ => hb0) (qok_run hi hph hs.waiters _)
    (fun h' => by change x0.sx = true at h'; rw [hsx] at h'; cases h')
    (fun h' => absurd h' hwk) (fun h' => by change x0.fd = true at h'; rw [hfd] at h'; cases h')
    (fun hr => by
      rw [upd_self] at hr
      have h1 : upd (upd G 0 (gM h x0)) 0 (gM hQ x0) 1 = upd G 0 (gM h x0) 1 :=
        upd_ne _ _ (by decide)
      have h2 : upd (upd G 0 (gM h x0)) 0 (gM hQ x0) 2 = upd G 0 (gM h x0) 2 :=
        upd_ne _ _ (by decide)
      rw [h1, h2]
      obtain ⟨a, b, c, d⟩ := hi.2.done (by rw [upd_self]; exact hr)
      exact ⟨a, b, VClock.le_trans c (hs.clock 0), VClock.le_trans d (hs.clock 0)⟩)
    (fun hr => by rw [upd_self] at hr; rw [upd_self]; exact hr)
  rwa [upd_upd] at hU

/-- A step of `main` on its own part `h` (`TTriple Pa x Qa`), in `CM`. -/
theorem wp_mownM {α σ : Type} {x : MemM α} {s : σ} {G : ThreadId → Gh} {m : Mem} {d : Nat}
    {x0 : X} {h : Heap} {Pa : Assn} {Qa : α → Assn} (ht : TTriple Pa x Qa)
    (hi : proto.inv (upd G 0 (gM h x0)) m) (hc : m.current = 0) (hp : Pa h)
    (hb0 : ∀ a hQ, Qa a hQ → ∀ y, hQ (0, y) = none)
    {Q : α × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ a m' hQ, (x.run m).run = some (.ok (a, m')) → m'.current = 0 →
      m'.threads = m.threads → Qa a hQ → proto.inv (upd G 0 (gM hQ x0)) m' → Q (a, s) G m' d) :
    proto.WP 0 ((liftM x : CM Tgt σ α).run s) Q G m d := by
  have hph : L.ph (upd G 0 (gM h x0) 0) = .out := by rw [upd_self]; rfl
  obtain ⟨ht0, hjt⟩ := hi.1.live 0 (by rw [hph]; decide)
  have hown : L.own (upd G 0 (gM h x0)) m 0 = h := by
    rw [L.own_live hjt, upd_self]; exact Heap.union_empty h
  refine WP.liftM_owned ht hi.1.own hc ht0 (by rw [hown]; exact hp)
    fun a m' hQ' hr ho' hq hs hm' hd => ?_
  exact hQ a m' hQ' hr (hs.current.trans hc) hs.threads hq
    (inv_mown hi hc ho' hs hm' hd (hb0 a hQ' hq))

/-! ## `main`'s futex wait at the event -/

/-- A thread that sleeps at a futex is not the last one: no thread waits at the mutex (`noWaits`),
so `main` sleeps at the event; a setter at `wk` goes on, and without a set a task did not end
(`last3`). -/
theorem live_all {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) (t : ThreadId) :
    proto.Live t G m := by
  intro hw hall
  obtain ⟨i, hi', -⟩ := Array.any_eq_true.mp hw
  have hwm := Array.getElem_mem hi'
  have hnoL := fits.noWaits hi.1 hall
  have hnot : ∀ w ∈ m.waiters, w.2 ≠ L.ptr := fun w hw' e =>
    hnoL (Array.any_eq_true.mpr (by
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hw'
      exact ⟨j, hj, by simp [e]⟩))
  have hmain : ∀ w ∈ m.waiters, w.1 = 0 := fun w hw' => by
    rcases hi.2.q w hw' with h | ⟨h, -⟩
    · exact absurd h (hnot w hw')
    · exact h
  rcases hi.2.q _ hwm with h | ⟨-, -, h3, h4⟩
  · exact hnot _ hwm h
  obtain ⟨-, -, -, d⟩ := hi.2.shape
  rcases d with ⟨-, d2, -⟩ | ⟨-, d2, -⟩ | ⟨d1, -, d3, d4, -⟩
  · change (G 0).2.ph.rank ≤ 1 at d2; rw [h3] at d2; simp [Ph.rank] at d2
  · change (G 0).2.ph = .sp1 at d2; rw [h3] at d2; cases d2
  change (G 1).2.ph.isTask = true at d3; change (G 2).2.ph.isTask = true at d4
  -- each task ended: it neither waits nor joins
  have htask : ∀ u, u = 1 ∨ u = 2 → (G u).2.ph = .fin := fun u hu => by
    rcases hall u (by rw [d1]; rcases hu with rfl | rfl <;> decide) with h | h | h
    · exact h.2
    · exfalso
      obtain ⟨j, hj, hje⟩ := Array.any_eq_true.mp h
      have h0 := hmain _ (Array.getElem_mem hj)
      have hje' : (m.waiters[j]).1 = u := by simpa using hje
      rw [hje'] at h0; rcases hu with rfl | rfl <;> cases h0
    · exfalso
      have ht : (G u).2.ph.isTask = true := by rcases hu with rfl | rfl <;> assumption
      rcases h.2 with e | e <;> rw [e] at ht <;> cases ht
  have f1 := htask 1 (.inl rfl)
  have f2 := htask 2 (.inr rfl)
  rcases h4 with hns | hw1 | hw2
  · have hp := hi.2.pre (by rw [h3]; decide)
    have := hp.last3 (by unfold X.e01; rw [h3]; rfl) (by unfold X.fd; rw [f1]; rfl) (by unfold X.fd; rw [f2]; rfl)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hns
    unfold X.st at this; rw [f1, f2, hns.1, hns.2] at this
    revert this; decide
  · rw [f1] at hw1; cases hw1
  · rw [f2] at hw2; cases hw2

/-- `main`'s lock place changes, with the same part and the same place in its code. -/
theorem U_l0 {G : ThreadId → Gh} {m : Mem} {a a' : LG} {x : X} (hu : U (upd G 0 (a, x)) m)
    (hpa : a'.part = a.part) (hfd : x.fd = false) : U (upd G 0 (a', x)) m := by
  have hX : ∀ u, (upd G 0 (a', x) u).2 = (upd G 0 (a, x) u).2 := fun u => by
    unfold upd; split <;> rfl
  have hX' : (fun u => (upd G 0 (a', x) u).2) = fun u => (upd G 0 (a, x) u).2 := funext hX
  have hG : ∀ u, u ≠ 0 → upd G 0 (a', x) u = upd G 0 (a, x) u := fun u h => by
    rw [upd_ne _ _ h, upd_ne _ _ h]
  refine ⟨by rw [hX']; exact hu.shape, fun u h => by rw [hG u h]; exact hu.parts u h,
    fun y => by have := hu.part0 y; rw [upd_self] at this ⊢; rw [hpa]; exact this,
    fun u h3 => by rw [hG u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h3))]; exact hu.out3 u h3,
    hu.blk, fun w hw => ?_, fun u => by rw [hX]; exact hu.sx1 u, fun u => by rw [hX]; exact hu.wks u,
    fun u => by rw [hX]; exact hu.fzc u, fun u hf => ?_, fun hr => ?_, fun hr => ?_⟩
  · rcases hu.q w hw with h | ⟨a1, a2, a3, a4⟩
    · exact .inl h
    · exact .inr ⟨a1, a2, by rw [hX]; exact a3, by simp only [hX]; exact a4⟩
  · by_cases h0 : u = 0
    · subst h0; rw [upd_self] at hf; change x.fd = true at hf; rw [hfd] at hf; cases hf
    · rw [hX] at hf; rw [hG u h0]; exact hu.lg u hf
  · rw [hX] at hr
    have hp := hu.pre hr
    exact Pre.keep (t := 0) hp (fun u => by rw [hX]; exact XEq.refl _) hp.wg hp.ev rfl rfl
      (fun _ => VClock.le_refl _) (by decide) (.inr fun e he => he) (fun e he => .inl he)
  · rw [hX] at hr; simp only [hX]; exact hu.done hr

/-- `main` away from the mutex's code, at the futex wait of the event, with its part `h`. -/
def gA (h : Heap) (x : X) : Gh := (⟨.away, h, Heap.empty⟩, x)

/-- `main` goes to the futex wait of the event (`away`). -/
theorem inv_away {G : ThreadId → Gh} {m : Mem} {h : Heap} {x : X}
    (hi : proto.inv (upd G 0 (gM h x)) m) (hfd : x.fd = false) :
    proto.inv (upd G 0 (gA h x)) m := by
  have hl := hi.1.ghost (t := 0) (g := gA h x) (by rw [upd_self]; rfl) (.inr (.inr rfl))
    (by rw [upd_self]; rfl) rfl
    (fun _ => hi.1.live 0 (by rw [upd_self]; exact (by decide : LPh.out ≠ LPh.gone)))
    (fun hL hR => by
      show R (fun u => (upd (upd G 0 (gM h x)) 0 (gA h x) u).2) hL
      rw [snd_upd_upd G 0 (gM h x) (gA h x) rfl]; exact hR)
  rw [upd_upd] at hl
  exact ⟨hl, U_l0 (a := (gM h x).1) hi.2 rfl hfd⟩

/-- `U` after an op of `main` at the event that keeps its writes (the kernel's read of a futex
wait), with the same ghost values. -/
theorem U_evRd {G : ThreadId → Gh} {m₁ M : Mem} (hi : proto.inv G m₁) (hr : (G 0).2.ph.rank ≤ 7)
    (hw' : EV.Ok M) (hop : EV.Op 0 m₁ M) (hh : EV.hist M = EV.hist m₁) (hq : QOk G M) :
    U G M := by
  have hp := hi.2.pre hr
  have hkG := Word.keep_op hop (W' := WG) (.inr (.inr (by decide)))
  have := U_main (g := G 0) hi
    (by rw [upd_same]; have hs := hi.2.shape; unfold Shape at hs ⊢; rw [hop.threads]; exact hs)
    (hop.cells _ (by rintro ⟨-, -, h⟩; simp only [EV] at h; omega)) hi.2.part0
    (by rw [upd_same]; exact hq)
    (fun _ => by
      rw [upd_same]
      exact Pre.keep hp (fun _ => XEq.refl _) (hp.wg.keep hkG) hw' (Word.hist_keep hp.wg hkG) hh
        hop.clocks (t := 0) (by decide) (.inl (main_x hi).2.2.1) hop.fpt)
    (fun h6 => by
      rw [upd_same] at h6
      obtain ⟨a, b, c, d⟩ := hi.2.done h6
      exact ⟨a, b, VClock.le_trans c (hop.clocks 0), VClock.le_trans d (hop.clocks 0)⟩)
    (main_x hi)
  rwa [upd_same] at this

/-- `main`'s futex wait at the event (value `1`) at `ev1`, with its part `h`: it sleeps only while
the newest write is its own `1` (no set yet). It goes on at `ev1`. -/
theorem wp_mwait {σ : Type} {s : σ} {G : ThreadId → Gh} {m : Mem} {n : Nat} {h : Heap}
    (hi : proto.inv (upd G 0 (gM h { ph := .ev1, e1 := true })) m)
    {Q : Unit × σ → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ k, n = k + 1 → ∀ G₁ m', m'.current = 0 →
      proto.inv (upd G₁ 0 (gM h { ph := .ev1, e1 := true })) m' → Q ((), s) G₁ m' k) :
    proto.WP 0 ((threadFutexWaitC EV.ptr (1 : BitVec 32) : CM Tgt σ Unit).run s) Q G m n := by
  rw [threadFutexWaitC_eq]
  refine WP.futexWaitC fun k hk => ⟨gA h { ph := .ev1, e1 := true }, inv_away hi rfl,
    fun G₁ m₁ hg₁ hi₁ => ?_⟩
  have hp := hi₁.2.pre (by rw [hg₁]; show Ph.ev1.rank ≤ 7; decide)
  have hw := hp.ev
  have hph : L.ph (G₁ 0) = .away := by rw [hg₁]; rfl
  have hgo : ∀ m', m'.current = 0 → L.Inv (upd G₁ 0 (L.set (G₁ 0) .out Heap.empty)) m' →
      U G₁ m' → proto.inv (upd G₁ 0 (gM h { ph := .ev1, e1 := true })) m' := fun m' _ hl hu => by
    refine ⟨by rw [show gM h { ph := .ev1, e1 := true } = L.set (G₁ 0) .out Heap.empty by
      rw [hg₁]; rfl]; exact hl, ?_⟩
    rw [← upd_g hg₁] at hu
    exact U_l0 (a := (gA h { ph := .ev1, e1 := true }).1) hu rfl rfl
  have hr0 : (G₁ 0).2.ph.rank ≤ 7 := by rw [hg₁]; show Ph.ev1.rank ≤ 7; decide
  have ht0 : (0 : ThreadId) < m₁.threads.size := (hi₁.1.live 0 (by rw [hph]; decide)).1
  have hi₀ := inv_cur hi₁ 0
  have hp₀ := hi₀.2.pre hr0
  refine ⟨fun _ => live_all hi₁ 0, fun hq0 => ⟨fun _ => ?_, fun b m' hr => ?_⟩⟩
  · exact hp₀.ev.futexWait_run ht0
  have hl := hi₁.1.waitOff hph (by decide)
    (Word.offWord hw (fun u => off_own hi₁ shE.b shE.o u) (off_R shE.b shE.o G₁) apE) hq0 hr
  -- the kernel's compare is an atomic read of the event: an op that keeps `U`
  have hrd : ∀ M, EV.Ok M → EV.Op 0 { m₁ with current := 0 } M →
      EV.hist M = EV.hist { m₁ with current := 0 } → U G₁ M := fun M hok hop hh =>
    U_evRd hi₀ hr0 hok hop hh fun w hw => hi₁.2.q w (by rw [hop.waiters] at hw; exact hw)
  rcases hp₀.ev.futexWait rfl ht0 (hcs_of hi₀) hr with
    ⟨-, rfl, rfl⟩ | ⟨-, M, hok, hop, hh, ⟨hH, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨-, hl'⟩ := hl
    exact hQ k hk G₁ _ rfl (hgo _ rfl hl' (U_mem hi₁.2 rfl rfl rfl rfl rfl hi₁.2.q))
  · -- it sleeps: the word is `1`, so no task set the event
    simp only [↓reduceIte] at hl ⊢
    have hlast := hw.holds_last.mp hH
    have hns : (!(G₁ 1).2.sx && !(G₁ 2).2.sx) = true := by
      cases e : ((G₁ 1).2.sx || (G₁ 2).2.sx)
      · simp only [Bool.or_eq_false_iff] at e; simp [e]
      · exfalso
        have h2 := ev_lastOf hp.evh (l := [0] ++ (if (G₁ 0).2.e1 then [1] else [])) (x := 2)
          (by unfold evL; rw [e]; rfl)
        have := val_eq hlast h2
        revert this; decide
    refine ⟨hl, U_mem (hrd _ hok hop hh) rfl rfl rfl rfl rfl fun w hw' => ?_⟩
    rcases Array.mem_push.mp hw' with hw' | rfl
    · exact hi₁.2.q w (by rw [hop.waiters] at hw'; exact hw')
    · exact .inr ⟨rfl, rfl, by rw [hg₁]; rfl, .inl hns⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
    obtain ⟨hc, hl'⟩ := hl
    exact hQ k hk G₁ _ hc (hgo _ hc hl' (hrd _ hok hop hh))

/-! ## `waitUntilSet` -/

/-- `Deadline.wait` with no timeout, by `main` at `ev1`: one futex wait at the event. -/
theorem dwait_spec {G : ThreadId → Gh} {m : Mem} {d : Nat} {p : Ptr} {hD : Heap} (hdl : DL p hD)
    (hi : proto.inv (upd G 0 (gM hD { ph := .ev1, e1 := true })) m) (hc : m.current = 0) :
    proto.WP 0 (Thread_Futex_Deadline_wait p EV.ptr 1) (fun r G' m' d' => r = .ok () ∧ d' < d ∧
      m'.current = 0 ∧ ∃ hD', DL p hD' ∧ proto.inv (upd G' 0 (gM hD' { ph := .ev1, e1 := true })) m')
      G m d := by
  obtain ⟨A, hA, hb⟩ := hdl.bytes
  unfold Thread_Futex_Deadline_wait
  refine WP.bind ?_
  rw [StateT.run'_eq, map_eq_pure_bind]
  refine WP.bind ?_
  simp only [StateT.run_bind, pure_bind, bind_assoc]
  refine WP.bind (wp_mownM (TTriple.loadAt (k := 0) (a := 8) (v := (none : Option (BitVec 64)))
    rfl (by decide) (by unfold bsD; rw [writeBytes_size _ _ _ (by rw [dl0_size]; decide)]; decide)
    (by rw [hdl.off]; simpa using hA) dl_none) hi hc hb
    (fun a hQ hq => by
      obtain ⟨-, hq'⟩ := sep_lift.mp hq
      obtain ⟨b, hpb, hb0⟩ := hdl.blk
      exact hb0_of hq' hpb hb0)
    fun a m' hQ _ hc' _ hq hi' => ?_)
  obtain ⟨rfl, hq'⟩ := sep_lift.mp hq
  simp only [StateT.run_pure, pure_bind, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind]
  refine WP.bind (WP.bind (wp_mwait hi' fun k hk G₁ m₁ hc₁ hi₁ => ?_))
  refine WP.pure' ?_
  simp only [StateT.run_pure]
  exact WP.pure' (WP.pure' (WP.pure' ⟨rfl, by omega, hc₁, hQ, ⟨hdl.off, hdl.blk, A, hA, hq'⟩, hi₁⟩))

theorem main_lt {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) : 0 < m.threads.size := by
  have h := hi.2.shape.1
  rcases e : m.threads.size with _ | n
  · rw [Array.getElem?_eq_none (by omega)] at h; cases h
  · omega

/-- The loop of `waitUntilSet` (`main` at `ev1`, with its deadline `q`). -/
def inv37 (q : Ptr) (_ : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → Gh)
    (m : Mem) (_ : Nat) : Prop :=
  m.current = 0 ∧ ∃ hD, DL q hD ∧ proto.inv (upd G 0 (gM hD { ph := .ev1, e1 := true })) m

/-- The loop ends: `main` read the set (`2`). -/
def post37 (q : Ptr)
    (r : Thread_ResetEvent_FutexImpl_waitUntilSetExit × Thread_ResetEvent_FutexImpl_waitUntilSetLocals)
    (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  r.1 = .br36 ∧ r.2.state = 2 ∧ m.current = 0 ∧ ∃ hD, DL q hD ∧
    proto.inv (upd G 0 (gM hD { ph := .rd, e1 := true })) m

theorem loop37_body (p0 q : Ptr) (hp1 : p0.add 0 = EV.ptr)
    (s : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (h : inv37 q s G m d) :
    proto.WP 0 ((Thread_ResetEvent_FutexImpl_waitUntilSet.loop37 p0 q).run s) (fun r G' m' d' =>
      if Thread_ResetEvent_FutexImpl_waitUntilSet.again37 r.1 then inv37 q r.2 G' m' d' ∧
        (d' < d ∨ d' = d ∧ (fun _ => 0) r.2 <
          (fun (_ : Thread_ResetEvent_FutexImpl_waitUntilSetLocals) => 0) s)
      else post37 q r G' m' d') G m d := by
  obtain ⟨hc, hD, hdl, hi⟩ := h
  unfold Thread_ResetEvent_FutexImpl_waitUntilSet.loop37
  simp only [StateT.run_bind]
  simp only [StateT.run_pure, pure_bind]
  rw [hp1, show EV.ptr.add 0 = EV.ptr from rfl]
  refine WP.bind (WP.bind (WP.callC (WP.mono ?_ (dwait_spec hdl hi hc))))
  rintro r G₁ m₁ d₁ ⟨rfl, hd₁, hc₁, hD₁, hdl₁, hi₁⟩
  simp only [StateT.run_pure, pure_bind, StateT.run_bind]
  refine WP.bind (WP.bind (wp_load shE hi₁ (fun G₂ m₂ hg hi₂ =>
      ⟨main_lt hi₂, by rw [hg]; show Ph.ev1.rank ≤ 7; decide⟩)
    fun k hk G₂ m₂ m₃ v j hg₂ hi₂ hr hj hv hfl hacq hh hw' hop hL => ?_))
  rcases inv_mread hi₂ hg₂ (.inr rfl) hj hv hfl (hacq rfl) hh hw' hop hL with ⟨rfl, hi₃⟩ | ⟨hb, hi₃⟩
  · refine WP.pure' ?_
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, StateT.run_pure]
    simp only [show ((2 : BitVec 32) != 1) = true from rfl, ↓reduceIte, StateT.run_pure]
    repeat (first
      | exact ⟨rfl, rfl, hop.current, hD₁, hdl₁, hi₃⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, Thread_ResetEvent_FutexImpl_waitUntilSet.again37,
          Bool.false_eq_true, ↓reduceIte])
    done
  · refine WP.pure' ?_
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, StateT.run_pure]
    rw [hb]
    simp only [show ((1 : BitVec 32) != 1) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      StateT.run_pure, if_true]
    have hi₄ : proto.inv (upd G₂ 0 (gM hD₁ { ph := .ev1, e1 := true })) m₃ := by
      rw [upd_g hg₂]; exact hi₃
    repeat (first
      | exact ⟨⟨hop.current, hD₁, hdl₁, hi₄⟩, .inl (by omega)⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, Thread_ResetEvent_FutexImpl_waitUntilSet.again37, ↓reduceIte])
    done

/-- A step of `main` on its own part `h` (`TTriple Pa x Qa`), in `ConcM`; the post's facts may
use the run. -/
theorem wp_mownR {α : Type} {x : MemM α} {G : ThreadId → Gh} {m : Mem} {d : Nat} {x0 : X}
    {h : Heap} {Pa : Assn} {Qa : α → Assn} (ht : TTriple Pa x Qa)
    (hi : proto.inv (upd G 0 (gM h x0)) m) (hc : m.current = 0) (hp : Pa h)
    {Q : α → (ThreadId → Gh) → Mem → Nat → Prop}
    (hQ : ∀ a m' hQ, (x.run m).run = some (.ok (a, m')) → Qa a hQ → (∀ y, hQ (0, y) = none) ∧
      (m'.current = 0 → m'.threads = m.threads → proto.inv (upd G 0 (gM hQ x0)) m' → Q a G m' d)) :
    proto.WP 0 (ConcM.liftMem x : ConcM Tgt α) Q G m d := by
  have hph : L.ph (upd G 0 (gM h x0) 0) = .out := by rw [upd_self]; rfl
  obtain ⟨ht0, hjt⟩ := hi.1.live 0 (by rw [hph]; decide)
  have hown : L.own (upd G 0 (gM h x0)) m 0 = h := by
    rw [L.own_live hjt, upd_self]; exact Heap.union_empty h
  refine WP.liftMem_owned ht hi.1.own hc ht0 (by rw [hown]; exact hp)
    fun a m' hQ' hr ho' hq hs hm' hd => ?_
  obtain ⟨hb0, hk⟩ := hQ a m' hQ' hr hq
  exact hk (hs.current.trans hc) hs.threads (inv_mown hi hc ho' hs hm' hd hb0)

/-- The end of `waitUntilSet`'s body: `main` at `rd`, with its deadline block `q`. -/
def postW (q : Ptr)
    (r : Thread_ResetEvent_FutexImpl_waitUntilSetExit × Thread_ResetEvent_FutexImpl_waitUntilSetLocals)
    (G : ThreadId → Gh) (m : Mem) (_ : Nat) : Prop :=
  r.1 = .ret (.ok ()) ∧ m.current = 0 ∧ ∃ hD bs e1, bs.size = 48 ∧ DLb q bs hD ∧
    proto.inv (upd G 0 (gM hD { ph := .rd, e1 := e1 })) m

theorem wus_spec (p0 : Ptr) (hp1 : (p0.add 0).add 0 = EV.ptr) (hp2 : p0.add 0 = EV.ptr)
    (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 0 (gM Heap.empty { ph := .ev0 })) m) (hc : m.current = 0) :
    proto.WP 0 (Thread_ResetEvent_FutexImpl_waitUntilSet p0 none) (fun r G' m' _ => r = .ok () ∧
      m'.current = 0 ∧ ∃ e1, proto.inv (upd G' 0 (gM Heap.empty { ph := .rd, e1 := e1 })) m')
      G m d := by
  unfold Thread_ResetEvent_FutexImpl_waitUntilSet
  have hbs : 0 < m.blocks.size := by
    obtain ⟨blk, h1, -⟩ := hi.2.blk
    exact (Array.getElem?_eq_some_iff.mp h1).1
  refine WP.bind (wp_mownR (TTriple.alloc .stack 48 8 (by decide)) hi hc rfl
    fun q m₁ hQ hr hq => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr
  obtain ⟨A, hA⟩ := hq
  obtain ⟨⟨-, hA8⟩, hb⟩ := sep_lift.mp hA
  have hdl : DLb ⟨some m.blocks.size, 0⟩ (Array.replicate 48 .undef) hQ :=
    ⟨rfl, ⟨m.blocks.size, rfl, Nat.pos_iff_ne_zero.mp hbs⟩, A, hA8, hb⟩
  refine ⟨hdl.b0, fun hc₁ _ hi₁ => ?_⟩
  generalize hq : (⟨some m.blocks.size, 0⟩ : Ptr) = q at hdl ⊢
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map (WP.mono (Q := postW q) (fun r G₂ m₂ d₂ hp => ?_) ?_)
  · -- the tail: `free` the deadline block
    obtain ⟨hr, hc₂, hD, bs, e1, hsz, hdl₂, hi₂⟩ := hp
    obtain ⟨A₂, -, hb₂⟩ := hdl₂.bytes
    show proto.WP 0 (ConcM.liftMem (free q) >>= fun _ => _) _ G₂ m₂ d₂
    refine WP.bind (wp_mownR (TTriple.free hsz hdl₂.off (by decide)) hi₂ hc₂ hb₂
      fun a m₃ hQ₃ hr₃ hq₃ => ⟨fun y => by rw [show hQ₃ = Heap.empty from hq₃]; rfl,
        fun hc₃ _ hi₃ => ?_⟩)
    rw [hr]
    exact WP.pure' ⟨rfl, hc₃, e1, by rw [show hQ₃ = Heap.empty from hq₃] at hi₃; exact hi₃⟩
  -- the body
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  rw [hp1]
  refine WP.bind (WP.bind (wp_load shE hi₁ (fun G₂ m₂ hg hi₂ =>
      ⟨main_lt hi₂, by rw [hg]; show Ph.ev0.rank ≤ 7; decide⟩)
    fun k hk G₂ m₂ m₃ v j hg₂ hi₂ hr hj hv hfl hacq hh hw' hop hL => ?_))
  refine WP.pure' ?_
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind, StateT.run_pure]
  rcases inv_mread hi₂ hg₂ (.inl rfl) hj hv hfl (hacq rfl) hh hw' hop hL with ⟨rfl, hi₃⟩ | ⟨hb, hi₃⟩
  · -- the set: `main` stops waiting
    simp only [show ((2 : BitVec 32) == 0) = false from rfl, show ((2 : BitVec 32) == 1) = false from rfl,
      show ((2 : BitVec 32) == 2) = true from rfl, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
      StateT.run_bind, StateT.run_get, pure_bind]
    repeat (first
      | exact ⟨rfl, hop.current, hQ, _, false, by simp, hdl, hi₃⟩
      | refine WP.pure' ?_
      | refine WP.bind (WP.callRC_ok dbg_true ?_)
      | simp only [StateT.run_pure, StateT.run_bind, StateT.run_get, pure_bind])
    done
  · -- `0`: `main`'s `cmpxchg(0 → 1)`
    simp only [Bool.false_eq_true, ↓reduceIte] at hb
    subst hb
    simp only [show ((0 : BitVec 32) == 0) = true from rfl, ↓reduceIte, StateT.run_pure,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [← upd_g hg₂] at hi₃
    refine WP.bind (WP.bind (WP.bind (WP.bind (wp_cas shE hi₃ (fun G₄ m₄ hg hi₄ =>
        ⟨main_lt hi₄, by rw [hg]; show Ph.ev0.rank ≤ 7; decide⟩)
      fun k₄ hk₄ G₄ m₄ m₅ hg₄ hi₄ _ hw₅ hop₅ hL₅ =>
        ⟨fun hv₄ _ hh₄ _ => ?_, fun j₄ b₄ hne hj₄ hv₄ hfl₄ hacq₄ hh₄ => ?_⟩))))
    · -- it wrote `1`: the futex loop
      have hi₅ := inv_mev1 hi₄ hg₄ hv₄ hh₄ hw₅ hop₅ hL₅
      repeat (first
        | refine WP.pure' ?_
        | simp only [StateT.run_pure, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind,
            Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            show ((1 : BitVec 32) == 1) = true from rfl])
      rw [dinit_eq]
      refine WP.bind (WP.bind (WP.callC (WP.pure' ?_)))
      obtain ⟨A₁, hA₁, hb₁⟩ := hdl.bytes
      refine WP.bind (wp_mownM (TTriple.storeBytesAt (p := q) (q := q) (k := 0) (a := 8) dl0
        (by cases q; simp [Ptr.add]) (by rw [dl0_size]; decide) (by simp [dl0_size]) (by rw [hdl.off]; simpa using hA₁) (by decide))
        hi₅ hop₅.current hb₁ (fun _ hQ' hq' => hb0_of hq' (hdl.blk.choose_spec.1) hdl.blk.choose_spec.2)
        fun _ m₆ hQ₆ _ hc₆ _ hq₆ hi₆ => ?_)
      have hdl₆ : DL q hQ₆ := ⟨hdl.off, hdl.blk, A₁, hA₁, hq₆⟩
      refine WP.bind (WP.mono ?_ (WP.loop _ _ (inv37 q) (fun _ => 0) (post37 q) (loop37_body p0 q hp2) _
        G₄ m₆ k₄ ⟨hc₆, hQ₆, hdl₆, hi₆⟩))
      rintro ⟨e, s'⟩ G₇ m₇ d₇ ⟨rfl, hst, hc₇, hD₇, hdl₇, hi₇⟩
      simp only [StateT.run_pure, StateT.run_bind, StateT.run_get, pure_bind]
      refine WP.pure' ?_
      change s'.state = 2 at hst
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hst]
      refine WP.bind (WP.callRC_ok dbg_true ?_)
      exact WP.pure' ⟨rfl, hc₇, hD₇, bsD, true, by unfold bsD; rw [writeBytes_size _ _ _ (by rw [dl0_size]; decide)]; simp, hdl₇, hi₇⟩
    · rcases inv_mread hi₄ hg₄ (.inl rfl) hj₄ hv₄ hfl₄ (hacq₄ rfl) hh₄ hw₅ hop₅ hL₅ with
        ⟨rfl, hi₅⟩ | ⟨hb₅, -⟩
      · repeat (first
          | refine WP.pure' ?_
          | simp only [StateT.run_pure, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind,
              Option.isSome_some, ↓reduceIte, optPayload, Bool.false_eq_true,
              show ((2 : BitVec 32) == 1) = false from rfl, show ((2 : BitVec 32) == 2) = true from rfl])
        exact ⟨rfl, hop₅.current, hQ, _, false, by simp, hdl, hi₅⟩
      · exact absurd hb₅ hne

/-! ## `main`'s `wait` -/

/-- The event's `wait` (`ResetEvent.wait`) by `main` at `ev0`: it ends at `rd`. -/
theorem evwait_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 0 (gM Heap.empty { ph := .ev0 })) m) (hc : m.current = 0) :
    proto.WP 0 (Thread_ResetEvent_wait (((bPtr.add 0).add 8)))
      (fun _ G' m' _ => m'.current = 0 ∧
        ∃ e1, proto.inv (upd G' 0 (gM Heap.empty { ph := .rd, e1 := e1 })) m') G m d := by
  unfold Thread_ResetEvent_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callC ?_)
  unfold Thread_ResetEvent_FutexImpl_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.bind (WP.callC ?_))
  unfold Thread_ResetEvent_FutexImpl_isSet
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  rw [evptr]
  refine WP.bind (WP.bind (wp_load shE hi (fun G₂ m₂ hg hi₂ =>
      ⟨main_lt hi₂, by rw [hg]; show Ph.ev0.rank ≤ 7; decide⟩)
    fun k hk G₂ m₂ m₃ v j hg₂ hi₂ hr hj hv hfl hacq hh hw' hop hL => ?_))
  rcases inv_mread hi₂ hg₂ (.inl rfl) hj hv hfl (hacq rfl) hh hw' hop hL with ⟨rfl, hi₃⟩ | ⟨hb, hi₃⟩
  · repeat (first
      | exact ⟨hop.current, false, hi₃⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind, show ((2 : BitVec 32) == 2) = true from rfl,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte, isNonErr])
    done
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb
    subst hb
    rw [← upd_g hg₂] at hi₃
    repeat (first
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind, show ((0 : BitVec 32) == 2) = false from rfl,
          Bool.not_false, ↓reduceIte])
    refine WP.bind (WP.callC (WP.mono ?_ (wus_spec _ rfl rfl G₂ m₃ k hi₃ hop.current)))
    rintro r G₄ m₄ d₄ ⟨rfl, hc₄, e1, hi₄⟩
    repeat (first
      | exact ⟨hc₄, e1, hi₄⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind, isNonErr, ↓reduceIte])
    done

/-- `WaitGroup.wait` by `main` at `run`: it ends at `rd`. -/
theorem wgwait_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 0 (gM Heap.empty { ph := .run })) m) (hc : m.current = 0) :
    proto.WP 0 (Thread_WaitGroup_wait (bPtr.add 0))
      (fun _ G' m' _ => m'.current = 0 ∧
        ∃ e1, proto.inv (upd G' 0 (gM Heap.empty { ph := .rd, e1 := e1 })) m') G m d := by
  unfold Thread_WaitGroup_wait
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, pure_bind]
  refine WP.bind (WP.bind (wp_rmw shG hi (fun G₁ m₁ hg hi₁ =>
      ⟨main_lt hi₁, by rw [hg]; show Ph.run.rank ≤ 7; decide⟩)
    fun k hk G₁ m₁ m' old hg₁ hi₁ hr hv _ hh hacq hw' hop hL => ?_))
  obtain ⟨w, rfl, hw, hi'⟩ := inv_add hi₁ hg₁ hv hh (hacq rfl) hw' hop hL
  refine WP.pure' ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  have hd : (BitVec.ofNat 64 w &&& 1 == 0) = true := by rcases hw with rfl | rfl | rfl <;> rfl
  rw [hd]
  refine WP.bind (WP.callRC_ok dbg_true ?_)
  simp only [StateT.run_pure, pure_bind, StateT.run_bind]
  have hdiv : (divTrunc false (BitVec.ofNat 64 w) 2).run = some (.ok (BitVec.ofNat 64 (w / 2))) := by
    rcases hw with rfl | rfl | rfl <;> rfl
  refine WP.bind (WP.bind (WP.callRC_ok hdiv ?_))
  by_cases h0 : w = 0
  · subst h0
    simp only [show gt false (BitVec.ofNat 64 (0 / 2)) 0 = false from rfl, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, pure_bind]
    repeat (first
      | exact ⟨hop.current, false, hi'⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind])
    done
  · have hg : gt false (BitVec.ofNat 64 (w / 2)) 0 = true := by
      rcases hw with rfl | rfl | rfl <;> first | exact absurd rfl h0 | rfl
    have hp : phA w = .ev0 := by simp [phA, h0]
    rw [hp] at hi'
    simp only [hg, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind]
    refine WP.bind (WP.callC (WP.mono ?_ (evwait_spec G₁ m' k hi' hop.current)))
    rintro _ G₂ m₂ d₂ ⟨hc₂, e1, hi₂⟩
    repeat (first
      | exact ⟨hc₂, e1, hi₂⟩
      | refine WP.pure' ?_
      | simp only [StateT.run_pure, StateT.run_bind, pure_bind])
    done

/-! ## `main`'s read of the `Tally`, and its joins -/

/-- The `Tally`'s decode, from the values of its four words. -/
theorem tally_decode {bs : Array Byte} {a : BitVec 64} {b c d : BitVec 32}
    (ha : (intOfBytes 64 (bs.extract 0 8)).run = some (.ok a))
    (hb : (intOfBytes 32 (bs.extract 8 12)).run = some (.ok b))
    (hc : (intOfBytes 32 (bs.extract 16 20)).run = some (.ok c))
    (hd : (intOfBytes 32 (bs.extract 20 24)).run = some (.ok d)) :
    (Enc.decode bs : Result Tally).run = some (.ok
      { wg := { state := { raw := a }, event := { impl := { state := { raw := b } } } },
        m := mutexOf c, n := d }) := by
  have ha' : intOfBytes 64 (bs.extract 0 8) = pure a := ha
  have hb' : intOfBytes 32 (bs.extract 8 12) = pure b := hb
  have hc' : intOfBytes 32 (bs.extract 16 20) = pure c := hc
  have hd' : intOfBytes 32 (bs.extract 20 24) = pure d := hd
  simp only [Enc.decode, Enc.decodeAt, Enc.size, Array.extract_extract, intSize,
    show alignUp ((64 + 7) / 8) (intAlign 64) = 8 from rfl,
    show alignUp ((32 + 7) / 8) (intAlign 32) = 4 from rfl]
  rw [show Min.min 8 (Min.min 8 16) = 8 from rfl,
    show Min.min (8 + 4) (Min.min (8 + 4) (Min.min (8 + 4) (Min.min (8 + 4) 16))) = 12 from rfl,
    show Min.min (16 + 4) (Min.min (16 + 4) (Min.min (16 + 4) (16 + 4))) = 20 from rfl,
    show (20 + 4 : Nat) = 24 from rfl, ha', hb', hc', hd']
  rfl

/-- `main` at `rd`: every other thread is `gone` for the lock. -/
theorem gone_rd {G : ThreadId → Gh} {m : Mem} {e1 : Bool} (hi : proto.inv G m)
    (hg : G 0 = gM Heap.empty { ph := .rd, e1 := e1 }) (u : ThreadId) (h0 : u ≠ 0) :
    L.ph (G u) = .gone := by
  have hd := hi.2.done (by rw [hg]; show 6 ≤ Ph.rd.rank; decide)
  by_cases h12 : u = 1 ∨ u = 2
  · have hfr : (G u).2.frozen := by rcases h12 with rfl | rfl; exact hd.1; exact hd.2.1
    apply hi.2.lg u
    unfold X.frozen at hfr; unfold X.fd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr ⊢
    exact ⟨hfr.1, by omega⟩
  · exact hi.2.out3 u (by unfold ThreadId at *; omega)

/-- `main` at `rd`: both tasks are frozen, so no thread holds the mutex. -/
theorem free_rd {G : ThreadId → Gh} {m : Mem} {e1 : Bool} (hi : proto.inv G m)
    (hg : G 0 = gM Heap.empty { ph := .rd, e1 := e1 }) : L.Free G := by
  intro u
  by_cases h0 : u = 0
  · subst h0; rw [hg]; show LPh.out ≠ LPh.holds; decide
  · rw [gone_rd hi hg u h0]; decide

/-- A frozen task did its store of the counter. -/
theorem cnt_frozen {x : X} (h : x.frozen) : x.cnt = 1 := by
  unfold X.frozen at h; unfold X.cnt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [if_pos ⟨h.1, by omega⟩]

/-- `main` at `rd`: the `Tally` holds the four words, and the counter `2`. -/
theorem tally_read {G : ThreadId → Gh} {m : Mem} {e1 : Bool} (hi : proto.inv G m)
    (hg : G 0 = gM Heap.empty { ph := .rd, e1 := e1 }) :
    ∃ (blk : Block) (v : Tally), m.blocks[0]? = some blk ∧ m.access bPtr (Enc.size Tally) 8 = pure (0, blk, 0) ∧
      Enc.decode (blk.bytes.extract 0 (0 + Enc.size Tally)) = pure v ∧ v.n = 2 := by
  obtain ⟨blk, h1, hlive, hsz, haddr, -⟩ := hi.2.blk
  have hacc : m.access bPtr (Enc.size Tally) 8 = pure (0, blk, 0) :=
    access_of rfl h1 hlive (by decide) (by simp [bPtr, hsz]; exact Int.le_refl 24) (by simp [bPtr, haddr])
  have hp := hi.2.pre (by rw [hg]; show Ph.rd.rank ≤ 7; decide)
  obtain ⟨a, ha⟩ := hp.wg.val
  rw [Word.holds_bytes (W := WG) h1] at ha
  obtain ⟨b, hb⟩ := hp.ev.val
  rw [Word.holds_bytes (W := EV) h1] at hb
  obtain ⟨w, -, hU, -⟩ := hi.1.word
  unfold Lock.U32 curBytes at hU
  rw [show L.b = 0 from rfl, show L.o = 16 from rfl, h1] at hU
  simp only [Option.map_some, Option.getD_some] at hU
  -- the counter: the lock's free resource
  obtain ⟨hL, hR, hsub, -, -, -⟩ := hi.1.free (free_rd hi hg)
  change R (fun u => (G u).2) hL at hR
  obtain ⟨A, S, K, bs, -, hs, hv, hbA, -⟩ := hR
  obtain ⟨hm, -⟩ := Heap.diff_split hsub
  obtain ⟨b', blk', hacc', -, -, -, hx⟩ := bytesAt_access hbA hm (q := (bPtr.add 20).add 0) (k := 0)
    (n := 4) (a := 1) rfl (by decide) (by rw [hs]; exact Nat.le_refl _) (Nat.mod_one _)
  obtain ⟨hqb, hblk', -⟩ := access_eq hacc'
  cases hqb
  rw [h1] at hblk'; cases hblk'
  have hd := hi.2.done (by rw [hg]; show 6 ≤ Ph.rd.rank; decide)
  have hc2 : (G 1).2.cnt + (G 2).2.cnt = 2 := by rw [cnt_frozen hd.1, cnt_frozen hd.2.1]
  rw [hc2] at hv
  have hs4 : bs.size = 4 := hs
  have hbs : bs.extract 0 (0 + 4) = bs := by rw [Array.extract_eq_self_iff]; omega
  rw [hbs] at hx
  have hd' : (intOfBytes 32 (blk.bytes.extract 20 24)).run = some (.ok (BitVec.ofNat 32 2)) := by
    have : blk.bytes.extract 20 24 = bs := hx
    rw [this]; exact hv
  have e : ∀ i j, (blk.bytes.extract 0 (0 + Enc.size Tally)).extract i j =
      blk.bytes.extract i (min j 24) := fun i j => by
    rw [Array.extract_extract]; simp [Enc.size]
  refine ⟨blk, _, h1, hacc, tally_decode (a := a) (b := b) (c := BitVec.ofNat 32 w)
    (by rw [e]; exact ha) (by rw [e]; exact hb) (by rw [e]; exact hU) (by rw [e]; exact hd'), rfl⟩

/-- `main`'s read of the whole `Tally` at `rd`: no race, and `main` goes to `rdd`. -/
theorem inv_read {G : ThreadId → Gh} {m : Mem} {e1 : Bool} (hi : proto.inv G m)
    (hg : G 0 = gM Heap.empty { ph := .rd, e1 := e1 }) (hc : m.current = 0) :
    NoRace m 0 0 (Enc.size Tally) .read ∧
      proto.inv (upd G 0 (gM Heap.empty { ph := .rdd })) (m.recordAt 0 0 (Enc.size Tally) .read) := by
  have hgx : (G 0).2 = { ph := .rd, e1 := e1 } := by rw [hg]; rfl
  have hp := hi.2.pre (by rw [hgx]; show Ph.rd.rank ≤ 7; decide)
  have hd := hi.2.done (by rw [hgx]; show 6 ≤ Ph.rd.rank; decide)
  obtain ⟨blk, h1, -⟩ := hi.2.blk
  refine ⟨noRace_of fun e he hb _ _ => .inl ?_, ?_, ?_⟩
  · obtain ⟨ht3, hle⟩ := hp.attr e he hb
    rw [hc]
    refine VClock.le_trans hle ?_
    unfold ac
    rcases (by unfold ThreadId at *; omega : e.tid = 0 ∨ e.tid = 1 ∨ e.tid = 2) with h | h | h <;> rw [h]
    · rw [hgx]; exact VClock.le_refl _
    · rw [if_pos hd.1]; exact hd.2.2.1
    · rw [if_pos hd.2.1]; exact hd.2.2.2
  · have hl := hi.1.readAll (b := 0) (o := 0) (n := Enc.size Tally)
      (Array.getElem?_eq_some_iff.mp h1).1 (by decide) (by rw [hc]; exact main_lt hi)
      (fun u _ hu => gone_rd hi hg u (by rw [hc] at hu; exact hu))
      (fun u x _ _ => by
        unfold Lock.own; split
        · rfl
        · show ((G u).1.part ∪ (G u).1.held) (0, x) = none
          have hh : (G u).1.held = Heap.empty := hi.1.idle u (by
            by_cases h0 : u = 0
            · subst h0; rw [hg]; show LPh.out ≠ LPh.holds; decide
            · rw [gone_rd hi hg u h0]; decide)
          rw [hh, Heap.union_empty]
          by_cases h0 : u = 0
          · subst h0; exact hi.2.part0 x
          · rw [hi.2.parts u h0]; rfl)
    exact linv_task hl (by rw [hg]; rfl) (by rw [hg]; rfl)
  · refine U_main hi (by
        rw [show (fun u => (upd G 0 (gM Heap.empty { ph := .rdd }) u).2) =
          upd (fun u => (G u).2) 0 { ph := .rdd } by funext u; unfold upd; split <;> rfl]
        exact shape_m hi.2.shape rfl (by rw [hgx]; show 3 ≤ Ph.rd.rank; decide)
          (by rw [hgx]; show Ph.rd ≠ .j1; decide) rfl (by decide)
          (by decide))
      (Mem.heap_recordAt _) (fun _ => rfl) (qok_run hi (by rw [hg]; rfl) rfl _)
      (fun hr => by rw [upd_self] at hr; exact absurd hr (by show ¬ Ph.rdd.rank ≤ 7; decide))
      (fun _ => ⟨hd.1, hd.2.1, VClock.le_trans hd.2.2.1 (recordAt_le _ _ _ _ _ _),
        VClock.le_trans hd.2.2.2 (recordAt_le _ _ _ _ _ _)⟩)
      ⟨rfl, by show Ph.rdd ≠ .wk; decide, rfl, rfl⟩

/-- A thread that is `gone` for the lock owns nothing (its part is empty). -/
theorem own_gone {G : ThreadId → Gh} {m : Mem} (hi : proto.inv G m) {u : ThreadId} (hu0 : u ≠ 0)
    (hg : L.ph (G u) = .gone) : L.own G m u = Heap.empty := by
  unfold Lock.own; split
  · rfl
  · show (G u).1.part ∪ (G u).1.held = Heap.empty
    rw [hi.2.parts u hu0, show (G u).1.held = Heap.empty from hi.1.idle u (by rw [hg]; decide)]; rfl

/-- `main`'s join of task 1 at `rdd`: it goes to `j1`. -/
theorem inv_j1 {G : ThreadId → Gh} {m m' : Mem} (hi : proto.inv G m)
    (hg : G 0 = gM Heap.empty { ph := .rdd })
    (hj : ((Thread.join 1).run { m with current := 0 }).run = some (.ok ((), m'))) :
    m'.current = 0 ∧ proto.inv (upd G 0 (gM Heap.empty { ph := .j1 })) m' := by
  have hgx : (G 0).2 = { ph := .rdd } := by rw [hg]; rfl
  have hd := hi.2.done (by rw [hgx]; show 6 ≤ Ph.rdd.rank; decide)
  have hg1 : L.ph (G 1) = .gone := by
    apply hi.2.lg 1
    have hfr := hd.1
    unfold X.frozen at hfr; unfold X.fd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr ⊢
    exact ⟨hfr.1, by omega⟩
  have hown := own_gone hi (by decide) hg1
  have hl := hi.1.join (t := 0) (u := 1) (g := gM Heap.empty { ph := .j1 }) (by decide) (by decide)
    (by rw [hg]; rfl) hg1 hj (by rw [hown, hg]; rfl) rfl rfl (fun hL hR => by
      show R (fun u => (upd G 0 (gM Heap.empty { ph := .j1 }) u).2) hL
      refine (R_cnt (Y := fun u => (G u).2) ?_ ?_ hL).mpr hR <;>
      · show (upd G 0 _ _).2.cnt = _; rw [upd_ne _ _ (by decide)])
  obtain ⟨rec, hrec, hrj, hm'⟩ := join_eq hj
  have hc' : m'.current = 0 := by rw [hm']
  refine ⟨hc', hl, ?_⟩
  obtain ⟨h00, -, h3, d⟩ := hi.2.shape
  rcases d with ⟨-, d2, -⟩ | ⟨-, d2, -⟩ | ⟨d1, -, d3, d4, d5, d6⟩
  · change (G 0).2.ph.rank ≤ 1 at d2; rw [hgx] at d2; simp [Ph.rank] at d2
  · change (G 0).2.ph = .sp1 at d2; rw [hgx] at d2; cases d2
  have hX : ∀ u, u ≠ 0 → (upd G 0 (gM Heap.empty { ph := .j1 }) u).2 = (G u).2 := fun u h => by
    rw [upd_ne _ _ h]
  have hX0 : (upd G 0 (gM Heap.empty { ph := .j1 }) 0).2 = { ph := .j1 } := by rw [upd_self]; rfl
  simp only at hrec
  change ({ m with current := 0 } : Mem).threads[1]? = some rec at hrec
  have hrec' : rec = { spawner := 0, joined := false } := by
    change m.threads[1]? = _ at hrec
    have : m.threads[1]? = some { spawner := 0, joined := decide ((G 0).2.ph = .j1) } := d5
    rw [this, hgx] at hrec; cases hrec; rfl
  subst hrec'
  have hth : m'.threads = m.threads.set! 1 { spawner := 0, joined := true } := by rw [hm']
  have hcl : VClock.le (m.clocks[0]!) (m'.clocks[0]!) = true := by
    rw [hm']; simp only
    rw [Proto.getElem!_set!_ite]
    split
    · exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
    · exact VClock.le_refl _
  refine U_main hi ⟨?_, by show (upd G 0 _ 0).2.ph.isMain = true; rw [hX0]; rfl, fun u hu => by
      show (upd G 0 _ u).2 = _
      rw [hX u (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hu))]; exact h3 u hu,
      .inr (.inr ⟨by rw [hth, Array.size_set!]; exact d1,
        by show 3 ≤ (upd G 0 _ 0).2.ph.rank; rw [hX0]; decide,
        by show (upd G 0 _ 1).2.ph.isTask = true; rw [hX 1 (by decide)]; exact d3,
        by show (upd G 0 _ 2).2.ph.isTask = true; rw [hX 2 (by decide)]; exact d4, ?_, ?_⟩)⟩
    (by rw [hm']; rfl) (fun _ => rfl) (qok_run hi (by rw [hg]; rfl) (by rw [hm']) _)
    (fun hr => by rw [upd_self] at hr; exact absurd hr (by show ¬ Ph.j1.rank ≤ 7; decide))
    (fun _ => ⟨hd.1, hd.2.1, VClock.le_trans hd.2.2.1 hcl, VClock.le_trans hd.2.2.2 hcl⟩)
    ⟨rfl, by show Ph.j1 ≠ .wk; decide, rfl, rfl⟩
  · rw [hth]; simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simpa using h00
  · rw [hth]; simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    show _ = some ({ spawner := 0, joined := decide ((upd G 0 (gM Heap.empty { ph := .j1 }) 0).2.ph = .j1) } : ThreadRec)
    rw [hX0]; simp [d1]
  · rw [hth]; simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simpa using d6

/-! ## `main` -/

/-- `startMany(2)` by `main` at `pre`: it ends at `sm`. -/
theorem startMany_spec (G : ThreadId → Gh) (m : Mem) (d : Nat)
    (hi : proto.inv (upd G 0 (gM Heap.empty { ph := .pre })) m) :
    proto.WP 0 (Thread_WaitGroup_startMany (bPtr.add 0) 2)
      (fun _ G' m' _ => m'.current = 0 ∧ proto.inv (upd G' 0 (gM Heap.empty { ph := .sm })) m') G m d := by
  unfold Thread_WaitGroup_startMany
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callRC_ok (v := (4 : BitVec 64)) rfl ?_)
  simp only [StateT.run_pure, pure_bind]
  refine WP.bind (WP.bind (wp_rmw shG hi (fun G₁ m₁ hg hi₁ =>
      ⟨main_lt hi₁, by rw [hg]; show Ph.pre.rank ≤ 7; decide⟩)
    fun k hk G₁ m₁ m' old hg₁ hi₁ hr hv _ hh _ hw' hop hL => ?_))
  obtain ⟨rfl, hi'⟩ := inv_sm hi₁ hg₁ hv hh hw' hop hL
  refine WP.pure' ?_
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine WP.bind (WP.callRC_ok (v := (0 : BitVec 64)) rfl ?_)
  simp only [StateT.run_pure, pure_bind, StateT.run_bind]
  refine WP.bind (WP.callRC_ok dbg_true ?_)
  repeat (first
    | exact ⟨hop.current, hi'⟩
    | refine WP.pure' ?_
    | simp only [StateT.run_pure, StateT.run_bind, pure_bind])
  done

/-- The number of threads at `main`'s spawns. -/
theorem size_sm {G : ThreadId → Gh} {m : Mem} {x : X} (hi : proto.inv (upd G 0 (gM Heap.empty x)) m) :
    (x.ph = .sm → m.threads.size = 1) ∧ (x.ph = .sp1 → m.threads.size = 2) := by
  obtain ⟨-, -, -, d⟩ := hi.2.shape
  have h0 : (upd G 0 (gM Heap.empty x) 0).2 = x := by rw [upd_self]; rfl
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    rcases d with ⟨d1, d2, -⟩ | ⟨d1, d2, -⟩ | ⟨d1, d2, -⟩
  · exact d1
  · change (upd G 0 _ 0).2.ph = _ at d2; rw [h0, h] at d2; cases d2
  · change 3 ≤ (upd G 0 _ 0).2.ph.rank at d2; rw [h0, h] at d2; simp [Ph.rank] at d2
  · change (upd G 0 _ 0).2.ph.rank ≤ 1 at d2; rw [h0, h] at d2; simp [Ph.rank] at d2
  · exact d1
  · change 3 ≤ (upd G 0 _ 0).2.ph.rank at d2; rw [h0, h] at d2; simp [Ph.rank] at d2

/-- The threads after both spawns, with `main` at `x` (rank 3 or more). -/
theorem shape3 {G : ThreadId → Gh} {m : Mem} {x : X} (hi : proto.inv (upd G 0 (gM Heap.empty x)) m)
    (h3 : 3 ≤ x.ph.rank) :
    m.threads.size = 3 ∧ m.threads[0]? = some { spawner := 0, joined := true } ∧
      m.threads[1]? = some { spawner := 0, joined := decide (x.ph = .j1) } ∧
      m.threads[2]? = some { spawner := 0, joined := false } := by
  obtain ⟨h00, -, -, d⟩ := hi.2.shape
  have h0 : (upd G 0 (gM Heap.empty x) 0).2 = x := by rw [upd_self]; rfl
  rcases d with ⟨-, d2, -⟩ | ⟨-, d2, -⟩ | ⟨d1, -, -, -, d5, d6⟩
  · change (upd G 0 _ 0).2.ph.rank ≤ 1 at d2; rw [h0] at d2; omega
  · change (upd G 0 _ 0).2.ph = _ at d2; rw [h0] at d2; rw [d2] at h3; simp [Ph.rank] at h3
  · refine ⟨d1, h00, ?_, d6⟩
    change _ = some ({ spawner := 0, joined := decide ((upd G 0 (gM Heap.empty x) 0).2.ph = .j1) } : ThreadRec) at d5
    rw [h0] at d5; exact d5

theorem main_spec (d : Nat) :
    proto.WP 0 waitGroup QM G0 { mem0 with current := 0 } d := by
  unfold waitGroup
  -- the `Tally`: block 0
  refine WP.bind (WP.liftMem_owned (own := fun _ => Heap.empty) (TTriple.alloc .stack 24 8 (by decide))
    (Owned.start rfl rfl) rfl (by decide) rfl fun s0 m₁ h₁ hr₁ ho₁ hq₁ hs₁ hm₁ hd₁ => ?_)
  obtain ⟨rfl, -⟩ := alloc_ok hr₁
  obtain ⟨A, hA⟩ := hq₁
  obtain ⟨⟨-, hA8⟩, hb₁⟩ := sep_lift.mp hA
  have hc₁ : m₁.current = 0 := hs₁.current
  rw [show (⟨some ({ mem0 with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = bPtr from rfl] at hb₁ ⊢
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have ho₁' : Owned (upd (fun _ => Heap.empty) 0 h₁) m₁ := ho₁
  obtain ⟨hsz, -⟩ := enc_tally
  refine WP.bind (WP.liftM_owned (TTriple.storeAt' (p := bPtr) (q := bPtr) (A := A) (S := 24)
    (K := .stack) (bs := Array.replicate 24 .undef) (k := 0) (a := 8) tally0 hsz rfl (by decide)
    (by simp [Enc.size]) (by simp [bPtr]; omega) (by decide)) ho₁' hc₁ (by rw [hs₁.threads]; decide)
    (by rw [upd_self]; exact hb₁) fun _ m₂ h₂ hr₂ ho₂ F₂ hs₂ _ _ => ?_)
  rw [upd_upd] at ho₂
  rw [writeBytes_all (by rw [hsz]; simp)] at F₂
  have hc₂ : m₂.current = 0 := hs₂.current.trans hc₁
  have hi₂ := inv_start ho₂ F₂ hA8 (by rw [hs₂.threads, hs₁.threads]; rfl)
    (by rw [hs₂.atomics, hs₁.atomics]; rfl) (by rw [hs₂.waiters, hs₁.waiters]; rfl)
    (fun e he => by
      have h0 : ∀ e ∈ m₁.footprint, e.tid = 0 ∧ VClock.le e.clock (m₁.clocks[0]!) = true := by
        intro e he
        rcases hs₁.fp e he with h | ⟨het, -, -⟩
        · simp [mem0, Mem.ofGlobals] at h
        · refine ⟨het, ?_⟩
          rcases hs₁.fpc e he with h | h
          · simp [mem0, Mem.ofGlobals] at h
          · exact h
      rcases hs₂.fp e he with h | ⟨het, -, -⟩
      · obtain ⟨a, b⟩ := h0 e h
        exact ⟨a, VClock.le_trans b (by have := hs₂.mine; rw [hc₁] at this; exact this)⟩
      · refine ⟨by rw [het, hc₁], ?_⟩
        rcases hs₂.fpc e he with h | h
        · exact VClock.le_trans (h0 e h).2 (by have := hs₂.mine; rw [hc₁] at this; exact this)
        · rw [hc₁] at h; exact h)
  -- `startMany(2)`
  refine WP.bind (WP.callC (WP.mono ?_ (startMany_spec G0 m₂ d hi₂)))
  rintro _ G₃ m₃ d₃ ⟨hc₃, hi₃⟩
  simp only [StateT.run_bind]
  -- the spawns
  refine WP.bind (WP.spawnC fun k _ => ⟨_, hi₃, fun G₄ m₄ hg₄ hi₄ => ⟨gT .lk, ⟨rfl, rfl⟩,
    fun c₁ m₅ hf₁ => ?_⟩⟩)
  rw [← upd_g hg₄] at hi₄
  obtain ⟨rfl, hi₅⟩ := inv_spawn (k := 1) hi₄ (by rw [upd_self]) (.inl ⟨rfl, rfl, rfl⟩)
    ((size_sm hi₄).1 rfl) hf₁
  rw [upd_g hg₄] at hi₅
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨_, hi₅, fun G₆ m₆ hg₆ hi₆ => ⟨gT .lk, ⟨rfl, rfl⟩,
    fun c₂ m₇ hf₂ => ?_⟩⟩)
  rw [← upd_g hg₆] at hi₆
  obtain ⟨rfl, hi₇⟩ := inv_spawn (k := 2) hi₆ (by rw [upd_self]) (.inr ⟨rfl, rfl, rfl⟩)
    ((size_sm hi₆).2 rfl) hf₂
  rw [upd_g hg₆] at hi₇
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  have hc₇ : m₇.current = 0 := by rw [(Lock.fork_eq hf₂).2]
  -- `wait`
  refine WP.bind (WP.callC (WP.mono ?_ (wgwait_spec _ m₇ k hi₇ hc₇)))
  rintro _ G₈ m₈ d₈ ⟨hc₈, e1, hi₈⟩
  -- the read of the `Tally`
  obtain ⟨blk, v, hblk, hacc, hdec, hn⟩ := tally_read hi₈ (upd_self _ _ _)
  obtain ⟨hnr, hi₉⟩ := inv_read hi₈ (upd_self _ _ _) hc₈
  rw [upd_upd] at hi₉
  have hrun : ((load Tally 8 bPtr).run m₈).run = some (.ok (v, m₈.recordAt 0 0 (Enc.size Tally) .read)) := by
    rw [load_run hacc hdec hnr]; rfl
  refine WP.bind (WP.liftM (fun e he => by rw [hrun] at he; cases he) fun a m₉ hr => ?_)
  rw [hrun] at hr
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨rfl, ?_⟩
  -- the join of task 1
  refine WP.bind (WP.joinC fun k₁ _ => ⟨_, hi₉, fun G₁₀ m₁₀ hg₁₀ hi₁₀ => ?_⟩)
  rw [← upd_g hg₁₀] at hi₁₀
  obtain ⟨hs₁₀, -, ht1, -⟩ := shape3 hi₁₀ (by decide)
  rw [upd_g hg₁₀] at hi₁₀
  refine ⟨fun _ => ⟨by decide, by rw [hs₁₀]; decide, ⟨rfl, .inl rfl⟩, by simp [Thread.joinValid, Mem.isGated, ht1]⟩, fun hfin => ⟨fun _ =>
    join_run (m := { m₁₀ with current := 0 }) ht1 rfl rfl, fun m₁₁ hj₁ => ?_⟩⟩
  obtain ⟨hc₁₁, hi₁₁⟩ := inv_j1 hi₁₀ hg₁₀ hj₁
  -- the join of task 2
  refine WP.bind (WP.joinC fun k₂ _ => ⟨_, hi₁₁, fun G₁₂ m₁₂ hg₁₂ hi₁₂ => ?_⟩)
  rw [← upd_g hg₁₂] at hi₁₂
  obtain ⟨hs₁₂, ht0, ht1', ht2⟩ := shape3 hi₁₂ (by decide)
  rw [upd_g hg₁₂] at hi₁₂
  refine ⟨fun _ => ⟨by decide, by rw [hs₁₂]; decide, ⟨rfl, .inr rfl⟩, by simp [Thread.joinValid, Mem.isGated, ht2]⟩, fun hfin₂ => ⟨fun _ =>
    join_run (m := { m₁₂ with current := 0 }) ht2 rfl rfl, fun m₁₃ hj₂ => ?_⟩⟩
  obtain ⟨rec, hrec, -, hm₁₃⟩ := join_eq hj₂
  change m₁₂.threads[2]? = some rec at hrec
  rw [ht2] at hrec; cases hrec
  refine WP.pure' ?_
  -- the free of the `Tally`
  obtain ⟨blk₀, hblk₀, hl₀, -⟩ := hi₁₂.2.blk
  have hb₁₃ : m₁₃.blocks[0]? = some blk₀ := by rw [hm₁₃]; exact hblk₀
  refine WP.bind (WP.liftMem (fun e he => (free_noErr hb₁₃ hl₀ (freeRaces_of_joined
    (by rw [hm₁₃]; simp only [Array.size_set!]; exact hi₁₂.1.own.csize) fun u hu => by
      rw [hm₁₃] at hu ⊢
      simp only [Array.size_set!, hs₁₂] at hu
      rcases (by omega : u = 0 ∨ u = 1 ∨ u = 2) with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨{ spawner := 0, joined := true }, by simp [Array.set!_eq_setIfInBounds, ht1'],
          rfl, rfl, rfl⟩
      · exact .inr ⟨{ spawner := 0, joined := true }, by simp [Array.set!_eq_setIfInBounds, hs₁₂],
          rfl, rfl, rfl⟩) e he).elim) fun _ m₁₄ hfr => ?_)
  obtain ⟨b', blk'', -, -, rfl⟩ := free_ok hfr
  refine ⟨rfl, WP.pure' ⟨by rw [hn], fun r hr hsp => ?_⟩⟩
  -- every thread is joined
  simp only [hm₁₃] at hr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · rename_i hne
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [Array.getElem?_eq_getElem (by omega)] at ht0; rw [Option.some.inj ht0]
    · rw [Array.getElem?_eq_getElem (by omega)] at ht1'; rw [Option.some.inj ht1']; rfl

/-! ## The results -/

/-- **`threadsync.waitGroup` gives 2 under every schedule** (every oracle `o`, every `fuel`). -/
theorem waitGroup_spec (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o waitGroup mem0).run = some (.ok (v, m))) :
    v = .ok 2 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec) h
  exact hv

/-- **No run of `threadsync.waitGroup` gives an error**: no data race on the `Tally` (its whole
read included), no deadlock at a futex, no panic, under every schedule. -/
theorem waitGroup_safe (env : Env) (henv : env.spawn = .available) {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run env dispatch fuel o waitGroup mem0).run ≠ some (.error e) :=
  proto.run_safe env (Proto.of_available henv) dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl main_spec

end Threadsync.WG
