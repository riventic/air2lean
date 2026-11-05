import ZigLean.Sep.Full.Sem
import ZigLean.Sep.Full.ThreadFacts
import ZigLean.Conc.Share

/-!
# The protocol of `semaphoreCounter`

`semaphoreCounter` (examples/sync, Zig 0.16.0; the 0.17.0 translation of this program is the same
code): `main` spawns one thread; each of the two threads adds 1 two times to a counter `n`,
between `wait` and `post` of an `Io.Semaphore` with one permit; `main` joins the kid and reads 4.
The `SemCounter` (block 0, 48 bytes, align 8): `io` at 0, the semaphore at 16 (its count at 16,
its mutex at 24, its condition's state and epoch at 28 and 32), `n` at 40. This file is the
protocol of that program for every implementation of the semaphore (`SemImpl`): the proof uses
only the contract, with the semaphore component `FSem` (`ZigLean/Sep/Full/Sem.lean`).

- **Ghost values** (`Gh = FLG × X`): the mutex's part (`FLG`), and `X`: the thread's place in the
  program (`Ph`: its increments, if it has the permit, and with the permit the value of `n` it
  took), its place in the condition's code (`CPh`) and in the semaphore's (`SPh`).
- **The mutex** (`L`, `FLock.prod`) owns the count and the pool (`R`, `FSem.R_eq`): the count is
  1 while no thread has the permit, else 0 (`pv`), and the free permit owns `n`, with the
  increments of both threads (`Pool`). The thread that took the permit owns `n` in its part.
- **The rest `U`**: the threads (`Shape`), the read shares of `io`, the cells of the condition's
  words, the invariants of the condition and the semaphore, at most one holder of the permit
  (`one`), whose recorded value is the increments of both threads (`tot`); only a thread without
  the permit and with increments left waits (`wtx`, the waiting role `wx`); and the window
  (`FCond.Win`): every epoch write happened before the mutex's holder (`ehb`), a waiter at its
  load saves the newest one (`f0`), and while a waiter is registered at most one post and so at
  most one epoch write happens (`f2`, `f3`, `f4`, `incS`, `rc`).
-/

namespace Zig
namespace SemCounter

open Conc Conc.Proto Full Full.FAssn

/-- Where a thread is in the program (module doc). -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- A thread in `semWork`: it did `k` increments; `hold`: it has the permit, with `s` the
  value of `n` while it has it. -/
  | work (k : Nat) (hold : Bool) (s : Nat)
  /-- `main` at its join. -/
  | joins
  /-- The kid has ended. -/
  | fin
  deriving DecidableEq

/-- The increments of a thread. -/
def Ph.count : Ph → Nat
  | .work k _ _ => k
  | .joins | .fin => 2
  | _ => 0

/-- The thread has the permit. -/
def Ph.holds : Ph → Bool
  | .work _ b _ => b
  | _ => false

/-- A thread's places (module doc). -/
structure X where
  ph : Ph := .none
  c : CPh := .out
  sp : SPh := .out

abbrev Gh := FLG × X

/-- The `SemCounter` (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩
/-- `n`. -/
def nPtr : Ptr := cPtr.add 40

/-- The increments of both threads. -/
def sum (Y : ThreadId → Ph) : Nat := (Y 0).count + (Y 1).count

/-- A thread has the permit. -/
def held (Y : ThreadId → Ph) : Bool := (Y 0).holds || (Y 1).holds

/-- The count: 1 while no thread has the permit. -/
def pv (Y : ThreadId → Ph) : BitVec 64 := if held Y then 0 else 1

/-- The free permit owns `n`, with the increments of both threads. -/
def Pool (Y : ThreadId → Ph) : FAssn :=
  if held Y then emp else up (pts nPtr 4 (BitVec.ofNat 32 (sum Y)))

/-- The mutex's resource: the count and the pool. -/
def R (Y : ThreadId → X) : FAssn :=
  up (pts (cPtr.add 16) 8 (pv fun u => (Y u).ph)) ⋆ Pool fun u => (Y u).ph

/-- The semaphore's mutex (`ioMutex.c = 2`). -/
abbrev L : FLock Gh := FLock.prod 0 24 R 2 (by decide)

/-- The condition's state and epoch. -/
def WS : Word 32 4 := { b := 0, o := 28 }
def WE : Word 32 4 := { b := 0, o := 32 }

/-- The bytes of the condition's two words: `28 .. 36`. -/
def BoxW (l : Zig.Loc) : Prop := l.1 = 0 ∧ 28 ≤ l.2 ∧ l.2 < 36

instance (l : Zig.Loc) : Decidable (BoxW l) := by unfold BoxW; infer_instance

/-- The condition: its place is `X.c`; the threads at `pst` signal (`FSem.sx_iff`). -/
def C : FCond Gh where
  S := WS
  Ep := WE
  ep_b := rfl
  ep_o := rfl
  ph g := g.2.c
  set g p := (g.1, { g.2 with c := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  sx g := g.2.sp.isPst = true
  sx_set _ _ := Iff.rfl

/-- The waiting role: a thread without the permit with increments left. -/
def Wx (p : Ph) : Prop := ∃ k s, k < 2 ∧ p = .work k false s

/-- The semaphore: its place is `X.sp`, its client part `X.ph`. -/
def S : FSem Gh Ph L C where
  ph g := g.2.sp
  set g s := (g.1, { g.2 with sp := s })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  p := cPtr.add 16
  ptr_l := rfl
  ptr_c := rfl
  off := by decide
  x g := g.2.ph
  pv := pv
  Pool := Pool
  R_eq _ := rfl
  x_l _ _ _ := rfl
  x_part _ _ := rfl
  x_c _ _ := rfl
  x_s _ _ := rfl
  wx g := Wx g.2.ph
  wx_l _ _ _ := Iff.rfl
  wx_part _ _ := Iff.rfl
  wx_c _ _ := Iff.rfl
  wx_s _ _ := Iff.rfl
  cph_set _ _ := rfl
  ph_cset _ _ := rfl
  set_cset _ _ _ := rfl
  sx_iff _ := Iff.rfl

/-- The threads that run the lock's code: out of the condition's busy code and out of `pst`. -/
def ok (g : Gh) : Prop := (g.2.c).busy = false ∧ (g.2.sp = .out ∨ g.2.sp = .wt)

/-- The accesses to the bytes of `io` (`0 .. 16`; a zero-length access touches none). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ 0 < e.len ∧ e.off < 16

/-- The bytes of `io` and the `SemCounter`'s full extent, in the protocol's rest. The extent pins
the block for every thread's step, so the cells of the condition's words in the rest are the
memory's at every stop. -/
def IoRest (r : Res) : Prop :=
  ∃ A bs, A % 8 = 0 ∧ bs.size = 16 ∧ Enc.decode bs = pure (⟨⟩ : Io) ∧
    (up (bytesAt cPtr A 48 .stack bs) ⋆ bext 0 48 .stack) r

/-- The protocol's rest `rX`: the cells of the condition's words, and `io`. -/
def Rest (rX : Res) (m : Mem) : Prop :=
  ∃ rIO, IoRest rIO ∧ (∀ l, BoxW l → rIO.heap l = none) ∧ rX = rsum (cellsAt BoxW m) rIO

/-- Block 0 is the live `SemCounter`, 48 bytes on the stack. -/
def BlkOk (m : Mem) : Prop :=
  ∃ blk, m.blocks[0]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 48 ∧ blk.kind = .stack

/-- The threads: `main` alone before its spawn; then `main` and the kid, which `main` spawned and
did not join yet. -/
def Shape (Y : ThreadId → Ph) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ Y 0 = .pre ∧ ∀ u, 1 ≤ u → Y u = .none) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (Y 0 = .joins ∨ ∃ k ≤ 2, ∃ b s, Y 0 = .work k b s) ∧
    (Y 1 = .fin ∨ ∃ k ≤ 2, ∃ b s, Y 1 = .work k b s) ∧
    ∀ u, 2 ≤ u → Y u = .none))

/-- The client parts of the ghost values. -/
abbrev xs (G : ThreadId → Gh) : ThreadId → Ph := fun u => (G u).2.ph

/-- The memory's part of the rest of the invariant: the threads, `io`, the rest's cells, the
block, the condition's words and the futex queue. -/
structure UM (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (xs G) m
  io : ReadShared IoR m
  rest : Rest rX m
  blk : BlkOk m
  ws : WS.Ok m
  we : WE.Ok m
  /-- A thread waits only at the mutex or at the epoch. -/
  q : ∀ w ∈ m.waiters, w.2 = L.ptr ∨ w.2 = WE.ptr

/-- The client's part of the rest of the invariant: the permit and the window (module doc). -/
structure Lg (G : ThreadId → Gh) (m : Mem) : Prop where
  /-- At most one thread has the permit. -/
  one : (G 0).2.ph.holds = false ∨ (G 1).2.ph.holds = false
  /-- The permit's holder recorded the increments of both threads. -/
  tot : ∀ u k s, (G u).2.ph = .work k true s → s = sum (xs G)
  /-- Only the waiting role waits for a permit. -/
  wtx : ∀ u, (G u).2.sp = .wt → Wx (G u).2.ph
  /-- Every epoch write happened before the mutex's holder (`FCond.ld_newest`). -/
  ehb : L.WordHB WE G m
  /-- A waiter at its load saved the newest epoch write. -/
  f0 : ∀ u i e, (G u).2.c = .ld i e → (WE.hist m).size = i + 1
  /-- No thread is in the condition's critical code while one is registered. -/
  rc : ∀ u v, ((G u).2.c).isReg = true → ((G v).2.c).crit = true → False
  /-- While a waiter is registered, at most one epoch write happens after its saved one. -/
  f2 : ∀ u i jr sn e, (G u).2.c = .reg i jr sn e → (WE.hist m).size ≤ i + 2
  /-- … none yet while a signaller is between its post and its epoch write … -/
  f3 : ∀ u i jr sn e v q n h, (G u).2.c = .reg i jr sn e → (G v).2.c = .inc q n h →
    (WE.hist m).size ≤ i + 1
  /-- … and after it every registered waiter is signalled, so no post follows. -/
  f4 : ∀ u i jr sn e, (G u).2.c = .reg i jr sn e → (WE.hist m).size = i + 2 → C.Sated m
  /-- After a post, every registered waiter is signalled. -/
  incS : ∀ v q n h, (G v).2.c = .inc q n h → C.Sated m

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  um : UM G rX m
  cinv : C.Inv L G m
  sinv : S.Inv G m
  lg : Lg G m

variable {Tgt : Type}

/-- The protocol, in strict mode; `semOf` reads the kid's argument from a spawn target. -/
def proto (semOf : Tgt → Option Ptr) : Proto Tgt Gh where
  inv G m := ∃ rX, L.Inv G rX m ∧ U G rX m
  init tgt g := semOf tgt = some cPtr ∧ ∃ rp, plain rp ∧
    g = (⟨.out, rp, rnil⟩, { ph := .work 0 false 0 })
  fin g := g.1.ph = .gone ∧ g.2 = { ph := .fin }
  strict := true
  joins g := g.1.ph = .out ∧ g.2 = { ph := .joins }

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 4 ∧ joinedAll 0 m

end SemCounter
end Zig
