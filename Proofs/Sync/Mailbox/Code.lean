import Proofs.Sync.Gen
import ZigLean.Sep.Full.Sem

/-!
# The mailbox: its code and its sync objects

A model client written in Lean (it is not a Zig export): a block (block 0, 32 bytes, 8-aligned)
holds an `Io.Semaphore` with no permit (bytes 0..24: the permit count at 0, its mutex at 8, its
condition's state and epoch at 12 and 16, padding at 20) and a two-field message `a` (24..28),
`b` (28..32). `main` stores zeros, spawns a producer and hands it the message cells. The producer
writes `a = 3`, `b = 4` and `post`s; `main` `wait`s, reads both fields, joins the producer and
returns `10 * a + b`. The code takes the semaphore as a `SemImpl` (`I.wait`, `I.post`): the proof
uses only that contract (`ZigLean/Sep/Full/Sem.lean`), and the results instantiate it with the
translated std semaphore (`Sync.ioSem`, `Proofs/Sync/IoSemaphore.lean`).

The sync objects, for every mutex value `c` of the semaphore's mutex (`Cfg`):
- **Ghost values** (`Gh = FLG × X`): the lock's part (`FLG`), and `X`: the thread's place in the
  program (`Ph`), in the condition's code (`CPh`) and in the semaphore's (`SPh`).
- **The mutex** (`L`, `FLock.prod` at byte 8): it owns the permit count and the free permit's
  resource, the written message while the producer posted and `main` has not taken it (`avail`).
- **The condition** (`C`, state at 12, epoch at 16): the signallers are the threads at the
  semaphore's `pst` (`FSem.sx_iff`).
- **The semaphore** (`S`, at byte 0): its client part is the program place (`Ph`); only `main`
  before its take waits (`wx`, ledger row `sem-wait-role`).
-/

open Zig Zig.Conc Zig.Full Zig.Full.FAssn

namespace Sync.Mailbox

/-- The semaphore with no permit. -/
def semZ : Io_Semaphore :=
  { mutex := ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex),
    cond := ({ state := ({ raw := (Packed.ofBits (0 : BitVec 32) : Io_Condition_State) } :
      atomic_Value_Io_Condition_State), epoch := ({ raw := (0 : BitVec 32) } : atomic_Value_u32) } :
      Io_Condition),
    permits := (0 : BitVec 64) }

/-! ## The code -/

section Code

variable (I : SemImpl Tgt)

/-- The producer: write the message, then `post`. -/
def producer (p : Ptr) : ConcM Tgt Unit :=
  (do
    Zig.store (α := BitVec 32) 4 (p.add 24) 3
    Zig.store (α := BitVec 32) 4 (p.add 28) 4
    callC (I.post p ⟨⟩) : CM Tgt Unit Unit).run' ()

/-- The spawn targets: `semWork p` runs the producer. -/
def dispatch : Tgt → ConcM Tgt Unit
  | .semWork p => producer I p
  | _ => pure ()

/-- `main`: build the mailbox, spawn the producer, `wait`, read the message, join, free. -/
def mailMain (io : Io) : ConcM Tgt (Except ErrName (BitVec 32)) := do
  let s1 ← Zig.allocStack 32 8
  let e ← ((do
    Zig.store (α := Io_Semaphore) 8 (s1.add 0) semZ
    Zig.store (α := BitVec 32) 4 (s1.add 24) 0
    Zig.store (α := BitVec 32) 4 (s1.add 28) 0
    let t ← Zig.spawnC (Tgt.semWork s1)
    match t with
    | .error e => pure (.error e)
    | .ok tid => do
      callC (I.wait s1 io)
      let x ← Zig.load (BitVec 32) 4 (s1.add 24)
      let y ← Zig.load (BitVec 32) 4 (s1.add 28)
      Zig.joinC tid
      pure (.ok (10 * x + y))) : CM Tgt Unit (Except ErrName (BitVec 32))).run' ()
  Zig.free s1
  pure e

end Code

/-! ## The ghost values -/

/-- Where a thread is in the program (module doc). -/
inductive Ph where
  | none
  /-- `main` before its spawn: it owns the message cells. -/
  | pre
  /-- `main` from its spawn to its take of the permit (in `wait`). -/
  | wt
  /-- `main` took the permit and the message. -/
  | got
  /-- `main` at its join. -/
  | joins
  /-- The producer wrote `k` of the two fields. -/
  | pr (k : Nat)
  /-- The producer gave the message to the permit (from its `post`'s store of the count on). -/
  | pd
  /-- The producer has ended. -/
  | fin
  deriving DecidableEq

/-- The producer posted. -/
def Ph.posted : Ph → Bool
  | .pd | .fin => true
  | _ => false

/-- `main` took the permit. -/
def Ph.took : Ph → Bool
  | .got | .joins => true
  | _ => false

/-- A thread's places (module doc). -/
structure X where
  ph : Ph := .none
  c : CPh := .out
  s : SPh := .out

abbrev Gh := FLG × X

/-! ## The layout -/

/-- The mailbox (block 0). -/
def cPtr : Ptr := ⟨some 0, 0⟩
def aPtr : Ptr := cPtr.add 24
def bPtr : Ptr := cPtr.add 28

/-- The condition's state and epoch. -/
def WS : Word 32 4 := { b := 0, o := 12 }
def WE : Word 32 4 := { b := 0, o := 16 }

/-- The bytes of the condition's two words: `12 .. 20`. -/
def BoxW (l : Zig.Loc) : Prop := l.1 = 0 ∧ 12 ≤ l.2 ∧ l.2 < 20

instance (l : Zig.Loc) : Decidable (BoxW l) := by unfold BoxW; infer_instance

theorem ws_box {l : Zig.Loc} (h : WS.In l) : BoxW l := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by simp [WS] at h3; omega⟩

theorem we_box {l : Zig.Loc} (h : WE.In l) : BoxW l := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by simp [WE] at h2; omega, by simp [WE] at h3; omega⟩

/-! ## The sync objects -/

/-- The permit is free: posted and not taken. -/
def avail (Y : ThreadId → Ph) : Bool := (Y 1).posted && !(Y 0).took

/-- The permit count. -/
def pv (Y : ThreadId → Ph) : BitVec 64 := if avail Y then 1 else 0

/-- The message after `k` of the producer's two stores. -/
def Msg (k : Nat) : FAssn :=
  up (pts aPtr 4 (if 1 ≤ k then (3 : BitVec 32) else 0)) ⋆
    up (pts bPtr 4 (if 2 ≤ k then (4 : BitVec 32) else 0))

/-- The free permit's resource: the written message while it is available. -/
def Pool (Y : ThreadId → Ph) : FAssn := if avail Y then Msg 2 else emp

/-- The mutex's resource: the count and the free permit's resource. -/
def R (Y : ThreadId → X) : FAssn :=
  up (pts cPtr 8 (pv fun u => (Y u).ph)) ⋆ Pool fun u => (Y u).ph

/-- The semaphore's mutex: its contended value (module doc). -/
structure Cfg where
  c : Nat
  c_ok : c = 1 ∨ c = 2 ∨ c = 3

variable (K : Cfg)

/-- The mutex (byte 8). -/
abbrev L : FLock Gh := FLock.prod 0 8 R K.c K.c_ok

/-- The condition: its place is `X.c`; the threads at the semaphore's `pst` signal. -/
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
  sx g := (g.2.s).isPst = true
  sx_set _ _ := Iff.rfl

/-- The semaphore (byte 0): its place is `X.s`, its client part `X.ph`; `main` waits. -/
def S : FSem Gh Ph (L K) C where
  ph g := g.2.s
  set g s := (g.1, { g.2 with s := s })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  p := cPtr
  ptr_l := by simp [cPtr, LockWord.ptr, FLock.prod, Ptr.add]
  ptr_c := by simp [cPtr, Word.ptr, C, WS, Ptr.add]
  off := by simp [FLock.prod]
  x g := g.2.ph
  pv := pv
  Pool := Pool
  R_eq _ := rfl
  x_l _ _ _ := rfl
  x_part _ _ := rfl
  x_c _ _ := rfl
  x_s _ _ := rfl
  wx g := g.2.ph = .wt
  wx_l _ _ _ := Iff.rfl
  wx_part _ _ := Iff.rfl
  wx_c _ _ := Iff.rfl
  wx_s _ _ := Iff.rfl
  cph_set _ _ := rfl
  ph_cset _ _ := rfl
  set_cset _ _ _ := rfl
  sx_iff _ := Iff.rfl

/-- The threads that run the lock's code: out of the condition's busy code and out of `pst`. -/
def ok (g : Gh) : Prop := (g.2.c).busy = false ∧ (g.2.s = .out ∨ g.2.s = .wt)

end Sync.Mailbox
