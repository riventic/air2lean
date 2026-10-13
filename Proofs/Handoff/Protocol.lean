import Proofs.Handoff.Layout
import ZigLean.Sep.Full.Cond
import ZigLean.Sep.Full.Mutex
import ZigLean.Conc.Share

/-!
# The protocol of `handoff`, once for every version

`handoff` (`Proofs/Handoff/Layout.lean`): `main` spawns a producer, locks the mutex and waits on
the condition until `ready`, reads `v`, unlocks, waits on the event and joins the producer. The
producer locks the mutex, stores `v = 7` and `ready = true`, unlocks, signals the condition and
sets the event. This file is the protocol of that program for every layout (`Layout`) and every
implementation of the three sync objects (`MutexImpl`, `CondImpl`, `EventImpl`): the program's
proof uses only their contracts, and each version's file walks `main` and the producer of its
generated code with the steps here.

- **Ghost values** (`Gh = FLG × X`): the lock's part (`FLG`), and `X`: the thread's place in the
  program (`Ph`), its place in the condition's code (`CPh`) and in the event's (`EPh`). `main`
  is `run` for the whole loop of the condition (the condition's place says where it is inside
  `wait`), and `ev` in the event's `wait`.
- **The lock** (`L`, `FLock.prod`): the mutex owns `v` and `ready`, whose values follow from the
  producer's place (`vOf`, `rdyOf`).
- **The condition** (`C`) and **the event** (`E`): their words are in the protocol's rest (with
  `io` for 0.16.0: read-shared); their invariants (`FCond.Inv`, `FEvent.Inv`) are part of `U`.
  Only the producer signals (`FCond.sx`); only `main` waits at the event (`FEvent.wx`).
- **The rest `U`**: the threads (`Shape`), and what the contracts' client premises need: the
  epoch has its first write only, which `main` made, until the producer signals (`ep1`, `ep0`:
  `hhb`); while `main` is in the condition's critical code the producer is before its lock
  (`ent`: `hent`, and from it `hone`); `main`'s registration happened before the producer
  (`reg`: `hseen`, through the mutex's release and acquire); after the producer's signal a
  registered `main` is signalled (`lvc`), and after its end the event is set (`fin`): `hlive`.
-/

namespace Zig
namespace Handoff

open Conc Conc.Proto Full Full.FAssn

/-- Where a thread is in the program (module doc). -/
inductive Ph where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` from its spawn to its unlock (the condition's loop). -/
  | run
  /-- `main` after its unlock, in the event's `wait`. -/
  | ev
  /-- `main` at its join. -/
  | joins
  /-- The producer before (or in) its lock. -/
  | lk
  /-- The producer holds the mutex. -/
  | hl
  /-- The producer stored `v = 7`. -/
  | v7
  /-- The producer stored `ready = true` (until it signals). -/
  | rdy
  /-- The producer in `signal`. -/
  | sg
  /-- The producer in the event's `set`. -/
  | st
  /-- The producer at its end. -/
  | fin
  deriving DecidableEq

namespace Ph

/-- `main`'s places. -/
def isMain : Ph → Bool
  | .pre | .run | .ev | .joins => true
  | _ => false

/-- The producer's places. -/
def isProd : Ph → Bool
  | .lk | .hl | .v7 | .rdy | .sg | .st | .fin => true
  | _ => false

/-- The producer stored `v`. -/
def hasV : Ph → Bool
  | .v7 | .rdy | .sg | .st | .fin => true
  | _ => false

/-- The producer stored `ready`. -/
def hasR : Ph → Bool
  | .rdy | .sg | .st | .fin => true
  | _ => false

/-- The producer is in or after its `signal`. -/
def sigd : Ph → Bool
  | .sg | .st | .fin => true
  | _ => false

end Ph

/-- A thread's places (module doc). -/
structure X where
  ph : Ph := .none
  c : CPh := .out
  e : EPh := .out

abbrev Gh := FLG × X

variable (Lo : Layout)

/-- `v`, from the producer's place. -/
def vOf (x : X) : Nat := if x.ph.hasV then 7 else 0

/-- The mutex's resource: `v` and `ready`, from the producer's place. -/
def R (Y : ThreadId → X) : FAssn :=
  up (pts (bPtr.add Lo.xo) 4 (BitVec.ofNat 32 (vOf (Y 1)))) ⋆
    up (pts (bPtr.add Lo.ro) 1 (Y 1).ph.hasR)

/-- The mutex. -/
abbrev L : FLock Gh := FLock.prod 0 Lo.mo (R Lo) Lo.c Lo.c_ok

/-- The condition: its place is `X.c`; the producer signals. -/
def C : FCond Gh where
  S := Lo.WS
  Ep := Lo.WE
  ep_b := rfl
  ep_o := rfl
  ph g := g.2.c
  set g p := (g.1, { g.2 with c := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  sx g := g.2.ph.isProd
  sx_set _ _ := Iff.rfl

/-- The event: its place is `X.e`; `main` waits. -/
def E : FEvent Gh where
  W := Lo.WV
  ph g := g.2.e
  set g p := (g.1, { g.2 with e := p })
  ph_set _ _ := rfl
  set_set _ _ _ := rfl
  set_self _ := rfl
  wx g := g.2.ph.isMain
  wx_set _ _ := Iff.rfl

/-- The threads that run the lock's code: out of the condition's busy code and of the event's
code, and not the producer while it holds the mutex (`Full/Cond.lean`, `CPh.busy`). -/
def ok (g : Gh) : Prop :=
  (g.2.c).busy = false ∧ g.2.e = .out ∧ g.2.ph ≠ .hl ∧ g.2.ph ≠ .v7

/-- The accesses to the bytes of `io` (`0 .. io` of the `Box`). -/
def IoR (e : FootprintEntry) : Prop := e.block = 0 ∧ e.off < Lo.io

/-- The bytes of `io`, in the protocol's rest. -/
def IoRest (r : Res) : Prop :=
  ∃ A bs, A % Lo.align = 0 ∧ bs.size = Lo.io ∧ up (bytesAt bPtr A Lo.size .stack bs) r

/-- The protocol's rest `rX`: the cells of the condition's and the event's words, and `io`. -/
def Rest (rX : Res) (m : Mem) : Prop :=
  ∃ rIO, IoRest Lo rIO ∧ (∀ l, Lo.BoxW l → rIO.heap l = none) ∧
    rX = rsum (cellsAt Lo.BoxW m) rIO

/-- The threads: `main` alone before its spawn; then `main` and the producer, which `main`
spawned and did not join yet. -/
def Shape (Y : ThreadId → X) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧
  ((m.threads.size = 1 ∧ Y 0 = { ph := .pre } ∧ ∀ u, 1 ≤ u → Y u = {}) ∨
   (m.threads.size = 2 ∧ m.threads[1]? = some { spawner := 0, joined := false } ∧
    (Y 0).ph.isMain ∧ (Y 0).ph ≠ .pre ∧ (Y 1).ph.isProd ∧ ∀ u, 2 ≤ u → Y u = {}))

/-- The rest of the invariant (module doc). -/
structure U (G : ThreadId → Gh) (rX : Res) (m : Mem) : Prop where
  shape : Shape (fun u => (G u).2) m
  io : ReadShared (IoR Lo) m
  rest : Rest Lo rX m
  ws : Lo.WS.Ok m
  we : Lo.WE.Ok m
  wv : Lo.WV.Ok m
  cinv : (C Lo).Inv (L Lo) G m
  einv : (E Lo).Inv (L Lo) G m
  /-- The producer does not wait at the condition. -/
  places : ((G 1).2.c).waits = false
  /-- Until the producer signals, the epoch has its first write, which `main` made. -/
  ep1 : (G 1).2.ph.sigd = false → (Lo.WE.hist m).size = 1
  ep0 : VClock.le (Lo.WE.hist m)[0]!.clock (m.clocks[0]!) = true
  /-- `main` in the condition's critical code: the producer is before its lock. -/
  ent : ((G 0).2.c).crit → (G 1).2.ph = .lk
  /-- The producer holds the mutex between its lock and its store of `ready`. -/
  hold : (G 1).2.ph = .hl ∨ (G 1).2.ph = .v7 → (G 1).1.ph = .holds
  /-- `main`'s registration happened before the producer, or before the mutex's release while
  the producer is before its lock. -/
  reg : ∀ i jr sn e, (G 0).2.c = .reg i jr sn e →
    VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[1]!) = true ∨
    ((G 1).2.ph = .lk ∧ (((G 0).1.ph = .holds ∧
      VClock.le (Lo.WS.hist m)[jr]!.clock (m.clocks[0]!) = true) ∨
      (L Lo).Before m (Lo.WS.hist m)[jr]!.clock))
  /-- After the producer's signal, a registered `main` is signalled. -/
  lvc : ((G 0).2.c).waits → (G 1).2.ph = .st ∨ (G 1).2.ph = .fin → (C Lo).Signalled m
  /-- After the producer's end, the event is set. -/
  fin : (G 1).2.ph = .fin → (E Lo).IsSet m
  /-- A thread waits only at the mutex, the epoch or the event. -/
  q : ∀ w ∈ m.waiters, w.2 = (L Lo).ptr ∨ w.2 = Lo.WE.ptr ∨ w.2 = Lo.WV.ptr

variable {Tgt : Type}

/-- The protocol, in strict mode; `prodOf` reads the producer's argument from a spawn target. -/
def proto (prodOf : Tgt → Option Ptr) : Proto Tgt Gh where
  inv G m := ∃ rX, (L Lo).Inv G rX m ∧ U Lo G rX m
  init tgt g := prodOf tgt = some bPtr ∧ g = (⟨.out, rnil, rnil⟩, { ph := .lk })
  fin g := g.1.ph = .gone ∧ g.2.ph = .fin
  strict := true
  joins g := g.1.ph = .out ∧ g.2.ph = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => v = .ok 7 ∧ joinedAll 0 m

end Handoff
end Zig
