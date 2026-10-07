import IdleLoop.Mem

/-!
# The scheduler states of the client

Between two turns each thread waits at one of finitely many stops of its code
(`MainAt`, `WorkerAt`); `At` adds the memory invariant and enough depth for the next stop.
This file also unfolds the runs from each stop to the next one.
-/

namespace IdleLoop.Client

open Zig Zig.Conc Zig.Conc.Proto

/-! ## The stops -/

/-- The worker after its acquire load. -/
def wAfter (c : Nat) : ConcM Tgt Unit :=
  ConcM.liftMem (atomicLoadAt (n := 32) c .acquire 4 fPtr) >>= fun v =>
    if v == 0 then (syncYield >>= fun _ => syncChoose 2 >>= fun _ => wLoop) else check

/-- The worker after its spin hint. -/
def wSpun : ConcM Tgt Unit := syncChoose 2 >>= fun _ => wLoop

/-- Where `main` waits: at the release store's pick, or at the join of the worker. -/
inductive MainAt where
  | store
  | join
  deriving DecidableEq

/-- Where the worker is: not started, at the load's pick, at the spin hint, at the yield, or
ended. -/
inductive WorkerAt where
  | start
  | load
  | spin
  | yld
  | done
  deriving DecidableEq

def mainP : MainAt → Nat → Sched.Paused Tgt Unit
  | .store, d => ⟨d, .pick storeCnt, fun c m => mainStore c 1 d m⟩
  | .join, d => ⟨d, .join 1, fun _ m => .leaf (some (.ok ((), m)))⟩

def workerTS : WorkerAt → Nat → Sched.TS Tgt Unit
  | .start, d => .paused ⟨d, .yield, fun _ m => dispatch .worker d m⟩
  | .load, d => .paused ⟨d, .pick loadCnt, fun c m => wAfter c d m⟩
  | .spin, d => .paused ⟨d, .yield, fun _ m => wSpun d m⟩
  | .yld, d => .paused ⟨d, .choose 2, fun _ m => wLoop d m⟩
  | .done, _ => .done

/-- After `main`'s store: `main` waits at its join. -/
def MainAt.stored : MainAt → Bool
  | .store => false
  | .join => true

/-- A state between two turns with `fuel` turns left: the two stops, the memory invariant, and
depths that reach the next stop (`main`'s spawn turn leaves it one stop behind the worker). -/
def At (fuel : Nat) (mp : MainAt) (wp : WorkerAt) (s : Sched.State Tgt Unit) : Prop :=
  ∃ d dw, s.main = .paused (mainP mp d) ∧ s.kids = #[workerTS wp dw] ∧ Inv mp.stored s.mem ∧
    fuel ≤ d + 1 ∧ fuel ≤ dw ∧ (wp = .done → mp = .join)

/-! ## The runs at the stops -/

theorem wLoop_succ (d : Nat) (m : Mem) :
    wLoop (d + 1) m = .sync (.pick loadCnt) m fun c m' => wAfter c d m' := by
  rw [wLoop_eq]; rfl

theorem worker_succ (d : Nat) (m : Mem) :
    dispatch .worker (d + 1) m = .sync (.pick loadCnt) m fun c m' => wAfter c d m' := by
  show worker (d + 1) m = _
  rw [worker_eq]; exact wLoop_succ d m

theorem wAfter_zero {c d : Nat} {m m' : Mem}
    (h : ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m).run = some (.ok (0, m'))) :
    wAfter c (d + 1) m = .sync .yield m' fun _ m'' => wSpun d m'' := by
  show (CoN.leaf ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m)).bind _ = _
  rw [show (atomicLoadAt (n := 32) c .acquire 4 fPtr).run m = ExceptT.mk (some (.ok (0, m'))) from h]
  rfl

theorem wAfter_one {c d : Nat} {m m' : Mem}
    (h : ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m).run = some (.ok (1, m'))) :
    wAfter c d m = check d m' := by
  show (CoN.leaf ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m)).bind _ = _
  rw [show (atomicLoadAt (n := 32) c .acquire 4 fPtr).run m = ExceptT.mk (some (.ok (1, m'))) from h]
  rfl

theorem check_run {d : Nat} {m : Mem} (hi : Inv true m) (hc : m.current = 1)
    (hle : DataLe m (m.clocks[1]!)) :
    check d m = .leaf (some (.ok ((), m.recordAt 0 0 4 .read))) := by
  show (CoN.leaf ((load (BitVec 32) 4 dPtr).run m)).bind _ = _
  rw [(read_run hi hc hle).1]
  rfl

theorem mainStore_succ {c d : Nat} {m m' : Mem}
    (h : ((atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m).run = some (.ok ((), m'))) :
    mainStore c 1 (d + 1) m = .sync (.join 1) m' fun _ m'' => .leaf (some (.ok ((), m''))) := by
  show (CoN.leaf ((atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m)).bind _ = _
  rw [show (atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m = ExceptT.mk (some (.ok ((), m'))) from h]
  rfl

end IdleLoop.Client
