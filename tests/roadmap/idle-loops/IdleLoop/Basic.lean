import IdleLoop.Gen
import ZigLean.Conc.Lemmas

/-!
# A worker idle loop and its setter

`IdleLoop.idle` is the checked translation of `progress.idle`
(`tests/roadmap/progress/progress.zig`): an acquire load of a `u32` flag, then
`std.atomic.spinLoopHint()` and `std.Thread.yield() catch {}` while the flag is 0.

The translated module has no spawn target, so its `Tgt` is empty. `retarget` maps the run of
a function into another spawn-target type. It keeps every sync op, memory and result. The
client below runs the translated loop in a spawned worker:

- `main` (thread 0) spawns the worker, writes 42 to `data` (a plain write), and stores 1 to
  `flag` with `.release`; then it joins the worker.
- The worker (thread 1) runs the translated idle loop on `flag`, then reads `data`. A value
  other than 42 is a panic, so a run without an error never observed a stale `data`.

`data` and `flag` are zero-initialized `u32` globals (blocks 0 and 1). The client is a
hand-written scheduler harness around the translated loop, not a translated source program.
`wLoop_eq` unfolds one iteration of the translated loop: the acquire load (a scheduler stop
whose response picks the message), then the spin hint (a scheduler stop) and the yield (a
stop with two outcomes) when the flag is 0.
-/

namespace IdleLoop.Client

open Zig

/-! ## Sync ops with their response types -/

/-- `ConcM.sync` with its response type unfolded. Rewriting with these avoids motives that are
type-correct only after unfolding `SyncOp.Resp`. -/
def syncPick {T : Type} (c : Mem → Nat) : ConcM T Nat := ConcM.sync (.pick c)
def syncYield {T : Type} : ConcM T Unit := ConcM.sync .yield
def syncChoose {T : Type} (k : Nat) : ConcM T Nat := ConcM.sync (.choose k)
def syncJoin {T : Type} (tid : ThreadId) : ConcM T Unit := ConcM.sync (.join tid)
def syncSpawn {T : Type} (t : T) : ConcM T (Except ErrName ThreadId) := ConcM.sync (.spawn t)

theorem pickC_eq {T σ : Type} (c : Mem → Nat) :
    (pickC c : CM T σ Nat) = StateT.lift (syncPick c) := rfl
theorem spinLoopHintC_eq {T σ : Type} : (spinLoopHintC : CM T σ Unit) = StateT.lift syncYield := rfl
theorem threadYieldC_eq {T σ : Type} : (threadYieldC : CM T σ (Except ErrName Unit)) =
    StateT.lift (syncChoose 2 >>= fun c => pure (threadYieldResult c)) := rfl

theorem bindC {T α β : Type} {x : ConcM T α} {f g : α → ConcM T β} (h : ∀ a, f a = g a) :
    x >>= f = x >>= g := congrArg (x >>= ·) (funext h)

theorem run_ite {σ α : Type} {m : Type → Type} (c : Prop) [Decidable c] (x y : StateT σ m α)
    (s : σ) : (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

/-! ## Moving a run to another spawn-target type -/

/-- A run with every spawn target mapped by `f`: the same ops, memories, responses and
results. -/
def treeMap {T T' α : Type} (f : T → T') : {n : Nat} → CoN T α n → CoN T' α n
  | _, .leaf r => .leaf r
  | _, .sync .yield m k => .sync .yield m fun r m' => treeMap f (k r m')
  | _, .sync (.choose c) m k => .sync (.choose c) m fun r m' => treeMap f (k r m')
  | _, .sync (.pick c) m k => .sync (.pick c) m fun r m' => treeMap f (k r m')
  | _, .sync (.spawn t) m k => .sync (.spawn (f t)) m fun r m' => treeMap f (k r m')
  | _, .sync .asyncChoice m k => .sync .asyncChoice m fun r m' => treeMap f (k r m')
  | _, .sync (.spawnGated t) m k => .sync (.spawnGated (f t)) m fun r m' => treeMap f (k r m')
  | _, .sync .gate m k => .sync .gate m fun r m' => treeMap f (k r m')
  | _, .sync (.join tid) m k => .sync (.join tid) m fun r m' => treeMap f (k r m')
  | _, .sync (.wait p e) m k => .sync (.wait p e) m fun r m' => treeMap f (k r m')
  | _, .sync (.wake p c) m k => .sync (.wake p c) m fun r m' => treeMap f (k r m')

/-- `x` with every spawn target mapped by `f`. -/
def retarget {T T' α : Type} (f : T → T') (x : ConcM T α) : ConcM T' α :=
  fun n m => treeMap f (x n m)

theorem treeMap_bind {T T' α β : Type} (f : T → T') {n : Nat} (x : CoN T α n)
    (g : α → (k : Nat) → CoN T β k) :
    treeMap f (x.bind g) = (treeMap f x).bind fun a k => treeMap f (g a k) := by
  induction x with
  | leaf r => rcases r with _ | _ | a <;> rfl
  | sync op m k ih =>
    cases op <;> simp only [CoN.bind, treeMap] <;> congr <;> funext r m' <;> exact ih r m'

theorem retarget_bind {T T' α β : Type} (f : T → T') (x : ConcM T α) (g : α → ConcM T β) :
    retarget f (x >>= g) = retarget f x >>= fun a => retarget f (g a) := by
  funext n m
  exact treeMap_bind f (x n m) _

theorem retarget_pure {T T' α : Type} (f : T → T') (a : α) :
    retarget f (pure a : ConcM T α) = pure a := rfl

theorem retarget_liftMem {T T' α : Type} (f : T → T') (x : MemM α) :
    retarget f (ConcM.liftMem x : ConcM T α) = ConcM.liftMem x := rfl

theorem retarget_syncPick {T T' : Type} (f : T → T') (c : Mem → Nat) :
    retarget f (syncPick c : ConcM T Nat) = syncPick c := by
  funext n m; cases n <;> rfl

theorem retarget_syncYield {T T' : Type} (f : T → T') :
    retarget f (syncYield : ConcM T Unit) = syncYield := by
  funext n m; cases n <;> rfl

theorem retarget_syncChoose {T T' : Type} (f : T → T') (k : Nat) :
    retarget f (syncChoose k : ConcM T Nat) = syncChoose k := by
  funext n m; cases n <;> rfl

/-! ## The client -/

/-- The worker is the only spawn target. -/
inductive Tgt where
  | worker
  deriving Inhabited

/-- `data` (block 0). -/
def dPtr : Ptr := ⟨some 0, 0⟩
/-- `flag` (block 1). -/
def fPtr : Ptr := ⟨some 1, 0⟩

/-- The two zero-initialized `u32` globals, at the addresses that the placement `σ` gives them. -/
def mem0 (σ : Placement) : Mem :=
  Mem.ofGlobals σ [(Enc.encode (0 : BitVec 32), 4, .global), (Enc.encode (0 : BitVec 32), 4, .global)]

/-- The translated idle loop does not spawn: its target type is empty. -/
def noTgt : IdleLoop.Tgt → Tgt := fun t => nomatch t

/-- The translated `progress.idle`, run on `flag`. -/
def idleFlag : ConcM Tgt Unit := retarget noTgt (IdleLoop.idle fPtr)

/-- After the idle loop: the read of `data`, which must be 42. -/
def check : ConcM Tgt Unit :=
  ConcM.liftMem (load (BitVec 32) 4 dPtr) >>= fun v => if v = 42 then pure () else throw .panic

/-- The worker: the translated idle loop, then the check. -/
def worker : ConcM Tgt Unit := idleFlag >>= fun _ => check

def dispatch : Tgt → ConcM Tgt Unit
  | .worker => worker

/-- The options of the release store of 1 to `flag`. -/
def storeCnt : Mem → Nat := storeCount 32 .release 4 fPtr

/-- The options of the worker's acquire load of `flag`. -/
def loadCnt : Mem → Nat := loadCount 32 .acquire 4 fPtr

/-- `main` after the release store: join the worker. -/
def mainStore (c : Nat) (h : ThreadId) : ConcM Tgt Unit :=
  ConcM.liftMem (atomicStoreAt c .release 4 fPtr (1 : BitVec 32)) >>= fun _ => syncJoin h

/-- The rest of `main` after its spawn: write `data`, publish `flag`, join the worker. -/
def publish (h : ThreadId) : ConcM Tgt Unit :=
  ConcM.liftMem (store 4 dPtr (42 : BitVec 32)) >>= fun _ =>
    syncPick storeCnt >>= fun c => mainStore c h

/-- `publish` after the spawn's result (an `available` environment: always a handle). -/
def publishE (r : Except ErrName ThreadId) : ConcM Tgt Unit :=
  match r with
  | .ok h => publish h
  | .error _ => throw .panic

/-- `main`: spawn the worker, then publish. -/
def main : ConcM Tgt Unit := syncSpawn .worker >>= publishE

/-! ## One iteration of the translated loop -/

/-- One body run of the translated loop. -/
def iterRun : ConcM IdleLoop.Tgt (IdleLoop.idleExit × IdleLoop.idleLocals) :=
  (IdleLoop.idle.loop2 fPtr).run default

/-- The translated loop, from its head. -/
def loopRun : ConcM IdleLoop.Tgt (IdleLoop.idleExit × IdleLoop.idleLocals) :=
  (Zig.loop (IdleLoop.idle.loop2 fPtr) IdleLoop.idle.again2).run default

/-- What the translated `idle` does after its loop. -/
def idleTail (r : IdleLoop.idleExit × IdleLoop.idleLocals) : ConcM IdleLoop.Tgt Unit :=
  (match r.1 with
    | .br1 => pure IdleLoop.idleExit.ret
    | e => pure e : ConcM IdleLoop.Tgt IdleLoop.idleExit) >>= fun e =>
  match e with
  | .ret => pure ()
  | _ => throw .panic

/-- The worker from the head of the translated loop. -/
def wLoop : ConcM Tgt Unit := retarget noTgt (loopRun >>= idleTail) >>= fun _ => check

theorem locals_eq (s : IdleLoop.idleLocals) : s = default := by cases s; rfl

theorem iterRun_eq : iterRun = (syncPick loadCnt >>= fun c =>
    ConcM.liftMem (atomicLoadAt (n := 32) c .acquire 4 fPtr) >>= fun v =>
    if v == 0 then (syncYield >>= fun _ => syncChoose 2 >>= fun _ =>
      pure (IdleLoop.idleExit.rep2, default)) else pure (IdleLoop.idleExit.br1, default)) := by
  unfold iterRun IdleLoop.idle.loop2
  simp only [atomicLoadC, pickC_eq, callMC, spinLoopHintC_eq, threadYieldC_eq, StateT.run_bind,
    StateT.run_lift, bind_assoc, pure_bind, run_ite]
  refine bindC fun c => bindC fun v => ?_
  split
  · simp only [bind_assoc]
    refine bindC fun u => bindC fun x => ?_
    unfold threadYieldResult
    split <;> rfl
  · rfl

theorem loopRun_eq : loopRun = iterRun >>= fun r =>
    if IdleLoop.idle.again2 r.1 then loopRun else pure r := by
  conv => lhs; rw [loopRun.eq_1, Zig.loop.eq_1]
  simp only [StateT.run_bind, run_ite]
  refine bindC fun r => ?_
  rw [locals_eq r.2]
  rfl

/-- **One iteration.** The worker at the head of the translated loop: the acquire load, then,
on 0, the spin hint, the yield and the loop again; on another value, the check. -/
theorem wLoop_eq : wLoop = syncPick loadCnt >>= fun c =>
    ConcM.liftMem (atomicLoadAt (n := 32) c .acquire 4 fPtr) >>= fun v =>
    if v == 0 then (syncYield >>= fun _ => syncChoose 2 >>= fun _ => wLoop) else check := by
  conv => lhs; rw [wLoop.eq_1, loopRun_eq, iterRun_eq]
  simp only [bind_assoc, retarget_bind, retarget_syncPick, retarget_liftMem]
  refine bindC fun c => bindC fun v => ?_
  split
  · simp only [bind_assoc, retarget_bind, retarget_syncYield, retarget_syncChoose]
    refine bindC fun u => bindC fun x => ?_
    simp only [retarget_pure, pure_bind, IdleLoop.idle.again2, ite_true, wLoop, retarget_bind,
      bind_assoc]
  · simp only [IdleLoop.idle.again2]
    rfl

/-- The worker starts at the head of the translated loop. -/
theorem worker_eq : worker = wLoop := by
  unfold worker idleFlag wLoop IdleLoop.idle idleTail
  simp only [StateT.run'_eq, StateT.run_bind, map_eq_pure_bind, bind_assoc, retarget_bind]
  refine bindC fun r => ?_
  rcases r with ⟨e, s⟩
  cases e <;> rfl

end IdleLoop.Client
