import Proofs.Sync.Gen
import Proofs.Threadsync.Lock

/-! Owner check of a mutex unlock (`Thread.mutexOwnerCheck`) on the translated std code: an
unlock by a thread that did not make the most recent successful acquire is `.illegal`; the
holder's unlock of a contended lock (a waiter wrote the word) is not. The translated
`Io.Mutex` (0.16.0, `Proofs/Sync/Gen.lean`) and `Thread.Mutex` (0.15.2, `Proofs/Threadsync/Gen.lean`:
`FutexImpl` on Linux, `DarwinImpl` with `Gen-darwin.lean` on macOS). Run with
`lake env lean --run tests/review/MutexOwner.lean`. -/

open Zig

deriving instance DecidableEq for Except

namespace MutexOwnerRegression

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def spawnT {T : Type} (t : T) : ConcM T ThreadId := do
  match ← ConcM.sync (.spawn t) with
  | .ok tid => pure tid
  | .error _ => throw .panic

/-- `main` locks the mutex word, spawns `tgt p`, yields until the spawned thread wrote the word
(at most 20 times), then unlocks it (`foreign = false`) or leaves the unlock to the spawned thread
(`foreign = true`), and joins. The result: the number of writes of the word before `main`'s unlock
(more than 2: a waiter wrote the held word). -/
private def prog {T : Type} (lock unlock : Ptr → ConcM T Unit) (tgt : Ptr → T) (foreign : Bool) :
    ConcM T Nat := do
  let p ← ConcM.liftMem (alloc .heap 4 4)
  ConcM.liftMem (store 4 p (0#32))
  lock p
  let tid ← spawnT (tgt p)
  let writes : ConcM T Nat := ConcM.liftMem do
    pure ((← get).atomics.foldl (fun n l => if some l.block == p.block then n + l.msgs.size else n) 0)
  let mut n ← writes
  for _ in [0:20] do
    if n > 2 then break
    let _ ← ConcM.sync .yield
    n ← writes
  unless foreign do unlock p
  ConcM.sync (.join tid)
  pure n

/-- Schedule oracles: periodic picks among the first options. -/
private def oracles : Array (Nat → Nat) :=
  #[fun _ => 0, fun i => (i + 1) % 3, fun i => (2 * i + 2) % 3, fun i => i % 2,
    fun i => (i / 2) % 2, fun i => if i % 3 == 0 then 1 else 0, fun i => (i / 3) % 3]

/-- The two regressions under several schedule oracles. `waiterWrites`: some oracle makes the
spawned thread write the held word (`xchg`/`swap` of the contended value) before `main`'s unlock. -/
private def run {T : Type} (label : String) (lock unlock : Ptr → ConcM T Unit)
    (dispatch : T → ConcM T Unit) (other foreign : Ptr → T) (waiterWrites : Bool) : IO Unit := do
  let res := fun (o : Nat → Nat) (f : Bool) =>
    (Sched.runTrace ⟨.any, .available⟩ dispatch 5000 o
      (prog lock unlock (if f then foreign else other) f) {}).1.map (·.map Prod.fst)
  let mut wrote := false
  for k in [0:oracles.size] do
    let o := oracles[k]!
    check s!"{label}: cross-thread unlock (oracle {k})" (res o true) (some (.error .illegal))
    match res o false with
    | some (.ok n) => wrote := wrote || n > 2
    | none =>
      -- `oracles[0]` (always the first option) must finish
      if k == 0 then throw (IO.userError s!"{label}: lock and unlock (oracle 0) did not finish")
    | r => throw (IO.userError s!"{label}: contended lock and unlock (oracle {k}): got {reprStr r}")
  if waiterWrites && !wrote then
    throw (IO.userError s!"{label}: no oracle made the waiter write the held word")
  check s!"{label}: double unlock" ((Sched.runTrace ⟨.any, .available⟩ dispatch 200 (fun _ => 0)
    (do let p ← ConcM.liftMem (alloc .heap 4 4); ConcM.liftMem (store 4 p (0#32))
        lock p; unlock p; unlock p; pure 7) {}).1.map (·.map Prod.fst)) (some (.error .illegal))

/-- `Io.Mutex`: `.work p` locks and unlocks, `.producer p` only unlocks. -/
private def ioMutex : IO Unit :=
  let lock := fun p => Sync.Io_Mutex_lockUncancelable p ⟨⟩
  let unlock := fun p => Sync.Io_Mutex_unlock p ⟨⟩
  run "Io.Mutex" lock unlock
    (fun | .work p => do lock p; unlock p | .producer p => unlock p | _ => pure ())
    .work .producer true

/-- `Thread.Mutex`: `.work p` locks and unlocks, `.producer p` only unlocks. -/
private def threadMutex : IO Unit :=
  run "Thread.Mutex" Threadsync.Thread_Mutex_lock Threadsync.Thread_Mutex_unlock
    (fun | .work p => do Threadsync.Thread_Mutex_lock p; Threadsync.Thread_Mutex_unlock p
         | .producer p => Threadsync.Thread_Mutex_unlock p | _ => pure ())
    -- a waiter writes the word on Linux (`FutexImpl`); `os_unfair_lock`'s waiters only read it
    .work .producer (Threadsync.mutexC != 1)

/-- The holder of a word from its messages (`ALoc.holder`): a waiter's write over a held word
keeps the holder; an unlock clears it; the next acquire names its writer. -/
private def holderTests : IO Unit := do
  let msg (v : Nat) (w : Option ThreadId) : Msg :=
    { id := 0, bytes := Enc.encode (BitVec.ofNat 32 v), clock := #[], relClock := #[], writer := w }
  let holder (ms : List Msg) : Option ThreadId := ALoc.holder { block := 0, off := 0, len := 4, msgs := ms.toArray }
  check "never locked" (holder [msg 0 none]) none
  check "acquire" (holder [msg 0 none, msg 1 (some 1)]) (some 1)
  check "waiter writes the contended value" (holder [msg 0 none, msg 1 (some 1), msg 2 (some 2)]) (some 1)
  check "unlock" (holder [msg 0 none, msg 1 (some 1), msg 2 (some 2), msg 0 (some 1)]) none
  check "waiter acquires" (holder [msg 0 none, msg 1 (some 1), msg 2 (some 2), msg 0 (some 1),
    msg 2 (some 2), msg 2 (some 3)]) (some 2)
  check "initially locked" (holder [msg 1 none]) none

end MutexOwnerRegression

def main : IO Unit := do
  MutexOwnerRegression.holderTests
  MutexOwnerRegression.ioMutex
  MutexOwnerRegression.threadMutex
  IO.println "Mutex owner regressions passed"
