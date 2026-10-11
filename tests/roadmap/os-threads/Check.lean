import ZigLean.Os
import ZigLean.Conc.Sched

/-! Runtime regressions of the trusted OS thread primitives (premises OSF-01, OSF-02, OST-01,
OST-02, OST-03, OSY-01, OSK-01, OSK-02, OSG-01, OSM-02; `docs/os-threads.md`). Concurrent cases
run every schedule (a depth-first search over the oracle's choices, `outcomes`) and compare the
set of results. `lake env lean tests/roadmap/os-threads/Check.lean`. -/

open Zig Zig.Os

namespace OsThreadsCheck

/-! ## Harness -/

/-- For `blocks[i]!` in the checks only. -/
local instance : Inhabited Block := ⟨{ bytes := #[], align := 0, kind := .heap, live := false, addr := 0 }⟩

/-- Spawn targets are numbers; each test gives their bodies. -/
abbrev Tgt := Nat

/-- The next schedule after `pre` with the option counts `opts`, depth first. -/
def nextSchedule (pre opts : Array Nat) : Option (Array Nat) :=
  let rec go : Nat → Option (Array Nat)
    | 0 => none
    | j + 1 =>
      let c := pre.getD j 0
      if c + 1 < opts.getD j 0 then some (((Array.range j).map (pre.getD · 0)).push (c + 1))
      else go j
  go opts.size

/-- A run's result as a short string. -/
def showOut {α : Type} (sh : α → String) : Sched.Out α → String
  | none => "none"
  | some (.error e) => s!"{repr e}"
  | some (.ok (v, _)) => sh v

/-- The run's environment: any `Io`; spawn succeeds unless a check passes `fallible`. -/
def runEnv : Zig.Env := { io := .any, spawn := .available }

/-- The distinct results of every schedule of `main` (at most `cap` runs), sorted. -/
def outcomes {α : Type} (dispatch : Tgt → ConcM Tgt Unit) (main : ConcM Tgt α) (sh : α → String)
    (fuel : Nat := 40) (cap : Nat := 4000) (m0 : Mem := {}) (renv : Zig.Env := runEnv) :
    List String :=
  let rec go : Nat → Array Nat → List String → List String
    | 0, _, acc => acc
    | k + 1, pre, acc =>
      let (out, opts) := Sched.runTrace renv dispatch fuel (pre.getD · 0) main m0
      let s := showOut sh out
      let acc := if acc.contains s then acc else s :: acc
      match nextSchedule pre opts with
      | some p => go k p acc
      | none => acc
  (go cap #[] []).mergeSort (· ≤ ·)

def noKids : Tgt → ConcM Tgt Unit := fun _ => pure ()

def lift {α : Type} (x : MemM α) : ConcM Tgt α := ConcM.liftMem x

/-- The scheduler's spawn; its failure (only under `fallible`) is `.unspecified` here. -/
def spawnKid (t : Tgt) : ConcM Tgt ThreadId := do
  match ← ConcM.sync (.spawn t) with
  | .ok c => pure c
  | .error _ => throw .unspecified

/-- A `u32` word, initialized to `v`: block 0 of a fresh memory. -/
def word (v : BitVec 32) : ConcM Tgt Ptr := lift do
  let p ← alloc .heap 4 4
  store 4 p v
  pure p

def p0 : Ptr := ⟨some 0, 0⟩

def seqLoad (p : Ptr) : ConcM Tgt (BitVec 32) := do
  let c ← pick (loadCount 32 .seqCst 4 p)
  lift (atomicLoadAt c .seqCst 4 p)

def seqStore (p : Ptr) (v : BitVec 32) : ConcM Tgt Unit := do
  let c ← pick (storeCount 32 .seqCst 4 p)
  lift (atomicStoreAt c .seqCst 4 p v)

def hex64 (v : BitVec 64) : String := s!"{v.toInt}"
def hex32 (v : BitVec 32) : String := s!"{v.toInt}"
def env := Os.Env.example

/-! ## OSF-01: futex wait -/

-- Untimed wait, word = expected: a spurious EINTR, a spurious return of the scheduler's wait
-- (`0`, C05), or sleep with nobody to wake (deadlock).
#guard outcomes noKids (do let p ← word 0; Linux.futex_4arg p 0x80 0 none) hex64 ==
  ["-4", "0", "Zig.Error.deadlock"]
-- Word ≠ expected: EAGAIN only (no sleep, no spurious option).
#guard outcomes noKids (do let p ← word 1; Linux.futex_4arg p 0x80 0 none) hex64 == ["-11"]
-- Timed wait: EINTR or ETIMEDOUT, never a deadlock (a timed sleeper stays runnable).
def timed (nsec : BitVec 64) : ConcM Tgt (BitVec 64) := do
  let p ← word 0
  let ts ← lift do
    let t ← alloc .heap 16 8
    store 8 t (0 : BitVec 64)
    store 8 (t.add 8) nsec
    pure t
  Linux.futex_4arg p 0 0 (some ts)
#guard outcomes noKids (timed 1000) hex64 == ["-110", "-4"]
-- An invalid timeout: EINVAL.
#guard outcomes noKids (timed 2000000000) hex64 == ["-22"]
-- Unmodelled commands: unspecified; a bad pointer: illegal.
#guard outcomes noKids (do let p ← word 0; Linux.futex_4arg p 9 0 none) hex64 == ["Zig.Error.unspecified"]
#guard outcomes noKids (Linux.futex_4arg ⟨none, 0⟩ 0x80 0 none) hex64 == ["Zig.Error.illegal"]
-- A racing plain write to the word is a data race (the compare is an atomic read with a footprint).
def racyKid : Tgt → ConcM Tgt Unit := fun _ => lift (store 4 p0 (1 : BitVec 32))
#guard (outcomes racyKid (do
    let p ← word 0
    let t ← spawnKid 0
    let r ← Linux.futex_4arg p 0x80 7 none
    ConcM.sync (.join t)
    pure r) hex64).contains "Zig.Error.illegal"
-- macOS: woken/mismatch are 0, a spurious return -EINTR, a timeout -ETIMEDOUT.
#guard outcomes noKids (do let p ← word 0; Darwin.__ulock_wait2 0x01000001 (some p) 0 5 0) hex32 ==
  ["-4", "-60"]
#guard outcomes noKids (do let p ← word 3; Darwin.__ulock_wait2 0x01000001 (some p) 0 0 0) hex32 == ["0"]
#guard outcomes noKids (do let p ← word 0; Darwin.__ulock_wait2 0x01000001 (some p) 0 0 1) hex32 ==
  ["Zig.Error.unspecified"]

/-! ## OSF-02: futex wake -/

-- The wake subset is the oracle's: with two waiters, a wake of one has two options.
def twoWaiters : Mem := { waiters := #[(1, p0), (2, p0), (3, ⟨some 1, 0⟩)] }
#guard wakeCount p0 (some 1) twoWaiters == 2
#guard wakeCount p0 (some 5) twoWaiters == 1
#guard wakeCount p0 none twoWaiters == 1
#guard ((wakeAt 0 p0 (some 1)).run twoWaiters).run.map (·.map fun (n, m) => (n, m.woken)) ==
  some (.ok (some 1, #[1]))
#guard ((wakeAt 1 p0 (some 1)).run twoWaiters).run.map (·.map fun (n, m) => (n, m.woken)) ==
  some (.ok (some 1, #[2]))
#guard ((wakeAt 2 p0 (some 1)).run twoWaiters).run.map (·.map fun (n, m) => (n, m.woken)) ==
  some (.ok (none, #[]))
#guard ((wakeAt 0 p0 none).run twoWaiters).run.map (·.map fun (n, m) => (n, m.waiters.size)) ==
  some (.ok (some 2, 1))
-- Linux FUTEX_WAKE with nobody waiting wakes 0; `val = 0` still wakes one (kernel `nr_wake`).
#guard outcomes noKids (do let p ← word 0; Linux.futex_3arg p 0x81 1) hex64 == ["0"]
#guard Linux.wakeLimit 0 == 1 && Linux.wakeLimit 0xffffffff == 1 && Linux.wakeLimit 3 == 3
-- macOS: nobody waiting is -ENOENT; a spurious -EINTR is allowed.
#guard outcomes noKids (do let p ← word 0; Darwin.__ulock_wake 0x01000001 (some p) 0) hex32 ==
  ["-2", "-4"]

-- A waiter woken by a wake goes on. Its return code is 0 (woken) or a spurious -EINTR; the word
-- was 0 when it started.
def wakeKid : Tgt → ConcM Tgt Unit := fun _ => do
  let r ← Linux.futex_4arg p0 0x80 0 none
  lift (store 8 (⟨some 1, 0⟩ : Ptr) r)
def wakeMain : ConcM Tgt (BitVec 64) := do
  let _ ← word 0
  let slot ← lift (alloc .heap 8 8)
  let t ← spawnKid 0
  seqStore p0 1
  let _ ← Linux.futex_3arg p0 0x81 1
  ConcM.sync (.join t)
  lift (load (BitVec 64) 8 slot)
#guard outcomes wakeKid wakeMain hex64 == ["-11", "-4", "0"]

/-! ## OST-01/02: Linux clone, CHILD_CLEARTID, the translated join loop -/

-- `instance`: block 0 = child_tid (i32, 1 at first), block 1 = data, block 2 = parent_tid.
def ctid : Ptr := ⟨some 0, 0⟩
def dataP : Ptr := ⟨some 1, 0⟩
def ptidP : Ptr := ⟨some 2, 0⟩

def cloneKid : Tgt → ConcM Tgt Unit := fun _ =>
  Linux.cloneThread (lift (store 8 dataP (42 : BitVec 64))) ctid

/-- `LinuxThreadImpl.join`: load `child_tid` until 0, futex-waiting on it (bounded here). -/
def joinLoop : Nat → ConcM Tgt Unit
  | 0 => throw .panic
  | k + 1 => do
    let tid ← seqLoad ctid
    if tid = 0 then return
    let _ ← Linux.futex_4arg ctid 0 tid none
    joinLoop k

def cloneSetup (env : Os.Env) : ConcM Tgt (BitVec 64) := do
  let _ ← word 1
  let _ ← lift (do let d ← alloc .heap 8 8; store 8 d (0 : BitVec 64))
  let _ ← lift (alloc .heap 4 4)
  Linux.clone env 0 0 Linux.stdCloneFlags (some ptidP) 0 (some ctid)

-- The join loop gets the join edge from the exit's release store: the child's plain write is
-- read without a race, every completed schedule gives 42 (the rest run out of fuel).
#guard outcomes cloneKid (do
    let _ ← cloneSetup env
    joinLoop 6
    lift (load (BitVec 64) 8 dataP)) hex64 (fuel := 30) == ["42", "Zig.Error.panic"]
-- The parent wrote the child's id to ptid.
#guard outcomes cloneKid (do
    let r ← cloneSetup env
    joinLoop 6
    let t ← lift (load (BitVec 32) 4 ptidP)
    pure (r == t.setWidth 64 && t == env.tid 1)) toString (fuel := 30) == ["Zig.Error.panic", "true"]
-- Without the join loop: reading the data races with the child, or the parent ends first (the
-- child's join obligation is open): illegal.
#guard (outcomes cloneKid (do
    let _ ← cloneSetup env
    lift (load (BitVec 64) 8 dataP)) hex64) == ["Zig.Error.illegal"]
-- An exit is no join: freeing the child's data without the join loop races with the child's write
-- in every schedule, even when the child already exited (`ThreadRec.released`).
#guard outcomes cloneKid (do
    let _ ← cloneSetup env
    ConcM.sync .yield
    ConcM.sync .yield
    ConcM.sync .yield
    lift (free dataP)) (fun _ => "ok") (fuel := 30) == ["Zig.Error.illegal"]
-- With the join loop the free is ordered after the child's write.
#guard outcomes cloneKid (do
    let _ ← cloneSetup env
    joinLoop 6
    lift (free dataP)) (fun _ => "ok") (fuel := 30) == ["Zig.Error.panic", "ok"]
-- Spawn failure is the run environment's under `fallible`: -EAGAIN, -ENOMEM, or a thread. A short
-- join loop keeps the depth-first enumeration (capped) from spending its runs on the spurious
-- futex returns of the loop before it reaches the spawn's error options.
#guard outcomes cloneKid (do
    let r ← cloneSetup env
    if r.toInt < 0 then return r
    joinLoop 2
    pure r) hex64 (fuel := 30) (renv := { runEnv with spawn := .fallible }) == ["-11", "-12", "1001", "Zig.Error.panic"]
-- Other clone flags: outside the model.
#guard outcomes cloneKid (Linux.clone env 0 0 0x100 (some ptidP) 0 (some ctid)) hex64 ==
  ["Zig.Error.unspecified"]

/-! ## OST-01/02: macOS pthread_create/join/detach -/

def pKid : Tgt → ConcM Tgt Unit := fun _ => lift (store 8 (⟨some 0, 0⟩ : Ptr) (7 : BitVec 64))
def pSetup : ConcM Tgt (Ptr × Ptr) := lift do
  let d ← alloc .heap 8 8
  let h ← alloc .heap 8 8
  pure (d, h)

-- pthread_join gives the edge from the end of the thread.
#guard outcomes pKid (do
    let (d, h) ← pSetup
    let _ ← Darwin.pthread_create h none 0
    let t ← lift (load ThreadId 8 h)
    let _ ← Darwin.pthread_join t none
    lift (load (BitVec 64) 8 d)) hex64 == ["7"]
-- Join twice, join after detach, detach twice: illegal.
#guard outcomes pKid (do
    let (_, h) ← pSetup
    let _ ← Darwin.pthread_create h none 0
    let t ← lift (load ThreadId 8 h)
    let _ ← Darwin.pthread_join t none
    Darwin.pthread_join t none) toString |>.all (· ∈ ["Zig.Error.illegal"])
#guard outcomes pKid (do
    let (_, h) ← pSetup
    let _ ← Darwin.pthread_create h none 0
    let t ← lift (load ThreadId 8 h)
    let _ ← lift (Darwin.pthread_detach t)
    Darwin.pthread_join t none) toString == ["Zig.Error.illegal"]
-- A detached thread needs no join.
#guard outcomes pKid (do
    let (_, h) ← pSetup
    let _ ← Darwin.pthread_create h none 0
    let t ← lift (load ThreadId 8 h)
    lift (Darwin.pthread_detach t)) toString == ["0x0000#16"]
-- A detach is no join: freeing the data races in the schedules where the detached thread wrote it
-- first (in the others the run ends before it runs).
#guard outcomes pKid (do
    let (d, h) ← pSetup
    let _ ← Darwin.pthread_create h none 0
    let t ← lift (load ThreadId 8 h)
    let _ ← lift (Darwin.pthread_detach t)
    ConcM.sync .yield
    ConcM.sync .yield
    lift (free d)) (fun _ => "ok") == ["Zig.Error.illegal", "ok"]
-- Spawn failure: EAGAIN under `fallible`.
#guard (outcomes pKid (do
    let (_, h) ← pSetup
    let r ← Darwin.pthread_create h none 0
    if r ≠ 0 then return r
    let t ← lift (load ThreadId 8 h)
    let _ ← Darwin.pthread_join t none
    pure r) toString (renv := { runEnv with spawn := .fallible })) == ["0x0000#16", "0x0023#16"]
-- Attributes: init/setstacksize/setguardsize/destroy; a stack below PTHREAD_STACK_MIN is EINVAL.
#guard outcomes noKids (lift do
    let a ← alloc .heap 64 8
    let r1 ← Darwin.pthread_attr_init a
    let r2 ← Darwin.pthread_attr_setstacksize a (16 * 1024 * 1024)
    let r3 ← Darwin.pthread_attr_setguardsize a 16384
    let r4 ← Darwin.pthread_attr_setstacksize a 100
    let r5 ← Darwin.pthread_attr_destroy a
    pure [r1, r2, r3, r4, r5]) toString == ["[0x0000#16, 0x0000#16, 0x0000#16, 0x0016#16, 0x0000#16]"]

/-! ## OST-03: ids and CPU count -/

#guard outcomes noKids (lift (Linux.gettid env)) hex32 == ["1000"]
#guard outcomes noKids (lift (Linux.getpid env)) hex32 == ["1000"]
#guard outcomes noKids (lift do
    let s ← alloc .heap 128 8
    let r ← Linux.sched_getaffinity env 0 128 s
    let b0 ← load (BitVec 8) 1 s
    let b1 ← load (BitVec 8) 1 (s.add 1)
    pure (r, b0, b1)) toString == ["(0x0000000000000000#64, (0x0f#8, 0x00#8))"]
#guard outcomes noKids (lift do
    let s ← alloc .heap 64 8
    Linux.sched_getaffinity env 0 64 s) hex64 == ["Zig.Error.unspecified"]
#guard env.cpus == 4 && ({ env with cpuMask := 0x101 } : Os.Env).cpus == 2
-- sysctlbyname("hw.logicalcpu") writes the CPU count; other names are outside the model.
def cstr (s : String) : MemM Ptr := do
  let bs := s.toList.map (fun c => Byte.int (BitVec.ofNat 8 c.toNat)) ++ [Byte.int 0]
  let p ← alloc .heap bs.length 1
  storeBytes p 1 bs.toArray
  pure p
def sysctl (name : String) : MemM (BitVec 32 × BitVec 32 × BitVec 64) := do
  let n ← cstr name
  let o ← alloc .heap 4 4
  let l ← alloc .heap 8 8
  store 8 l (4 : BitVec 64)
  let r ← Darwin.sysctlbyname env n (some o) (some l) none 0
  pure (r, ← load (BitVec 32) 4 o, ← load (BitVec 64) 8 l)
#guard outcomes noKids (lift (sysctl "hw.logicalcpu")) toString ==
  ["(0x00000000#32, (0x00000004#32, 0x0000000000000004#64))"]
#guard outcomes noKids (lift (sysctl "hw.ncpu")) toString == ["Zig.Error.unspecified"]
#guard outcomes noKids (lift do
    let s ← Darwin.pthread_self
    let i ← alloc .heap 8 8
    let r ← Darwin.pthread_threadid_np env none i
    pure (s, r, ← load (BitVec 64) 8 i)) toString == ["(0, (0x00000000#32, 0x00000000000003e8#64))"]

/-! ## OSY-01: yield -/

#guard outcomes noKids (Linux.sched_yield) hex64 == ["0"]
#guard outcomes noKids (Darwin.sched_yield) hex32 == ["0"]

/-! ## OSG-01: interrupts -/

-- A signal wakes a sleeper, which then returns EINTR; otherwise it is pending.
def sleeper : Mem := { threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
                       clocks := #[#[], #[]], waiters := #[(1, p0)] }
#guard ((interrupt 1).run sleeper).run.map (·.map fun (_, m) => (m.waiters.size, m.woken, m.os.interrupts)) ==
  some (.ok (0, #[1], #[1]))
#guard ((interrupt 0).run sleeper).run.map (·.map fun (_, m) => (m.waiters.size, m.woken, m.os.interrupts)) ==
  some (.ok (1, #[], #[0]))
-- tgkill finds the thread by id; an unknown id or another process: ESRCH; not SIG.IO: unspecified.
#guard ((Linux.tgkill env 1000 1001 29).run sleeper).run.map (·.map fun (r, m) => (r, m.woken)) ==
  some (.ok (0, #[1]))
#guard ((Linux.tgkill env 1000 1005 29).run sleeper).run.map (·.map (·.1)) == some (.ok (negErrno 3))
#guard ((Linux.tgkill env 999 1001 29).run sleeper).run.map (·.map (·.1)) == some (.ok (negErrno 3))
#guard ((Linux.tgkill env 1000 1001 9).run sleeper).run.map (·.map (·.1)) == some (.error .unspecified)
#guard ((Darwin.pthread_kill 1 23).run sleeper).run.map (·.map fun (r, m) => (r, m.woken)) ==
  some (.ok (0, #[1]))
-- A detached thread stays signalable; a joined one is gone (ESRCH).
def detachKill : MemM (BitVec 32) := do
  let _ ← Darwin.pthread_detach 1
  Darwin.pthread_kill 1 23
#guard (detachKill.run sleeper).run.map (·.map fun (r, m) => (r, m.woken)) == some (.ok (0, #[1]))
#guard ((Darwin.pthread_kill 1 23).run { sleeper with
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := true }] }).run.map
  (·.map (·.1)) == some (.ok 3)
-- A canceled sleeper: thread 1 waits, main signals it, then wakes nobody; the waiter returns
-- EINTR (signal or spurious), 0 (a spurious return of the scheduler's wait), or deadlocks only
-- when main's signal came before its sleep.
def intrKid : Tgt → ConcM Tgt Unit := fun _ => do
  let r ← Linux.futex_4arg p0 0x80 0 none
  lift (store 8 (⟨some 1, 0⟩ : Ptr) r)
#guard outcomes intrKid (do
    let _ ← word 0
    let slot ← lift (alloc .heap 8 8)
    let t ← spawnKid 0
    ConcM.sync .yield
    let _ ← lift (Linux.tgkill env 1000 1001 29)
    ConcM.sync (.join t)
    lift (load (BitVec 64) 8 slot)) hex64 == ["-4", "0", "Zig.Error.deadlock"]
-- A pending interrupt is delivered at the next wait's start: it forces nothing.
#guard ((takeInterrupt).run { os := { interrupts := #[0] } }).run.map (·.map fun (b, m) => (b, m.os.interrupts)) ==
  some (.ok (true, #[]))

/-! ## OSK-01/02: clocks and sleep -/

def readTwo (clk : BitVec 32) : ConcM Tgt (List (BitVec 64)) := do
  let ts ← lift (alloc .heap 16 8)
  let _ ← Linux.clock_gettime { env with clock := fun _ i => 999999999 + i } clk ts
  let a ← lift (load (BitVec 64) 8 ts)
  let b ← lift (load (BitVec 64) 8 (ts.add 8))
  let _ ← Linux.clock_gettime { env with clock := fun _ i => 999999999 + i } clk ts
  pure [a, b, ← lift (load (BitVec 64) 8 ts), ← lift (load (BitVec 64) 8 (ts.add 8))]
#guard outcomes noKids (readTwo 1) toString ==
  ["[0x0000000000000000#64, 0x000000003b9ac9ff#64, 0x0000000000000001#64, 0x0000000000000000#64]"]
#guard outcomes noKids (readTwo 2) toString == ["Zig.Error.unspecified"]
#guard outcomes noKids (do let ts ← lift (alloc .heap 16 8); Darwin.clock_gettime env 8 ts) hex32 == ["0"]
#guard outcomes noKids (do let ts ← lift (alloc .heap 16 8); Darwin.clock_gettime env 1 ts) hex32 ==
  ["Zig.Error.unspecified"]
-- Clock reads of two threads are ordered by the run; each read is a scheduling point.
#guard ({ env with clock := fun _ i => i } : Os.Env).clock .awake 3 == 3
def req (nsec : BitVec 64) : MemM Ptr := do
  let t ← alloc .heap 16 8
  store 8 t (1 : BitVec 64)
  store 8 (t.add 8) nsec
  pure t
-- Linux: 0 or EINTR (the time left is the request); EINVAL for a bad request.
#guard outcomes noKids (do
    let r ← lift (req 5)
    let rem ← lift (alloc .heap 16 8)
    let rc ← Linux.clock_nanosleep 1 0 r (some rem)
    if rc = 0 then return rc
    let s ← lift (load (BitVec 64) 8 rem)
    pure (rc + s * 100)) hex64 == ["0", "96"]
#guard outcomes noKids (do let r ← lift (req 1000000000); Linux.clock_nanosleep 1 0 r none) hex64 == ["-22"]
-- macOS: -1 with errno EINTR.
#guard outcomes noKids (do
    let r ← lift (req 5)
    let rc ← Darwin.nanosleep r none
    let e ← lift (do load (BitVec 32) 4 (← Darwin.__error))
    pure (rc, e)) toString == ["(0x00000000#32, 0x00000000#32)", "(0xffffffff#32, 0x00000004#32)"]

/-! ## OSM-02: macOS malloc/free -/

def mrun {α : Type} (x : MemM α) (m : Mem := {}) : Option (Except Error (α × Mem)) := (x.run m).run
def mtag {α : Type} (x : MemM α) (m : Mem := {}) : String :=
  match mrun x m with
  | none => "none"
  | some (.error e) => s!"{repr e}"
  | some (.ok _) => "ok"
def mallocOk (n : BitVec 64) (e : Os.Env := env) : MemM Ptr := do
  match ← Darwin.malloc e n with
  | some p => pure p
  | none => throw .panic

#guard mtag (do let p ← mallocOk 10; store 1 (p.add 9) (1 : BitVec 8)) == "ok"
#guard mtag (do let p ← mallocOk 10; store 1 (p.add 10) (1 : BitVec 8)) == "Zig.Error.illegal"
#guard (mrun (mallocOk 10)).map (·.map fun (_, m) => (m.blocks[0]!.addr % 16, m.blocks[0]!.kind == .heap,
  m.blocks[0]!.bytes.size)) == some (.ok (0, true, 10))
-- The bytes are undefined until written.
#guard mtag (do let p ← mallocOk 4; load (BitVec 32) 4 p) == "Zig.Error.unspecified"
-- Slack: malloc_size reports it, and the slack bytes are usable.
#guard (mrun (do let p ← mallocOk 10 { env with mallocSlack := fun _ _ => 6 }
                 store 1 (p.add 15) (1 : BitVec 8)
                 Darwin.malloc_size (some p))).map (·.map (·.1)) == some (.ok 16)
-- malloc(0) is a fresh, freeable pointer.
#guard mtag (do let p ← mallocOk 0; Darwin.free (some p)) == "ok"
-- Failure: null, nothing allocated.
#guard (mrun (Darwin.malloc env 10) { allocPolicy := { fails := fun _ _ => true } }).map
  (·.map fun (r, m) => (r, m.blocks.size)) == some (.ok (none, 0))
-- free: null is a no-op; a double free, use after free, inner pointer, stack block: illegal.
#guard mtag (Darwin.free none) == "ok"
#guard mtag (do let p ← mallocOk 8; Darwin.free (some p); load (BitVec 8) 1 p) == "Zig.Error.illegal"
#guard mtag (do let p ← mallocOk 8; Darwin.free (some p); Darwin.free (some p)) == "Zig.Error.illegal"
#guard mtag (do let p ← mallocOk 8; Darwin.free (some (p.add 1))) == "Zig.Error.illegal"
#guard mtag (do let p ← alloc .stack 8 8; Darwin.free (some p)) == "Zig.Error.illegal"
#guard mtag (do let p ← mallocOk 8; Darwin.free (some p); Darwin.malloc_size (some p)) == "Zig.Error.illegal"
#guard (mrun (Darwin.malloc_size none)).map (·.map (·.1)) == some (.ok 0)
-- A concurrent free races with an access of another thread.
def freeKid : Tgt → ConcM Tgt Unit := fun _ => lift (Darwin.free (some ⟨some 0, 0⟩))
#guard (outcomes freeKid (do
    let p ← lift (mallocOk 8)
    let t ← spawnKid 0
    lift (store 1 p (1 : BitVec 8))
    ConcM.sync (.join t)) toString).all (· ∈ ["Zig.Error.illegal", "none"])

end OsThreadsCheck
