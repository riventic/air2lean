import ZigLean.Os
import ZigLean.Os.Mmap
import ZigLean.Conc.Sched

/-! MM-19 regressions: a Linux thread's locals lie in the stack part of its thread mapping
(`docs/architecture-audit/memory-model.md` §MM-19). Every run is evaluated by the kernel
(`decide +kernel`).

Std's `LinuxThreadImpl.spawn` maps one region (guard page, stack, TLS area, `Instance`) and passes
the end of the stack part to `clone`; natively the child's locals lie there (E3 of §MM-18). Before
the fix `clone` ignored its `stack` argument and the mapping stayed a live block over the whole
range, so `@intFromPtr(&child_local)` inside the mapping was provably false for every placement,
and the `apart` rule claimed each owned byte of a block lies before every other block. Now:

* `child_local_in_mapping`: some placement puts the child's local inside its thread mapping.
* `old_apart_false`: there the child's live local and a live byte of the mapping (its TLS part)
  lie neither way round the old `apart` fact (each owned byte before the other block's start);
  the corrected `Holds.apart` compares with the other block's live bytes.
* `heap_not_in_stack`, `parent_stack_not_in_child_stack`: only the thread's own stack blocks may
  lie in its native stack; a heap block or another thread's stack block proposed there falls back
  outside the mapping.
* `parent_access_illegal`: the parent's access to the child's stack through the mapping is
  illegal while the child runs. That std's `munmap` of the whole mapping succeeds after the join
  is a runtime check (`tests/roadmap/os-threads/Check.lean`): the kernel does not reduce a run
  over the restored page-sized byte arrays. -/

open Zig Zig.Os

namespace ThreadStack

/-- The run's environment: any `Io`, spawn always succeeds. -/
def runEnv : Zig.Env := { io := .any, spawn := .available }

/-- The result of the schedule `o` from the memory with placement `σ`. -/
def result {α : Type} (σ : Placement) (dispatch : Nat → ConcM Nat Unit) (fuel : Nat) (o : List Nat)
    (main : ConcM Nat α) : Option (Except Error α) :=
  ((Sched.run runEnv dispatch fuel (o.getD · 0) main { place := σ }).run).map (·.map (·.1))

-- Blocks: 0 = child_tid, 1 = a slot for the child's local's address, 2 = parent_tid,
-- 3 = the thread mapping (two pages), 4 = the next block.
def ctid : Ptr := ⟨some 0, 0⟩
def slot : Ptr := ⟨some 1, 0⟩
def ptid : Ptr := ⟨some 2, 0⟩
def mapP : Ptr := ⟨some 3, 0⟩

/-- The mapping at 1 MiB and block 4 at 2 KiB into it, inside the stack part. -/
def nativeLayout : Placement :=
  { propose := fun b => if b = 3 then some 0x100000 else if b = 4 then some 0x100800 else none }

/-- The child: one escaping local, whose address it stores in the slot. -/
def kid : Nat → ConcM Nat Unit := fun _ =>
  Linux.cloneThread (ConcM.liftMem do
    let p ← allocStack 8 8
    store 8 slot (BitVec.ofInt 64 (← ptrAddr p))
    free p) ctid

/-- `LinuxThreadImpl.join`: a `seq_cst` load of `child_tid` until it is 0, with a futex wait. -/
def joinLoop : Nat → ConcM Nat Unit
  | 0 => throw .panic
  | k + 1 => do
    let c ← pick (loadCount 32 .seqCst 4 ctid)
    let tid : BitVec 32 ← ConcM.liftMem (atomicLoadAt c .seqCst 4 ctid)
    if tid = 0 then return
    let _ ← Linux.futex_4arg ctid 0 tid none
    joinLoop k

/-- Std's spawn: the mapping of two pages, the first the stack (its end is the stack top), the
second the TLS area and `Instance`; then `clone`. -/
def spawn : ConcM Nat Unit := do
  let _ ← ConcM.liftMem do
    let w ← alloc .heap 4 4
    store 4 w (1 : BitVec 32)
    let s ← alloc .heap 8 8
    store 8 s (0 : BitVec 64)
    alloc .heap 4 4
  let top ← ConcM.liftMem do
    let .ok s ← mmap .linux none 8192 (Target.protReadWrite .linux)
        (Target.mapPrivateAnonymous .linux) noFd 0 | throw .unspecified
    pure (BitVec.ofInt 64 ((← ptrAddr s.ptr) + 4096))
  let _ ← Linux.clone Env.example 0 top Linux.stdCloneFlags (some ptid) 0 (some ctid)

/-- The child's local `L` lies in the stack part `[M, M + 4096)` of the mapping at `M`, so neither
`L + 0 < M` nor `M + 4096 < L`: byte 0 of the local and live byte 4096 of the mapping do not lie
apart in the sense of the old `apart` fact (now `Holds.apart`: before the other's live bytes). -/
def localInMapping : ConcM Nat Bool := do
  spawn
  joinLoop 3
  ConcM.liftMem do
    let L := (← load (BitVec 64) 8 slot).toNat
    let M ← ptrAddr mapP
    pure (decide (M ≤ L ∧ L + 8 ≤ M + 4096))

theorem child_local_in_mapping : result nativeLayout kid 20 [] localInMapping = some (.ok true) := by
  decide +kernel

/-- The child, while its local (block 4, address `L`) is live, reads live byte 4096 of the
mapping (address `M + 4096`) and stores whether the old `apart` fact for these two live bytes
(`L + 0 < M ∨ M + 4096 < L`, each byte before the other block's start) fails. -/
def kidApart : Nat → ConcM Nat Unit := fun _ =>
  Linux.cloneThread (ConcM.liftMem do
    let p ← allocStack 8 8
    let L ← ptrAddr p
    let _ ← load (BitVec 8) 1 (mapP.add 4096)
    let M ← ptrAddr mapP
    store 8 slot (if L + 0 < M ∨ M + 4096 < L then (0 : BitVec 64) else 1)
    free p) ctid

/-- **The old `apart` fact is false** in a reachable memory: two live bytes of two live blocks
that lie neither way round it (the corrected `Holds.apart` compares with the other block's live
bytes, which start at `M + 4096`). -/
theorem old_apart_false : result nativeLayout kidApart 20 [] (do
    spawn
    joinLoop 3
    ConcM.liftMem (load (BitVec 64) 8 slot)) = some (.ok 1) := by
  decide +kernel

/-- The parent makes block 4, a heap block, right after the `clone`: proposed in the child's
stack, it falls back outside the mapping. -/
def heapAfterClone (kind : BlockKind) : ConcM Nat Bool := do
  spawn
  let inside ← ConcM.liftMem do
    let p ← alloc kind 8 8
    let A ← ptrAddr p
    let M ← ptrAddr mapP
    pure (decide (M ≤ A ∧ A < M + 8192))
  joinLoop 3
  pure inside

theorem heap_not_in_stack :
    result nativeLayout kid 20 [] (heapAfterClone .heap) = some (.ok false) := by
  decide +kernel

theorem parent_stack_not_in_child_stack :
    result nativeLayout kid 20 [] (heapAfterClone .stack) = some (.ok false) := by
  decide +kernel

/-- While the child runs, the parent's read of the stack part through the mapping is illegal. -/
theorem parent_access_illegal :
    result nativeLayout kid 20 [] (do spawn; ConcM.liftMem (load (BitVec 64) 8 mapP)) =
      some (.error .illegal) := by
  decide +kernel

#print axioms child_local_in_mapping
#print axioms old_apart_false
#print axioms heap_not_in_stack
#print axioms parent_stack_not_in_child_stack
#print axioms parent_access_illegal

end ThreadStack
