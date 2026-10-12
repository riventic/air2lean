import ZigLean.Mem.Lemmas
import ZigLean.Mem.Alloc

/-! MM-18 regressions: per-thread stack regions (`docs/architecture-audit/memory-model.md`
§MM-18). Every run is evaluated by the kernel (`decide +kernel`).

* The three scenarios that made a stack-room resource unsound over the old model, in their fixed
  form: a `free` gives the charge back (1), heap traffic (2) and a placement at the end of the
  address space (3) leave the stack's slack alone. The old behaviour stays for a thread without a
  budget (`*_noBudget`).
* `.stackOverflow` exactly at the budget, and the general lemma `alloc_stack_overflow`.
* Splittable room is unsound: after an out-of-order `free` the next block overflows a budget that
  a credit returned by that `free` would cover.
* Native layouts stay reachable (E1, E1' of MM-18): some placement puts an inlined callee's local
  above its caller's, and a later local on the address of a dead one. -/

open Zig

/-- An address space of 4096 + 256 bytes: the reserve and a few blocks fit. -/
def small : Placement := { propose := fun _ => none, addrLimit := 4096 + 256 }

/-- The start memory of `σ` with a main-thread stack budget `S` (MM-18, `Mem.withStack`). -/
def withBudget (σ : Placement) (S : Nat) : Mem := ({ place := σ } : Mem).withStack S

/-- `n` times: a stack block of 8 bytes made and freed (a loop that calls a function with one
escaping local). -/
def allocFree : Nat → MemM Unit
  | 0 => pure ()
  | n + 1 => do let p ← allocStack 8 8; free p; allocFree n

/-- (1) A `free` gives the charge back: 40 iterations in a budget of one block (charge 16). -/
theorem s1_free_returns : ((allocFree 40).run' (withBudget small 16)).run = some (.ok ()) := by
  decide +kernel

/-- (1) Without a budget, the old model: dead blocks raise `Mem.top` until the fallback leaves
the address space. -/
theorem s1_noBudget : ((allocFree 40).run' { place := small }).run = some (.error .stackOverflow) := by
  decide +kernel

/-- Heap blocks of 64 bytes until `rawAlloc` fails (true) or `n` succeeded (false). -/
def fillHeap : Nat → MemM Bool
  | 0 => pure false
  | n + 1 => do
    match ← rawAlloc 64 8 with
    | none => pure true
    | some _ => fillHeap n

/-- (2) Heap traffic leaves the slack alone: the heap fills the address space, and a stack block
is still made. -/
def heapThenStack : MemM Bool := do
  let full ← fillHeap 10
  let p ← allocStack 8 8
  free p
  pure full

theorem s2_heap_leaves_slack :
    (heapThenStack.run' (withBudget small 16)).run = some (.ok true) := by
  decide +kernel

/-- A placement that puts block 0 at the last byte of the address space. -/
def atLimit : Placement :=
  { propose := fun b => if b = 0 then some (2 ^ 20 - 1) else none, addrLimit := 2 ^ 20 }

def blockAtLimitThenStack : MemM Unit := do
  let _ ← alloc .heap 1 1
  let p ← allocStack 8 8
  free p

/-- (3) A block at the end of the address space leaves the slack alone. -/
theorem s3_limit_leaves_slack :
    (blockAtLimitThenStack.run' (withBudget atLimit 64)).run = some (.ok ()) := by
  decide +kernel

/-- (3) Without a budget, the old model: every later fallback fails. -/
theorem s3_noBudget :
    (blockAtLimitThenStack.run' { place := atLimit }).run = some (.error .stackOverflow) := by
  decide +kernel

/-- `n` nested stack blocks of 8 bytes (charge 16 each), freed LIFO. -/
def nest : Nat → MemM Unit
  | 0 => pure ()
  | n + 1 => do let p ← allocStack 8 8; nest n; free p

/-- Exactly at the budget: 3 blocks fit in 48 bytes, the 4th overflows. -/
theorem budget_fits : ((nest 3).run' (withBudget small 48)).run = some (.ok ()) := by decide +kernel
theorem budget_overflows :
    ((nest 4).run' (withBudget small 48)).run = some (.error .stackOverflow) := by decide +kernel

/-- The general form: a block whose charge passes the budget overflows, under every placement. -/
example (m : Mem) (h : (m.stackOf m.current).budget = some 0) :
    ((allocStack 8 8).run m).run = some (.error .stackOverflow) :=
  alloc_stack_overflow h (by simp [stackCharge])

/-- A recursive call's frame charges `frameBase` (16): 6 frames fit in 96 bytes, 7 do not. -/
def down : Nat → MemM Unit
  | 0 => do enterFrame; leaveFrame
  | n + 1 => do enterFrame; down n; leaveFrame

theorem frames_fit : ((down 5).run' (withBudget small 96)).run = some (.ok ()) := by decide +kernel
theorem frames_overflow :
    ((down 6).run' (withBudget small 96)).run = some (.error .stackOverflow) := by decide +kernel

/-- **Splittable room is unsound** (`docs/sep-full-state.md` §Stack depth): `b`, `b'`, then a
`free` of `b` below the top, then `b''`. A credit returned by that `free` would pay for `b''` in
the budget `charge b + charge b'`; the stack's slack is still 0, and `b''` overflows. -/
def outOfOrder : MemM Unit := do
  let b ← allocStack 8 8
  let _ ← allocStack 8 8
  free b
  let _ ← allocStack 8 8

theorem splitRoom_cx : (outOfOrder.run' (withBudget small 32)).run = some (.error .stackOverflow) := by
  decide +kernel

/-- The LIFO order of the same frees gives the charge back. -/
def inOrder : MemM Unit := do
  let _ ← allocStack 8 8
  let b' ← allocStack 8 8
  free b'
  let _ ← allocStack 8 8

theorem lifo_returns : (inOrder.run' (withBudget small 32)).run = some (.ok ()) := by decide +kernel

/-- A placement with the native layout of MM-18 E1/E1': the caller's local (block 0), an inlined
callee's local above it (block 1) and a later local of the caller on the callee's dead slot
(block 2). -/
def native : Placement :=
  { propose := fun b => if b = 0 then some 0x10000 else if b = 1 ∨ b = 2 then some 0x10040 else none }

/-- The addresses of the caller's `x`, the inlined callee's `y` and the caller's later `z`. -/
def callerInl : MemM (Int × Int × Int) := do
  let x ← allocStack 8 8
  let ax ← ptrAddr x
  let y ← allocStack 8 8
  let ay ← ptrAddr y
  free y
  let z ← allocStack 8 8
  let az ← ptrAddr z
  free z
  free x
  pure (ax, ay, az)

/-- E1 and E1': under a budget the native layout is still a placement's: `y` above `x`, and `z`
on `y`'s address. (A model with LIFO addresses would prove `y < x` and `z ≠ y`.) -/
theorem e1_native_layout :
    (callerInl.run' (withBudget native 4096)).run = some (.ok (0x10000, 0x10040, 0x10040)) := by
  decide +kernel

#print axioms s1_free_returns
#print axioms s2_heap_leaves_slack
#print axioms s3_limit_leaves_slack
#print axioms budget_overflows
#print axioms splitRoom_cx
#print axioms e1_native_layout
