import AllocArena.ArenaLinux
import AllocArena.ArenaMacos

/-!
# Translated `ArenaAllocator`: executable regressions (`check.sh`)

`std.heap.ArenaAllocator` (Zig 0.16.0, lock-free) is translated from its AIR with its child
allocator (`FixedBufferAllocator`, `page_allocator`) reached through ordinary indirect calls. On
the schedule that the oracle `fun _ => 0` picks (one thread), the results equal the native run of
the same functions (`expected.txt`, `native.zig`).
-/

namespace AllocArena.Eval

/-- The first schedule's result of a concurrent client. -/
def first {Tgt α : Type} [ToString α] (main : Zig.ConcM Tgt α) (dispatch : Tgt → Zig.ConcM Tgt Unit)
    (m : Zig.Mem) : String :=
  match (Zig.Sched.run dispatch 100000 (fun _ => 0) main m).run with
  | some (.ok (v, _)) => s!"ok {v}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

instance : ToString (BitVec 64) := ⟨fun v => toString v.toNat⟩
instance : ToString Bool := ⟨fun b => if b then "1" else "0"⟩

section Linux
open AllocArena.ArenaLinux
#guard [first (arena_sum 1) dispatch (mem0 .fresh), first (arena_sum 10) dispatch (mem0 .fresh),
  first (arena_sum 3000) dispatch (mem0 .fresh), first (arena_sum 5000) dispatch (mem0 .fresh)] =
  ["ok 1", "ok 10", "ok 0", "ok 0"]
#guard [first (arena_resize 10 20) dispatch (mem0 .fresh), first (arena_resize 10 5) dispatch (mem0 .fresh),
  first (arena_resize 10 100) dispatch (mem0 .fresh), first (arena_resize 10 4000) dispatch (mem0 .fresh)] =
  ["ok 1", "ok 1", "ok 0", "ok 0"]
#guard [first (arena_reset 10 true) dispatch (mem0 .fresh), first (arena_reset 10 false) dispatch (mem0 .fresh),
  first (arena_reset 500 true) dispatch (mem0 .fresh), first (arena_reset 1500 true) dispatch (mem0 .fresh)] =
  ["ok 229", "ok 229", "ok 7001", "ok 1"]
#guard [first (arena_page 10) dispatch (mem0 .fresh), first (arena_page 20000) dispatch (mem0 .fresh)] =
  ["ok 12", "ok 20002"]
-- Two live allocations do not overlap (`mutant.sh` breaks this).
#guard [first (arena_two 1) dispatch (mem0 .fresh), first (arena_two 100) dispatch (mem0 .fresh)] =
  ["ok 21", "ok 21"]
-- `@returnAddress` reads the explicit oracle; any values give the same results.
#guard first (arena_reset 10 true) dispatch { (mem0 .fresh) with arbitrary := #[7, 9, 11] } = "ok 229"
end Linux

section Macos
open AllocArena.ArenaMacos
#guard [first (arena_sum 10) dispatch (mem0 .fresh), first (arena_resize 10 20) dispatch (mem0 .fresh),
  first (arena_reset 500 true) dispatch (mem0 .fresh), first (arena_page 20000) dispatch (mem0 .fresh)] =
  ["ok 10", "ok 1", "ok 7001", "ok 20002"]
end Macos

end AllocArena.Eval
