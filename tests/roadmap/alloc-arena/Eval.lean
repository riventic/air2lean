import AllocArena.ArenaLinux
import AllocArena.ArenaMacos
import AllocArena.ArenaFixedLinux

/-!
# Translated `ArenaAllocator`: executable regressions (`check.sh`)

`std.heap.ArenaAllocator` (Zig 0.16.0, lock-free) is translated from its AIR with its child
allocator (`FixedBufferAllocator`, `page_allocator`) reached through ordinary indirect calls. On
the schedule that the oracle `fun _ => 0` picks (one thread), the results equal the native run of
the same functions (`expected.txt`, `native.zig`), with one exception: `arena_oom_free`, where the
stock arena's `free` forms an out-of-bounds pointer after a failed `alloc` (O-E). Natively that is
undefined behaviour without a visible effect (`true`); the translated `free` is illegal.

The patched arena (`ArenaFixedLinux`, `docs/upstream/arena-oob-gep.md`) equals its native run
(`expected-fixed.txt`, `native.zig` built with the patched standard library), `arena_oom_free`
included.
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
-- Three live allocations do not overlap (`mutant.sh` breaks this).
#guard [first (arena_three 1) dispatch (mem0 .fresh), first (arena_three 100) dispatch (mem0 .fresh)] =
  ["ok 321", "ok 321"]
-- `@returnAddress` reads the explicit oracle; any values give the same results.
#guard first (arena_reset 10 true) dispatch { (mem0 .fresh) with arbitrary := #[7, 9, 11] } = "ok 229"
-- O-E from real runs: natively `true` (undefined behaviour without a visible effect).
#guard first (arena_oom_free 8) dispatch (mem0 .fresh) = "fail Zig.Error.illegal"
#guard [first (arena_fit 55) dispatch (mem0 .fresh), first (arena_fit 60) dispatch (mem0 .fresh)] =
  ["ok 60055", "ok 60060"]
end Linux

section Fixed
open AllocArena.ArenaFixedLinux
#guard [first (arena_sum 1) dispatch (mem0 .fresh), first (arena_sum 10) dispatch (mem0 .fresh),
  first (arena_sum 3000) dispatch (mem0 .fresh), first (arena_sum 5000) dispatch (mem0 .fresh)] =
  ["ok 1", "ok 10", "ok 0", "ok 0"]
#guard [first (arena_resize 10 20) dispatch (mem0 .fresh), first (arena_resize 10 5) dispatch (mem0 .fresh),
  first (arena_resize 10 100) dispatch (mem0 .fresh), first (arena_resize 10 4000) dispatch (mem0 .fresh)] =
  ["ok 1", "ok 1", "ok 0", "ok 0"]
-- The in-place growth no longer includes the failed reservation, so the node grows less.
#guard [first (arena_reset 10 true) dispatch (mem0 .fresh), first (arena_reset 10 false) dispatch (mem0 .fresh),
  first (arena_reset 500 true) dispatch (mem0 .fresh), first (arena_reset 1500 true) dispatch (mem0 .fresh)] =
  ["ok 229", "ok 229", "ok 5001", "ok 15001"]
#guard [first (arena_page 10) dispatch (mem0 .fresh), first (arena_page 20000) dispatch (mem0 .fresh)] =
  ["ok 12", "ok 20002"]
#guard [first (arena_three 1) dispatch (mem0 .fresh), first (arena_three 100) dispatch (mem0 .fresh)] =
  ["ok 321", "ok 321"]
#guard first (arena_oom_free 8) dispatch (mem0 .fresh) = "ok 1"
-- A request that fits the node although its reservation would not: taken in the resize path (a
-- retry there would never end).
#guard [first (arena_fit 55) dispatch (mem0 .fresh), first (arena_fit 60) dispatch (mem0 .fresh)] =
  ["ok 60055", "ok 60060"]
end Fixed

section Macos
open AllocArena.ArenaMacos
#guard [first (arena_sum 10) dispatch (mem0 .fresh), first (arena_resize 10 20) dispatch (mem0 .fresh),
  first (arena_reset 500 true) dispatch (mem0 .fresh), first (arena_page 20000) dispatch (mem0 .fresh),
  first (arena_fit 55) dispatch (mem0 .fresh)] =
  ["ok 10", "ok 1", "ok 7001", "ok 20002", "ok 60055"]
end Macos

end AllocArena.Eval
