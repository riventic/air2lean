import AllocTranslated.FbaLinux
import AllocTranslated.FbaMacos
import AllocTranslated.PageLinux
import AllocTranslated.PageMacos
import ZigLean.Mem.AllocLemmas

/-!
# Translated allocators: executable regressions (`check.sh`)

`FixedBufferAllocator` is translated from its AIR, `mem.Allocator`'s wrappers included, with
its vtable call as an ordinary indirect call. Its results equal the native run of the same
functions (`expected.txt`, `native.zig`) on both targets. The page allocator reaches the
trusted page-mapping model (`ZigLean/Os/Mmap.lean`, premise OSM-01); on the schedule that the
oracle `fun _ => 0` picks its results equal the native ones too.
-/

namespace AllocTranslated.Eval

def word (r : Zig.MemM (BitVec 64)) (m : Zig.Mem) : String :=
  match (r.run m).run with
  | some (.ok (v, _)) => s!"ok {v.toNat}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

def flag (r : Zig.MemM Bool) (m : Zig.Mem) : String :=
  match (r.run m).run with
  | some (.ok (v, _)) => s!"ok {if v then 1 else 0}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

section Linux
open AllocTranslated.FbaLinux
#guard [word (fba_sum 0) (mem0 .fresh), word (fba_sum 10) (mem0 .fresh), word (fba_sum 256) (mem0 .fresh),
  word (fba_sum 257) (mem0 .fresh)] = ["ok 0", "ok 10", "ok 256", "ok 0"]
#guard word ((BitVec.zeroExtend 64 ·) <$> fba_create 7) (mem0 .fresh) = "ok 7"
#guard [flag (fba_resize 10 20) (mem0 .fresh), flag (fba_resize 10 300) (mem0 .fresh), flag (fba_resize 0 5) (mem0 .fresh),
  flag (fba_resize 10 0) (mem0 .fresh)] = ["ok 1", "ok 0", "ok 0", "ok 1"]
#guard [word (fba_reset 100) (mem0 .fresh), word (fba_reset 200) (mem0 .fresh), word (fba_reset 0) (mem0 .fresh)] =
  ["ok 200", "ok 400", "ok 0"]
-- `@returnAddress` reads the explicit oracle; any values give the same results.
#guard word (fba_sum 10) { (mem0 .fresh) with arbitrary := #[7, 9, 11] } = "ok 10"
end Linux

section Macos
open AllocTranslated.FbaMacos
#guard [word (fba_sum 0) (mem0 .fresh), word (fba_sum 10) (mem0 .fresh), word (fba_sum 256) (mem0 .fresh),
  word (fba_sum 257) (mem0 .fresh)] = ["ok 0", "ok 10", "ok 256", "ok 0"]
#guard [flag (fba_resize 10 20) (mem0 .fresh), flag (fba_resize 10 300) (mem0 .fresh)] = ["ok 1", "ok 0"]
#guard [word (fba_reset 100) (mem0 .fresh), word (fba_reset 200) (mem0 .fresh)] = ["ok 200", "ok 400"]
end Macos

/-- The first schedule's result of a concurrent page-allocator client. -/
def first {α : Type} [ToString α] (main : Zig.ConcM Tgt α) (dispatch : Tgt → Zig.ConcM Tgt Unit)
    (m : Zig.Mem) : String :=
  match (Zig.Sched.run ⟨.any, .available⟩ dispatch 10000 (fun _ => 0) main m).run with
  | some (.ok (v, _)) => s!"ok {v}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

instance : ToString (BitVec 64) := ⟨fun v => toString v.toNat⟩
instance : ToString (BitVec 32) := ⟨fun v => toString v.toNat⟩

section PageLinux
open AllocTranslated.PageLinux
#guard [first (page_sum 0) dispatch (mem0 .fresh), first (page_sum 10) dispatch (mem0 .fresh),
  first (page_sum 10000) dispatch (mem0 .fresh)] = ["ok 0", "ok 10", "ok 10000"]
#guard first (page_create 7) dispatch (mem0 .fresh) = "ok 7"
-- `resize` within a page; across pages it fails (x86_64 stacks grow down, so a `resize`, which
-- may not move, does not call `mremap`); a shrink unmaps the tail page. The native x86_64-linux run
-- agrees (`expected-linux.txt`).
#guard [first (page_resize 10 20) dispatch (mem0 .fresh), first (page_resize 10 5000) dispatch (mem0 .fresh),
  first (page_resize 8192 10) dispatch (mem0 .fresh)] = ["ok true", "ok false", "ok true"]
-- Every mapping fails: the allocator's `OutOfMemory` path, no illegal behaviour.
#guard first (page_sum 10) dispatch { (mem0 .fresh) with allocPolicy := { fails := fun _ _ => true } } =
  "ok 0"
-- M03 over the translated allocator: several failures in one run, each one `mmap` attempt
-- (`Mem.mapDenied`). Each `page_sum` maps once, so the attempt index is the request index; a
-- failed request gives 0, and every success is unmapped again (`defer a.free`).
def sums (ns : List (BitVec 64)) : Zig.ConcM Tgt (List (BitVec 64)) := ns.mapM page_sum
def sumsUnder (P : Zig.AllocPolicy) (ns : List (BitVec 64)) : String :=
  first (sums ns) dispatch { (mem0 .fresh) with allocPolicy := P }
instance : ToString (List (BitVec 64)) := ⟨fun l => toString (l.map BitVec.toNat)⟩
#guard sumsUnder { failures := [0, 2] } [10, 10, 10, 10] = "ok [0, 10, 0, 10]"
#guard sumsUnder { fails := fun i _ => i % 2 == 1 } [10, 10, 10, 10] = "ok [10, 0, 10, 0]"
-- The cap and an oracle by size see the page-rounded mapping length (4 KiB pages).
#guard sumsUnder { maxBytes := 8192 } [10, 10000, 4096] = "ok [10, 0, 4096]"
#guard sumsUnder { fails := fun _ n => 8192 < n } [10, 10000, 4096] = "ok [10, 0, 4096]"
-- A finite policy and its oracle form (`AllocPolicy.asOracle`, `mapDenied_asOracle`) agree.
#guard let P : Zig.AllocPolicy := { maxBytes := 8192, failures := [1, 3] }
  let ns : List (BitVec 64) := [10, 10, 10000, 10, 4096]
  sumsUnder P ns = sumsUnder P.asOracle ns ∧ sumsUnder P ns = "ok [10, 0, 0, 0, 4096]"
end PageLinux

section PageMacos
open AllocTranslated.PageMacos
#guard [first (page_sum 10) dispatch (mem0 .fresh), first (page_create 7) dispatch (mem0 .fresh)] =
  ["ok 10", "ok 7"]
-- 16 KiB pages: the native results of `expected.txt` (recorded on aarch64-macos); no `mremap`,
-- so a growth past the page fails.
#guard [first (page_resize 10 20) dispatch (mem0 .fresh), first (page_resize 10 5000) dispatch (mem0 .fresh),
  first (page_resize 8192 10) dispatch (mem0 .fresh), first (page_resize 10 20000) dispatch (mem0 .fresh)] =
  ["ok true", "ok true", "ok true", "ok false"]
#guard [first (page_sum 0) dispatch (mem0 .fresh), first (page_sum 10000) dispatch (mem0 .fresh)] = ["ok 0", "ok 10000"]
end PageMacos

end AllocTranslated.Eval
