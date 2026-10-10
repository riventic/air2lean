import AllocTranslated.FbaLinux
import AllocTranslated.FbaMacos
import AllocTranslated.PageLinux
import AllocTranslated.PageMacos

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
#guard [word (fba_sum 0) mem0, word (fba_sum 10) mem0, word (fba_sum 256) mem0,
  word (fba_sum 257) mem0] = ["ok 0", "ok 10", "ok 256", "ok 0"]
#guard word ((BitVec.zeroExtend 64 ·) <$> fba_create 7) mem0 = "ok 7"
#guard [flag (fba_resize 10 20) mem0, flag (fba_resize 10 300) mem0, flag (fba_resize 0 5) mem0,
  flag (fba_resize 10 0) mem0] = ["ok 1", "ok 0", "ok 0", "ok 1"]
#guard [word (fba_reset 100) mem0, word (fba_reset 200) mem0, word (fba_reset 0) mem0] =
  ["ok 200", "ok 400", "ok 0"]
-- `@returnAddress` reads the explicit oracle; any values give the same results.
#guard word (fba_sum 10) { mem0 with arbitrary := #[7, 9, 11] } = "ok 10"
end Linux

section Macos
open AllocTranslated.FbaMacos
#guard [word (fba_sum 0) mem0, word (fba_sum 10) mem0, word (fba_sum 256) mem0,
  word (fba_sum 257) mem0] = ["ok 0", "ok 10", "ok 256", "ok 0"]
#guard [flag (fba_resize 10 20) mem0, flag (fba_resize 10 300) mem0] = ["ok 1", "ok 0"]
#guard [word (fba_reset 100) mem0, word (fba_reset 200) mem0] = ["ok 200", "ok 400"]
end Macos

/-- The first schedule's result of a concurrent page-allocator client. -/
def first {α : Type} [ToString α] (main : Zig.ConcM Tgt α) (dispatch : Tgt → Zig.ConcM Tgt Unit)
    (m : Zig.Mem) : String :=
  match (Zig.Sched.run dispatch 10000 (fun _ => 0) main m).run with
  | some (.ok (v, _)) => s!"ok {v}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

instance : ToString (BitVec 64) := ⟨fun v => toString v.toNat⟩
instance : ToString (BitVec 32) := ⟨fun v => toString v.toNat⟩

section PageLinux
open AllocTranslated.PageLinux
#guard [first (page_sum 0) dispatch mem0, first (page_sum 10) dispatch mem0,
  first (page_sum 10000) dispatch mem0] = ["ok 0", "ok 10", "ok 10000"]
#guard first (page_create 7) dispatch mem0 = "ok 7"
-- `resize` within a page; across pages it fails (x86_64 stacks grow down, so a `resize`, which
-- may not move, does not call `mremap`); a shrink unmaps the tail page. The native x86_64-linux run
-- agrees (`expected-linux.txt`).
#guard [first (page_resize 10 20) dispatch mem0, first (page_resize 10 5000) dispatch mem0,
  first (page_resize 8192 10) dispatch mem0] = ["ok true", "ok false", "ok true"]
-- Every mapping fails: the allocator's `OutOfMemory` path, no illegal behaviour.
#guard first (page_sum 10) dispatch { mem0 with allocPolicy := { fails := fun _ _ => true } } =
  "ok 0"
end PageLinux

section PageMacos
open AllocTranslated.PageMacos
#guard [first (page_sum 10) dispatch mem0, first (page_create 7) dispatch mem0] =
  ["ok 10", "ok 7"]
-- 16 KiB pages: the native results of `expected.txt` (recorded on aarch64-macos); no `mremap`,
-- so a growth past the page fails.
#guard [first (page_resize 10 20) dispatch mem0, first (page_resize 10 5000) dispatch mem0,
  first (page_resize 8192 10) dispatch mem0, first (page_resize 10 20000) dispatch mem0] =
  ["ok true", "ok true", "ok true", "ok false"]
#guard [first (page_sum 0) dispatch mem0, first (page_sum 10000) dispatch mem0] = ["ok 0", "ok 10000"]
end PageMacos

end AllocTranslated.Eval
