import AllocTranslated.FbaLinux
import AllocTranslated.FbaMacos
import AllocTranslated.PageLinux
import AllocTranslated.PageMacos

/-!
# Translated allocators: executable regressions (`check.sh`)

`FixedBufferAllocator` is translated from its AIR, `mem.Allocator`'s wrappers included, with
its vtable call as an ordinary indirect call. Its results equal the native run of the same
functions (`expected.txt`, `native.zig`) on both targets. The page allocator reaches the
trusted `posix.mmap` stub (`ZigLean/Os/Mmap.lean`), which throws `.unspecified` until P2's
model replaces it, on every schedule the oracle `fun _ => 0` picks.
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

/-- The first schedule's outcome of a concurrent page-allocator client. -/
def first {α : Type} (main : Zig.ConcM Tgt α) (dispatch : Tgt → Zig.ConcM Tgt Unit)
    (m : Zig.Mem) : String :=
  match (Zig.Sched.run dispatch 10000 (fun _ => 0) main m).run with
  | some (.ok _) => "ok"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

#guard first (Tgt := AllocTranslated.PageLinux.Tgt) (AllocTranslated.PageLinux.page_sum 10)
  AllocTranslated.PageLinux.dispatch AllocTranslated.PageLinux.mem0 = "fail Zig.Error.unspecified"
#guard first (Tgt := AllocTranslated.PageMacos.Tgt) (AllocTranslated.PageMacos.page_create 7)
  AllocTranslated.PageMacos.dispatch AllocTranslated.PageMacos.mem0 = "fail Zig.Error.unspecified"
-- A zero-length allocation returns the integer sentinel without reaching the OS.
#guard first (Tgt := AllocTranslated.PageLinux.Tgt) (AllocTranslated.PageLinux.page_sum 0)
  AllocTranslated.PageLinux.dispatch AllocTranslated.PageLinux.mem0 = "ok"

end AllocTranslated.Eval
