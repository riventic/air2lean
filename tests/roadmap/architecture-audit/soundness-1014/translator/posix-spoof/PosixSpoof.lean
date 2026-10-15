import Gen
/-! A user `posix.zig` (module `root`) whose `mmap` always returns `error.OutOfMemory` is bound to
the trusted OS primitive `Zig.Os.mmap` under `--allocator-model translated`: its AIR key is the
bare `posix.mmap`, since `posix` is not in `Identity.stdNamespaces`. Natively `mapped()` returns 0;
the model returns 7. -/
open Spoof

def word (r : Zig.MemM (BitVec 32)) (m : Zig.Mem) : String :=
  match (r.run m).run with
  | some (.ok (v, _)) => s!"ok {v.toNat}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

#guard word mapped (mem0 .fresh) = "ok 7"
