import AllocFba.Gen

/-!
# The translated client evaluates to the native results (`expected.txt`, `native.zig`)

Every `std.mem.Allocator` wrapper and the `FixedBufferAllocator` are translated from the AIR
(`--allocator-model translated`); `@returnAddress()` reads the oracle `Mem.arbitrary`, so other
oracle values give the same results.
-/

namespace AllocFba.Eval

open AllocFba.Gen

def word {n : Nat} (r : Zig.MemM (BitVec n)) (m : Zig.Mem) : String :=
  match (r.run m).run with
  | some (.ok (v, _)) => s!"{v.toNat}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

#guard [word (fba_client 0) mem0, word (fba_client 5) mem0, word (fba_client 255) mem0] =
  ["1", "16", "510"]
#guard [word (fba_create 7) mem0, word (fba_aligned 3) mem0, word (fba_aligned 64) mem0,
  word (fba_dupe 9) mem0, word (fba_sentinel 4) mem0, word (fba_sentinel 20) mem0,
  word (fba_realloc_move 42) mem0] = ["7", "3", "1", "11", "7", "0", "42"]
#guard word (fba_client 5) { mem0 with arbitrary := #[3, 1, 4, 1, 5] } = "16"

end AllocFba.Eval
