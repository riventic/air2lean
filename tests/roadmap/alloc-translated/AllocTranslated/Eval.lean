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

/-- A run's result from the memory `m`, its value printed by `fmt`. -/
def shown {α : Type} (fmt : α → String) (r : Zig.MemM α) (m : Zig.Mem) : String :=
  match (r.run m).run with
  | some (.ok (v, _)) => s!"ok {fmt v}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

/-- Words as `native.zig` prints a row: decimal, separated by spaces. -/
def words (vs : List (BitVec 64)) : String := " ".intercalate (vs.map fun v => toString v.toNat)

def word : Zig.MemM (BitVec 64) → Zig.Mem → String := shown fun v => toString v.toNat

def flag : Zig.MemM Bool → Zig.Mem → String := shown fun v => if v then "1" else "0"

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

/-! ## M02: the fixed buffer's growth by `remap` and `realloc` against the native run

`fba.zig`'s `fba_grow` observes a growth as one word (its bits and the buffer's end index are in
`fba.zig`). `fbaGrowLine` prints the model's results in the format of `native.zig`'s `fba_grow`
line; `check.sh` compares it with `expected-linux.txt` and `expected.txt`, the files the native
run is compared with. -/

/-- The five growths of one `native.zig` row (`how`: `0` is `remap`, `1` is `realloc`), one after
another in one run as natively: in place as the last allocation, a shrink, behind another block,
past the buffer, and behind another block past the buffer. -/
def fbaGrowRow (grow : BitVec 64 → BitVec 64 → BitVec 8 → Bool → Zig.MemM (BitVec 64))
    (how : BitVec 8) : Zig.MemM (List (BitVec 64)) :=
  [(10, 20, false), (100, 10, false), (10, 20, true), (10, 300, false), (10, 250, true)].mapM
    fun (n, m, behind) => grow n m how behind

/-- The model's `fba_grow` line. -/
def fbaGrowLine (grow : BitVec 64 → BitVec 64 → BitVec 8 → Bool → Zig.MemM (BitVec 64))
    (m : Zig.Mem) : String :=
  let row := fun how => shown words (fbaGrowRow grow how) m
  s!"fba_grow remap {row 0} realloc {row 1}"

/-- The model's `fba_grow` line for x86_64-linux (`expected-linux.txt`). -/
def fbaGrowLinux : IO Unit := IO.println (fbaGrowLine FbaLinux.fba_grow (FbaLinux.mem0 .fresh))

/-- The model's `fba_grow` line for aarch64-macos (`expected.txt`). -/
def fbaGrowMacos : IO Unit := IO.println (fbaGrowLine FbaMacos.fba_grow (FbaMacos.mem0 .fresh))

/-- The first schedule's result of a concurrent page-allocator client, printed by `fmt` from
the value and the final memory. -/
def firstWith {α : Type} (fmt : α → Zig.Mem → String) (main : Zig.ConcM Tgt α)
    (dispatch : Tgt → Zig.ConcM Tgt Unit) (m : Zig.Mem) : String :=
  match (Zig.Sched.run ⟨.any, .available⟩ dispatch 10000 (fun _ => 0) main m).run with
  | some (.ok (v, m')) => s!"ok {fmt v m'}"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

/-- The first schedule's result of a concurrent page-allocator client. -/
def first {α : Type} [ToString α] : Zig.ConcM Tgt α → (Tgt → Zig.ConcM Tgt Unit) → Zig.Mem → String :=
  firstWith fun v _ => toString v

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
-- failed request gives 0, and every success is unmapped again (`defer a.free`): no live mapping
-- is left at the end.
def sums (ns : List (BitVec 64)) : Zig.ConcM Tgt (List (BitVec 64)) := ns.mapM page_sum
def sumsUnder (P : Zig.AllocPolicy) (ns : List (BitVec 64)) : String :=
  firstWith (fun v m => s!"{v} live {(m.blocks.filter fun b => b.live && b.kind matches .mapped _).size}")
    (sums ns) dispatch { (mem0 .fresh) with allocPolicy := P }
#guard sumsUnder { failures := [0, 2] } [10, 10, 10, 10] = "ok [0, 10, 0, 10] live 0"
#guard sumsUnder { fails := fun i _ => i % 2 == 1 } [10, 10, 10, 10] = "ok [10, 0, 10, 0] live 0"
-- The cap and an oracle by size see the page-rounded mapping length (4 KiB pages).
#guard sumsUnder { maxBytes := 8192 } [10, 10000, 4096] = "ok [10, 0, 4096] live 0"
#guard sumsUnder { fails := fun _ n => 8192 < n } [10, 10000, 4096] = "ok [10, 0, 4096] live 0"
-- A finite policy and its oracle form (`AllocPolicy.asOracle`, `mapDenied_asOracle`) agree.
#guard let P : Zig.AllocPolicy := { maxBytes := 8192, failures := [1, 3] }
  let ns : List (BitVec 64) := [10, 10, 10000, 10, 4096]
  let r := sumsUnder P ns
  r = sumsUnder P.asOracle ns ∧ r = "ok [10, 0, 0, 0, 4096] live 0"
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

/-! ## M02: growth by `remap` and `realloc` against the native run

`page.zig`'s `page_grow`, `page_grow_blocked` and `page_grow_stale` observe a growth as one word
(the bits are in `page.zig`). `growLines` prints the model's results in the format of
`native.zig`'s `page_grow` lines; `check.sh` compares them with `expected-linux.txt` and
`expected.txt`, the files the native run is compared with. -/

/-- The five growths of one `native.zig` row (`how`: `0` is `remap`, `1` is `realloc`), one after
another in one run: in place after the pages behind the block were freed, within the page, a
shrink, a length no address space holds, and one byte into a neighbouring live block's pages. -/
def growRow {Tgt : Type}
    (grow : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 8 → Zig.ConcM Tgt (BitVec 64))
    (blocked : BitVec 64 → BitVec 8 → Zig.ConcM Tgt (BitVec 64)) (how : BitVec 8) :
    Zig.ConcM Tgt (List (BitVec 64)) := do
  let a ← grow 81920 10 49152 how
  let b ← grow 10 10 20 how
  let c ← grow 49152 49152 10 how
  let d ← grow 10 10 (2 ^ 47) how
  let e ← blocked 10 how
  return [a, b, c, d, e]

/-- A run's result as `native.zig` prints it. A read that the model calls `.illegal` is the native
run's fault (`SIGSEGV`/`SIGBUS` of the child process): `fault`. -/
def nativeWord {Tgt α : Type} (fmt : α → String) (main : Zig.ConcM Tgt α)
    (dispatch : Tgt → Zig.ConcM Tgt Unit) (m : Zig.Mem) : String :=
  match (Zig.Sched.run ⟨.any, .available⟩ dispatch 10000 (fun _ => 0) main m).run with
  | some (.ok (v, _)) => s!"ok {fmt v}"
  | some (.error .illegal) => "fault"
  | some (.error e) => s!"fail {repr e}"
  | none => "diverge"

def growLines {Tgt : Type} (dispatch : Tgt → Zig.ConcM Tgt Unit) (m : Zig.Mem)
    (grow : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 8 → Zig.ConcM Tgt (BitVec 64))
    (blocked stale : BitVec 64 → BitVec 8 → Zig.ConcM Tgt (BitVec 64)) : List String :=
  let row := fun how => nativeWord words (growRow grow blocked how) dispatch m
  let old := fun how => nativeWord (fun v => toString v.toNat) (stale 10 how) dispatch m
  [s!"page_grow remap {row 0} realloc {row 1}", s!"page_grow_stale remap {old 0} realloc {old 1}"]

/-- The main thread's stack budget of the compared runs: 8 MiB, the default main-thread stack of
both targets. As natively, the stack is a reserve of its own (`Mem.withStack`, MM-18, premise
STK-02) that no mapping meets. Without one (`mem0 .fresh` alone) a stack block of a wrapper
(0.17.1's `reallocAdvanced` keeps its result in one) lies right behind the last mapping, so
`mremap` finds no room and moves where the native kernel grows in place: one of the legal
outcomes the proofs cover, but not the native layout. -/
def stackBytes : Nat := 8 * 1024 * 1024

/-- The model's `page_grow` lines for x86_64-linux (`expected-linux.txt`). -/
def growLinux : IO Unit :=
  (growLines PageLinux.dispatch ((PageLinux.mem0 .fresh).withStack stackBytes) PageLinux.page_grow
    PageLinux.page_grow_blocked PageLinux.page_grow_stale).forM IO.println *> pure ()

/-- The model's `page_grow` lines for aarch64-macos (`expected.txt`). -/
def growMacos : IO Unit :=
  (growLines PageMacos.dispatch ((PageMacos.mem0 .fresh).withStack stackBytes) PageMacos.page_grow
    PageMacos.page_grow_blocked PageMacos.page_grow_stale).forM IO.println *> pure ()

section GrowLinux
open AllocTranslated.PageLinux
-- What the kernel decides is the model's oracle. With room behind the block the kernel grew it
-- in place (13); `mremapMoves` is the other legal choice, a move (15): the bytes are kept either
-- way. A denied growth (`fails`) is the failure path: the old block keeps its bytes (4).
#guard first (page_grow 81920 10 49152 0) dispatch (mem0 .fresh) = "ok 13"
#guard first (page_grow 81920 10 49152 0) dispatch
  { (mem0 .fresh) with allocPolicy := { os := { mremapMoves := fun _ _ => true } } } = "ok 15"
#guard first (page_grow 81920 10 49152 0) dispatch
  { (mem0 .fresh) with allocPolicy := { fails := fun i _ => i == 1 } } = "ok 4"
-- `realloc` after a denied `mremap` takes a new mapping, copies and frees the old one (15); with
-- that mapping denied too it fails and the old block stays (4).
#guard first (page_grow 81920 10 49152 1) dispatch
  { (mem0 .fresh) with allocPolicy := { fails := fun i _ => i == 1 } } = "ok 15"
#guard first (page_grow 81920 10 49152 1) dispatch
  { (mem0 .fresh) with allocPolicy := { fails := fun i _ => i ≥ 1 } } = "ok 4"
-- No run leaves a mapping behind: success in place, moved, and failure.
#guard [0, 1].all fun how =>
  firstWith (fun (_ : List (BitVec 64)) m => s!"{(m.blocks.filter fun b => b.live && b.kind matches .mapped _).size}")
    (growRow page_grow page_grow_blocked how) dispatch (mem0 .fresh) = "ok 0"
end GrowLinux

end AllocTranslated.Eval
