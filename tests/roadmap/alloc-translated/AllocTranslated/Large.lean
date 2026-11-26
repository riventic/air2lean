import AllocTranslated.Eval

/-!
# M03: requests above 1 MiB through the translated `PageAllocator` (compiled runner)

`page.zig`'s `page_sum` asks `std.heap.page_allocator` for `n` bytes, writes every byte, reads
every byte back and frees the block. Here it runs for sizes above the old fixed cap of the model
(1 MiB, `Zig.maxAllocBytes`) under the model's default policy (`{}`: no cap), over the translated
`PageAllocator` down to `Zig.Os.mmap`/`munmap` (premise OSM-01). `line` prints the results in the
format of `native.zig`'s `page_large` line; `check.sh` compares it with `expected-linux.txt` and
`expected.txt`, the files the native run is compared with.

This module is the root of the executable `alloc-translated-large`
(`tests/roadmap/lakefile.toml`) and nothing here is evaluated at elaboration time: Lean's
interpreter keeps a frame for every iteration of a `Zig.loop` in `Zig.ConcM` (the loop's next
round is a call through `CoN.bind`'s continuation, which compiled code makes as a tail call), so
`#eval` of these sizes ends in "deep recursion was detected". The compiled run needs a stack of
any size and about 350 MiB per MiB requested (the model keeps every byte of the block).
-/

namespace AllocTranslated.Large
open AllocTranslated.Eval

/-- The requested sizes: one byte above the old fixed cap of 1 MiB, and 4 MiB. -/
def sizes : List (BitVec 64) := [1048577, 4194304]

/-- The model's `page_large` line: `pageSum` of each of `sizes`, one after another in one run from
`m` under the policy `P`. A request the policy denies gives 0 (`page_sum`'s `catch return 0`). -/
def line {Tgt : Type} (dispatch : Tgt → Zig.ConcM Tgt Unit) (m : Zig.Mem)
    (pageSum : BitVec 64 → Zig.ConcM Tgt (BitVec 64)) (P : Zig.AllocPolicy := {}) : String :=
  s!"page_large {nativeWord words (sizes.mapM pageSum) dispatch { m with allocPolicy := P }}"

/-- The line over the translation for `os` (`linux`: x86_64-linux, `expected-linux.txt`; `macos`:
aarch64-macos, `expected.txt`), from the program's start memory with the main thread's stack
reserve of the compared runs. -/
def lineOf (os : String) (P : Zig.AllocPolicy := {}) : Option String :=
  match os with
  | "linux" => some (line PageLinux.dispatch ((PageLinux.mem0 .fresh).withStack stackBytes) PageLinux.page_sum P)
  | "macos" => some (line PageMacos.dispatch ((PageMacos.mem0 .fresh).withStack stackBytes) PageMacos.page_sum P)
  | _ => none

end AllocTranslated.Large

open AllocTranslated.Large in
/-- `alloc-translated-large OS`: the model's `page_large` line under the default policy.
`alloc-translated-large OS capped`: the same run under the differential harness's policy, the old
fixed cap (`AllocPolicy.harness`): every request is denied, which is what a model that kept the
cap would print (`check.sh` requires that this line is not the native one). -/
def main (args : List String) : IO UInt32 := do
  let run (os : String) (P : Zig.AllocPolicy) : IO UInt32 :=
    match lineOf os P with
    | some l => do IO.println l; pure 0
    | none => do IO.eprintln s!"alloc-translated-large: unknown target {os}"; pure 2
  match args with
  | [os] => run os {}
  | [os, "capped"] => run os .harness
  | _ => do IO.eprintln "usage: alloc-translated-large linux|macos [capped]"; pure 2
