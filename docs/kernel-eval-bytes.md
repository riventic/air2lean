# Kernel evaluation of writes into page-sized blocks

Small writes into a page-sized byte array should remain practical for kernel
evaluation. The allocation/store regressions below write 16 bytes with
`memset`, then 4 bytes at offset zero, into a 4 KiB or 16 KiB block; they do
not write the whole block. Separate cases check the unchanged suffix and a
4-byte write at offset 4092.

`Zig.writeBytes` originally evaluated

```lean
a.extract 0 o ++ bs ++ a.extract (o + bs.size) a.size
```

Lean 4.34's kernel definition of `Array.extract` is a loop that indexes the
source and calls `Array.push` at each step (`Array.extract` in
`Init/Prelude.lean`). `Array.push` uses `List.concat` in that same module.
`Array.append` similarly folds with `Array.push` in
`Init/Data/Array/Basic.lean`. Thus even a
small write at offset zero rebuilds the entire untouched suffix, with repeated
linear traversals of the growing output. Native array implementations hide
this cost; kernel reduction must check the reference definitions.

Historical standard-library-only probes, each checked with `decide +kernel` and
`trace.Kernel`, isolate the old splice from the rest of the memory model:

| Array bytes | Outcome | Workload time | Peak sampled RSS |
| --- | --- | --- | --- |
| 64 | success | 0.337 s | 443824 KiB |
| 256 | 512 MiB cap | 0.770 s | 543824 KiB |
| 1024 | 512 MiB cap | 0.838 s | 544240 KiB |
| 4096 | kernel recursion error | 0.727 s | 523776 KiB |

The low memory cap makes the middle rows lower bounds, not completed runtime
measurements. Times exclude scheduler waiting. These development measurements
are historical observations, not a portable benchmark or current gate.

The private historical `T36.lean` reproducer failed both the undefined-byte and
zero-byte memset cases with `(kernel) deep recursion detected`: 1.429 s of
workload time, peak 879504 KiB. Shared-lock waiting is excluded from that time.
The initial pre-707 baseline full build passes; warm CAS workload times are
1.193 s (root), 0.191 s (diff), and 3.532 s (standalone files). Its 271 s wall time includes
shared-lock contention and must not be used as an implementation speed ratio.

The refinement keeps `Array Byte` and every memory-model result. It
uses the kernel's list spine directly:

```lean
(a.toList.take o ++ bs.toList ++ a.toList.drop (o + bs.size)).toArray
```

This traverses only the prefix and replacement before sharing the suffix.
Its equality theorem covers every array, offset and replacement, including
out-of-range inputs. The original equation remains available to symbolic
proofs, and a checked compiler simplification retains native array performance.

The retained allocation/memset/store and translated page-environment
`Lists.Open.push` regressions use the existing semantics. They add no
judgment, tactic, axiom, premise, admission or legacy proof dependency.

The original blocker is engine-ledger row #77, introduced by PR #387 and
closed by the shared refinement. PR #449 also completed the tutorial controls
and closed row #74; the extra regressions here do not reopen either row.

## Implementation

`writeBytes` now shares its list suffix. `writeBytes_eq` is a checked
unconditional equality to the original equation above. Existing proofs use that
equation explicitly; their theorem statements are unchanged. The standard
`csimp` attribute consumes a checked function equality derived from this theorem
to retain native array operations in compiled execution. There is no unchecked
compiler redirection or new kernel-escape allowance; both trust/framework gates
accept the change without allowance edits.

The definition is `irreducible` to elaborator unification, which keeps greedy
symbolic proof search from expanding concrete byte lists. Proofs can still
explicitly rewrite `writeBytes_eq`, and kernel reduction sees the list
definition. Without this transparency boundary, the existing WaitGroup proof
reached its recursion limit while trying a pure-step rule; its unchanged proof
builds with the boundary.

The existing `fsym` evaluator still tries ordinary normalization first. If a
closed natural-number size remains opaque, it reduces that closed term at full
transparency without retaining Meta-state changes. The ownership provider proves
the resulting size equality and transports its generic joined-ownership proof
along that equality. Terms with variables or metavariables never use this
fallback, and the symbolic resource is not unfolded. The existing Parts and
WaitGroup proofs need no client-specific steps.

The existing closed-array-size simplifier also returns an explicit equality
for a size reduced by the kernel. This preserves the original expression when
the simplifier transports a hypothesis across an irreducible definition; normal
declaration checking validates the conversion. The unchanged Deadline load
proof exercises this path without extra client steps.

The general equality was independently kernel-checked for arbitrary element
type as well as arbitrary source, offset and replacement (0.295 s, 363520 KiB).
The retained memory-model theorem specializes this general argument to `Byte`.

A historical standard-library native microbenchmark (2,000 writes into a 4 KiB array)
measured 26 ms for the original array splice and 61 ms for the plain list
splice. With the checked `csimp` equality, a second run measured 27 ms for
the original and 26 ms for the new operation, with identical final values.
These are historical operation-level probes, separate from memory-model
proofs. Native evaluation is used for timing, never to prove a theorem.

Historical probes isolating the component operations support the source-level diagnosis:
`Array.extract` alone succeeds at 64 elements (0.488 s, 415440 KiB), exceeds
the 512 MiB diagnostic cap at 256, and reports kernel deep recursion at 4096.
`Array.append` alone succeeds at 64 (0.361 s, 421616 KiB), and exceeds that
cap at 256 and 4096. These probes use only `Init` and `trace.Kernel`; they do
not depend on the project memory representation.

Retained regressions are `tests/roadmap/sep-auto/KernelBytes.lean` (undefined
and zero memset, 4 KiB and 16 KiB blocks, suffix preservation, end-of-page
write) and `tests/roadmap/alloc-translated/KernelBytes.lean` (the translated
`Lists.Open.push` with the real PageAllocator vtable and generated global
memory). The latter also proves the concrete start memory satisfies `Mem.FSeq`
using `Mem.init_fseq` and a kernel-checked `GlobalsFit` obligation.

The private historical T36 reproducer passed both 4 KiB cases at default
limits: 0.97 s, 736208 KiB peak RSS after integrating main 958596cf. The
private historical T32 page environment passed in 2.06 s, 1518832 KiB; that file
retained its original recursion option. A historical run of the retained page
fixture independently proved the admissible start memory and translated
`push` success at default limits in 1.51 s, 1491536 KiB. These historical
memory-model measurements are separate from the array-splice equality and
microbenchmarks; current acceptance comes from the retained regression files.
