# Audit: recursive pointees in the error-storage cast check (#245, `cycles := true`)

Class: suspected SOUNDNESS (checker fail-open). Status: not confirmed. The analysis is sound;
the failing controls were stale. Fixed by retargeting the controls (branch
`codex/error-storage-cycles`).

## Report

Since #245 the "Finite symbolic error-storage model and checker controls" CI step
(`tests/roadmap/error-storage/Qualifier.lean`, part `native`, Zig 0.16.0) failed on `main` with
`accepted a representation-changing optional wrap`. #245 set `cycles := true` in
`castErrorCapability` (`Air2Lean/Check.lean`). The suspicion was that the capability fixpoint
starts optimistic, so a recursive type looks error-free and an error behind a cycle gets through.

## What the failing controls tested

The rejected-then-accepted inputs are the four `rejectWrap` mutants of the retained 0.15.2
`lists.listSum` cast `*Node → ?*Node` and four of the five qualifier mutants of `?*Node →
?*const Node`. Here `Node = struct { val: u32, next: ?*Node }`, so the pointee holds no error
storage. The mutants change only pointer metadata: the optional's `ptrAlign`, a `sentinel` flag,
`?*const Node`, `[*]Node` and `?[*]const Node`. The fifth mutant (bit-pointer host size) is still
rejected by the bit-pointer rule.

Before #245 the strict capability scan rejected every cycle ("unresolved or cyclic symbolic
storage provenance"). The only way through for a recursive pointee was the narrow
`qualifierOnly` / `optionalWrapOnly` exceptions, and the controls checked how narrow those
exceptions were. The same mutants over an acyclic error-free pointee (`next: *u32`) were always
accepted, because both capabilities are `false` and nothing exposes symbolic storage. After #245 a
recursive pointee gets the same verdict as an acyclic one. The controls had depended on the
blanket cycle rejection, not on any property of error storage.

## Why the analysis is sound

- `errorCapabilityScan` with `cycles` is a depth-first walk that cuts only at a type already on
  the current path. The cut type is still being walked higher up the path, and that first visit
  follows every one of its edges. So every type reachable from the root is visited, and the
  result is the least fixpoint of "reaches an `errorSet`/`errorUnion`". A cycle adds nothing and
  hides nothing. Unknown types, `anyerror` and the 1024-node budget still return `none`, which
  fails closed.
- The decoder comparison `sameTyUpToIds` is a bisimulation (greatest fixpoint) over pairs. Error
  set names are part of `Ty.head`, so two recursive types that differ only in an error domain
  past the cycle compare unequal.

Probe, run on `main` at d8a609802 with error storage reachable through the cycle. Every case
behaves as required:

| cast | verdict |
|---|---|
| `*ENode → ?*ENode'` (`ENode'` has another error domain) | rejected: exposes symbolic storage |
| `*ENode → *ENode''` (other domain reached only through `next`) | rejected |
| `*MA → *u32`, where `MA → *MB → *MA`, `MB → *MC`, `MC { e: E }` | rejected |
| `*u32 → *MA` (recovery) | rejected |
| `*ENode → ?*ENode`, `*ENode → *const ENode` | accepted (decoder unchanged) |

## Change

`Qualifier.lean` now checks the property itself rather than the side effect:

- **Agreement.** Each of the nine retained list mutants gets the same `checkOp` verdict as it
  gets when `Node.next` is the acyclic error-free `*u32`. A recursion-only exception or rejection
  in either direction fails this check.
- **Error-bearing recursion.** `Node.val` becomes the retained finite set `error{OutOfMemory}`.
  The exact wrap and the qualifier cast are still accepted. Six casts are rejected, each with its
  diagnostic checked: a target node over `error{Other}`, a node whose `Other` domain is reached
  only through `next`, `*u32`, the qualifier cast retargeted to either changed node, and recovery
  from `usize`.

Regression check: an optimistic cycle was injected into `errorCapabilityScan` (a child's
capability ignored when `cycles` is set). The new negatives then fail with `accepted an
error-domain-changing recursive pointer cast`, and `GlobalAlias.lean`'s
`calleeNestedPointerRecovery` fails as well. Without the injection, `main`'s analysis passes all
of them. The old controls failed on `main` and pass nowhere after #245. The new controls pass on
`main` and fail on the fail-open variant.

No checker change was needed. The `qualifierOnly` / `optionalWrapOnly` exceptions are now
reachable only when the capability walk does not finish (unknown types or an exhausted budget).
They keep the decoder by construction (same pointee id).
