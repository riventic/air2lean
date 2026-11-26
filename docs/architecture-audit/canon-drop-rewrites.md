# Canon's dropping rewrites against `Sem`: four boundaries

Class: SOUNDNESS of the certificate chain (V02), found while proving the preservation theorems
of the Canon rewrites that drop instructions (`Air2Lean/SemDrop.lean`). Status: finding 3 fixed
(the rewrite's condition); findings 2 and 4 open (they need a decision); finding 1 is a limit of
the statement, documented. Severity: latent (see "Reachability").

All four are kernel-checked in `tests/roadmap/air-semantics/CanonDrop.lean`, for every program
and call oracle (1 to 3 for every start memory, 4 on one memory). They are statements about the
formal AIR semantics `Sem` (`Air2Lean/Sem.lean`). None is a native miscompilation: the
translator's output for the canonical function is what the compiler's code does.

## 1. `dropDeadAllocPlaceholders`: no equality (the function before is stuck)

```
%0 = bitcast(*u8, @as(usize, 0))     ; Sema's placeholder of a comptime-resolved local
ret void
```

`Sem` has no value for an integer as a pointer operand, so `execFunc` of this function is stuck
(`CanonDrop.placeholder_before`). Without `%0` it returns (`placeholder_after`). So
`execFunc (R f) = execFunc f` is false (`placeholder_not_equal`).

What holds is the refinement `Drop.execFunc_drop_le`: `execFunc f ⊑ execFunc (R f)`. It is the
strongest statement over today's `Sem`, and it says nothing on the paths that run a placeholder.
An equality needs `Sem` to give the unread placeholder a meaning (a value that no operation
accepts), which changes the meaning that SEM-06 trusts: a maintainer decision. Until then the
rewrite stays on the `trusted-Canon` lines.

## 2. `dropDeadRuntimeLanePtrs`: not a refinement (the function before is `.illegal`)

```
%0 = arg(*@Vector(4, bool), 0)
%1 = arg(usize, 1)
%2 = ptr_elem_ptr(%0, %1)            ; runtime lane pointer, never read
ret void
```

With `%1 = 9`, `Sem` is `.illegal` at `%2`: `Sem.itemBase` checks the index against the vector's
count where the pointer is formed (`Sem.checkCount`), before it finds that the lane pointer type
is outside the fragment. Without `%2` the function returns (`CanonDrop.lanePtr_not_refined`). A
proof about the canonical function therefore does not show that the function before the rewrite
is free of illegal behaviour in `Sem`.

Options:

* state this rewrite as a refinement that also admits `.illegal` before (the usual
  undefined-behaviour refinement). It needs its own loop lemma (`.illegal` is not the bottom of
  `Zig.Result`'s order), and a theorem about the canonical function then says nothing about
  illegal behaviour of the function before;
* make the index check of an item pointer lazy in `Sem`, with the pointer poison of
  docs/research/V01-V02.md stage 1 (`Zig.ptrProject` total, illegal on use). An unread pointer
  then has no behaviour to lose, and the drop is an equality.

## 3. `itemReads`: a fold away from the pointer moves the index check (fixed)

```
%0 = arg(*[4]u8, 0)
%1 = arg(usize, 1)
%2 = arg(bool, 2)
%3 = ptr_elem_ptr(%0, %1)
cond_br(%2) { %5 = load(%3); ret %5 } else { ret 0 }
```

`Raw.itemReads` used to fold `%3` and its only reader `%5` into `%5 = ptr_elem_val(%0, %1)` at
the load. With `%1 = 9` and `%2 = false`, `Sem` is `.illegal` at `%3` before that fold and
returns `0` after it (`CanonDrop.itemReads_not_preserved`). The `ptr_elem_ptr`/`load` and
`slice_elem_ptr`/`load` patterns accepted a `load` anywhere after the pointer; only the
`load`/`array_elem_val` pattern required the second instruction directly after the first
(`nextNonDebug`).

By the same argument (not kernel-checked) the gap existed without a branch: a call between `%3`
and `%5` that panics or does not return ran before the check after the fold, and after it
before.

Fix: the two patterns now require `next[x.id]? == some u.id` too, so the check stays where it
was. `CanonDrop.lean`'s `main` checks that the rewrite leaves the function above alone. No
committed generated module changed: `scripts/gen-integrity.py check` passes for all 262 cases
with the condition in place, without a change to a golden or a `Gen.lean`.

## 4. `itemReads` on an adjacent pair: still no equality (the base may be out of its block)

```
%0 = arg(*[4]u8, 0)
%1 = arg(usize, 1)
%2 = ptr_elem_ptr(%0, %1)
%3 = load(%2)
ret %3
```

`Raw.itemReads` folds this to `%3 = ptr_elem_val(%0, %1)` (`main` checks it). Before the fold,
`%2` is `Zig.ptrProject`: illegal behaviour unless the base and the result are both inside the
base's block (`getelementptr inbounds`, MM-3). After it, `Sem` loads from the item's address
and forms no pointer from the base. With `%0` one byte before a live block and `%1 = 1`, the
function before the fold is `.illegal` and the function after it returns byte 0 of the block
(`CanonDrop.itemReads_adjacent_not_preserved`). So `itemReads` has no equality theorem over
today's `Sem`, and it stays on the `trusted-Canon` lines.

Two more differences are expected by reading the two arms of `Sem.evalMem`, and are not
kernel-checked: the load before the fold uses the alignment of the item pointer's type, the
load after it the smaller of the base pointer's alignment and the item's ABI alignment
(`Sem.itemLayout`); and a `ptr_elem_ptr` of a slice operand has a meaning in `Sem`, while a
`ptr_elem_val` of one is stuck.

Options: the refinement that admits `.illegal` before (as for 2); the lazy pointer check of
stage 1, with which the out-of-block base is illegal only when used, here by the load on both
sides; or a meaning of `ptr_elem_val` in `Sem` that forms the item pointer first
(`Zig.ptrProject`, then the load), which is a change of what SEM-06 trusts and of the generated
code it must agree with.

## Reachability

1 and 2: the compiler generates no code for either dropped instruction (Liveness marks it
unused), and both shapes come only from Sema. For 2, Sema's `vector_store_elem` after the lane
pointer has the same index, so a native run with an index past the count is illegal behaviour
anyway (checked in safe modes).

3: in safe modes Sema puts the bounds check before `ptr_elem_ptr`, so the panic comes first in
both functions. In `ReleaseFast` the function before the rewrite forms an out-of-bounds item
pointer that it may never read: illegal behaviour in the model, poison that is never used in
LLVM. A proof of the canonical function does not show its absence.

4: `Zig.ptrProject` never returns a pointer outside its block, so such a base reaches the pair
only as an argument or a loaded value. The generated code for
`ptr_elem_val` is what the canonical function means; the difference is only that the function
before the fold has more illegal behaviour in `Sem` than the canonical one.
