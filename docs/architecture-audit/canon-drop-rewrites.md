# Canon's dropping rewrites against `Sem`: three boundaries

Class: SOUNDNESS of the certificate chain (V02), found while proving the preservation theorems
of the Canon rewrites that drop instructions (`Air2Lean/SemDrop.lean`). Status: open (findings 2
and 3 need a decision; finding 1 is a limit of the statement, documented). Severity: latent (see
"Reachability").

All three are kernel-checked in `tests/roadmap/air-semantics/CanonDrop.lean`, for every program,
call oracle and start memory. They are statements about the formal AIR semantics `Sem`
(`Air2Lean/Sem.lean`). None is a native miscompilation: the translator's output for the
canonical function is what the compiler's code does.

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

## 3. `itemReads`: the fold moves the index check (not preserved as implemented)

```
%0 = arg(*[4]u8, 0)
%1 = arg(usize, 1)
%2 = arg(bool, 2)
%3 = ptr_elem_ptr(%0, %1)
cond_br(%2) { %5 = load(%3); ret %5 } else { ret 0 }
```

`Raw.itemReads` folds `%3` and its only reader `%5` into `%5 = ptr_elem_val(%0, %1)` at the load
(`CanonDrop.lean`'s `main` checks that this is the rewrite's output). With `%1 = 9` and
`%2 = false`, `Sem` is `.illegal` at `%3` before the rewrite and returns `0` after it
(`CanonDrop.itemReads_not_preserved`). The `ptr_elem_ptr`/`load` and `slice_elem_ptr`/`load`
patterns accept a `load` anywhere after the pointer; only the `load`/`array_elem_val` pattern
requires the second instruction directly after the first (`nextNonDebug`).

The same gap exists without a branch: a call between `%3` and `%5` that panics, returns an
error or does not return runs before the check after the rewrite and after it before.

Fix (not in this PR, it changes `Canon.lean` and possibly goldens): require
`next[x.id]? == some u.id` for these two patterns too, as for the third. With the pair adjacent
the check stays where it was, and the remaining proof obligation is one lemma over
`Zig.ptrProject`/`Zig.load` (the alignment of the item pointer's type against
`Sem.itemLayout`'s).

## Reachability

1 and 2: the compiler generates no code for either dropped instruction (Liveness marks it
unused), and both shapes come only from Sema. For 2, Sema's `vector_store_elem` after the lane
pointer has the same index, so a native run with an index past the count is illegal behaviour
anyway (checked in safe modes).

3: in safe modes Sema puts the bounds check before `ptr_elem_ptr`, so the panic comes first in
both functions. In `ReleaseFast` the function before the rewrite forms an out-of-bounds item
pointer that it may never read: illegal behaviour in the model, poison that is never used in
LLVM. A proof of the canonical function does not show its absence.
