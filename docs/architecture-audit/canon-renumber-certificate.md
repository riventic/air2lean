# Canonicalization certificates: debug-definition IDs

Task 12, 2026-10-15. Research proposal; no canonicalization step is certified by this
document. The parked `codex/canon-cert` worktree is unchanged. This branch starts at
`origin/main` `96dfa27e5` rather than importing its unmerged ancestry.

## Proposed smallest step

Factor the existing `Raw.renumber` into live-ID/operand renumbering and a final
**debug-definition-ID** step. Certify the final step. Live-ID and operand renumbering,
and all preceding passes, remain unverified. This is a real part of the current
transformation: `renumber` already assigns debug instructions their final IDs after the
live instructions. The factorization must preserve those final IDs and the generated
program, rather than adding an unused alternate path.

The meaning is the existing definitional interpreter, `Air2Lean.Sem.execFunc`, over
the actual normalized functions immediately before and after the debug-ID step.
This is relative to SEM-06 and the existing ZigLean semantics premises. An equality
between two executions of this fragment does not establish native behavior for an
instruction outside the fragment: those executions can both be `stuck`.

The planned generic theorem erases only `.line` and `.dbg` definition IDs, including
inside nested blocks, loops, branches and `try` bodies. Erasing those IDs must preserve
`execFunc` for every oracle, argument list and memory. `execInst` ignores the definition
IDs of these operations, and `regAlloc` ignores them too. The theorem must establish both
facts for the whole recursive body. `dbg_inline_block` normalizes to an ordinary block;
its block ID and targets stay unchanged by this step.

The certificate therefore needs no transport of SSA bindings, branch targets,
register-local cells, or oracle results. Those names and all operands remain unchanged.

The per-run certificate must identify the actual pre/post functions, prove that their
debug-ID erasures are equal, and instantiate that theorem. Its printed terms must be
bound to the translator's actual intermediate values. It must not merely apply a
generic theorem to an unrelated symbolic function. Printing the same non-debug payload
once and sharing it between the two terms may reduce certificate size; the serializer
and its round-trip check must cover every operation admitted by the translator.

Coverage should reuse `scripts/gen-integrity.py`'s existing translation-case inventory
and `scripts/regen.py`, rather than maintain another module list. Shared golden modules
can represent several Zig/OS inputs with different intermediate debug IDs, so the
proposed certificates are sidecars per translation case. Each module's current cases
must have fresh, compiled sidecars; the inventory's existing reviewed non-current
historical/handwritten exceptions must remain explicit. This changes certificate output,
not the generated program's instructions. The full-build discovery must include those
sidecars, and removal of one must fail coverage.

Certificates must be emitted and compiled for every committed generated module. A
mutation that changes a live ID, operand or branch target must make the real certificate
fail. The full-build time must be measured before and after enabling them. Neither the
generic theorem nor this pipeline integration is implemented yet. No new program
judgment, tactic, command elaborator, axiom, premise admission or proof-framework
allow-list entry is proposed. The trust report can classify only this precise substep
as checked, and only after that evidence exists.

## Why full renumbering is not the first certified step

The current design in
[air-semantics.md](../air-semantics.md#canonicalization-v02) requires the same oracle on
both sides:

```text
execFunc o before args = execFunc o after args
```

`Sem.Oracle` is currently an unrestricted function returning `Sem.Value`.
`execInst` accepts its return without validating the result against the call's AIR
result type. Consequently an oracle can manufacture `Value.cell k`, an interpreter
implementation detail naming a register-local slot in the caller. The slot name changes
under renumbering, while the same oracle's result does not.

A minimal scenario takes a pointer parameter and has six instructions: bind that
parameter at 10; allocate register local 11; store `true` through it; call a pointer
identity function on the parameter; load and return through the call's result. An
oracle returning `Value.cell 11` reads the initialized slot before renumbering.
Afterwards the local is slot 1, so the same oracle reads the undefined slot 11. This is
a failure of the proposed general equality even though no generated native call can
obtain a caller's unescaped register-local address. The pointer identity callee can be
present in the checked program; the issue is the unrestricted oracle in the stated
per-function theorem, not the absence of an AIR definition for the callee.

This source-level counterexample is prepared in scratch and is not yet kernel-checked.
The scratch version has two stores to the local, so the preceding copy-forwarding pass
cannot remove it. Acceptance and whole-pipeline checks still need to run.

The semantics boundary needs a maintainer decision before a future certificate for
**full** renumbering can honestly assert the documented equality. Candidate permanent
resolutions are:

1. Validate oracle results against the declared AIR result type, rejecting interpreter
   cells at the call boundary. This changes the definitional interpreter; all existing
   emission certificates and their call lemmas need rechecking. This repairs the stated
   counterexample only; it is not yet a proof that all possible cell aliases or
   name-sensitive oracle behavior are excluded.
2. State and prove a general oracle contract that rules out escaping interpreter cells,
   discharge it for the program's least-fixpoint oracle, and require it explicitly for
   external implementations. This changes the documented preservation statement; it
   must not enter as an implicit or per-example assumption.

Merely checking a renaming table, defining the input meaning by renumbering it first,
or changing `canonicalization` to `kernel-checked` without the semantic theorem would
not resolve this obstruction. The existing trust classification remains unchanged.

## Independent copy-forwarding boundary

The existing `forwardReadOnlyCopies` deletes a copy's allocation, store, pointer
bitcasts and loads. For a copy whose address is cast to a const pointer, `Sem.regUse`
classifies the bitcast as taking the address, so `Sem.execInst` creates a real stack
block. Even a call-free store/bitcast/load/return example leaves that block's allocation
history in the full memory when the frame is freed. Its forwarded pure return does
not. This is the placement/memory-extension boundary already recorded in
[air-semantics.md](../air-semantics.md#locals), independent of oracle cell fabrication.

Retaining the allocation alone does not suffice: deleting a load also changes its
recorded read footprint and clock. A value-only stage retaining all effects would be
possible in principle, but needs a general store/load and continuation-substitution
proof. The current unrestricted oracle additionally prevents assuming an intervening
call leaves the unescaped copy's bytes alone. The debug-ID factorization avoids these
memory and oracle boundary changes while certifying an actual existing rewrite.
