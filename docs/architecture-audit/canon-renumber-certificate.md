# Renumbering certificates: proposed boundary and obstruction

Task 12, 2026-10-15. Research proposal; no canonicalization step is certified by this
document. The parked `codex/canon-cert` worktree is unchanged. This branch starts at
`origin/main` `96dfa27e5` rather than importing its unmerged ancestry.

## Proposed smallest step

Certify only `Raw.renumber`, the final pass of `Raw.canonicalize`. All preceding passes
remain unverified. Copy forwarding is a larger first step: removing an addressable copy
changes block identifiers and the placement oracle, as recorded in
[air-semantics.md](../air-semantics.md#locals).

The meaning is the existing definitional interpreter, `Air2Lean.Sem.execFunc`, over
`normalizeCanonical` of the raw function immediately before and after renumbering.
This is relative to SEM-06 and the existing ZigLean semantics premises. An equality
between two executions of this fragment does not establish native behavior for an
instruction outside the fragment: those executions can both be `stuck`.

The generic theorem must transport every name-bearing part of that semantics:

* instruction definitions, SSA uses and branch/repeat targets;
* `Sem.Env` keys and the `Sem.Exit` labels of nested blocks and loops;
* register-local addresses (`Sem.Value.cell`) and `Sem.Frame.cells` keys;
* `regAlloc`'s whole-function use analysis and, when used, `Ctx.view` keys.

The per-run certificate should identify the actual pre/post functions and the finite
injective renaming, check that all other fields and instruction structure agree, and
instantiate that theorem. The printed terms must be independently bound to the
translator's actual intermediate values. Certificates must be emitted and compiled for
every committed generated module, with a mutation that changes one operand or target
rejected by the kernel. The full-build time must be measured before and after enabling
them. No new program judgment, tactic, command elaborator, axiom, premise admission or
proof-framework allow-list entry is proposed.

## Obstruction in the documented same-oracle equality

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

The semantics boundary needs a maintainer decision before the proposed certificate
can honestly assert the documented equality. Candidate permanent resolutions are:

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
