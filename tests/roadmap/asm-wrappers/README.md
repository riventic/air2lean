# Generated asm wrappers under an executable interpretation (A03)

The differential test (`tests/diff/Diff.lean`) calls the `Asm.airAsm_*` opaques directly: the
generated wrappers in `Proofs/Asm/Gen.lean` were compiled against the opaques' `Inhabited`
placeholders. This gate runs the wrappers themselves.

`harness.py` reads `Proofs/Asm/Gen.lean`, the translator's checked output for
`examples/asm/asm.zig`. It recomputes the translator's `asmDefName` hash from each AIR
`assembly` instruction in `tests/golden/asm/air/`, so every `opaque airAsm_<hash>` is bound to
its exact source template, constraints and operand widths. It rewrites only the opaque lines
(into `def`s calling `AsmHarness.Interp.run`), the namespace lines (`Asm` becomes
`AsmHarness.Wrappers`) and the `import`. It fails if any other uninterpreted declaration, an
unbound opaque or a width or type mismatch appears. Every wrapper line is kept verbatim.

`Interp.lean` is a small x86_64 register machine. It allocates registers from the
constraints, fills unbound registers and the upper bits of inputs with junk, expands the
template and runs `bswap`, `popcnt`, `lzcnt`, `xor` and `div`. It rejects writes to undeclared
registers, `#DE` and unsupported syntax, and requires the same outputs under three allocations:
two distinct-register pools and one where an `r` input shares a plain `=r` output's register. `Runner.lean` compares every wrapper with the Zig source semantics (`AsmHarness.Oracle`) on
about 700 inputs per function, including the diff-test inputs, edge values and deterministic
pseudo-random values. It also evaluates the ASM-02 hypotheses that `Proofs/Asm/Proofs.lean`
states, under the interpretation. `divmod`'s remainder reaches the result only through the
wrapper's store to the local `rem`, so the result comparison also checks the memory plumbing.

Mutants are applied in memory to the generated text before the rewrite. Each must elaborate and
then exit 1 with a `MISMATCH wrapper <fn>` line, without a panic:

| Mutant | Change in the generated wrapper |
|---|---|
| `operand_order` | `airAsm_<divmod> p0 p1` becomes `p1 p0` |
| `result_placement` | `divmod` binds `a4.2` instead of `a4.1` as the asm result |
| `store_dropped` | `divmod` drops `modify (fun s => { s with rem := a4.2 })` |
| `store_misplaced` | `divmod` stores `a4.1` to `rem` |
| `single_result_placement` | `bswap32` returns `p0` instead of the asm result |

## Separation from proofs

The harness Lean files are not in any Lake library and contain no `import`; `harness.py`
assembles them into one temporary program for `lake env lean --run`. `audit.py` checks that no
Lake target root or glob covers `tests/` and that no file in `ZigLean`, `Proofs`, `Air2Lean`,
`tools` or a root module names `AsmHarness` or imports `tests`. It also checks that the harness
declares only in `AsmHarness.*` and adds no theorem, axiom, instance, `@[csimp]`,
`@[implemented_by]`, `@[extern]` or `sorry`. With `--assurance`, it reads a
`scripts/assumptions.py` report and requires the following:

- No `AsmHarness` or `tests` declaration appears in the audited graph.
- Every `Asm.airAsm_*` is still a plain opaque.
- The `Proofs.Asm.Proofs` theorems depend on no other project opaque, redirection or extern.

## Harness assumptions

These assumptions belong to this test only. They are not theorem premises; ASM-01 and ASM-02 in
`docs/premises.md` remain the only asm assumptions of the proofs.

- AH-01: The instruction semantics in `Interp.lean` follow the Intel SDM for the five
  mnemonics. This was not checked against hardware here. The diff test compares the same ops
  natively on x86_64.
- AH-02: Flags are not modeled. No template in `examples/asm` reads a flag.
- AH-03: Register allocation follows GCC-style constraints (`{reg}` pins, `r`, matching
  digits). Only three of the legal allocations are tried: two distinct-register pools and one
  that shares an input with a non-early-clobber output.
- AH-04: `Proofs/Asm/Gen.lean` is the current translation of `examples/asm/asm.zig`.
  `scripts/check.sh` compares it with fresh output on x86_64.
- AH-05: The AIR in `tests/golden/asm/air/` (Zig 0.16.0) is the AIR the opaques were generated
  from. The hash binding fails otherwise.
- AH-06: `divmod` inputs exclude zero operands. A zero divisor is a CPU fault in Zig too
  (`examples/asm/asm.zig`; the model traps on it through `Zig.asmTrap`, and the differential
  test covers it), and the operand-swap mutant would otherwise fault rather than return a
  wrong result.

## Running

```sh
lake build ZigLean
python3 -m unittest discover -s tests/roadmap/asm-wrappers -v   # offline, no Lean
python3 tests/roadmap/asm-wrappers/audit.py
python3 tests/roadmap/asm-wrappers/harness.py                  # control + 5 mutants
# Optional: dependency audit of the asm proofs.
python3 scripts/assumptions.py --module Proofs.Asm.Gen --module Proofs.Asm.Proofs --output "$out"
python3 tests/roadmap/asm-wrappers/audit.py --assurance "$out"
```

The harness does not cover memory or immediate constraints, read-write (`+r`) outputs or
multi-instruction templates beyond `examples/asm`. The translator rejects the first three.
