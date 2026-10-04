# L02 integer bitops validation

The coordinating agent runs every Zig/Lake/Lean command through the serialized monitored
queue. The dedicated end-to-end gate is `tests/roadmap/bitops/check.sh`; CI must invoke it
explicitly with `AIR2LEAN_ZIG_AIR` and `AIR2LEAN_ZIG`. It runs all stages sequentially and
fails on missing export roots, incomplete observations, or a surviving mutant. `Cases.lean` materializes checked synthetic AIR translations and rejection tests;
execute each emitted `.lean` separately with `--run` with `-R` set to its temporary directory.
The gate exports reference x86_64-linux AIR and compares stock host-native execution;
its manifest reports those targets separately and hashes the source, compilers and artifacts. `Runtime.lean` contains kernel-evaluated assertions.
No `native_decide`, project axiom, or proof placeholder is used.

```sh
lake build ZigLean Air2Lean air2lean
lake env lean tests/roadmap/bitops/Runtime.lean
lake env lean --run tests/roadmap/bitops/Cases.lean /tmp/bitops-generated
# In serialized order: lake env lean -R /tmp/bitops-generated --run each generated .lean
python3 tests/roadmap/bitops/mutations.py /tmp/bitops-mutants
# Compile control.lean successfully, then each named mutant must fail.
```

Mutants swap leading/trailing counts, erase population counts, ignore signedness for overflow,
invert the overflow flag, and allow an illegal oversized shift. Their assertions distinguish those changes directly. A kill requires Lean exit status 1 and only located `decide` false-proposition errors, each ending in `is false`. Import, syntax, elaboration and process failures cannot count as kills; offline adversarial fixtures check this classifier.

`tests/roadmap/bitops/bitops.zig` supplies compiler-generated AIR and native differential inputs.
The scalar domains should exhaust all 256 u8/i8 bit patterns and all eight shifts (four for
u3/i3, with shift 3 excluded from native execution as illegal behavior); vector probes should mix zero, maximum, sign boundary, and overflow within one vector. The gate compares 3,092
observation rows exactly and records 256 excluded narrow-shift rows (512 function evaluations)
separately. Kernel assertions check invalid scalar and vector results.
`firstSet`, `clearLowest`, and `cardinality` form the production-style bitset workload.
The generated AIR and Lean fixture, commands, and results are recorded by the root validation
queue in `qualified/0.16.0/`. Generated fixture assertions use compiled evaluation; the pure runtime assertions and runtime lemmas use kernel reduction. Only Zig 0.16.0 is qualified by this package; other exporter versions
already decode these tags but require their own fixture/differential qualification.

The checked-in `qualified/0.16.0/` snapshot contains the 16 fresh AIR files, `Gen.lean`,
the exact native/Lean observation streams, and the unmodified successful-run manifest.
The manifest's artifact paths are relative to the original complete gate output, and its
hashes also cover all generated fixtures, mutant source/log files and the native executable.
Those additional artifacts are retained locally in `.lake/bitops-checked/` (ignored by Git);
their presence is not claimed by the tracked snapshot. Compiler paths identify the original
local execution, while their hashes preserve the binary identities. CI retains the complete
output in its runner temporary directory for the current job.

To reproduce the complete evidence from fresh compiler exports, run:

```sh
AIR2LEAN_ZIG_AIR="$PWD/zig-air-0.16.0/bin/zig" AIR2LEAN_ZIG=zig \
  AIR2LEAN_BITOPS_OUT_DIR="$PWD/.lake/bitops-checked" tests/roadmap/bitops/check.sh
```

The tracked snapshot is historical evidence; the gate validates fresh exports and execution,
then rewrites the retained output and manifest after all checks succeed.
