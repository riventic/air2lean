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
lake env lean tests/roadmap/bitops/Bitset.lean
mkdir -p /tmp/bitops-gen && cp tests/roadmap/bitops/qualified/0.16.0/Gen.lean tests/roadmap/bitops/GeneratedBitset.lean /tmp/bitops-gen/
lake env lean -R /tmp/bitops-gen -o /tmp/bitops-gen/Gen.olean /tmp/bitops-gen/Gen.lean
LEAN_PATH="/tmp/bitops-gen:$(lake env printenv LEAN_PATH)" lake env lean -R /tmp/bitops-gen /tmp/bitops-gen/GeneratedBitset.lean
lake env lean --run tests/roadmap/bitops/Cases.lean /tmp/bitops-generated
# In serialized order: lake env lean -R /tmp/bitops-generated --run each generated .lean
python3 tests/roadmap/bitops/mutations.py /tmp/bitops-mutants
# Compile control.lean successfully, then each named mutant must fail.
```

Mutants swap leading/trailing counts, erase population counts, ignore signedness for overflow,
invert the overflow flag, allow an illegal oversized shift, and swap operands: the reverse
shift of the overflow check shifts the operand instead of the result, and the count-width
bound compares width against count (both `operand-order` in `assurance/mutation-map.json`). Their assertions distinguish those changes directly. A kill requires Lean exit status 1 and only located `decide` false-proposition errors, each ending in `is false`. Import, syntax, elaboration and process failures cannot count as kills; offline adversarial fixtures check this classifier.

`tests/roadmap/bitops/bitops.zig` supplies compiler-generated AIR and native differential inputs.
The scalar domains should exhaust all 256 u8/i8 bit patterns and all eight shifts (four for
u3/i3, with shift 3 excluded from native execution as illegal behavior); vector probes should mix zero, maximum, sign boundary, and overflow within one vector. The gate compares 3,092
observation rows exactly and records 256 excluded narrow-shift rows (512 function evaluations)
separately. Kernel assertions check invalid scalar results; compiled fixture checks cover invalid vector lanes.
`firstSet`, `clearLowest`, and `cardinality` form the production-style bitset workload;
`GeneratedBitset.lean` proves their generated translations correct (lowest member or the 64
sentinel, exact bounded count, strictly decreasing iteration step), and `Bitset.lean` proves a
`std.bit_set`-style `IntegerBitSet(2^k)`/`ArrayBitSet([N]u64)` client.
Wider and non-power-of-two widths (u16-u128, i128, u24, u40, i7, u3/u64/u24 lanes) are covered by
`Runtime.lean` kernel assertions and the `clzWide`, `ctzWide`, `popcountWide`, `shiftWide` and
`wideVector` generated fixtures from synthetic AIR; apart from the u64 bitset kernels they are
not yet in the compiler export or native differential corpus. Qualifying them needs `bitops.zig`/`native.zig`/`DiffMain.lean.inc`
probes for those widths, the new export inventory and row count in `check.sh`, and a rerun of
the gate below.
The generated AIR and Lean fixture, commands, and results are recorded by the root validation
queue in `qualified/0.16.0/`. Generated fixture assertions use compiled evaluation; the pure runtime assertions and runtime lemmas use kernel reduction. Only Zig 0.16.0 is qualified by this package; other exporter versions
already decode these tags but require their own fixture/differential qualification.

The checked-in `qualified/0.16.0/` snapshot contains the 16 fresh AIR files, `Gen.lean`,
the exact native/Lean observation streams, and a portable derivative of the successful-run manifest.
The manifest's artifact paths are relative to the original complete gate output, and its
hashes also cover all generated fixtures, mutant source/log files and the native executable.
Those additional artifacts and the raw manifest are retained locally in `.lake/bitops-rechecked/`
(ignored by Git); their presence is not claimed by the tracked snapshot. The tracked manifest
replaces the three machine-specific compiler paths with documented environment inputs and
the delegated compiler sibling filename. Its derivation records the raw manifest hash; the
raw manifest preserves the actual original paths. All binary, source and artifact hashes,
validation classifications and execution facts remain unchanged. CI retains the complete
output in its runner temporary directory for the current job.

To reproduce the complete evidence from fresh compiler exports, run:

```sh
AIR2LEAN_ZIG_AIR="$PWD/zig-air-0.16.0/bin/zig" AIR2LEAN_ZIG=zig \
  AIR2LEAN_BITOPS_OUT_DIR="$PWD/.lake/bitops-rechecked" tests/roadmap/bitops/check.sh
```

The tracked snapshot is historical evidence; the gate validates fresh exports and execution,
then rewrites the retained output and manifest after all checks succeed.
