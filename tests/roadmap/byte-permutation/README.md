# Byte permutation gate

The implementation handles signed and unsigned scalar integers and integer
vectors. Width-zero values are compiler folded. `@byteSwap` requires a multiple of
eight bits; `@bitReverse` uses every source bit even for a non-byte width.

The root validation queue runs this sequential gate once per exact release:

```bash
AIR2LEAN_EXPECT_ZIG_VERSION=0.16.0 \
AIR2LEAN_ZIG_AIR=/absolute/path/to/patched/zig \
AIR2LEAN_ZIG=/absolute/path/to/stock/zig \
AIR2LEAN_PERMUTATIONS_OUT_DIR=/absolute/path/to/fresh/output \
bash tests/roadmap/byte-permutation/check.sh
```

Repeat with matching 0.14.1 and 0.15.2 compilers. Each run exports 30 functions,
checks the exact unary/type-preserving payloads, compiles the generated translation,
checks general runtime contracts and kernel-reduced edge cases, runs five generated
signature/loop/vector fixtures, compares 795 native/Lean observation rows and kills
six semantic mutants. The shared bitops classifier accepts only located `decide`
refutations as mutant kills; import, elaboration and process failures do not count.
The manifest records source and artifact hashes, compiler hashes, the AIR target,
the native host and the proof/execution trust boundary.

Portable preparation requires only Python and shell syntax parsing:

```bash
python3 -B tests/roadmap/byte-permutation/test_portable.py
python3 -B tests/roadmap/byte-permutation/mutations.py /private/tmp/permutation-mutants
bash -n tests/roadmap/byte-permutation/check.sh
```

Portable tests check the bit-index law across every legal byte-aligned width and
all 65536 two-byte values. They are arithmetic/source checks, not Lean proof or
compiler execution. See `docs/byte-permutation.md` for the exact domain and limits.
