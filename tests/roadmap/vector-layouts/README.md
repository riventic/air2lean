# Vector memory layouts (L09)

`probe.zig` prints the size, alignment and memory bytes of bit-packed vectors (`u9`, `i9`,
`u12`, `u4`, `u1`, `u24`, `u40`, `f80`, `bool`) and byte-lane controls, before and after a
store through a lane pointer. `Model.lean` prints the same lines from the Lean encoding
(`ZigLean/Vec.lean`'s `Vec.packedEnc`) and compares them with a probe output. `Checker.lean`
checks the translator's backend gate and lane-pointer rejection. The theorems are in
`ZigLean/VecMem.lean`; `docs/vector-proofs.md` §Memory layout gives the scope.

`lanes.zig` uses lane pointers into `u9`, `u3`, `u24` and `bool` vectors (§Lane pointers).
`air/<version>` holds the AIR that the patched compilers exported from it, `Lanes/Gen.lean` the
0.16.0 translation, `Lanes/Proofs.lean` theorems on it, and `Lanes/Checks.lean`
(`lanes_checks.py`) kernel-checked runs of the native test's inputs. `lanes.sh` retranslates both
versions, compares the 0.16.0 translation with `Lanes/Gen.lean` and checks the proofs and runs;
`--native` runs the test with a stock Zig and `--export DIR` exports fresh AIR with the patched
0.16.0 and compares its translation.

```sh
lake build ZigLean Air2Lean
zig run -fllvm -OReleaseSafe tests/roadmap/vector-layouts/probe.zig 2> observed.txt   # stock Zig 0.16.0
lake env lean --run tests/roadmap/vector-layouts/Model.lean observed.txt
lake env lean --run tests/roadmap/vector-layouts/Model.lean tests/roadmap/vector-layouts/aarch64-macos-ReleaseSafe.txt
lake env lean --run tests/roadmap/vector-layouts/Checker.lean
bash tests/roadmap/vector-layouts/lanes.sh
AIR2LEAN_ZIG_NATIVE=zig bash tests/roadmap/vector-layouts/lanes.sh --native
AIR2LEAN_ZIG_AIR=zig-air-0.16.0/bin/zig bash tests/roadmap/vector-layouts/lanes.sh --export "$(mktemp -d)"
```

`aarch64-macos-ReleaseSafe.txt` is the output of stock Zig 0.16.0 on aarch64-macos (Apple M1).
Debug and ReleaseFast, and stock Zig 0.15.2, printed the same lines. CI compares its own x86_64-linux output. A
probe line covers only the listed vectors on the host that printed it.
