# Vector memory layouts (L09)

`probe.zig` prints the size, alignment and memory bytes of bit-packed vectors (`u9`, `i9`,
`u12`, `u4`, `u1`, `u24`, `u40`, `f80`, `bool`) and byte-lane controls, before and after a
store through a lane pointer. `Model.lean` prints the same lines from the Lean encoding
(`ZigLean/Vec.lean`'s `Vec.packedEnc`) and compares them with a probe output. `Checker.lean`
checks the translator's backend gate and lane-pointer rejection. The theorems are in
`ZigLean/VecMem.lean`; `docs/vector-proofs.md` §Memory layout gives the scope.

```sh
lake build ZigLean Air2Lean
zig run -fllvm -OReleaseSafe tests/roadmap/vector-layouts/probe.zig 2> observed.txt   # stock Zig 0.16.0
lake env lean --run tests/roadmap/vector-layouts/Model.lean observed.txt
lake env lean --run tests/roadmap/vector-layouts/Model.lean tests/roadmap/vector-layouts/aarch64-macos-ReleaseSafe.txt
lake env lean --run tests/roadmap/vector-layouts/Checker.lean
```

`aarch64-macos-ReleaseSafe.txt` is the output of stock Zig 0.16.0 on aarch64-macos (Apple M1).
Debug and ReleaseFast printed the same lines. CI compares its own x86_64-linux output. A
probe line covers only the listed vectors on the host that printed it.
