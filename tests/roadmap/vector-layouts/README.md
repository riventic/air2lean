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
(`lanes_checks.py`) kernel-checked runs of the native test's inputs. `lanes.sh` retranslates every
version (0.17.1, 0.16.0, 0.15.2), compares the 0.16.0 translation with `Lanes/Gen.lean` and checks
the runs on each version's translation and the proofs on the 0.17.1 and 0.16.0 ones (0.15.2 types
the lane pointers with the vector's alignment, another access statement); `--native` runs the test with a stock Zig and
`--export DIR [VERSION]` exports fresh AIR with the patched compiler (default 0.16.0) and compares
its translation with the committed export's. Zig 0.17.1 writes `&v[i]` as a `ptr_cast` to the lane
pointer type; its lane accesses translate as 0.16.0's (`Canon.laneElemPtrs`).
`lane_reads.zig` (`air-reads/<version>`) reads lanes through a
vector pointer; `test_lane_reads.py BINARY` checks its translations against the native values and
that byte-strided `ptr_elem_val` reads and runtime-index lane pointers into bit-packed vectors are
rejected.

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
probe line covers only the listed vectors on the host that printed it. Stock Zig 0.17.1 printed
the same lines in the three modes on x86_64-linux (a `linux/amd64` container), and on
aarch64-macos and aarch64-linux except `f80x2` (`--skip f80x2`: the declared divergence of
`docs/aarch64-abi.md`, rejected by the translator); `lanes.zig`'s and `lane_reads.zig`'s tests pass
with it on the three targets.

## Element stride

`probe_strided.zig` prints the layout of the self-hosted x86_64 backend (`-fno-llvm`), which
keeps integer and float lanes at their ABI stride: `@sizeOf`/`@alignOf` of 812 vector types and
the images of 16 vectors around lane stores. `ModelStrided.lean` prints the same lines from
`ZigLean/VecStride.lean` (`Vec.stridedEnc`, `x86VecSize`) and compares them with
`stage2-x86_64-linux.txt`, the output of the stock compilers of Zig 0.14.1, 0.15.2, 0.16.0 and
0.17.1 (Debug and ReleaseSafe, baseline CPU, a `linux/amd64` container under Rosetta; all eight
byte-identical). `strided.sh` runs the comparison; `--native` also rebuilds and reruns the probe
with the stock compilers that are set. The translator does not use this layout yet
(`docs/vector-proofs.md` §Element-stride layout).

The probe builds its vectors lane by lane: the 0.14.1 self-hosted backend, run under Rosetta,
gave a wrong image for the coercion of a `[16]bool` array to a vector (`00 80` for `2d 80`; 9
lanes were right, 15 and more wrong; 0.15.2 and later were right). That is a value operation,
not a layout, and was not checked on x86_64 hardware.

```sh
lake build ZigLean.VecStride
bash tests/roadmap/vector-layouts/strided.sh
AIR2LEAN_ZIG_NATIVE=zig bash tests/roadmap/vector-layouts/strided.sh --native   # x86_64-linux
```
