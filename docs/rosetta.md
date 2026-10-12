# Running x86_64-linux under Rosetta

Docker Desktop on Apple silicon runs `--platform linux/amd64` containers under Rosetta for Linux
at near-native speed. That is how every x86_64-linux CI part runs locally
(`scripts/local-ci.sh`, `scripts/build-mode-docker.sh`). Rosetta is not a bug-compatible x86_64
kernel: it refuses one ELF layout that Zig's linker produces.

## The trigger

`rosetta error: bss_size overflow` (then SIGTRAP, exit 133) means: the executable has a `PT_LOAD`
segment with `p_filesz == 0` and `p_memsz > 0`. It is not the compiler's size, the build mode,
static or dynamic linking, or the binary's use of bss.

LLD (Zig's linker for every release mode, and for the JIT-built `zig build` runner) makes such a
segment when the RELRO region holds nothing but alignment padding: an empty `.got` and the
NOBITS `.relro_padding`, plus a `PT_GNU_RELRO` over the same range.

```
LOAD  0x01be60 0x101de60 0x101de60 0x000000 0x0001a0 RW  0x1000   <- filesz 0, memsz 0x1a0
LOAD  0x01be60 0x101ee60 0x101ee60 0x004a80 0x0071b8 RW  0x1000
GNU_RELRO ... 0x000000 0x0001a0 R 0x1
```

Evidence (Docker Desktop 29.8, Rosetta, stock Zig 0.17.0 and 0.16.0, tiny program, static musl):

| mode | default | `-z norelro` |
| --- | --- | --- |
| Debug, ReleaseSafe, ReleaseFast | runs | runs |
| ReleaseSmall | `bss_size overflow` | runs |

ReleaseFast runs because its first RW segment has bytes (`filesz 8`). Whether a binary fails
depends on its content, so a build that works today can fail after a source change. Turning that
one segment into `PT_NULL` makes the failing ReleaseSmall binary run; so the segment, not the rest of
the layout, is what Rosetta rejects. The official x86_64 `zig` itself runs (it has bytes in its first
RW segment); the x86_64 `zig build` of Zig 0.17.0 does not, even for an empty `build.zig`: the
runner it compiles on the fly (`maker`; `zig build` of 0.16.0 does run) has the empty segment. This is a Rosetta limitation (and a Zig/LLD layout it does not handle), not an air2lean bug;
what is ours is to link what we build and run in a way Rosetta accepts, in every path.

## What we do (scripts/rosetta.sh)

One sourced helper, a no-op on real x86_64 Linux and on macOS:

- Detection: Rosetta reports the CPU vendor `VirtualApple` in `/proc/cpuinfo`. `AIR2LEAN_ROSETTA=1/0`
  forces it. `scripts/local-ci.sh --inside` and `scripts/build-mode-docker.sh --inside` source the
  helper, so everything they run inherits the result. `build-mode-docker.sh` cross-builds the harness on
  the Mac and cannot tell what the Docker engine is, so it forces `1` (the flag is harmless elsewhere).
- `AIR2LEAN_ROSETTA_LINK_FLAGS` (`-z norelro` under Rosetta, unset otherwise): every script that builds
  an x86_64-linux executable and runs it appends `${AIR2LEAN_ROSETTA_LINK_FLAGS:-}` to its
  `zig build-exe` command line (`scripts/diff.sh`, `scripts/abi-probe.py`, `scripts/floatprobe.sh`,
  `scripts/counterexample.py`, the native probes of `tests/roadmap/`, including L10
  `error-width/native.py`). A new script that builds and runs a native binary does the same. Without
  RELRO the harness loses only the hardening of a read-only GOT; no semantics change, and CI on real
  x86_64 (variable unset) builds exactly what it did.
- `air2lean_rosetta_run CMD...` for what we cannot pass flags to: `zig-patch/build.sh` runs
  `zig build` through it (the golden row's `--prepare` builds the patched compiler this way). When the
  command dies of `bss_size overflow`, `scripts/rosetta-elf.py` turns the empty segment (and the
  RELRO over it) of the executables in Zig's global and project caches into `PT_NULL` and the command
  is run again. It only patches a segment whose range holds no section other than empty ones and
  `.relro_padding`, so nothing the program uses is unmapped; anything else is left alone and reported.

## Fallback

If a binary still fails with `bss_size overflow` (an executable we neither link nor can patch), run
it under `qemu-x86_64` (`apt-get install qemu-user-static` in the container; about 50x slower than
Rosetta, so only for single binaries, never for `zig build`). Record the binary and the ELF headers
(`readelf -lW`) that trigger it.
