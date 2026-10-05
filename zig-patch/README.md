# air2lean Zig patch

Adds an AIR-JSON exporter to the Zig compiler: one `<fqn>.json` per function,
schema in `docs/air-json.md`, for the Lean 4 translator to read.

## What it does
- `air-json/json.zig` → `src/Air/json.zig`: walks AIR, writes one JSON file per
  function. One source for every supported version: its `Compat` section holds
  the version differences (comptime branches on `builtin.zig_version`).
- `<version>/hook.patch`: the one-line call in `src/Zcu/PerThread.zig`, after the
  function body is analysed. The only per-version file of the exporter.
- `<version>/TAGS.md`: that version's AIR differences from the other versions.

New dumps include `target_endian` (`little` or `big`) in schema 11. The translator rejects
explicitly non-little-endian dumps; older dumps without this optional field assume little
endian. Memory layout checks also enforce the model's 64-bit ABI.

## Env vars
- `ZIG_AIR_JSON_DIR` — output directory. Unset disables the exporter.
- `ZIG_AIR_JSON_FILTER=<prefix>` — dump only functions whose fqn starts with it.

## Recommended flags
`-OReleaseSafe -fno-error-tracing -fno-emit-bin` — keeps safety checks in AIR,
drops error-return-trace noise, skips linking a binary.

## Build
    ./build.sh <version> [prefix]

Downloads the pinned tarball (sha256-checked), copies `air-json/json.zig` in,
applies `<version>/hook.patch`, builds with
`-Denable-llvm=false -Ddebug-extensions=true`, installs `lib/` into the prefix
(no `-Dno-lib`) so the built `zig` needs no `--zig-lib-dir`. Needs a host `zig`
of the same version on `PATH`: `Compat` selects its branch by that version. `AIR2LEAN_OPTIMIZE` / `AIR2LEAN_CACHE` override
the optimize mode and download cache dir.
Concurrent builds download into separate temporary files and publish only verified tarballs.
An invalid existing cache entry is reported with its path; remove it before retrying.

### With or without LLVM

| | Default | `AIR2LEAN_LLVM=1` |
|---|---|---|
| What the compiler can do | write AIR only (`build-obj -fno-emit-bin`) | everything a stock zig can do, plus AIR |
| Lock | yes: `lock.sh` puts a wrapper in `bin/zig` that refuses every other command; the compiler is `bin/zig-unlocked` | no |
| Needs | a host `zig` | also cmake, and LLVM, Clang and LLD of the version in `versions.toml` (`llvm`: 19 for 0.14.1, 20 for 0.15.2, 21 for 0.16.0) |
| Build | `zig build` | `cmake` configures only (writes `build/config.h`), then `zig build -Denable-llvm -Dconfig_h=…` |

`AIR2LEAN_LLVM_PREFIX` gives the LLVM, Clang and LLD install prefixes (`;`-separated); the default is Homebrew's `llvm@<N>` and `lld@<N>`. CI uses the default: the checks only write AIR.

The bootstrap defaults to stripped `Debug` and one build job (`-j1`) to reduce peak memory.
It also sets `-Dno-langref=true` on all supported versions, omitting the generated
`doc/langref.html` and its example-compilation dependencies from installation. The compiler
and its standard library are still installed; `-Dno-lib` is not used. `-j1` alone does not
prevent documentation tools from launching child compilers.
Set `AIR2LEAN_OPTIMIZE=ReleaseFast` for a faster compiler when bootstrap memory allows it.
The exporter flags and LLVM selection stay the same in either mode.

Builds install into an adjacent temporary directory and apply the AIR-only lock before
publishing the prefix. A failed build leaves the previous compiler available. Writers to the
same prefix fail promptly while another build owns its lock; different prefixes share the
verified download cache. On successful replacement, the script reports and retains the old
installation as `.PREFIX.air2lean-previous.*`, so any extra files remain recoverable.
An interrupted publication restores the previous prefix if the replacement was not installed.

Why the lock: without LLVM, the compiler makes native code with Zig's own backends. On aarch64-macos that backend crashes at once (SIGBUS), also for a hello world, and each crash made macOS's crash reporter use tens of GB of memory. Build and run programs (for example `tests/diff/gen_inputs.zig`) with a stock `zig`.

The lock rejects response-file arguments (`@file`) and every explicit `-femit-bin` override.
For allowed compilation commands it inserts `-fno-emit-bin` immediately after the command,
where Zig parses it as an option even when another flag-looking argument is an option value.

## Porting to a new Zig version
See PLAN.md §Zig version support.

## `versions.toml`: CI-only sections
Besides one `["<version>"]` table per supported Zig version, `versions.toml` has two
CI-only tables, `[ci.host-zig."<version>"]` and `[ci.elan]`: URL + sha256 for the tools `.github/workflows/ci.yml`
downloads to build and run the checks (host zig to bootstrap `build.sh`, elan to install Lean).
`toml-get.sh <table-header> <key>` is the one reader for this file (`build.sh` and `ci.yml`
call it). It matches a table by its exact header line, so a dotted CI header never matches a
bare `["<version>"]` table.
