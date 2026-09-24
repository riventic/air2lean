# air2lean Zig patch

Adds an AIR-JSON exporter to the Zig compiler: one `<fqn>.json` per function,
schema in `docs/air-json.md`, for the Lean 4 translator to read.

## What it does
- `src/Air/json.zig`: walks AIR, writes one JSON file per function.
- One-line hook in `src/Zcu/PerThread.zig`, after `analyzeFnBodyInner`.

## Env vars
- `ZIG_AIR_JSON_DIR` — output directory. Unset disables the exporter.
- `ZIG_AIR_JSON_FILTER=<prefix>` — dump only functions whose fqn starts with it.

## Recommended flags
`-OReleaseSafe -fno-error-tracing -fno-emit-bin` — keeps safety checks in AIR,
drops error-return-trace noise, skips linking a binary.

## Build
    ./build.sh <version> [prefix]

Downloads the pinned tarball (sha256-checked), patches, builds with
`-Denable-llvm=false -Ddebug-extensions=true`, installs `lib/` into the prefix
(no `-Dno-lib`) so the built `zig` needs no `--zig-lib-dir`. Needs a host `zig`
of the same version on `PATH`. `AIR2LEAN_OPTIMIZE` / `AIR2LEAN_CACHE` override
the optimize mode and download cache dir.

## Porting to a new Zig version
See PLAN.md §Zig version support.

## `versions.toml`: CI-only sections
Besides one `["<version>"]` table per supported Zig version, `versions.toml` has two
CI-only tables, `[ci.host-zig."<version>"]` and `[ci.elan]`: URL + sha256 for the tools `.github/workflows/ci.yml`
downloads to build and run the checks (host zig to bootstrap `build.sh`, elan to install Lean).
They use a dotted header, never a bare `["<version>"]` string, so `build.sh`'s awk reader (which
matches a version by the exact line `["<version>"]`) never mistakes one for a version section.
