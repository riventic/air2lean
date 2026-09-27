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

## Porting to a new Zig version
See PLAN.md §Zig version support.

## `versions.toml`: CI-only sections
Besides one `["<version>"]` table per supported Zig version, `versions.toml` has two
CI-only tables, `[ci.host-zig."<version>"]` and `[ci.elan]`: URL + sha256 for the tools `.github/workflows/ci.yml`
downloads to build and run the checks (host zig to bootstrap `build.sh`, elan to install Lean).
`toml-get.sh <table-header> <key>` is the one reader for this file (`build.sh` and `ci.yml`
call it). It matches a table by its exact header line, so a dotted CI header never matches a
bare `["<version>"]` table.
