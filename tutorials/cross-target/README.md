# Tutorial: cross-target verification

## Status

Partial: documentation only, not run by `scripts/tutorials.py check` or `scripts/clean-env.sh`.
No second target has a checked proof workflow from a clean environment. What is qualified today
is listed below; the open work is roadmap Q05 (cross-target continuous integration).

## What a proof is about

Every generated module states the target it models. A schema-12 translation starts with a
`-- air2lean-profile:` line that records the target triple, CPU and features, build mode, Zig
version, backend and error-set width of the analyzed AIR ([profiles](../../docs/profiles.md)).
For example the first line of [`Proofs/Sync/Gen.lean`](../../Proofs/Sync/Gen.lean) records
`x86_64-linux-musl`, Zig 0.16.0, ReleaseSafe. A theorem over that module carries premise
[PRF-02](../../docs/premises.md#prf-02): it is about exactly that profile. A module without the
line uses the legacy reference model, [PRF-01](../../docs/premises.md#prf-01) (64-bit,
little-endian). See which premise a theorem has with
`python3 scripts/premises.py explain <theorem>`.

## What is qualified

- **Model ABI scopes:** `x86_64-linux-<abi>` and `aarch64-macos-<abi>`, 64-bit little-endian
  only; narrower or big-endian targets are rejected by the translator
  ([profiles](../../docs/profiles.md)).
- **Target-specific std code:** where std differs by OS, the translation differs too. For Zig
  0.15.2 `Thread.Mutex` is `FutexImpl` on Linux and `os_unfair_lock` on macOS; the Darwin
  translation is the committed golden `tests/golden/0.15.2/threadsync/Gen-darwin.lean`, and its
  lock is a contract ([THR-06](../../docs/premises.md#thr-06)).
- **Native ABI observations:** `scripts/abi-probe.py` records bounded layout and integer
  observations for x86_64-linux-gnu and aarch64-linux-gnu on the matching CPU and compares
  them ([bounded Linux native ABI observations](../../docs/profiles.md#bounded-linux-native-abi-observations)).
  These are evidence for listed layouts, not a proof of correspondence.
- **CI:** three Zig versions on Linux and selected macOS paths
  ([support matrix](../../docs/support-matrix.md)).

## To verify for a second target (manual, not yet a checked tutorial)

1. Export AIR with the patched Zig for the target (`-target ...`) and translate it
   ([getting started](../../docs/getting-started.md)); the profile line names the target.
2. Re-run the proofs against that translation (`scripts/check.sh` compares it with the
   per-version and per-OS goldens).
3. Check that every theorem you rely on lists the expected profile premise.

## Assumptions and remaining obligations

- [PRF-01](../../docs/premises.md#prf-01), [PRF-02](../../docs/premises.md#prf-02): each proof
  is about one recorded profile; nothing transfers a proof between profiles.
- [TRU-02](../../docs/premises.md#tru-02), [TRU-03](../../docs/premises.md#tru-03): the
  translation models the AIR, and the backend lowers it faithfully for that target.
- Remaining: WASM and 32-bit/big-endian targets, a cross-target proof run in CI and a clean
  container per target (Q05).
