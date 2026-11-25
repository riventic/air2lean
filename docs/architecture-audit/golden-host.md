# Mac exports filed as the linux golden

Audit of 2026-11-25 on main `8da7f0887`. A golden case is (example, Zig version, host); a set
under `tests/golden/<v>/<ex>/air/` with no `air-<host>/` beside it is the `linux` case, the
x86_64-linux reference host (`scripts/gen-integrity.py golden_profiles`, `scripts/check.sh`'s
`air-<os>[-<arch>]` overlays). Five of them were AIR exports of the Mac.

## Facts on main `8da7f0887`

- **The exports.** Every file of `tests/golden/{0.14.1,0.15.2,0.16.0,0.17.1}/layout/air/` (51
  each) and of `tests/golden/0.17.1/lists/air/` (25) is schema 12 with profile `target_triple`
  `aarch64-macos.27.0.1...27.0.1-none`, `abi` `none`, `cpu` `apple_m1` (0.14.1–0.16.0) or
  `apple_m5` (0.17.1), 64-bit little-endian. The 0.14.1–0.16.0 layout sets come from `0045b3cdc`
  (2026-10-13, "Refresh schema-11 fixtures with padded integers to schema-12 exports"); the
  0.17.x layout set has been a Mac export since `1f6304031` (2026-10-07, Z1, then 0.17.0); the
  0.17.1 layout and lists sets are new exports in `9c67bd74a` (2026-11-16, the 0.17.1
  migration, whose qualification record ran `translation:layout` on the Mac).
  `tests/golden/0.17.1/layout/Gen.lean`'s profile record also named `aarch64-macos`. The other
  layout records (`tests/golden/0.1{4.1,5.2}/layout/Gen.lean`, `Proofs/Layout/Gen.lean`) name
  x86_64-linux.
- **`gen-integrity.py`.** `compose` keeps the profile of a set that is one export of the checked
  version (written for `layout`: its padded integers need a backend). It compared that profile
  with the golden host only for an enrolled (namespaced) case, and there a bare `linux` host
  checked the OS only, so an aarch64-linux export also passed as `linux`. So `gen-integrity check`
  translated the five `linux` cases as aarch64-macos programs and compared the body only;
  `header_error` compared only the record's float semantics.
- **`check.sh`.** On the x86_64-linux CI host it exports the example afresh, compares that AIR
  with the goldens after `normalize-air.py` drops the profile and normalizes compiler
  identities, and compares the fresh translation with the committed `Gen.lean` after its first
  line. So it checks the x86_64-linux body, and is blind to the profile the golden records.
- **Consumers.** No theorem imports `tests/golden/**/Gen.lean`: the Layout and Lists proofs
  build over `Proofs/Layout/Gen.lean` (an x86_64-linux record) and `Proofs/Lists/Gen.lean` (no
  record, the legacy 0.16.0 translation), and check trees use the host's fresh translation.
  `scripts/premises.py profile_target` reads the record of a generated module in the build
  graph, which these goldens are not. The support matrix's "golden-checked in its CI job"
  rests on `check.sh` on x86_64-linux.

## Finding: the `linux` golden of five cases was an aarch64-macos program

The five cases' committed input and the translation `gen-integrity` checks were the
aarch64-macos ones, labelled and counted as the x86_64-linux case. Nothing at export or commit
time compared a kept profile with the host the directory names.

Re-export on x86_64-linux (host `p0`, `Linux 7.0.0-42-generic x86_64`, the patched compilers of
`main` from `scripts/zig-air.sh`, `AIR2LEAN_CI=1 scripts/check.sh --example <ex>` per version):
all seven (version, example) runs pass, including the strict comparison of the fresh
translation with the committed `Gen.lean` body. Profile `x86_64-linux.7.0...7.0-gnu.2.43`,
`znver4`. With the profile removed the fresh files equal the committed ones except for compiler
identities that `check.sh` normalizes (`…inactiveUnionField__func_733` vs `__func_666`,
`mem.Allocator.dupe__func_117` vs `__func_150`, `debug.SafetyLock.State__enum_1` vs `__enum_2`;
same `instance_key`s): layout 0.14.1 and 0.15.2 identical, 0.16.0 and 0.17.1 one file each,
lists 0.17.1 18 of 25.

So no committed statement was false: these programs have no target-dependent construct that
differs between aarch64-macos and x86_64-linux (both LP64 little-endian, no `c_longdouble`,
`f80`, `builtin.os` branch or syscall), and `check.sh` on the CI host compared the body that
matters. The concrete failure is latent: an example whose AIR does depend on the target (an
`f80`, `c_longdouble`, `std.atomic.cache_line` or an OS branch) and is exported on the Mac into
`air/` passes `gen-integrity`, which retranslates the Mac program and finds its body equal to
the Mac `Gen.lean`, while its committed record claims aarch64-macos for the `linux` case. Only
`check.sh` on x86_64-linux would catch it, and only for the version and examples its CI job
runs; a version with its own `Gen.lean` that the CI job does not select would keep the wrong
translation. That is the fail-closed gap.

## Fix

- `compose` checks every kept profile against the golden host, enrolled or not:
  `host_target` maps a host to `(arch, os)`, a bare `linux` being x86_64 and a bare `darwin`
  aarch64; a profile without a target or of another target fails with "actual profile … does
  not match golden host … export it on that host".
- `header_error` also fails when the committed record of a golden module names another target
  than the translation of the case that owns it (`owns_record`: `Gen-<host>.lean` is its
  host's, any other golden module the `linux` host's; a darwin case that shares
  `Proofs/Sync/Gen.lean` does not own its record). `write` then takes the owning case's fresh
  record.
- The five sets are re-exported on x86_64-linux (the files above, identities renamed to
  `__func_N`); `gen-integrity write` replaced only the profile record of
  `tests/golden/0.17.1/layout/Gen.lean`. All translation bodies are unchanged.

Regressions: `tests/roadmap/gen-integrity/test_gen_integrity.py`
(`test_kept_profile_must_be_the_golden_hosts_target`,
`test_golden_check_refuses_another_hosts_export_filed_as_linux`,
`test_profile_record_names_the_translated_target`).

## Remaining

- `tests/golden/0.1{5.2,6.0}/lists/air/lists.allocatorWord.json` are single Mac exports inside
  mixed legacy sets; `compose` drops their profile and translates the set under the legacy
  profile (no target recorded), so no target is claimed. They go when Lists is enrolled with a
  complete export per host.
- The x86_64-linux exports record the exporting host's CPU and OS range (`znver4`,
  `7.0...7.0-gnu.2.43`, here; `x86_64`, `5.10...6.19-gnu.2.31` for the Rosetta exports). The gate
  binds arch and OS only; the CPU does not change these translations (`check.sh` above).
