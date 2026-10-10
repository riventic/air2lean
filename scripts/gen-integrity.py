#!/usr/bin/env python3
"""Retranslate every committed generated Lean module from its committed AIR.

A generated module holds only translator output: theorems about it are theorems about
generated code. This gate finds every tracked generated module (a file named `Gen.lean` or
`Gen-<os>.lean`, or any `.lean` file whose first line is an `-- air2lean-profile:` record), maps
it to the committed AIR and translator arguments of its own check, runs the current translator
and requires the committed file to equal the fresh output:

- `exact`: byte-identical, for a fixture translated straight from one committed AIR directory;
- `body`: identical after the first-line `-- air2lean-profile:` record, for a fixture whose
  committed AIR predates schema 12 or whose check validates that record on a fresh export;
- `golden`: an example's translation (scripts/check.sh) from its golden overlays
  tests/golden/<ex>/air, then tests/golden/<v>/<ex>/air, then tests/golden/<v>/<ex>/air-<os>,
  compared as `body`: goldens recorded by several versions/schemas carry no single profile, so
  check.sh validates the record against fresh AIR instead (docs/generated-code.md). A golden
  case's file is Gen-<os>.lean, else <v>/<ex>/Gen.lean, else Proofs/<Ex>/Gen.lean.

A tracked generated module that no rule covers fails. EXCEPTIONS lists each reviewed file
that is not current translator output, with its reason; no Lean module may import one.

`attest [PATH ...]` (default: every tracked generated module) is the check for evidence
consumers (proof receipts, theorem inventory records): each file must equal (as above) a fresh
translation of one of its own cases. Verification never replaces a committed module
(scripts/check.sh builds another version's translation in a check tree), so no other
translation is accepted. It prints one JSON record per file (sha256 and the matching cases) and
fails on any file without a match.

Usage: gen-integrity.py check  [--translator PATH] [--only SUBSTRING]
       gen-integrity.py attest [--translator PATH] [PATH ...]
       gen-integrity.py list   (each case and its inputs; no translation)
"""
import argparse
import dataclasses
import functools
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
# Host keys of the golden overlays (scripts/check.sh): `uname -s` in lower case, then
# `<os>-<uname -m>` for a host whose AIR or translation differs from its OS's (aarch64-linux).
OSES = ("linux", "darwin", "linux-aarch64")
PROFILE_PREFIX = b"-- air2lean-profile: "
# The compiler-identity marker that check.sh's overlay normalization rewrites to `__<kind>_N`.
IDENTITY = runpy.run_path(str(Path(__file__).with_name("normalize-air.py")))["IDENTITY_MARKER"]
GEN_NAME = re.compile(r"Gen(-[a-z]+(-[a-z0-9_]+)?)?\.lean")

# Direct fixtures: (generated file, committed AIR dir, translator arguments, comparison), with
# the arguments of the fixture's own check script.
FIXTURES = [
    ("tests/roadmap/aggregate-casts/AggregateCasts/Gen.lean", "tests/roadmap/aggregate-casts/air/0.16.0",
     ["--namespace", "AggregateCasts", "--prefix", "aggregate_casts."], "exact"),
    # Retained qualification artifact (its manifest.json pins the hash); schema-11 AIR.
    ("tests/roadmap/bitops/qualified/0.16.0/Gen.lean", "tests/roadmap/bitops/qualified/0.16.0/air",
     ["--namespace", "Bitops", "--prefix", "bitops."], "body"),
    ("tests/roadmap/global-init/GlobalInit/Gen.lean", "tests/roadmap/global-init/air/0.16.0",
     ["--namespace", "GlobalInit", "--prefix", "global_init."], "exact"),
    ("tests/roadmap/idle-loops/IdleLoop/Gen.lean", "tests/roadmap/idle-loops/air",
     ["--namespace", "IdleLoop", "--prefix", "progress."], "exact"),
    ("tests/roadmap/packed-fields/PackedFields/Gen.lean", "tests/roadmap/packed-fields/air/0.16.0",
     ["--namespace", "PackedFields", "--prefix", "packed_fields."], "exact"),
    ("tests/roadmap/spawn-failure/SpawnFailure/Gen.lean", "tests/roadmap/spawn-failure/air/0.16.0",
     ["--namespace", "SpawnFailure", "--prefix", "spawn_failure.", "--spawn-policy", "fallible"], "exact"),
    # Its check.sh compares with normalize-generated.py compare (body only); schema-11 AIR.
    ("tests/roadmap/thread-tuples/ThreadTuples/Gen.lean", "tests/roadmap/thread-tuples/air/0.16.0",
     ["--namespace", "ThreadTuples", "--prefix", "thread_tuples."], "body"),
    ("tests/roadmap/try-pointers/TryPointers/Gen.lean", "tests/roadmap/try-pointers/air/0.16.0",
     ["--namespace", "TryPointers", "--prefix", "try_pointers."], "exact"),
    ("tests/roadmap/try-pointers/aliases/TryAliases/Gen.lean", "tests/roadmap/try-pointers/aliases/air/0.16.0",
     ["--namespace", "TryAliases", "--prefix", "try_aliases."], "exact"),
    ("tests/roadmap/undef-locals/UndefLocals/Gen.lean", "tests/roadmap/undef-locals/air/0.16.0",
     ["--namespace", "UndefLocals", "--prefix", "undef_locals."], "exact"),
    ("tests/roadmap/undef-operands/UndefOperands/Gen.lean", "tests/roadmap/undef-operands/air/0.16.0",
     ["--namespace", "UndefOperands", "--prefix", "undef_operands."], "exact"),
    # scripts/flow-time.sh pins `--profile abi64-le-v1` on its fresh export; the committed
    # (normalized, schema-11) AIR carries no profile.
    ("case-studies/flow-time/FlowTime/Gen.lean", "case-studies/flow-time/air",
     ["--namespace", "FlowTime", "--prefix", "flow_time.", "--float-semantics", "ieee"], "body"),
    ("tests/roadmap/bitcast-017/BitCastReal/Gen.lean", "tests/roadmap/bitcast-017/air/0.17.0",
     ["--namespace", "BitCastReal", "--prefix", "bitcast017."], "exact"),
    ("tests/roadmap/zig017/divceil/DivCeil/Gen.lean", "tests/roadmap/zig017/divceil/air/0.17.0",
     ["--namespace", "DivCeil", "--prefix", "divceil."], "body"),  # committed without the host header
    ("tests/roadmap/noreturn-variants/NoreturnVariants/Gen.lean", "tests/roadmap/noreturn-variants/air/0.16.0",
     ["--namespace", "NoreturnVariants", "--prefix", "noreturn_variants."], "exact"),
    ("Proofs/Provenance/Gen.lean", "assurance/provenance/air",
     ["--namespace", "Provenance", "--prefix", "provenance."], "exact"),
    ("tests/roadmap/asm-effects/AsmEffects/Gen.lean", "tests/roadmap/asm-effects/air/0.16.0",
     ["--namespace", "AsmEffects", "--prefix", "asm_effects."], "exact"),
    ("tests/roadmap/const-bases/ConstBases/Gen.lean", "tests/roadmap/const-bases/air/0.16.0",
     ["--namespace", "ConstBases", "--prefix", "const_bases.", "--allow-unqualified-build-mode"], "exact"),
    ("tests/roadmap/illegal-behavior/Gen.lean", "tests/roadmap/illegal-behavior/air",
     ["--namespace", "IllegalBehavior", "--prefix", "ib."], "exact"),
    ("tests/roadmap/const-locals/ConstLocals/Gen.lean", "tests/roadmap/const-locals/air/0.16.0",
     ["--namespace", "ConstLocals", "--prefix", "const_locals."], "exact"),
    ("tests/roadmap/const-locals/FuzzS19/Gen.lean", "tests/roadmap/const-locals/air-fuzz_s19/0.16.0",
     ["--namespace", "FuzzS19", "--prefix", "fuzz_s19."], "exact"),
    # G1 extern calls: the 0.16.0 translation (check.sh) and the trusted-base binding.
    ("tests/roadmap/extern-calls/ExternCalls/Gen.lean", "tests/roadmap/extern-calls/air/0.16.0",
     ["--namespace", "ExternCalls", "--prefix", "extern_calls."], "exact"),
    ("tests/roadmap/extern-calls/ExternCalls/Trusted.lean", "tests/roadmap/extern-calls/air/0.16.0-trusted",
     ["--namespace", "ExternCalls.Trusted", "--prefix", "trusted.", "--model-registry",
      "tests/roadmap/extern-calls/registry.json"], "exact"),
    ("tests/roadmap/futures/Futures/Gen.lean", "tests/roadmap/futures/air/0.16.0",
     ["--namespace", "Futures", "--prefix", "futures."], "exact"),
    ("tests/roadmap/loop-tactics/nested/Nested/Gen.lean", "tests/roadmap/loop-tactics/nested/air",
     ["--namespace", "Nested", "--prefix", "nested."], "exact"),
    ("tests/roadmap/thread-locals/ThreadLocals/Gen.lean", "tests/roadmap/thread-locals/air/0.16.0",
     ["--namespace", "ThreadLocals", "--prefix", "thread_locals."], "exact"),
    ("tests/roadmap/vector-layouts/Lanes/Gen.lean", "tests/roadmap/vector-layouts/air/0.16.0",
     ["--namespace", "Lanes", "--prefix", "lanes."], "exact"),
    ("tests/roadmap/volatile-effects/DeviceEffects/Gen.lean", "tests/roadmap/volatile-effects/air/0.16.0",
     ["--namespace", "DeviceEffects", "--prefix", "device_effects.",
      "--device-contract", str(ROOT / "tests/roadmap/volatile-effects/uart.json")], "exact"),
    # check-device.sh translates only `elapsed` (the declared rdtsc device event).
    ("tests/roadmap/volatile-effects/DeviceAsm/Gen.lean",
     "tests/roadmap/volatile-effects/air-asm/0.16.0/device_asm.elapsed.json",
     ["--namespace", "DeviceAsm", "--prefix", "device_asm.",
      "--device-contract", str(ROOT / "tests/roadmap/volatile-effects/tsc.json")], "exact"),
] + [
    (f"tests/roadmap/big-endian/BigEndian/{ns}/Gen.lean", f"tests/roadmap/big-endian/air/0.16.0/{target}",
     ["--namespace", f"BigEndian.{ns}", "--prefix", "big_endian."], "exact")
    for ns, target in (("S390x", "s390x-linux"), ("X64", "x86_64-linux"))
] + [
    (f"tests/roadmap/pointer-width/PointerWidth/{ns}/Gen.lean", f"tests/roadmap/pointer-width/air/0.16.0/{target}",
     ["--namespace", f"PointerWidth.{ns}", "--prefix", "pointer_width."], "exact")
    for ns, target in (("Wasm32", "wasm32-freestanding"), ("Wasi", "wasm32-wasi"), ("X64", "x86_64-linux"))
] + [
    # tests/roadmap/env-boundaries/translate.sh: the committed ENV-03 registry binds the OS primitives.
    (f"tests/roadmap/env-boundaries/expected/EnvStd{v}.lean", f"tests/roadmap/env-boundaries/air/{zv}",
     ["--namespace", f"EnvStd{v}", "--prefix", f"std_io{v}.",
      "--model-registry", str(ROOT / f"tests/roadmap/env-boundaries/registry/std{v}.json")], "exact")
    for v, zv in (("15", "0.15.2"), ("16", "0.16.0"))
] + [
    (f"tests/roadmap/error-width/expected/ErrorWidth{bits}.lean", f"tests/roadmap/error-width/air/bits{bits}",
     ["--namespace", f"ErrorWidth{bits}", "--prefix", "error_width."], "exact")
    for bits in (8, 10, 16, 17)
]

# Reviewed generated-looking files that are not current translator output.
EXCEPTIONS = {
    "tests/roadmap/try-pointers/origin/TryPointers/Gen.lean":
        "historical translator output retained byte-for-byte as a provenance input "
        "(tests/roadmap/try-pointers/README.md); check-artifacts.py pins its hash and no "
        "Lean module imports it",
    "tests/roadmap/architecture-audit/claims/AuditClaims/Gen.lean":
        "hand-written stand-in for a translation in the architecture-audit claim counterexamples "
        "(docs/architecture-audit/claims.md); only those untrusted fixtures import it",
}
# Exceptions that counterexample fixtures import on purpose; assurance/premises.json keeps those
# fixtures out of the theorem universe.
STAND_INS = {"tests/roadmap/architecture-audit/claims/AuditClaims/Gen.lean"}


@dataclasses.dataclass
class Case:
    path: str
    dirs: list
    args: list
    mode: str
    label: str
    version: str | None = None


def git_files(*patterns):
    out = subprocess.run(["git", "-C", str(ROOT), "ls-files", "-z", "--", *patterns],
                         check=True, capture_output=True).stdout
    return [p for p in out.decode().split("\0") if p]


# Architecture-audit counterexamples (docs/architecture-audit): untrusted by design, excluded
# from the premise index (assurance/premises.json) and from this gate alike.
AUDIT = "tests/roadmap/architecture-audit/"


def tracked_generated():
    found = set()
    for path in git_files("*.lean"):
        if path.startswith(AUDIT):
            continue
        if GEN_NAME.fullmatch(Path(path).name):
            found.add(path)
            continue
        with open(ROOT / path, "rb") as stream:
            if stream.read(len(PROFILE_PREFIX)) == PROFILE_PREFIX:
                found.add(path)
    return sorted(found)


def example_versions(ex):
    listed = ROOT / "examples" / ex / "zig-versions"
    if listed.is_file():
        return listed.read_text().split()
    data = json.loads((ROOT / "compatibility.json").read_text())
    return [v["version"] for v in data["zig"]["versions"]]


def golden_cases():
    """Each (version, OS) translation that scripts/check.sh compares, with its expected file."""
    for ex_dir in sorted((ROOT / "examples").iterdir()):
        ex = ex_dir.name
        if not (ex_dir / f"{ex}.zig").is_file():
            continue
        Ex = ex[0].upper() + ex[1:]
        args = ["--namespace", Ex, "--prefix", ex + "."]
        if (ex_dir / "translate.args").is_file():
            args += (ex_dir / "translate.args").read_text().split()
        for version in example_versions(ex):
            golden = ROOT / "tests/golden" / version / ex
            for os_name in OSES:
                os_dir, os_gen = golden / f"air-{os_name}", golden / f"Gen-{os_name}.lean"
                # Linux is the reference host; another OS has a case when it has its own files.
                if os_name != "linux" and not os_dir.is_dir() and not os_gen.is_file():
                    continue
                # An <os>-<arch> host also takes its OS's overlay (check.sh's order).
                base_os = os_name.split("-")[0]
                base_dir, base_gen = golden / f"air-{base_os}", golden / f"Gen-{base_os}.lean"
                expected = next(g for g in (os_gen, base_gen, golden / "Gen.lean", ROOT / "Proofs" / Ex / "Gen.lean")
                                if g.is_file())
                overlays = (base_dir, os_dir) if base_os != os_name else (os_dir,)
                dirs = [d for d in (ROOT / "tests/golden" / ex / "air", golden / "air", *overlays) if d.is_dir()]
                yield Case(str(expected.relative_to(ROOT)), dirs, args, "golden",
                           f"{ex} {version} {os_name}", version)


def all_cases():
    cases = [Case(path, [ROOT / air], args, mode, path) for path, air, args, mode in FIXTURES]
    return cases + list(golden_cases())


def strip_identities(value, root=True):
    """`value` without the module identity keys of the current exporter (`module` of the file,
    of a function reference, of a named type or global; `comptime_fn_module`)."""
    if isinstance(value, list):
        return [strip_identities(v, False) for v in value]
    if not isinstance(value, dict):
        return value
    named = root or "func" in value or "name" in value
    return {k: strip_identities(v, False) for k, v in value.items()
            if k != "comptime_fn_module" and not (k == "module" and named)}


def compose(dirs, destination, version):
    """Apply golden overlays as scripts/check.sh does: a later directory replaces every file
    whose normalized function name it provides. Profile metadata is dropped (schema 12 is the
    schema-11 payload plus that record) and `zig_version` is the checked version, which check.sh
    does not compare, so that goldens recorded by several versions form one input."""
    chosen = {}
    for directory in dirs:
        layer = {}
        for path in sorted(directory.glob("*.json")):
            doc = json.loads(path.read_text(encoding="utf-8"))
            layer.setdefault(IDENTITY.sub(r"__\1_N", doc["name"]), []).append((path.name, doc))
        chosen.update(layer)
    # A non-Linux host's own export (`air-<os>`) that replaces every function keeps its
    # schema-12 profile: its translation depends on the target (aarch64 floats, fix-target-floats),
    # as check.sh's does on that host.
    docs = [doc for entries in chosen.values() for _, doc in entries]
    last = dirs[-1].name if dirs else ""
    if (last.startswith("air-") and last != "air-linux" and docs
            and all(doc.get("schema") == 12 for doc in docs)
            and len({json.dumps(doc.get("profile"), sort_keys=True) for doc in docs}) == 1
            and set(chosen) =={IDENTITY.sub(r"__\1_N", json.loads(p.read_text(encoding="utf-8"))["name"])
                                for p in dirs[-1].glob("*.json")}):
        for entries in chosen.values():
            for name, doc in entries:
                (destination / name).write_text(json.dumps(doc), encoding="utf-8")
        return
    for entries in chosen.values():
        for name, doc in entries:
            doc = {k: v for k, v in doc.items() if k != "profile"}
            doc.update(zig_version=version, schema=min(doc["schema"], 11))
            # A legacy (schema-11) program names no modules (docs/air-json.md §Identity): the
            # identities of a schema-12 overlay go with its profile.
            doc = strip_identities(doc)
            (destination / name).write_text(json.dumps(doc), encoding="utf-8")


@functools.cache
def split_generated():
    return runpy.run_path(str(Path(__file__).with_name("normalize-generated.py")))["split_generated"]


def comparable(data, mode):
    """The compared bytes: all of them (`exact`), else the body after the profile record."""
    if mode == "exact":
        return data
    first, _, rest = data.partition(b"\n")
    return rest if first.startswith(PROFILE_PREFIX) else data


def header_error(committed, fresh):
    """A committed profile record must be valid (not ignorable metadata) and name the float
    semantics the translation used: consumers attach it to the generated module."""
    if not committed.startswith(PROFILE_PREFIX):
        return None
    mine = split_generated()(committed, required=True)[0]
    theirs = split_generated()(fresh)[0] if fresh.startswith(PROFILE_PREFIX) else None
    if theirs and mine["float_semantics"] != theirs["float_semantics"]:
        return f"profile record says float_semantics {mine['float_semantics']!r}, translation used {theirs['float_semantics']!r}"
    return None


def first_difference(committed, fresh):
    a, b = committed.decode(errors="replace").splitlines(), fresh.decode(errors="replace").splitlines()
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return f"line {i + 1}: committed {x[:100]!r}, fresh {y[:100]!r}"
    return f"committed {len(a)} lines, fresh {len(b)} lines"


class Translator:
    """Fresh translations, each made once per case."""
    def __init__(self, binary, work):
        self.binary, self.work, self.done = binary, Path(work), {}

    def output(self, index, case):
        """The fresh output bytes, or raise ValueError with the translator's message."""
        if index not in self.done:
            air = self.work / f"air{index}"
            air.mkdir()
            if case.mode == "golden":
                compose(case.dirs, air, case.version)
            else:
                # A fixture's AIR is a directory, or the one file its check translates.
                source = case.dirs[0]
                for src in (sorted(source.glob("*.json")) if source.is_dir() else [source]):
                    shutil.copyfile(src, air / src.name)
            out = self.work / f"Gen{index}.lean"
            # Schema-11 (legacy) AIR translates only with the explicit legacy profile opt-in
            # (docs/profiles.md), as each fixture's own check passes it.
            legacy = ["--profile", "legacy-abi64-le"] if "--profile" not in case.args and all(
                json.loads(f.read_bytes()).get("schema", 0) < 12 for f in air.glob("*.json")) else []
            result = subprocess.run([self.binary, str(air), "-o", str(out), *legacy, *case.args],
                                    capture_output=True, text=True)
            if result.returncode != 0 or not out.is_file():
                message = (result.stderr.strip() or result.stdout.strip() or f"exit {result.returncode}")
                self.done[index] = ValueError(f"AIR does not translate: {message.splitlines()[0][:300]}")
            else:
                self.done[index] = out.read_bytes()
        if isinstance(self.done[index], ValueError):
            raise self.done[index]
        return self.done[index]

    def matches(self, index, case, path):
        """None if `path` equals the fresh output of `case`, else the difference."""
        fresh = self.output(index, case)
        committed = (ROOT / path).read_bytes()
        if case.mode != "exact" and (error := header_error(committed, fresh)):
            return error
        mine, theirs = comparable(committed, case.mode), comparable(fresh, case.mode)
        return None if mine == theirs else first_difference(mine, theirs)


def coverage_errors(cases):
    errors = []
    covered = {case.path for case in cases}
    for path in tracked_generated():
        if path not in covered and path not in EXCEPTIONS:
            errors.append(f"{path}: tracked generated module with no retranslation rule")
    for case in cases:
        if not (ROOT / case.path).is_file() or not case.dirs or any(not d.exists() for d in case.dirs):
            errors.append(f"{case.path} [{case.label}]: generated file or AIR input missing")
    lean = git_files("*.lean")
    for path in EXCEPTIONS:
        if not (ROOT / path).is_file():
            errors.append(f"{path}: listed exception no longer exists; remove it from EXCEPTIONS")
            continue
        if path in STAND_INS:
            continue
        # An importer resolves `<Dir>.Gen` against its own `-R` root: only a module below the
        # exception's package root can import it.
        package = Path(path).parent.parent
        module = ".".join(Path(path).relative_to(package).with_suffix("").parts)
        pattern = re.compile(rf"^import\s+(.*\s)?{re.escape(module)}(\s|$)", re.M)
        for importer in lean:
            if Path(importer).is_relative_to(package) and importer != path and \
                    pattern.search((ROOT / importer).read_text(errors="replace")):
                errors.append(f"{importer}: imports the non-generated exception {path}")
    return errors


def run_check(translator, cases, only):
    errors = coverage_errors(cases)
    for index, case in enumerate(cases):
        if only and only not in case.path and only not in case.label:
            continue
        if not (ROOT / case.path).is_file() or any(not d.exists() for d in case.dirs):
            continue  # Reported by coverage_errors.
        try:
            difference = translator.matches(index, case, case.path)
        except ValueError as error:
            difference = str(error)
        if difference:
            errors.append(f"{case.path} [{case.label}]: not the fresh translation ({difference})")
        else:
            print(f"ok {case.label}: {case.path}", file=sys.stderr)
    return errors


def run_attest(translator, cases, paths):
    errors = coverage_errors(cases)
    records = []
    for path in paths or tracked_generated():
        if path in EXCEPTIONS:
            records.append(dict(path=path, sha256=hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
                                exception=EXCEPTIONS[path]))
            continue
        matched = []
        for index, case in enumerate(cases):
            if case.path == path:
                try:
                    if translator.matches(index, case, path) is None:
                        matched.append(case.label)
                except ValueError:
                    pass
        if not matched:
            errors.append(f"{path}: not a fresh translation of its committed AIR")
        records.append(dict(path=path, sha256=hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
                            fresh_translation_of=matched))
    print(json.dumps(dict(format="air2lean-gen-integrity-v1", files=records), indent=2, sort_keys=True))
    return errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("check", "attest", "list"))
    parser.add_argument("paths", nargs="*", help="attest: generated files (default: every tracked one)")
    parser.add_argument("--translator", default=os.environ.get("AIR2LEAN_TRANSLATOR",
                                                             str(ROOT / ".lake/build/bin/air2lean")))
    parser.add_argument("--only", default="", help="check: only cases whose file or label contains this")
    args = parser.parse_args(argv)
    if args.paths and args.command != "attest":
        parser.error("paths are only accepted by attest")
    cases = all_cases()
    try:
        errors = run(args, cases)
    except (ValueError, OSError) as error:
        errors = [str(error)]
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if errors:
        print("hint: never edit a generated module by hand: regenerate it from committed AIR "
              "(scripts/check.sh) and put hand-written definitions in a separate module", file=sys.stderr)
        return 1
    return 0


def run(args, cases):
    if args.command == "list":
        for case in cases:
            dirs = ",".join(str(d.relative_to(ROOT)) for d in case.dirs)
            print(f"{case.label}\t{case.path}\t{case.mode}\t{dirs}\t{' '.join(case.args)}")
        for path, reason in EXCEPTIONS.items():
            print(f"exception\t{path}\t{reason}")
        return coverage_errors(cases)
    if not os.access(args.translator, os.X_OK):
        return [f"translator not found: {args.translator} (lake build air2lean)"]
    with tempfile.TemporaryDirectory(prefix="air2lean-gen-integrity.") as work:
        translator = Translator(args.translator, work)
        if args.command == "check":
            return run_check(translator, cases, args.only)
        return run_attest(translator, cases, [str(Path(p)) for p in args.paths])


if __name__ == "__main__":
    sys.exit(main())
