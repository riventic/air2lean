#!/usr/bin/env python3
"""Native differential qualification of the wide integer bit-operation corpus (roadmap L02).

run:      export AIR of wide.zig for each requested target with the patched compiler, translate it,
          evaluate it in Lean, build the corpus natively with stock Zig for each target and
          optimization mode, execute it, compare every row, and write an evidence file.
native:    build and run the native programs only and compare them with the Lean stream digests
          recorded in committed evidence (a runner without Lean, for example native aarch64-linux).
verify:   a fresh `run` evidence file must reproduce the committed Lean and native stream digests.
check:    offline; fail unless the committed evidence covers every version and target with the
          current corpus, the full row count and no mismatch.

Shift counts >= W (`panics.zig`, Debug and ReleaseSafe only; illegal behavior in the other modes)
must panic natively with `shiftRhsTooBig` exactly where Lean throws that check's constructor
(`scripts/panic-policy.tsv`), and the legal W - 1 control rows must agree in value.

Run `run` and `native` under scripts/build-guard.py (one guard around the whole invocation).
"""
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import gen  # noqa: E402

EVIDENCE = HERE / "evidence"
VERSIONS = ["0.14.1", "0.15.2", "0.16.0"]
TARGETS = ["x86_64-linux", "aarch64-linux", "aarch64-macos"]
MODES = ["Debug", "ReleaseSafe", "ReleaseFast", "ReleaseSmall"]
SAFE_MODES = ["Debug", "ReleaseSafe"]
# Native binaries are static musl on Linux so that one minimal image runs them anywhere.
NATIVE_TRIPLE = {"x86_64-linux": "x86_64-linux-musl", "aarch64-linux": "aarch64-linux-musl",
                 "aarch64-macos": "aarch64-macos"}
IMAGE = "alpine:3.21"
AIR_IMAGE = "ubuntu:24.04"  # the compiler lock wrapper is a bash script
# Rosetta (Docker on Apple silicon) rejects some non-PIE x86_64 binaries ("bss_size overflow").
NATIVE_FLAGS = ["-fno-strip", "-fPIE"]
SRC_FILES = ["wide.zig", "native.zig", "panics.zig", "Diff.lean.inc"]
PANIC_POLICY = dict(line.split("\t") for line in
                    (ROOT / "scripts" / "panic-policy.tsv").read_text().splitlines() if line)


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, **kw):
    print("+", " ".join(map(str, cmd)), flush=True)
    return subprocess.run(cmd, check=True, **kw)


def corpus_hashes():
    return {name: sha(HERE / name) for name in SRC_FILES}


def zig_version(zig):
    return subprocess.run([zig, "version"], check=True, capture_output=True, text=True).stdout.strip()


def air_compiler_version(spec):
    if spec.startswith("docker:"):
        _, plat, install = spec.split(":", 2)
        cmd = ["docker", "run", "--rm", "--platform", plat, "-v", f"{install}:/zig:ro", AIR_IMAGE, "/zig/bin/zig", "version"]
        return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout.strip()
    return zig_version(spec)


def export_air(zig_air, target, out):
    """Dump AIR. `zig_air` is a path, or docker:<platform>:<install dir> for a Linux compiler."""
    out.mkdir(parents=True)
    flags = ["build-obj", "-fno-emit-bin", "-OReleaseSafe", "-fno-error-tracing", "-target", target,
             "-mcpu=baseline"]
    if zig_air.startswith("docker:"):
        _, plat, install = zig_air.split(":", 2)
        src = out.parent / f"src-{target}"
        src.mkdir()
        shutil.copy(HERE / "wide.zig", src / "wide.zig")
        run(["docker", "run", "--rm", "--platform", plat, "-v", f"{install}:/zig:ro", "-v", f"{src}:/src:ro",
             "-v", f"{out}:/air", "-e", "ZIG_AIR_JSON_DIR=/air", "-e", "ZIG_AIR_JSON_FILTER=wide.",
             "-w", "/tmp", AIR_IMAGE, "/zig/bin/zig", *flags, "/src/wide.zig"])
    else:
        run([zig_air, *flags, str(HERE / "wide.zig")],
            env={**os.environ, "ZIG_AIR_JSON_DIR": str(out), "ZIG_AIR_JSON_FILTER": "wide."})
    files = sorted(out.glob("*.json"))
    names = sorted(json.loads(p.read_text())["name"].removeprefix("wide.") for p in files)
    if names != sorted(gen.exports()) or len(files) != len(gen.exports()):
        raise SystemExit(f"wide export inventory mismatch for {target}: {names}")
    h = hashlib.sha256()
    for p in files:
        h.update(p.name.encode() + b"\0" + p.read_bytes())
    return h.hexdigest()


TRANSLATABLE = ("x86_64-linux", "aarch64-macos")


def air_differences(ref, other):
    """Names of exported functions whose AIR differs from `ref` in anything but `profile`."""
    bad = []
    for p in sorted(ref.glob("*.json")):
        a, b = json.loads(p.read_text()), json.loads((other / p.name).read_text())
        a.pop("profile", None)
        b.pop("profile", None)
        if a != b:
            bad.append(p.name)
    return bad


def lean_stream(air, work, label):
    gen_lean = work / f"Gen-{label}.lean"
    run(["lake", "exe", "air2lean", str(air), "-o", str(gen_lean), "--namespace", "Wide", "--prefix", "wide."],
        cwd=ROOT)
    diff = work / f"Diff-{label}.lean"
    diff.write_text(gen_lean.read_text() + (HERE / "Diff.lean.inc").read_text())
    lines = run(["lake", "env", "lean", "-R", str(work), "--run", str(diff)], cwd=ROOT,
                stdout=subprocess.PIPE, text=True).stdout.splitlines(keepends=True)
    out, panics = work / f"lean-{label}.txt", work / f"lean-panics-{label}.txt"
    out.write_text("".join(x for x in lines if not x.startswith("P ")))
    panics.write_text("".join(x for x in lines if x.startswith("P ")))
    return out, panics


def executor(spec, exe):
    if spec == "host":
        return [str(exe)]
    if spec.startswith("docker:"):
        return ["docker", "run", "--rm", "--platform", spec.split(":", 1)[1], "-v", f"{exe.parent}:/w:ro",
                IMAGE, f"/w/{exe.name}"]
    if spec.startswith("qemu:"):
        return [spec.split(":", 1)[1], str(exe)]
    raise SystemExit(f"unknown executor {spec}")


exit_codes = {}


def native_stream(zig, target, mode, exec_spec, work, root="native"):
    exe = work / f"{root}-{target}-{mode}"
    run([zig, "build-exe", f"-O{mode}", *NATIVE_FLAGS, "-mcpu=baseline", "-target", NATIVE_TRIPLE[target],
         f"-femit-bin={exe}", "--dep", "wide", f"-Mroot={HERE / f'{root}.zig'}", f"-Mwide={HERE / 'wide.zig'}"],
        cwd=work)
    out = work / f"{root}-{target}-{mode}.txt"
    with open(out, "w") as f:
        proc = subprocess.run(executor(exec_spec, exe), stderr=f)
    exit_codes[str(out)] = proc.returncode
    return out


def compare(native, lean):
    a, b = Path(native).read_text().splitlines(), Path(lean).read_text().splitlines()
    mismatches = [(i + 1, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y]
    mismatches_total = len(mismatches) + abs(len(a) - len(b))
    return {"rows": len(a), "lean_rows": len(b), "mismatches": mismatches_total,
            "first_mismatches": [{"row": i, "native": x, "lean": y} for i, x, y in mismatches[:5]]}


def lean_panic_line(line):
    """A Lean `P` row in native form: the thrown constructor becomes the native check name that
    panic-policy.tsv maps to it, if the constructor is that of `shiftRhsTooBig`."""
    head, sep, kind = line.rpartition(" panic ")
    if sep and PANIC_POLICY["shiftRhsTooBig"] == kind:
        return f"{head} panic shiftRhsTooBig"
    return line


def compare_panics(native, lean):
    """Native `panics.zig` stream against the Lean `P` rows; every illegal count must panic."""
    a = Path(native).read_text().splitlines()
    b = [lean_panic_line(x) for x in Path(lean).read_text().splitlines()]
    mismatches = [(i + 1, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y]
    panics = sum(x.endswith(" panic shiftRhsTooBig") for x in a)
    want = sum(int(k) >= int(t[1:]) for _, t, _, _, k in (r.split()[:5] for r in b))
    return {"rows": len(a), "lean_rows": len(b), "panics": panics, "expected_panics": want,
            "mismatches": len(mismatches) + abs(len(a) - len(b)),
            "first_mismatches": [{"row": i, "native": x, "lean": y} for i, x, y in mismatches[:5]]}


def panics_bad(r):
    return (r["mismatches"] or r["native_exit"] or r["rows"] != len(gen.panic_rows())
            or r["panics"] != r["expected_panics"])


def parse_pairs(text):
    return dict(item.split("=", 1) for item in text.split(",") if item)


def cmd_run(a):
    execs = parse_pairs(a.exec)
    work = Path(tempfile.mkdtemp(prefix="air2lean-bitops-native."))
    try:
        if subprocess.run([sys.executable, "-B", str(HERE / "gen.py"), "--check"]).returncode:
            raise SystemExit("generated corpus is stale; run gen.py")
        expected_rows = gen.row_count()
        zig_stock = zig_version(a.zig)
        if zig_stock != a.version:
            raise SystemExit(f"stock Zig is {zig_stock}, expected {a.version}")
        air_version = air_compiler_version(a.zig_air)
        if air_version != a.version:
            raise SystemExit(f"patched Zig is {air_version}, expected {a.version}")
        evidence = {"schema": "air2lean-bitops-native/1", "zig": a.version,
                    "stock_zig_sha256": a.zig_sha256, "native_flags": NATIVE_FLAGS, "corpus": corpus_hashes(), "expected_rows": expected_rows,
                    "host": f"{platform.system().lower()}-{platform.machine()}", "targets": {}}
        targets = a.targets.split(",")
        airs, hashes, leans = {}, {}, {}
        for target in sorted(targets, key=lambda t: t == "aarch64-linux"):
            airs[target] = work / f"air-{target}"
            hashes[target] = export_air(a.zig_air, target, airs[target])
            entry = {"air_sha256": hashes[target], "executor": execs[target], "modes": {}, "panics": {}}
            if target in TRANSLATABLE:
                leans[target] = lean_stream(airs[target], work, target)
                lean, lean_panics = leans[target]
            else:
                # The translator is guarded to the model ABI scope (x86_64-linux, aarch64-macos):
                # aarch64-linux AIR is accepted only if it equals the x86_64-linux AIR but for
                # `profile`, and the Lean stream is that of the x86_64-linux translation.
                if "x86_64-linux" not in leans:
                    raise SystemExit(f"{target} needs x86_64-linux in --targets as its AIR reference")
                diff = air_differences(airs["x86_64-linux"], airs[target])
                if diff:
                    raise SystemExit(f"{target} AIR differs from x86_64-linux beyond `profile`: {diff[:5]}")
                lean, lean_panics = leans["x86_64-linux"]
                entry["air_equivalent_to"] = "x86_64-linux"
            entry.update({"lean_sha256": sha(lean), "lean_rows": len(lean.read_text().splitlines()),
                          "lean_panics_sha256": sha(lean_panics)})
            for mode in a.modes.split(","):
                nat = native_stream(a.zig, target, mode, execs[target], work)
                res = compare(nat, lean)
                res["native_sha256"] = sha(nat)
                res["native_exit"] = exit_codes[str(nat)]
                if res["native_exit"]:
                    res["crash_after_row"] = res["rows"]
                entry["modes"][mode] = res
                print(f"{a.version} {target} {mode}: rows={res['rows']} mismatches={res['mismatches']}", flush=True)
                if mode in SAFE_MODES:
                    nat = native_stream(a.zig, target, mode, execs[target], work, "panics")
                    res = compare_panics(nat, lean_panics)
                    res.update({"native_sha256": sha(nat), "native_exit": exit_codes[str(nat)]})
                    entry["panics"][mode] = res
                    print(f"{a.version} {target} {mode} panics: rows={res['rows']} panics={res['panics']}/"
                          f"{res['expected_panics']} mismatches={res['mismatches']}", flush=True)
            evidence["targets"][target] = entry
        out = Path(a.evidence)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
        bad = [(t, m) for t, e in evidence["targets"].items() for m, r in e["modes"].items()
               if r["mismatches"] or r["native_exit"] or r["rows"] != expected_rows or r["lean_rows"] != expected_rows]
        bad += [(t, m, "panics") for t, e in evidence["targets"].items() for m, r in e["panics"].items()
                if panics_bad(r)]
        if bad:
            raise SystemExit(f"mismatching or incomplete lanes (triage required): {bad}")
    finally:
        if not a.keep:
            shutil.rmtree(work, ignore_errors=True)
        else:
            print(f"kept {work}")


def cmd_native(a):
    committed = json.loads(Path(a.evidence).read_text())
    work = Path(tempfile.mkdtemp(prefix="air2lean-bitops-native."))
    try:
        if committed["corpus"] != corpus_hashes():
            raise SystemExit("committed evidence was recorded for a different corpus")
        if zig_version(a.zig) != a.version:
            raise SystemExit(f"stock Zig is not {a.version}")
        target = a.target
        want = committed["targets"][target]["lean_sha256"]
        failed = []
        for mode in a.modes.split(","):
            nat = native_stream(a.zig, target, mode, a.exec, work)
            rows = len(nat.read_text().splitlines())
            ok = exit_codes[str(nat)] == 0 and sha(nat) == want and rows == committed["expected_rows"]
            print(f"{a.version} {target} {mode}: rows={rows} {'match' if ok else 'MISMATCH'}", flush=True)
            if not ok:
                failed.append(mode)
            if mode in SAFE_MODES:
                want_panics = committed["targets"][target]["panics"][mode]["native_sha256"]
                nat = native_stream(a.zig, target, mode, a.exec, work, "panics")
                ok = exit_codes[str(nat)] == 0 and sha(nat) == want_panics
                print(f"{a.version} {target} {mode} panics: {'match' if ok else 'MISMATCH'}", flush=True)
                if not ok:
                    failed.append(f"{mode} panics")
        if failed:
            raise SystemExit(f"native stream differs from committed Lean stream: {failed}")
    finally:
        shutil.rmtree(work, ignore_errors=True)


def cmd_verify(a):
    """A fresh run must reproduce the committed Lean and native streams for every target it covers."""
    fresh, committed = (json.loads(Path(x).read_text()) for x in (a.fresh, a.committed))
    problems = []
    if fresh["corpus"] != committed["corpus"]:
        problems.append("corpus differs from the committed evidence")
    for target, entry in fresh["targets"].items():
        ref = committed["targets"].get(target)
        if ref is None:
            problems.append(f"{target}: not in committed evidence")
            continue
        if entry["lean_sha256"] != ref["lean_sha256"]:
            problems.append(f"{target}: Lean stream differs from committed evidence")
        for mode, r in entry["modes"].items():
            if r["mismatches"] or r["native_sha256"] != ref["lean_sha256"]:
                problems.append(f"{target} {mode}: mismatches={r['mismatches']}")
        if entry["lean_panics_sha256"] != ref["lean_panics_sha256"]:
            problems.append(f"{target}: Lean shift-count panic stream differs from committed evidence")
        for mode, r in entry["panics"].items():
            if panics_bad(r) or r["native_sha256"] != ref["panics"][mode]["native_sha256"]:
                problems.append(f"{target} {mode} panics: mismatches={r['mismatches']}")
    if problems:
        print("\n".join(problems), file=sys.stderr)
        raise SystemExit(1)
    print(f"fresh run reproduces committed evidence for {', '.join(fresh['targets'])}")


def cmd_check(a):
    problems = []
    expected_rows = gen.row_count()
    corpus = corpus_hashes()
    for version in VERSIONS:
        path = EVIDENCE / f"{version}.json"
        if not path.exists():
            problems.append(f"missing evidence {path.name}")
            continue
        ev = json.loads(path.read_text())
        if ev["corpus"] != corpus:
            problems.append(f"{version}: recorded for a different corpus")
        if ev["expected_rows"] != expected_rows:
            problems.append(f"{version}: row count {ev['expected_rows']} != {expected_rows}")
        for target in TARGETS:
            entry = ev["targets"].get(target)
            if entry is None:
                problems.append(f"{version}: missing target {target}")
                continue
            if entry["lean_rows"] != expected_rows:
                problems.append(f"{version} {target}: Lean rows {entry['lean_rows']}")
            for mode in MODES:
                r = entry["modes"].get(mode)
                if r is None:
                    problems.append(f"{version} {target}: missing mode {mode}")
                elif r["mismatches"] or r.get("native_exit") or r["rows"] != expected_rows or r["native_sha256"] != entry["lean_sha256"]:
                    problems.append(f"{version} {target} {mode}: mismatches={r['mismatches']} rows={r['rows']}")
            for mode in SAFE_MODES:
                r = entry.get("panics", {}).get(mode)
                if r is None:
                    problems.append(f"{version} {target}: missing shift-count panic lane {mode}")
                elif panics_bad(r):
                    problems.append(f"{version} {target} {mode} panics: mismatches={r['mismatches']} "
                                    f"panics={r['panics']}/{r['expected_panics']}")
    if problems:
        print("\n".join(problems), file=sys.stderr)
        raise SystemExit(1)
    print(f"bitops-native evidence current: {len(VERSIONS)} versions x {len(TARGETS)} targets x "
          f"{len(MODES)} modes, {expected_rows} rows each, 0 mismatches; shift-count panics "
          f"{len(gen.panic_rows())} rows x {len(SAFE_MODES)} safe modes")


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--version", required=True, choices=VERSIONS)
    r.add_argument("--zig-air", required=True)
    r.add_argument("--zig", required=True)
    r.add_argument("--zig-sha256", default="", help="sha256 of the stock Zig archive, recorded as provenance")
    r.add_argument("--targets", default=",".join(TARGETS))
    r.add_argument("--exec", required=True, help="target=executor,... (host | docker:<platform> | qemu:<bin>)")
    r.add_argument("--modes", default=",".join(MODES))
    r.add_argument("--evidence", required=True)
    r.add_argument("--keep", action="store_true")
    n = sub.add_parser("native")
    n.add_argument("--version", required=True, choices=VERSIONS)
    n.add_argument("--zig", required=True)
    n.add_argument("--target", required=True, choices=TARGETS)
    n.add_argument("--exec", default="host")
    n.add_argument("--modes", default=",".join(MODES))
    n.add_argument("--evidence", required=True)
    v = sub.add_parser("verify")
    v.add_argument("--fresh", required=True)
    v.add_argument("--committed", required=True)
    sub.add_parser("check")
    a = p.parse_args()
    {"run": cmd_run, "native": cmd_native, "verify": cmd_verify, "check": cmd_check}[a.cmd](a)


if __name__ == "__main__":
    main()
