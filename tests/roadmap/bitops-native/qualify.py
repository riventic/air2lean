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
# Native binaries are static musl on Linux so that one minimal image runs them anywhere.
NATIVE_TRIPLE = {"x86_64-linux": "x86_64-linux-musl", "aarch64-linux": "aarch64-linux-musl",
                 "aarch64-macos": "aarch64-macos"}
IMAGE = "alpine:3.21"
SRC_FILES = ["wide.zig", "native.zig", "Diff.lean.inc"]


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
        cmd = ["docker", "run", "--rm", "--platform", plat, "-v", f"{install}:/zig:ro", IMAGE, "/zig/bin/zig", "version"]
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
             "-w", "/tmp", IMAGE, "/zig/bin/zig", *flags, "/src/wide.zig"])
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


def lean_stream(air, work, label):
    gen_lean = work / f"Gen-{label}.lean"
    run(["lake", "exe", "air2lean", str(air), "-o", str(gen_lean), "--namespace", "Wide", "--prefix", "wide."],
        cwd=ROOT)
    diff = work / f"Diff-{label}.lean"
    diff.write_text(gen_lean.read_text() + (HERE / "Diff.lean.inc").read_text())
    out = work / f"lean-{label}.txt"
    with open(out, "w") as f:
        run(["lake", "env", "lean", "-R", str(work), "--run", str(diff)], cwd=ROOT, stdout=f)
    return out


def executor(spec, exe):
    if spec == "host":
        return [str(exe)]
    if spec.startswith("docker:"):
        return ["docker", "run", "--rm", "--platform", spec.split(":", 1)[1], "-v", f"{exe.parent}:/w:ro",
                IMAGE, f"/w/{exe.name}"]
    if spec.startswith("qemu:"):
        return [spec.split(":", 1)[1], str(exe)]
    raise SystemExit(f"unknown executor {spec}")


def native_stream(zig, target, mode, exec_spec, work):
    exe = work / f"native-{target}-{mode}"
    run([zig, "build-exe", f"-O{mode}", "-mcpu=baseline", "-target", NATIVE_TRIPLE[target],
         f"-femit-bin={exe}", "--dep", "wide", f"-Mroot={HERE / 'native.zig'}", f"-Mwide={HERE / 'wide.zig'}"],
        cwd=work)
    out = work / f"native-{target}-{mode}.txt"
    with open(out, "w") as f:
        run(executor(exec_spec, exe), stderr=f)
    return out


def compare(native, lean):
    a, b = Path(native).read_text().splitlines(), Path(lean).read_text().splitlines()
    mismatches = [(i + 1, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y]
    mismatches_total = len(mismatches) + abs(len(a) - len(b))
    return {"rows": len(a), "lean_rows": len(b), "mismatches": mismatches_total,
            "first_mismatches": [{"row": i, "native": x, "lean": y} for i, x, y in mismatches[:5]]}


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
                    "stock_zig_sha256": a.zig_sha256, "corpus": corpus_hashes(), "expected_rows": expected_rows,
                    "host": f"{platform.system().lower()}-{platform.machine()}", "targets": {}}
        for target in a.targets.split(","):
            air = work / f"air-{target}"
            air_hash = export_air(a.zig_air, target, air)
            lean = lean_stream(air, work, target)
            entry = {"air_sha256": air_hash, "lean_sha256": sha(lean), "lean_rows": len(lean.read_text().splitlines()),
                     "executor": execs[target], "modes": {}}
            for mode in a.modes.split(","):
                nat = native_stream(a.zig, target, mode, execs[target], work)
                res = compare(nat, lean)
                res["native_sha256"] = sha(nat)
                entry["modes"][mode] = res
                print(f"{a.version} {target} {mode}: rows={res['rows']} mismatches={res['mismatches']}", flush=True)
            evidence["targets"][target] = entry
        out = Path(a.evidence)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
        bad = [(t, m) for t, e in evidence["targets"].items() for m, r in e["modes"].items()
               if r["mismatches"] or r["rows"] != expected_rows or r["lean_rows"] != expected_rows]
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
            ok = sha(nat) == want and rows == committed["expected_rows"]
            print(f"{a.version} {target} {mode}: rows={rows} {'match' if ok else 'MISMATCH'}", flush=True)
            if not ok:
                failed.append(mode)
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
        elif entry["lean_sha256"] != ref["lean_sha256"]:
            problems.append(f"{target}: Lean stream differs from committed evidence")
        for mode, r in entry["modes"].items():
            if r["mismatches"] or r["native_sha256"] != ref["lean_sha256"]:
                problems.append(f"{target} {mode}: mismatches={r['mismatches']}")
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
                elif r["mismatches"] or r["rows"] != expected_rows or r["native_sha256"] != entry["lean_sha256"]:
                    problems.append(f"{version} {target} {mode}: mismatches={r['mismatches']} rows={r['rows']}")
    if problems:
        print("\n".join(problems), file=sys.stderr)
        raise SystemExit(1)
    print(f"bitops-native evidence current: {len(VERSIONS)} versions x {len(TARGETS)} targets x "
          f"{len(MODES)} modes, {expected_rows} rows each, 0 mismatches")


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
