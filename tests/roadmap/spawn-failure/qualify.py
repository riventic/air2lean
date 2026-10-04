#!/usr/bin/env python3
"""Sequential raw-artifact qualification for explicit fallible assignment."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT / "tests/roadmap/spawn-failure"
HEADER = "Thread assignment policy: fallible"
def source_paths():
    paths = [ROOT / "Air2Lean.lean", ROOT / "ZigLean.lean", ROOT / "lean-toolchain"]
    for name in ("Air2Lean", "ZigLean"):
        for base, directories, files in os.walk(ROOT / name, topdown=True):
            directories[:] = sorted(d for d in directories if not d.startswith("."))
            paths.extend(Path(base) / file for file in sorted(files) if file.endswith(".lean"))
    return sorted(paths)

def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def artifacts(destination):
    found = {}
    for base, directories, files in os.walk(destination, topdown=True):
        directories[:] = sorted(d for d in directories if d not in {"zig-cache", "native-cache"})
        for name in sorted(files):
            path = Path(base) / name
            if name != "report.json":
                found[str(path.relative_to(destination))] = {"sha256": digest(path), "bytes": path.stat().st_size}
    return dict(sorted(found.items()))

class Gate:
    def __init__(self, destination):
        self.destination = destination
        self.steps = []

    def run(self, label, argv, *, env=None, expected=0, marker=None, timeout=180):
        logfile = self.destination / (label + ".log")
        step = {"label": label, "argv": list(map(str, argv)), "expected_exit": expected,
                "status": "pending", "log": logfile.name}
        self.steps.append(step)
        with logfile.open("wb") as output:
            proc = subprocess.Popen(step["argv"], cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = proc.wait(timeout=timeout)
            except BaseException as failure:
                # Keep the leader unreaped until group cleanup finishes, anchoring its PGID.
                step["status"] = "timeout" if isinstance(failure, subprocess.TimeoutExpired) else "interrupted"
                try:
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    time.sleep(0.2)
                finally:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    try:
                        proc.wait(timeout=2)
                    except subprocess.TimeoutExpired as exc:
                        step["status"] = "cleanup_failed"
                        raise RuntimeError(label + ": process cleanup timed out") from exc
                raise RuntimeError(label + ": command timed out or was interrupted") from failure
        step["exit"] = code
        if logfile.stat().st_size > 16 * (1 << 20):
            step["status"] = "oversized_log"
            raise RuntimeError(label + ": output exceeded 16 MiB")
        text = logfile.read_text(errors="replace")
        if code != expected or (marker is not None and marker not in text):
            step["status"] = "failed"
            raise RuntimeError(label + ": wrong exit or missing evidence marker")
        if expected != 0 and any(": error:" in line or line.startswith("error:") for line in text.splitlines()):
            step["status"] = "elaboration_failed"
            raise RuntimeError(label + ": compilation failure is not a mutation detection")
        step["status"] = "passed"
        return text


def qualify(mode, destination):
    gate = Gate(destination)
    report = {"schema": 1, "status": "failed", "mode": mode, "spawn_policy": "fallible",
              "scope": "finite safety/result contracts; no fairness, native adequacy, cancellation or custom allocator",
              "steps": gate.steps, "sources": {str(p.relative_to(ROOT)): digest(p) for p in source_paths()},
              "legacy_references": {str(p.relative_to(ROOT)): digest(p) for p in
                  sorted((ROOT / "tests/roadmap/thread-tuples/air/0.16.0").glob("*.json")) +
                  [ROOT / "tests/roadmap/thread-tuples/ThreadTuples/Gen.lean", ROOT / "tests/roadmap/thread-tuples/provenance.json"]},
              "fixture": {p.name: digest(p) for p in FIXTURE.iterdir() if p.is_file()}}
    try:
        lean = [os.environ["AIR2LEAN_LEAN"]] if os.environ.get("AIR2LEAN_LEAN") else ["lake", "env", "lean"]
        translator = Path(os.environ.get("AIR2LEAN_TRANSLATOR", ROOT / ".lake/build/bin/air2lean")).resolve()
        report["translator_sha256"] = digest(translator)
        lean_binary = Path(lean[0]).resolve() if len(lean) == 1 else Path(
            gate.run("lean-binary", ["lake", "env", "which", "lean"]).strip()).resolve()
        report["lean_sha256"] = digest(lean_binary)
        report["lean_version"] = gate.run("lean-version", lean + ["--version"]).strip()
        report["lean_toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        gate.run("proof-modules", ["lake", "build", "ZigLean.Conc.SpawnLemmas", "ZigLean.Conc.Csl"])
        gate.run("resource-boundary", lean + ["--run", str(FIXTURE / "Boundary.lean")],
                 marker="audited spawn resource boundary passed")
        gate.run("kernel-runtime", lean + ["--run", str(FIXTURE / "Runtime.lean")],
                 marker="spawn failure kernel frames and runtime outcomes passed")
        generated = destination / "synthetic"
        generated.mkdir()
        gate.run("pipeline", lean + ["--run", str(FIXTURE / "Pipeline.lean"), str(generated)],
                 marker="all-version spawn policy and caller fallback pipeline fixtures passed")
        expected_synthetic = {"spawn-14.lean", "spawn-15.lean", "spawn-16.lean",
                              "group-async.lean", "group-concurrent.lean"}
        if {p.name for p in generated.iterdir()} != expected_synthetic:
            raise RuntimeError("synthetic all-version artifact inventory differs")
        for path in sorted(generated.glob("*.lean")):
            gate.run("synthetic-" + path.stem, lean + ["-R", str(generated), str(path)])
        gate.run("invalid-policy", [str(translator), str(generated), "-o", str(destination / "invalid.lean"),
                 "--namespace", "Invalid", "--spawn-policy", "unknown"], expected=1,
                 marker="invalid --spawn-policy")
        if mode == "--full":
            version = os.environ["AIR2LEAN_SPAWN_VERSION"]
            if version not in ("0.15.2", "0.16.0"):
                raise RuntimeError("fresh qualification requires Zig 0.15.2 or 0.16.0")
            patched = Path(os.environ["AIR2LEAN_ZIG_AIR"]).resolve()
            native = Path(os.environ["AIR2LEAN_ZIG_NATIVE"]).resolve()
            audit = json.loads((FIXTURE / "api-audit.json").read_text())["versions"][version]
            candidates = [native.parent / "lib/std", native.parent.parent / "lib/std",
                          native.parent.parent / "lib/zig/std"]
            stdlib = next((directory for directory in candidates if (directory / "Thread.zig").is_file()), None)
            if stdlib is None:
                raise RuntimeError("stock compiler standard library source is missing")
            report["stdlib_sha256"] = {name: digest(stdlib / name) for name in audit}
            if any(report["stdlib_sha256"][name] != record["sha256"] for name, record in audit.items()):
                raise RuntimeError("stock standard library differs from the pristine API audit")
            report.update(version=version, target="x86_64-linux", cpu="baseline", build_mode="ReleaseSafe",
                          tool_sha256={"patched": digest(patched), "stock": digest(native)})
            for label, tool in (("patched", patched), ("stock", native)):
                observed = gate.run(label + "-version", [str(tool), "version"]).strip()
                if observed != version:
                    raise RuntimeError(label + ": mismatched compiler version")
            air = destination / "air"
            air.mkdir()
            names = [n for n in (FIXTURE / "filter").read_text().splitlines()
                     if version == "0.16.0" or ".group" not in n]
            export_env = dict(os.environ, ZIG_AIR_JSON_DIR=str(air), ZIG_AIR_JSON_FILTER=",".join(names))
            gate.run("fresh-export", [str(patched), "build-obj", "-fno-emit-bin", "-OReleaseSafe",
                     "-fno-error-tracing", "-target", "x86_64-linux", "-mcpu=baseline",
                     str(FIXTURE / "spawn_failure.zig"), "--cache-dir", str(destination / "zig-cache")], env=export_env)
            records = [json.loads(p.read_text()) for p in sorted(air.glob("*.json"))]
            if sorted(r["name"] for r in records) != sorted(names) or any(
                    r["schema"] != 11 or r["zig_version"] != version or r["target_endian"] != "little" for r in records):
                raise RuntimeError("fresh AIR inventory/version/schema/endianness differs")
            default = destination / "Default.lean"
            available = destination / "Available.lean"
            for label, path, policy in [("default-policy", default, []),
                                        ("explicit-available", available, ["--spawn-policy", "available"])]:
                gate.run(label, [str(translator), str(air), "-o", str(path), "--namespace", "SpawnFailure",
                         "--prefix", "spawn_failure."] + policy)
            if default.read_bytes() != available.read_bytes():
                raise RuntimeError("default and explicit availability policy emission differ")
            gate.run("available-kernel", lean + ["-R", str(destination), str(default)])
            legacy = destination / "TupleDefault.lean"
            gate.run("legacy-default-bytes", [str(translator), str(ROOT / "tests/roadmap/thread-tuples/air/0.16.0"),
                     "-o", str(legacy), "--namespace", "ThreadTuples", "--prefix", "thread_tuples."])
            if legacy.read_bytes() != (ROOT / "tests/roadmap/thread-tuples/ThreadTuples/Gen.lean").read_bytes():
                raise RuntimeError("historical default capture/dispatch emission changed")
            raw = destination / "Gen.lean"
            gate.run("translate", [str(translator), str(air), "-o", str(raw), "--namespace", "SpawnFailure",
                     "--prefix", "spawn_failure.", "--spawn-policy", "fallible"])
            source = raw.read_text()
            required = [HEADER, "Zig.spawnWithPolicyC .fallible"]
            if version == "0.16.0":
                required += ["Zig.groupAsyncWithPolicyC .fallible", "Zig.groupConcurrentWithPolicyC .fallible"]
            if any(token not in source for token in required):
                raise RuntimeError("raw generated fallible policy/effects lost")
            template = (FIXTURE / "source-runtime.lean").read_text()
            if version == "0.16.0":
                template += (FIXTURE / "source-group.lean").read_text()
            combined = destination / "source-allowed-outcomes.lean"
            combined.write_text(source + template)
            gate.run("source-kernel-and-execution", lean + ["-R", str(destination), "--run", str(combined)],
                     marker="SOURCE_GROUP_OUTCOMES_OK" if version == "0.16.0" else "SOURCE_THREAD_OUTCOMES_OK")
            for label, before, after in [("no-failure", "spawnWithPolicyC .fallible", "spawnWithPolicyC .available")]:
                mutant = destination / (label + ".lean")
                if before not in source:
                    raise RuntimeError("mutation target missing")
                mutant.write_text(source.replace(before, after) + template)
                gate.run(label, lean + ["-R", str(destination), "--run", str(mutant)], expected=1, marker="SOURCE_REJECTED:")
            if version == "0.16.0":
                mutant = destination / "no-fallback.lean"
                mutant.write_text(source.replace("groupAsyncWithPolicyC .fallible", "groupAsyncWithPolicyC .available") + template)
                gate.run("no-fallback", lean + ["-R", str(destination), "--run", str(mutant)], expected=1, marker="SOURCE_REJECTED:")
            gate.run("native-allowed-outcomes", [str(native), "test", "-OReleaseSafe", "--cache-dir",
                     str(destination / "native-cache"), "--dep", "spawn_failure_source",
                     "-Mroot=" + str(FIXTURE / "native.zig"), "-Mspawn_failure_source=" + str(FIXTURE / "spawn_failure.zig")])
        report["status"] = "passed"
    finally:
        report["artifacts"] = artifacts(destination)
        (destination / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    if len(sys.argv) > 2:
        raise SystemExit("usage: check.sh --synthetic|--full")
    mode = sys.argv[1] if len(sys.argv) == 2 else "--synthetic"
    if mode not in ("--synthetic", "--full"):
        raise SystemExit("usage: check.sh --synthetic|--full")
    root = os.environ.get("AIR2LEAN_SPAWN_ARTIFACT_DIR")
    destination = Path(root).resolve() if root else Path(tempfile.mkdtemp(
        prefix="air2lean-spawn-failure-", dir=os.environ.get("RUNNER_TEMP")))
    destination.mkdir(parents=True, exist_ok=True)
    if any(destination.iterdir()):
        raise SystemExit("artifact directory must be empty")
    print("retaining spawn-failure evidence:", destination, flush=True)
    def interrupted(signum, _frame):
        raise KeyboardInterrupt("qualification interrupted by signal " + str(signum))
    for signum in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, interrupted)
    try:
        qualify(mode, destination)
    except (RuntimeError, OSError, KeyError) as exc:
        raise SystemExit(str(exc)) from exc
    print("spawn failure qualification passed")

if __name__ == "__main__":
    main()
