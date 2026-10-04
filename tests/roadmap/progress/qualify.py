#!/usr/bin/env python3
"""Serial C03 qualification with fresh, retained artifacts and explicit scope."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = ROOT / "tests/roadmap/progress"


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("artifact-only", "full"), nargs="?", default="artifact-only")
    args = parser.parse_args()
    retention = Path(os.environ.get("AIR2LEAN_PROGRESS_ARTIFACT_DIR", str(ROOT / ".lake"))).resolve()
    retention.mkdir(parents=True, exist_ok=True)
    artifacts = Path(tempfile.mkdtemp(prefix="progress-hints-", dir=retention))
    timeout = int(os.environ.get("AIR2LEAN_PROGRESS_TIMEOUT_SECONDS", "600"))
    report = {
        "schema": 1, "mode": args.mode, "status": "running", "artifacts": str(artifacts),
        "host": {"system": platform.system(), "machine": platform.machine()},
        "export_profile": {"target": "x86_64-linux", "cpu": "baseline", "mode": "ReleaseSafe",
                           "error_tracing": False} if args.mode == "full" else None,
        "scope": {"proof": "safety and partial correctness over arbitrary model schedules",
                  "termination": "not claimed; no-result executions allowed",
                  "fairness": "not assumed", "correspondence": "not proved",
                  "synthetic_versions": ["0.14.1", "0.15.2", "0.16.0"],
                  "source_exports": "not run" if args.mode == "artifact-only" else "0.16.0 only",
                  "native": "not run" if args.mode == "artifact-only" else "finite host calls only; idle is never executed",
                  "search": "no bounded schedule search used as exhaustive correspondence evidence",
                  "trust": "compiler, exporter and selected instruction validity remain trusted"},
        "steps": [], "source_hashes": {}, "compiler_inputs": {},
    }
    print(f"Progress qualification artifacts: {artifacts}", flush=True)

    def save():
        (artifacts / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(name, argv, env=None, expected_failure=None):
        log = artifacts / f"{name}.log"
        step = {"name": name, "argv": [str(x) for x in argv], "log": str(log), "status": "running"}
        report["steps"].append(step)
        save()
        start = time.monotonic()
        with log.open("w") as stream:
            try:
                proc = subprocess.Popen(step["argv"], cwd=ROOT, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT, start_new_session=True)
            except OSError as error:
                step.update(status="failed_to_start", error=str(error))
                save()
                raise
            try:
                code = proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                step.update(status="timeout", elapsed_seconds=time.monotonic() - start)
                save()
                raise RuntimeError(f"{name}: timed out; retained {log}")
        step.update(exit_code=code, elapsed_seconds=time.monotonic() - start)
        if expected_failure:
            valid = code == 85 and expected_failure in log.read_text().splitlines()
            step["status"] = "mutation_rejected_by_assertion" if valid else "failed"
        else:
            valid = code == 0
            step["status"] = "passed" if valid else "failed"
        save()
        if not valid:
            raise RuntimeError(f"{name}: qualification failed; retained {log}")
        return log

    def compiler(name, variable):
        configured = os.environ.get(variable)
        if not configured:
            raise RuntimeError(f"full mode requires explicit {variable}")
        if os.sep in configured:
            executable = Path(configured)
            if not executable.is_absolute():
                executable = ROOT / executable
        else:
            executable = Path(shutil.which(configured) or configured)
        executable = executable.resolve()
        version_log = run(name + "-version", [executable, "version"])
        version = version_log.read_text().strip()
        if not (version == "0.16.0" or version.startswith("0.16.0-")):
            raise RuntimeError(f"{name}: expected qualified 0.16.0 compiler, got {version}")
        env_log = run(name + "-env", [executable, "env"])
        raw_env = env_log.read_text()
        try:
            compiler_env = json.loads(raw_env)
        except json.JSONDecodeError:
            # Preserve raw env output; supported Zig snapshots can print ZON instead of JSON.
            compiler_env = dict(re.findall(r'[.]?(\w+)\s*[:=]\s*"([^"\n]+)"', raw_env))
        binary = Path(compiler_env.get("zig_exe", str(executable))).resolve()
        entry = {"version": version, "executable": str(executable), "sha256": digest(executable),
                 "binary": str(binary), "binary_sha256": digest(binary), "env_log": str(env_log)}
        report["compiler_inputs"][name] = entry
        save()
        lib = compiler_env.get("lib_dir") or compiler_env.get("zig_lib_dir")
        std = compiler_env.get("std_dir")
        if not lib and std:
            lib = str(Path(std).parent)
        if not lib or not Path(lib).is_dir():
            raise RuntimeError(f"{name}: compiler environment did not identify a readable library closure")
        library_hashes = {str(p.relative_to(lib)): digest(p) for p in sorted(Path(lib).rglob("*"))
                          if p.is_file()}
        library_manifest = artifacts / f"{name}-library-hashes.json"
        library_manifest.write_text(json.dumps(library_hashes, indent=2) + "\n")
        entry.update(library=str(lib), library_manifest=str(library_manifest),
                     library_manifest_sha256=digest(library_manifest))
        report["compiler_inputs"][name] = entry
        save()
        return executable

    try:
        report["git_revision"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        report["git_dirty"] = subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)
        paths = {ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                 ROOT / "ZigLean.lean", ROOT / "Air2Lean.lean", ROOT / "scripts/progress-hints.sh"}
        for directory, pattern in [("ZigLean", "*.lean"), ("Air2Lean", "*.lean"),
                                   ("zig-patch", "*"), ("tests/roadmap/progress", "*")]:
            paths.update(p for p in (ROOT / directory).rglob(pattern) if p.is_file() and "__pycache__" not in p.parts)
        for path in sorted(paths):
            if path.is_file():
                report["source_hashes"][str(path.relative_to(ROOT))] = digest(path)
        for fixture in ["progress.zig", "finite.zig", "Runtime.lean", "Pipeline.lean", "Participation.lean"]:
            shutil.copy2(FIXTURES / fixture, artifacts / fixture)
        report["model_source_hashes"] = {p: h for p, h in report["source_hashes"].items()
                                          if p.startswith("ZigLean/") or p == "ZigLean.lean"}
        save()
        run("lean-version", ["lake", "env", "lean", "--version"])
        run("lake-version", ["lake", "--version"])
        report["lean_toolchain_binaries"] = {}
        for tool in ("lean", "lake"):
            executable_log = run(tool + "-executable", ["lake", "env", "which", tool])
            executable = Path(executable_log.read_text().strip()).resolve()
            report["lean_toolchain_binaries"][tool] = {"path": str(executable), "sha256": digest(executable)}
        run("build", ["lake", "build", "ZigLean", "Air2Lean", "air2lean"])
        translator = ROOT / ".lake/build/bin/air2lean"
        report["translator_binary"] = {"path": str(translator), "sha256": digest(translator)}
        run("runtime", ["lake", "env", "lean", "--run", FIXTURES / "Runtime.lean"])
        run("pipeline", ["lake", "env", "lean", "--run", FIXTURES / "Pipeline.lean",
                         artifacts / "ProgressPipeline.lean", artifacts])
        for version in report["scope"]["synthetic_versions"]:
            run("synthetic-" + version, ["lake", "env", "lean", artifacts / f"ProgressPipeline-{version}.lean"])
        run("participation", ["lake", "env", "lean", "--run", FIXTURES / "Participation.lean"])
        original = (FIXTURES / "Participation.lean").read_text()
        marker = "private def hint : ConcM Unit Unit := spinLoopHint"
        if original.count(marker) != 1:
            raise RuntimeError("scheduler participation mutation marker must occur exactly once")
        mutant = artifacts / "ParticipationMutant.lean"
        mutant.write_text(original.replace(marker, "private def hint : ConcM Unit Unit := pure ()"))
        run("participation-mutant", ["lake", "env", "lean", "--run", mutant],
            expected_failure="C03_ASSERTION: spin scheduler participation lost")
        if args.mode == "full":
            patched = compiler("patched-zig", "AIR2LEAN_ZIG_AIR")
            stock = compiler("stock-zig", "AIR2LEAN_ZIG")
            air = artifacts / "air"
            air.mkdir()
            export_env = dict(os.environ, ZIG_AIR_JSON_DIR=str(air), ZIG_AIR_JSON_FILTER="progress.")
            run("export", [patched, "build-obj", "-fno-emit-bin", "-OReleaseSafe", "-fno-error-tracing",
                           "-target", "x86_64-linux", "-mcpu", "baseline", "--cache-dir", artifacts / "zig-cache",
                           "--global-cache-dir", artifacts / "zig-global-cache", FIXTURES / "progress.zig"], env=export_env)
            exported = [json.loads(p.read_text()) for p in sorted(air.glob("*.json"))]
            names = {f["name"] for f in exported}
            required = {"progress.spinOnce", "progress.yieldOnce", "progress.idle", "progress.catchesYield"}
            if not required <= names:
                raise RuntimeError(f"missing source AIR roots: {sorted(required - names)}")
            if any(not n.startswith("progress.") for n in names):
                raise RuntimeError("unexpected exported boundary body; modeled Thread.yield needs no AIR body")
            report["exported_functions"] = sorted(names)
            report["modeled_boundaries"] = ["Thread.yield", "audited operand-free volatile pause"]
            generated = artifacts / "ProgressSource.lean"
            run("translate", ["lake", "exe", "air2lean", air, "-o", generated,
                              "--namespace", "ProgressSource", "--prefix", "progress."])
            run("source-kernel-check", ["lake", "env", "lean", generated])
            run("native-finite", [stock, "test", "-OReleaseSafe", "-fno-error-tracing", "-target", "native",
                                  "--cache-dir", artifacts / "stock-cache", "--global-cache-dir", artifacts / "stock-global-cache",
                                  f"-femit-bin={artifacts / 'finite-tests'}", FIXTURES / "finite.zig"])
            report["native_profile"] = {"target": "native host, separately from x86_64-linux AIR",
                                        "mode": "ReleaseSafe", "iterations": 64, "idle_executed": False}
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        report["artifact_hashes"] = {str(p.relative_to(artifacts)): digest(p) for p in sorted(artifacts.rglob("*"))
                                    if p.is_file() and p.name != "report.json" and not any("cache" in a for a in p.relative_to(artifacts).parts)}
        save()
        print(f"Progress qualification {report['status']}: {artifacts / 'report.json'}", flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
