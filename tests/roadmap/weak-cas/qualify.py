#!/usr/bin/env python3
"""Serial C11 qualification with fresh, retained artifacts and explicit scope."""
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
FIXTURES = ROOT / "tests/roadmap/weak-cas"


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def retained_files(directory):
    paths = []
    for parent, directories, files in os.walk(directory, topdown=True):
        directories[:] = [name for name in directories if "cache" not in name]
        for name in files:
            if name == "report.json" or "cache" in name:
                continue
            path = Path(parent) / name
            if path.is_file():
                paths.append(path)
    return sorted(paths)


def cleanup_process_group(proc, grace_seconds=2, reap_seconds=2):
    """Keep the timed-out leader unreaped until every group signal has been sent."""
    cleanup = {"attempts": [], "errors": []}
    for sig in (signal.SIGTERM, signal.SIGKILL):
        attempt = {"signal": sig.name, "process_group": proc.pid}
        cleanup["attempts"].append(attempt)
        try:
            os.killpg(proc.pid, sig)
            attempt["status"] = "sent"
        except ProcessLookupError:
            attempt["status"] = "already_gone"
        except OSError as error:
            attempt["status"] = "failed"
            cleanup["errors"].append(str(error))
        if sig == signal.SIGTERM:
            # No poll/wait here: the unreaped PID anchors this group through SIGKILL,
            # even when its leader exits on TERM while a descendant ignores TERM.
            try:
                time.sleep(grace_seconds)
            except Exception as error:
                cleanup["errors"].append(str(error))
    try:
        cleanup["leader_exit_code"] = proc.wait(timeout=reap_seconds)
    except (subprocess.TimeoutExpired, OSError) as error:
        cleanup["errors"].append(str(error))
    cleanup["status"] = "failed" if cleanup["errors"] else "completed"
    return cleanup


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("artifact-only", "full"), nargs="?", default="artifact-only")
    args = parser.parse_args()
    retention = Path(os.environ.get("AIR2LEAN_WEAK_CAS_ARTIFACT_DIR", str(ROOT / ".lake"))).resolve()
    retention.mkdir(parents=True, exist_ok=True)
    artifacts = Path(tempfile.mkdtemp(prefix="weak-cas-", dir=retention))
    timeout = int(os.environ.get("AIR2LEAN_WEAK_CAS_TIMEOUT_SECONDS", "600"))
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
                  "native": "not run" if args.mode == "artifact-only" else "bounded source weak/strong/retry allowed outcomes; no failure frequency required",
                  "search": "no bounded schedule search used as exhaustive correspondence evidence",
                  "trust": "compiler, exporter and selected instruction validity remain trusted"},
        "steps": [], "source_hashes": {}, "compiler_inputs": {},
    }
    print(f"Weak CAS qualification artifacts: {artifacts}", flush=True)

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
                cleanup = cleanup_process_group(proc)
                step.update(status="timeout", cleanup=cleanup,
                            elapsed_seconds=time.monotonic() - start)
                save()
                detail = "; process-group cleanup failed" if cleanup["errors"] else ""
                raise RuntimeError(f"{name}: timed out{detail}; retained {log}")
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
        executable_hash = digest(executable)
        binary_hash = executable_hash if executable.samefile(binary) else digest(binary)
        entry = {"version": version, "executable": str(executable), "sha256": executable_hash,
                 "binary": str(binary), "binary_sha256": binary_hash, "env_log": str(env_log)}
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
                 ROOT / "ZigLean.lean", ROOT / "Air2Lean.lean", ROOT / "scripts/weak-cas.sh"}
        for directory, pattern in [("ZigLean", "*.lean"), ("Air2Lean", "*.lean"), ("Proofs", "*.lean"),
                                   ("zig-patch", "*"), ("tests/roadmap/weak-cas", "*")]:
            paths.update(p for p in (ROOT / directory).rglob(pattern) if p.is_file() and "__pycache__" not in p.parts)
        for path in sorted(paths):
            if path.is_file():
                report["source_hashes"][str(path.relative_to(ROOT))] = digest(path)
        for fixture in ["weakcas.zig", "native.zig", "Runtime.lean", "Messages.lean", "Preparation.lean", "Pipeline.lean", "Mutation.lean", "SourceCheck.lean.in", "Harness.py", "qualify.py"]:
            shutil.copy2(FIXTURES / fixture, artifacts / fixture)
        report["model_source_hashes"] = {p: h for p, h in report["source_hashes"].items()
                                          if p.startswith("ZigLean/") or p == "ZigLean.lean"}
        save()
        run("harness-cleanup", [sys.executable, FIXTURES / "Harness.py"])
        run("lean-version", ["lake", "env", "lean", "--version"])
        run("lake-version", ["lake", "--version"])
        report["lean_toolchain_binaries"] = {}
        for tool in ("lean", "lake"):
            executable_log = run(tool + "-executable", ["lake", "env", "which", tool])
            executable = Path(executable_log.read_text().strip()).resolve()
            report["lean_toolchain_binaries"][tool] = {"path": str(executable), "sha256": digest(executable)}
        run("build", ["lake", "build", "ZigLean", "ZigLean.Conc.WeakWord", "Air2Lean", "air2lean"])
        run("shipped-client-proofs", ["lake", "build", "Proofs"])
        translator = ROOT / ".lake/build/bin/air2lean"
        report["translator_binary"] = {"path": str(translator), "sha256": digest(translator)}
        run("runtime", ["lake", "env", "lean", "--run", FIXTURES / "Runtime.lean"])
        run("message-precision", ["lake", "env", "lean", "--run", FIXTURES / "Messages.lean"])
        run("preparation-equivalence", ["lake", "env", "lean", "--run", FIXTURES / "Preparation.lean"])
        run("pipeline", ["lake", "env", "lean", "--run", FIXTURES / "Pipeline.lean", artifacts])
        for version in report["scope"]["synthetic_versions"]:
            run("synthetic-" + version, ["lake", "env", "lean", "-R", artifacts, artifacts / f"WeakCasPipeline-{version}.lean"])
        run("mutation-baseline", ["lake", "env", "lean", "--run", FIXTURES / "Mutation.lean"])
        original = (FIXTURES / "Mutation.lean").read_text()
        marker = "cmpxchgWeakAt 1 .acqRel .acquire 1 p (42#8) (7#8)"
        if original.count(marker) != 1:
            raise RuntimeError("weak-CAS mutation marker must occur exactly once")
        mutant = artifacts / "WeakCasMutant.lean"
        mutant.write_text(original.replace(marker, "cmpxchgAt 0 .acqRel .acquire 1 p (42#8) (7#8)"))
        run("weak-failure-mutant", ["lake", "env", "lean", "-R", artifacts, "--run", mutant],
            expected_failure="C11_ASSERTION: spurious failure branch removed")
        if args.mode == "full":
            patched = compiler("patched-zig", "AIR2LEAN_ZIG_AIR")
            stock = compiler("stock-zig", "AIR2LEAN_ZIG")
            air = artifacts / "air"
            air.mkdir()
            export_env = dict(os.environ, ZIG_AIR_JSON_DIR=str(air), ZIG_AIR_JSON_FILTER="weakcas.")
            run("export", [patched, "build-obj", "-fno-emit-bin", "-OReleaseSafe", "-fno-error-tracing",
                           "-target", "x86_64-linux", "-mcpu", "baseline", "--cache-dir", artifacts / "zig-cache",
                           "--global-cache-dir", artifacts / "zig-global-cache", FIXTURES / "weakcas.zig"], env=export_env)
            exported = [json.loads(p.read_text()) for p in sorted(air.glob("*.json"))]
            names = {f["name"] for f in exported}
            required = {"weakcas.weak", "weakcas.strong", "weakcas.weakBool", "weakcas.retry"}
            if names != required:
                raise RuntimeError(f"source AIR root mismatch: {sorted(names ^ required)}")
            report["exported_functions"] = sorted(names)
            generated = artifacts / "WeakCasSource.lean"
            run("translate", ["lake", "exe", "air2lean", air, "-o", generated,
                              "--namespace", "WeakCasSource", "--prefix", "weakcas."])
            source_check = artifacts / "WeakCasSourceCheck.lean"
            source_check.write_text(generated.read_text() + (FIXTURES / "SourceCheck.lean.in").read_text())
            report["source_validation"] = {
                "step": "source-kernel-and-allowed-outcomes",
                "checks": "combined emitted-module kernel elaboration and allowed-outcome execution",
                "failure_scope": "failure may be elaboration or runtime; inspect the retained log"}
            run("source-kernel-and-allowed-outcomes",
                ["lake", "env", "lean", "-R", artifacts, "--run", source_check])
            run("native-finite", [stock, "test", "-OReleaseSafe", "-fno-error-tracing", "-target", "native",
                                  "--cache-dir", artifacts / "stock-cache", "--global-cache-dir", artifacts / "stock-global-cache",
                                  f"-femit-bin={artifacts / 'native-tests'}", FIXTURES / "native.zig"])
            report["native_profile"] = {"target": "native host, separately from x86_64-linux AIR",
                                        "mode": "ReleaseSafe", "iterations": 64, "retry_budget": 3,
                                        "comparison": "allowed source outcomes, not identical failure frequency"}
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        report["artifact_hashes"] = {str(p.relative_to(artifacts)): digest(p)
                                    for p in retained_files(artifacts)}
        save()
        print(f"Weak CAS qualification {report['status']}: {artifacts / 'report.json'}", flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
