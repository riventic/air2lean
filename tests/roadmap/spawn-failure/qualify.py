#!/usr/bin/env python3
"""Sequential raw-artifact qualification for explicit fallible assignment."""
import ctypes
import errno
import hashlib
import json
import os
import re
import runpy
import shutil
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT / "tests/roadmap/spawn-failure"
HEADER = "Thread assignment policy: fallible"
HELPERS = runpy.run_path(str(ROOT / "scripts/normalize-generated.py"))
def fresh_profile(records, version, names):
    if sorted(r["name"] for r in records) != sorted(names) or not records:
        raise ValueError("fresh AIR function inventory differs")
    profiles = []
    for record in records:
        profile = HELPERS["fresh_linux_profile"](record, version)
        profiles.append(profile)
    if any(profile != profiles[0] for profile in profiles):
        raise ValueError("fresh AIR has mixed profiles")
    return profiles[0]


def generated_receipt(generated, air, receipt):
    # Keep full raw bytes and input digests; only the validated first-line record is
    # excluded from semantic-body comparison. These hashes are not an attestation.
    HELPERS["write_report"](generated, air, receipt)
    _, _, metadata = HELPERS["checked_generated"](generated, receipt)
    if metadata["float_semantics"] != "ieee":
        raise ValueError("generated float semantics differs from the default")
    return HELPERS["load_report"](receipt)

def project_integration(gate, destination, air, profile, translator, direct):
    """Exercise ordinary project commands on the same fresh, retained AIR bytes."""
    inputs = destination / "project-inputs"
    inputs.mkdir()
    shutil.copytree(air, inputs / "air")
    files = [FIXTURE / "spawn_failure.zig", FIXTURE / "source-runtime.lean",
             ROOT / "zig-patch/air-json/json.zig", ROOT / "ZigLean/Conc/Spawn.lean",
             ROOT / "ZigLean/Conc/SpawnLemmas.lean", ROOT / "lean-toolchain"]
    if profile["zig_version"] == "0.16.0":
        files.append(FIXTURE / "source-group.lean")
    for path in files:
        shutil.copyfile(path, inputs / path.name)
    # fresh_linux_profile adds the AIR schema for generated-header comparisons;
    # the project profile contains exactly the producer's target-profile fields.
    manifest_profile = {key: value for key, value in profile.items() if key != "schema"}
    (inputs / "profile.json").write_text(json.dumps(manifest_profile, indent=2) + "\n")
    manifest = {"schema": 1, "profile": "profile.json", "float_semantics": "ieee",
                "source_closure": ["spawn_failure.zig"],
                "components": {"compiler_patch": ["json.zig"],
                               "runtime": ["Spawn.lean", "SpawnLemmas.lean"],
                               "toolchain": ["lean-toolchain"]},
                "allowed_assumptions": [],
                "roots": [{"id": "snapshot", "function": "spawn_failure.threadPair",
                           "air": ["air/" + p.name for p in sorted(air.glob("*.json"))],
                           "namespace": "SpawnFailure", "prefix": "spawn_failure.",
                           "contracts": [p.name for p in files if p.name.startswith("source-")],
                           "goals": [],
                           "assumptions": [], "exclusions": [
                               "Declared input inventories do not establish dependency completeness.",
                               "Project receipts do not attest proofs or native correspondence."]}]}
    generated = {}
    for label, policy in (("omitted", None), ("available", "available"), ("fallible", "fallible")):
        effective = policy or "available"
        selected = dict(manifest)
        if policy is not None:
            selected["spawn_policy"] = policy
        path = inputs / (label + ".json")
        path.write_text(json.dumps(selected, indent=2) + "\n")
        prefix = "project-" + label
        command = [sys.executable, str(ROOT / "scripts/project.py")]
        preflight = json.loads(gate.run(prefix + "-report", command + ["report", str(path)]))
        if (preflight["spawn_policy"] != effective or preflight["diagnostics"] or
                any(root["input_validation"]["status"] != "passed" for root in preflight["roots"]) or
                any(stage["status"] != "not_run" for root in preflight["roots"]
                    for stage in root["stages"].values())):
            raise RuntimeError(prefix + ": project preflight inflated or lost policy")
        receipt = destination / (prefix + "-diagnostics.json")
        checks = json.loads(gate.run(prefix + "-diagnostics", [sys.executable,
            str(ROOT / "scripts/project-diagnostics.py"), "check", str(path),
            "--translator", str(translator), "--out", str(receipt)]))
        if (checks != json.loads(receipt.read_text()) or checks["status"] != "checked" or
                checks["evidence"]["spawn_policy"] != effective or
                checks["proof_status"] != "not_run" or checks["runtime_outcomes"] != "not_observed" or
                checks["source_correspondence"] != "not_attested" or
                any(root["status"] != "checked" or
                    root["execution"]["argv"][-2:] != ["--spawn-policy", effective]
                    for root in checks["root_checks"])):
            raise RuntimeError(prefix + ": diagnostic policy or evidence boundary differs")
        artifact = destination / (prefix + "-artifact")
        translated = json.loads(gate.run(prefix + "-translate", command + ["translate", str(path),
            "--translator", str(translator), "--out", str(artifact)]))
        stored = json.loads((artifact / "report.json").read_text())
        argv = stored["roots"][0]["stages"]["translated"]["argv"]
        if (translated != stored or stored["spawn_policy"] != effective or
                argv[-2:] != ["--spawn-policy", effective] or
                stored["roots"][0]["stages"]["proved"]["status"] != "not_run"):
            raise RuntimeError(prefix + ": stored project translation lost policy")
        verified = json.loads(gate.run(prefix + "-verify", command + ["verify", str(path),
            "--artifact", str(artifact)]))
        if verified["status"] != "hashes_match" or verified["proof_status"] != "not_attested":
            raise RuntimeError(prefix + ": receipt verification inflated proof evidence")
        generated[label] = artifact / "snapshot/Gen.lean"
        if generated[label].read_bytes() != direct[effective].read_bytes():
            raise RuntimeError(prefix + ": project emission differs from direct translation")
    # A historical receipt is an available-policy receipt. Removing the policy
    # field cannot make it valid for an actual fallible project.
    artifact = generated["fallible"].parents[1]
    receipt = artifact / "report.json"
    original = receipt.read_bytes()
    legacy = json.loads(original)
    del legacy["spawn_policy"]
    receipt.write_text(json.dumps(legacy, indent=2) + "\n")
    try:
        gate.run("project-fallible-reject-legacy", [sys.executable, str(ROOT / "scripts/project.py"),
            "verify", str(inputs / "fallible.json"), "--artifact", str(artifact)], expected=2,
            marker="artifact spawn_policy differs from manifest")
    finally:
        receipt.write_bytes(original)
    return generated["fallible"]

UNTRUSTED = ("sorry", "admit", "native_decide", "axiom")
PROOFS = ("Group", "Pair")

def checked_air():
    """The retained fresh 0.16.0 AIR of spawn_failure.zig, bound to its source and hashes."""
    air = FIXTURE / "air/0.16.0"
    record = json.loads((FIXTURE / "air/provenance.json").read_text())
    if digest(FIXTURE / "spawn_failure.zig") != record["source_sha256"]:
        raise ValueError("stale checked spawn-failure AIR: source changed; re-export and refresh provenance")
    found = {p.name: digest(p) for p in sorted(air.glob("*.json"))}
    if found != record["air_sha256"]:
        raise ValueError("checked spawn-failure AIR inventory or hashes differ from provenance")
    return air

def checked_proofs(gate, destination, lean, translator):
    """Retranslate the checked AIR, require the checked Gen body, and kernel-check the proofs."""
    air = checked_air()
    work = destination / "proofs"
    (work / "SpawnFailure").mkdir(parents=True)
    generated = work / "SpawnFailure/Gen.lean"
    gate.run("checked-translate", [str(translator), str(air), "-o", str(generated), "--namespace",
             "SpawnFailure", "--prefix", "spawn_failure.", "--spawn-policy", "fallible"])
    receipt = destination / "checked-generated-receipt.json"
    HELPERS["write_report"](generated, air, receipt)
    HELPERS["compare"](FIXTURE / "SpawnFailure/Gen.lean", generated, receipt)
    for name in PROOFS + ("Budget",):
        text = (FIXTURE / "SpawnFailure" / (name + ".lean")).read_text()
        for number, line in enumerate(text.splitlines(), 1):
            if any(re.search(r"\b" + word + r"\b", line) for word in UNTRUSTED):
                raise ValueError(f"SpawnFailure/{name}.lean:{number}: untrusted declaration")
    env = dict(os.environ)
    env["LEAN_PATH"] = str(work) + ((":" + env["LEAN_PATH"]) if env.get("LEAN_PATH") else "")
    gate.run("checked-gen-kernel", lean + ["-R", str(work), "-o", str(work / "SpawnFailure/Gen.olean"),
             str(generated)], env=env, timeout=1800)
    for name in PROOFS:
        gate.run("proof-" + name.lower(), lean + ["-R", str(FIXTURE), "-o",
                 str(work / "SpawnFailure" / (name + ".olean")),
                 str(FIXTURE / "SpawnFailure" / (name + ".lean"))], env=env, timeout=3600)
    gate.run("budget-executions", lean + ["-R", str(FIXTURE), "--run",
             str(FIXTURE / "SpawnFailure/Budget.lean")], env=env, timeout=1800,
             marker="spawn budget executions passed")

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
            if path != destination / "report.json":
                found[str(path.relative_to(destination))] = {"sha256": digest(path), "bytes": path.stat().st_size}
    return dict(sorted(found.items()))

# Python omits waitid on some Darwin builds. Darwin's public siginfo_t prefix
# contains these six 32-bit fields; a larger zeroed buffer holds the native tail.
def peek_status(proc):
    if hasattr(os, "waitid"):
        info = os.waitid(os.P_PID, proc.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
        return None if info is None else info.si_status if info.si_code == os.CLD_EXITED else -info.si_status
    if sys.platform != "darwin":
        raise RuntimeError("nonreaping process observation is unavailable")
    libc = ctypes.CDLL(None, use_errno=True)
    native_waitid = libc.waitid
    native_waitid.argtypes = [ctypes.c_int, ctypes.c_uint32, ctypes.c_void_p, ctypes.c_int]
    native_waitid.restype = ctypes.c_int
    info = ctypes.create_string_buffer(256)
    if native_waitid(1, proc.pid, info, 0x4 | 0x1 | 0x20) != 0:  # P_PID, WEXITED, WNOHANG, WNOWAIT
        error = ctypes.get_errno()
        if error == errno.EINTR:
            return None
        raise OSError(error, os.strerror(error))
    fields = (ctypes.c_int32 * 6).from_buffer(info)
    return None if fields[3] == 0 else fields[5] if fields[2] == 1 else -fields[5]


def darwin_exited_anchor_only(proc):
    # Use only the exported PID-array interface, not private process-info structs.
    # XNU lists both live and zombie group members under the process-list lock.
    if sys.platform != "darwin" or peek_status(proc) is None:
        return False
    library = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
    query = library.proc_listpids
    query.argtypes = [ctypes.c_uint32, ctypes.c_uint32, ctypes.c_void_p, ctypes.c_int]
    query.restype = ctypes.c_int
    pids = (ctypes.c_int32 * 128)()
    ctypes.set_errno(0)
    size = query(2, proc.pid, pids, ctypes.sizeof(pids))  # PROC_PGRP_ONLY
    # Zero can mean a query error; a full buffer can mean silent truncation.
    if ctypes.get_errno() or not 0 < size < ctypes.sizeof(pids) or size % ctypes.sizeof(ctypes.c_int32):
        return False
    return size == ctypes.sizeof(ctypes.c_int32) and pids[0] == proc.pid


def stop_group(proc):
    # No poll/wait/reap before the last group signal: the leader anchors the PGID
    # even after a successful exit while descendants still hold the output pipe.
    deadline = time.monotonic() + 2
    errors = []
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(proc.pid, sig)
        except ProcessLookupError:
            pass
        except OSError as error:
            errors.append(error)
        if sig == signal.SIGTERM:
            time.sleep(0.1)
    if (errors and sys.platform == "darwin" and time.monotonic() < deadline and
            all(error.errno == errno.EPERM for error in errors)):
        try:
            if darwin_exited_anchor_only(proc):
                errors.clear()
        except (OSError, RuntimeError, AttributeError, ValueError):
            pass  # Keep the original signal errors when proof is unavailable.
    try:
        code = proc.wait(timeout=max(0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired as error:
        errors.append(error)
    if errors:
        raise RuntimeError("group cleanup or bounded reap failed") from errors[0]
    return code


class Gate:
    def __init__(self, destination):
        self.destination = destination
        self.steps = []

    def run(self, label, argv, *, env=None, expected=0, marker=None, timeout=180,
            log_limit=16 * (1 << 20)):
        if not 0 < log_limit <= 16 * (1 << 20):
            raise ValueError("log limit must be positive and at most 16 MiB")
        logfile = self.destination / (label + ".log")
        step = {"label": label, "argv": list(map(str, argv)), "expected_exit": expected,
                "status": "pending", "log": logfile.name}
        self.steps.append(step)
        interrupted = [None]
        def interrupt(signum, _frame):
            interrupted[0] = signum
        previous = {sig: signal.signal(sig, interrupt)
                    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
        previous[signal.SIGCHLD] = signal.signal(signal.SIGCHLD, signal.SIG_DFL)
        proc = None
        cleanup_attempted = False
        def cleanup():
            nonlocal cleanup_attempted
            cleanup_attempted = True
            try:
                return stop_group(proc)
            except BaseException as failure:
                step["status"] = "cleanup_failed"
                raise RuntimeError(label + ": process cleanup failed") from failure
        try:
            with logfile.open("wb") as output, selectors.DefaultSelector() as selector:
                proc = subprocess.Popen(step["argv"], cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, start_new_session=True)
                os.set_blocking(proc.stdout.fileno(), False)
                selector.register(proc.stdout, selectors.EVENT_READ)
                deadline = time.monotonic() + timeout
                output_bytes = 0
                output_open = True
                def read_output():
                    nonlocal output_bytes, output_open
                    if not output_open:
                        return "eof"
                    try:
                        chunk = os.read(proc.stdout.fileno(), 65536)
                    except BlockingIOError:
                        return "blocked"
                    if not chunk:
                        selector.unregister(proc.stdout)
                        output_open = False
                        return "eof"
                    output.write(chunk[:max(0, log_limit - output_bytes)])
                    output_bytes += len(chunk)
                    if output_bytes > log_limit:
                        step["status"] = "oversized_log"
                    return "data"
                try:
                    while True:
                        if interrupted[0] is not None:
                            step["status"] = "interrupted"
                            break
                        if time.monotonic() >= deadline:
                            step["status"] = "timeout"
                            break
                        if selector.select(min(0.02, max(0, deadline - time.monotonic()))):
                            read_output()
                        if step["status"] == "oversized_log" or peek_status(proc) is not None:
                            break
                finally:
                    if not cleanup_attempted:
                        code = cleanup()
                    # Only bounded pipe reads follow reaping; no later group signal.
                    for _ in range(16):
                        if read_output() != "data":
                            break
                    else:
                        if read_output() == "data":
                            step["status"] = "output_incomplete"
                if interrupted[0] is not None:
                    step["interrupted_by"] = interrupted[0]
                    if step["status"] == "pending":
                        step["status"] = "interrupted"
                step["output_bytes"] = output_bytes
        finally:
            try:
                if proc is not None and not cleanup_attempted:
                    cleanup()
            finally:
                if proc is not None:
                    proc.stdout.close()
                for sig, handler in previous.items():
                    signal.signal(sig, handler)
        step["exit"] = code
        if step["status"] in ("timeout", "interrupted", "oversized_log", "output_incomplete"):
            raise RuntimeError(label + ": " + step["status"])
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
              "normalizer_sha256": digest(ROOT / "scripts/normalize-generated.py"),
              "project_tools_sha256": {name: digest(ROOT / "scripts" / name) for name in
                  ("project.py", "project-diagnostics.py")},
              "steps": gate.steps, "sources": {str(p.relative_to(ROOT)): digest(p) for p in source_paths()},
              "legacy_references": {str(p.relative_to(ROOT)): digest(p) for p in
                  sorted((ROOT / "tests/roadmap/thread-tuples/air/0.16.0").glob("*.json")) +
                  [ROOT / "tests/roadmap/thread-tuples/ThreadTuples/Gen.lean", ROOT / "tests/roadmap/thread-tuples/provenance.json"]},
              # Recursive: the checked AIR, translation and proofs are evidence too.
              "fixture": {str(p.relative_to(FIXTURE)): digest(p) for p in sorted(FIXTURE.rglob("*"))
                          if p.is_file() and "__pycache__" not in p.parts}}
    try:
        lean = [os.environ["AIR2LEAN_LEAN"]] if os.environ.get("AIR2LEAN_LEAN") else ["lake", "env", "lean"]
        translator = Path(os.environ.get("AIR2LEAN_TRANSLATOR", ROOT / ".lake/build/bin/air2lean")).resolve()
        report["translator_sha256"] = digest(translator)
        lean_binary = Path(lean[0]).resolve() if len(lean) == 1 else Path(
            gate.run("lean-binary", ["lake", "env", "which", "lean"]).strip()).resolve()
        report["lean_sha256"] = digest(lean_binary)
        report["lean_version"] = gate.run("lean-version", lean + ["--version"]).strip()
        report["lean_toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        gate.run("proof-modules", ["lake", "build", "ZigLean", "ZigLean.Conc.SpawnLemmas", "ZigLean.Conc.Csl",
                                   "ZigLean.Conc.Transfer"], timeout=3600)
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
        checked_proofs(gate, destination, lean, translator)
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
            records = [HELPERS["parse_json"](p.read_text()) for p in sorted(air.glob("*.json"))]
            report["fresh_profile"] = fresh_profile(records, version, names)
            default = destination / "Default.lean"
            available = destination / "Available.lean"
            for label, path, policy in [("default-policy", default, []),
                                        ("explicit-available", available, ["--spawn-policy", "available"])]:
                gate.run(label, [str(translator), str(air), "-o", str(path), "--namespace", "SpawnFailure",
                         "--prefix", "spawn_failure."] + policy)
                generated_receipt(path, air, destination / (label + "-receipt.json"))
            if default.read_bytes() != available.read_bytes():
                raise RuntimeError("default and explicit availability policy emission differ")
            gate.run("available-kernel", lean + ["-R", str(destination), str(default)])
            legacy = destination / "TupleDefault.lean"
            # The thread-tuples AIR is a schema-12 export: its own profile, no legacy flag.
            gate.run("legacy-default-bytes", [str(translator), str(ROOT / "tests/roadmap/thread-tuples/air/0.16.0"),
                     "-o", str(legacy), "--namespace", "ThreadTuples", "--prefix", "thread_tuples."])
            legacy_receipt = destination / "legacy-default-receipt.json"
            generated_receipt(legacy, ROOT / "tests/roadmap/thread-tuples/air/0.16.0", legacy_receipt)
            HELPERS["compare"](ROOT / "tests/roadmap/thread-tuples/ThreadTuples/Gen.lean",
                               legacy, legacy_receipt)
            gate.run("legacy-full-header-kernel", lean + ["-R", str(destination), str(legacy)])
            raw = destination / "Gen.lean"
            gate.run("translate", [str(translator), str(air), "-o", str(raw), "--namespace", "SpawnFailure",
                     "--prefix", "spawn_failure.", "--spawn-policy", "fallible"])
            generated_receipt(raw, air, destination / "fallible-generated-receipt.json")
            if version == "0.16.0":
                # The checked proofs are about this body: fresh AIR must still translate to it.
                HELPERS["compare"](FIXTURE / "SpawnFailure/Gen.lean", raw,
                                   destination / "fallible-generated-receipt.json")
            source = raw.read_text()
            required = [HEADER, "Zig.spawnWithPolicyC .fallible"]
            if version == "0.16.0":
                required += ["Zig.groupAsyncWithPolicyC .fallible", "Zig.groupConcurrentWithPolicyC .fallible"]
            if any(token not in source for token in required):
                raise RuntimeError("raw generated fallible policy/effects lost")
            template = (FIXTURE / "source-runtime.lean").read_text()
            if version == "0.16.0":
                template += (FIXTURE / "source-group.lean").read_text()
            project_raw = project_integration(gate, destination, air, report["fresh_profile"],
                                              translator, {"available": available, "fallible": raw})
            combined = destination / "source-allowed-outcomes.lean"
            combined.write_text(project_raw.read_text() + template)
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
    except (RuntimeError, OSError, KeyError, ValueError, TypeError) as exc:
        raise SystemExit(str(exc)) from exc
    print("spawn failure qualification passed")

if __name__ == "__main__":
    main()
