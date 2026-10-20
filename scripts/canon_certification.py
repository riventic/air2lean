"""Check native debug-ID bindings and audit the generic semantics theorem separately.

gen-integrity supplies every actual translation. Its compact native reports remain
TRU-02 evidence: they are never per-case kernel proofs. The generic CanonSem theorem
is checked once through the existing fresh Assurance replay, without a success cache.
"""
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
PARSE_JSON = runpy.run_path(str(Path(__file__).with_name("normalize-generated.py")))["parse_json"]
MODULE = "Air2Lean.CanonSem"
GENERIC_ROOTS = frozenset(f"Air2Lean.DebugIds.{name}" for name in (
    "execFunc_mapDebugArray", "erase_mapDebugArray", "execFunc_of_body_erase_eq", "execFunc_erase"))


def native_binding(data):
    """Validate the exact native protocol, without promoting it to kernel evidence."""
    if not isinstance(data, bytes):
        raise ValueError("native binding must be UTF-8 JSON bytes")
    try:
        report = PARSE_JSON(data.decode("utf-8"))
    except (UnicodeError, ValueError) as error:
        raise ValueError(f"invalid native binding JSON: {error}") from error
    if (not isinstance(report, dict) or set(report) != {"kind", "version", "functions", "changed"}
            or report["kind"] != "canon-debug-native-binding"
            or type(report["version"]) is not int or report["version"] != 1
            or type(report["functions"]) is not int or report["functions"] < 0
            or type(report["changed"]) is not bool):
        raise ValueError("invalid native binding schema or unsupported version")
    return report


def generic_artifact():
    path = ROOT / ".lake/build/lib/lean/Air2Lean/CanonSem.olean"
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return dict(olean=str(path.resolve()), olean_sha256=digest)


def check_audit(report, artifact):
    """Require the actual generic roots and their freshly replayed CanonSem artifact."""
    replay = report.get("kernel_replay", {})
    freshness = report.get("freshness", {})
    if (report.get("status") != "pass" or report.get("violations") != []
            or report.get("modules") != [MODULE] or replay.get("status") != "pass"
            or replay.get("rejected") != [] or replay.get("reused") != []
            or freshness.get("lake_trace_check", {}).get("status") != "up-to-date"):
        raise ValueError("generic canonicalization audit did not freshly accept its complete scope")
    theorems = report.get("theorems", [])
    if any(theorem.get("allowed") is not True or theorem.get("module") != MODULE for theorem in theorems):
        raise ValueError("generic canonicalization audit contains a rejected or out-of-scope theorem")
    for name in sorted(GENERIC_ROOTS):
        roots = [theorem for theorem in theorems if theorem.get("name") == name]
        nodes = [node for node in report.get("nodes", []) if node.get("name") == name]
        if (len(roots) != 1 or roots[0].get("module") != MODULE
                or len(nodes) != 1 or nodes[0].get("module") != MODULE
                or nodes[0].get("kind") != "theorem"):
            raise ValueError(f"missing actual generic canonicalization root: {name}")
    artifacts = [row for row in freshness.get("artifacts", []) if row.get("module") == MODULE]
    if len(artifacts) != 1:
        raise ValueError("generic canonicalization replay did not bind its actual artifact")
    recorded = Path(artifacts[0].get("olean", ""))
    if not recorded.is_absolute():
        recorded = ROOT / recorded
    if (recorded.resolve() != Path(artifact["olean"])
            or artifacts[0].get("olean_sha256") != artifact["olean_sha256"]):
        raise ValueError("generic canonicalization replay did not bind its actual artifact")


def audit_certificates(work):
    artifact = generic_artifact()
    environment = dict(os.environ)
    environment["AIR2LEAN_REPLAY_JOBS"] = environment.get("AIR2LEAN_JOBS", "1")
    path = work / "audit.json"
    arguments = [str(ROOT / "scripts/assumptions.sh"), "--no-build", "--module", MODULE,
                 "--output", str(path)]
    start = time.monotonic()
    # No --replay-cache: the generic artifact and its non-toolchain closure replay now.
    result = subprocess.run(arguments, cwd=ROOT, env=environment, capture_output=True,
                            text=True, timeout=7200)
    if result.returncode != 0:
        raise ValueError("generic canonicalization Assurance audit failed\n" + result.stdout + result.stderr)
    check_audit(json.loads(path.read_text()), artifact)
    if generic_artifact() != artifact:
        raise ValueError("generic canonicalization artifact changed during its audit")
    print(f"canonicalization: generic CanonSem fresh Assurance audit/replay "
          f"{time.monotonic() - start:.3f}s", flush=True)


def certify_case(translator, index, case):
    difference = translator.matches(index, case, case.path)
    if difference is not None:
        raise ValueError(f"{case.label}: generated module changed ({difference})")
    try:
        report = native_binding(translator.certificate(index, case))
    except ValueError as error:
        raise ValueError(f"{case.label}: {error}") from error
    (translator.work / f"NativeBinding{index}.json").write_text(json.dumps(report, sort_keys=True) + "\n")
    print(f"{case.label}: TRU-02 native binding checked ({report['functions']} functions)", flush=True)
    return report


def certify(translator, indexed_cases):
    """Cases are independent (each index owns its work files), so they run on AIR2LEAN_JOBS
    workers. The generic audit still starts only after every case has passed."""
    from concurrent.futures import ThreadPoolExecutor  # Lazy import, like assumptions.py.
    import threading
    failed = threading.Event()  # Fail fast: no case starts after one has failed.

    def run_case(item):
        if failed.is_set():
            return None
        try:
            return certify_case(translator, *item)
        except BaseException:
            failed.set()
            raise

    jobs = max(1, int(os.environ.get("AIR2LEAN_JOBS") or 1))
    with ThreadPoolExecutor(jobs) as pool:
        reports = list(pool.map(run_case, indexed_cases))
    cases = len(reports)
    functions = sum(report["functions"] for report in reports)
    changed = any(report["changed"] and report["functions"] > 0 for report in reports)
    if not cases:
        raise ValueError("no translation cases selected for canonicalization certification")
    if not functions:
        raise ValueError("selected cases did not contain any actual function")
    if not changed:
        raise ValueError("selected cases did not change any actual debug definition ID")
    audit_certificates(translator.work)
    print(f"canonicalization: {cases} TRU-02 native bindings, {functions} functions; "
          "generic CanonSem kernel replay checked separately", flush=True)
