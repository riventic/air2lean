"""Check native debug-ID bindings and audit the generic semantics theorems separately.

gen-integrity supplies every actual translation. Its compact native reports remain
TRU-02 evidence: they are never per-case kernel proofs. The generic Canon theorems
(`CanonSem`: debug-definition IDs; `Renumber`: instruction-ID renaming) are checked once
through the existing fresh Assurance replay, without a success cache.
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
# Each generic module with the theorem roots the certificates rely on.
GENERIC_ROOTS = {
    "Air2Lean.CanonSem": frozenset(f"Air2Lean.DebugIds.{name}" for name in (
        "execFunc_mapDebugArray", "erase_mapDebugArray", "execFunc_of_body_erase_eq", "execFunc_erase")),
    "Air2Lean.Renumber": frozenset(f"Air2Lean.Renumber.{name}" for name in (
        "execFunc_rename", "run_cellFree", "runOn_cellFree", "zipRen_inj",
        "execFunc_rename_run", "execFunc_rename_runOn")),
    # The whole-program lift of a body rewrite, shared by both (`SemRewrite`), and its
    # instance for `renumber` (`RenumberProgram`).
    "Air2Lean.SemRewrite": frozenset(f"Air2Lean.Sem.{name}" for name in (
        "execFunc_prog", "tickPolicy_map", "run_map", "runOn_map")),
    "Air2Lean.RenumberProgram": frozenset(f"Air2Lean.Renumber.{name}" for name in (
        "tickPolicy_renumber", "run_renumber", "runOn_renumber")),
}
MODULES = tuple(GENERIC_ROOTS)


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


def generic_artifact(module):
    path = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return dict(olean=str(path.resolve()), olean_sha256=digest)


def generic_artifacts():
    return {module: generic_artifact(module) for module in MODULES}


def check_audit(report, artifacts):
    """Require the actual generic roots and the freshly replayed artifact of every generic module."""
    replay = report.get("kernel_replay", {})
    freshness = report.get("freshness", {})
    if (report.get("status") != "pass" or report.get("violations") != []
            or report.get("modules") != list(MODULES) or replay.get("status") != "pass"
            or replay.get("rejected") != [] or replay.get("reused") != []
            or freshness.get("lake_trace_check", {}).get("status") != "up-to-date"):
        raise ValueError("generic canonicalization audit did not freshly accept its complete scope")
    theorems = report.get("theorems", [])
    if any(theorem.get("allowed") is not True or theorem.get("module") not in GENERIC_ROOTS
           for theorem in theorems):
        raise ValueError("generic canonicalization audit contains a rejected or out-of-scope theorem")
    for module, names in GENERIC_ROOTS.items():
        for name in sorted(names):
            roots = [theorem for theorem in theorems if theorem.get("name") == name]
            nodes = [node for node in report.get("nodes", []) if node.get("name") == name]
            if (len(roots) != 1 or roots[0].get("module") != module
                    or len(nodes) != 1 or nodes[0].get("module") != module
                    or nodes[0].get("kind") != "theorem"):
                raise ValueError(f"missing actual generic canonicalization root: {name}")
    for module in MODULES:
        rows = [row for row in freshness.get("artifacts", []) if row.get("module") == module]
        if len(rows) != 1:
            raise ValueError("generic canonicalization replay did not bind its actual artifact")
        recorded = Path(rows[0].get("olean", ""))
        if not recorded.is_absolute():
            recorded = ROOT / recorded
        if (recorded.resolve() != Path(artifacts[module]["olean"])
                or rows[0].get("olean_sha256") != artifacts[module]["olean_sha256"]):
            raise ValueError("generic canonicalization replay did not bind its actual artifact")


def audit_certificates(work):
    artifacts = generic_artifacts()
    environment = dict(os.environ)
    environment["AIR2LEAN_REPLAY_JOBS"] = environment.get("AIR2LEAN_JOBS", "1")
    path = work / "audit.json"
    arguments = [str(ROOT / "scripts/assumptions.sh"), "--no-build",
                 *(argument for module in MODULES for argument in ("--module", module)),
                 "--output", str(path)]
    start = time.monotonic()
    # No --replay-cache: the generic artifacts and their non-toolchain closure replay now.
    result = subprocess.run(arguments, cwd=ROOT, env=environment, capture_output=True,
                            text=True, timeout=7200)
    if result.returncode != 0:
        raise ValueError("generic canonicalization Assurance audit failed\n" + result.stdout + result.stderr)
    check_audit(json.loads(path.read_text()), artifacts)
    if generic_artifacts() != artifacts:
        raise ValueError("generic canonicalization artifact changed during its audit")
    print(f"canonicalization: generic CanonSem/Renumber fresh Assurance audit/replay "
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
          "generic CanonSem/Renumber kernel replay checked separately", flush=True)
