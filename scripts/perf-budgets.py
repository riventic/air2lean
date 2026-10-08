#!/usr/bin/env python3
"""Record, baseline and gate translation/proof performance budgets on real modules.

Subcommands (docs/perf-budgets.md):
  record    run the workload suite serially and write a measurement JSON
  baseline  derive per-phase limits from a measurement into the budgets file
  gate      compare a measurement against the budgets; nonzero on a regression

`record` starts the translator and Lake; run it once under scripts/build-guard.py so
the whole suite holds the shared build lock with LEAN_NUM_THREADS=1. `baseline`
and `gate` only read JSON and never start a process.
"""

import argparse
import copy
import datetime
import hashlib
import json
import os
import platform
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUDGETS = ROOT / "assurance/perf-budgets.json"
BUDGETS_SCHEMA = "air2lean-perf-budgets/1"
MEASUREMENT_SCHEMA = "air2lean-perf-measurement/1"
TIMING_SCHEMA = "air2lean-timing/1"
# Phases reported by `air2lean --timing-json` that carry a budget.
INTERNAL_PHASES = ("parse", "normalize", "check", "emit")
LEAN_PHASES = ("elaborate", "proof.cold", "proof.warm")
EXIT_PENDING = 3


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_json(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream)


def write_json(path, data):
    path = Path(path)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def platform_key():
    return {"system": platform.system(), "machine": platform.machine()}


def phase_class(phase):
    return "lean" if phase in LEAN_PHASES else "translator"


def validate_budgets(data, root=ROOT):
    """Return a list of structural errors in a budgets document."""
    errors = []
    if data.get("schema") != BUDGETS_SCHEMA:
        return [f"budgets schema must be {BUDGETS_SCHEMA}"]
    if data.get("status") not in ("pending", "recorded"):
        errors.append("status must be 'pending' or 'recorded'")
    for name in ("translator", "lean"):
        tolerance = data.get("tolerance", {}).get(name)
        if not isinstance(tolerance, dict) or not all(
                isinstance(tolerance.get(key), (int, float)) and tolerance[key] >= 0 for key in
                ("time_ratio", "time_slack_seconds", "rss_ratio", "rss_slack_kib")):
            errors.append(f"tolerance.{name} needs nonnegative time/rss ratio and slack")
        elif tolerance["time_ratio"] < 1 or tolerance["rss_ratio"] < 1:
            errors.append(f"tolerance.{name} ratios must be at least 1")
    seen = set()
    workloads = data.get("workloads")
    if not isinstance(workloads, list) or not workloads:
        return errors + ["workloads must be a nonempty list"]
    for workload in workloads:
        ident = workload.get("id")
        if not isinstance(ident, str) or not ident or ident in seen:
            errors.append(f"workload id {ident!r} is missing or duplicated")
            continue
        seen.add(ident)
        air = workload.get("air")
        if not isinstance(air, list) or not air:
            errors.append(f"{ident}: air must list golden directories")
        elif not all((root / directory).is_dir() for directory in air):
            errors.append(f"{ident}: missing AIR directory in {air}")
        else:
            try:
                air_set(root, air, workload.get("air_zig_version"))
            except RuntimeError as error:
                errors.append(f"{ident}: {error}")
        for key in ("namespace", "prefix", "air_zig_version"):
            if not isinstance(workload.get(key), str):
                errors.append(f"{ident}: {key} must be a string")
        reference = workload.get("reference_gen", "")
        if reference is not None and not (isinstance(reference, str) and (root / reference).is_file()):
            errors.append(f"{ident}: reference_gen must be null or an existing file")
        if not isinstance(workload.get("translate_args"), list):
            errors.append(f"{ident}: translate_args must be a list")
        for module in workload.get("proof_modules", []):
            if not (root / (module.replace(".", "/") + ".lean")).is_file():
                errors.append(f"{ident}: missing proof module {module}")
        budget = workload.get("budget")
        if budget is None:
            if data.get("status") == "recorded":
                errors.append(f"{ident}: status is 'recorded' but the budget is pending")
            continue
        if not isinstance(budget.get("phases"), dict) or not budget["phases"]:
            errors.append(f"{ident}: budget.phases must be a nonempty object")
        output = budget.get("output", {})
        if not isinstance(output.get("sha256"), str):
            errors.append(f"{ident}: budget.output.sha256 is required")
    if data.get("status") == "recorded" and not data.get("reference_platform"):
        errors.append("a recorded budget needs reference_platform")
    return errors


# ---------------------------------------------------------------------------
# Gate


def gate(budgets, measurement, allow_pending=False, allow_platform_mismatch=False):
    """Compare one measurement with the budgets.

    Returns (exit_code, findings). Each finding is a dict with `kind`, `workload`,
    optional `phase` and a `message`. Every kind except `pending` is a failure.
    """
    findings = []

    def add(kind, workload, message, phase=None):
        item = {"kind": kind, "workload": workload, "message": message}
        if phase is not None:
            item["phase"] = phase
        findings.append(item)

    if measurement.get("schema") != MEASUREMENT_SCHEMA:
        add("invalid-measurement", None, f"measurement schema must be {MEASUREMENT_SCHEMA}")
        return 1, findings
    if measurement.get("lean_num_threads") != "1":
        add("unserialized-measurement", None,
            "measurement was not taken with LEAN_NUM_THREADS=1; record it under build-guard.py")
    reference = budgets.get("reference_platform")
    measured_platform = measurement.get("platform", {})
    if reference and not allow_platform_mismatch and any(
            measured_platform.get(key) != value for key, value in reference.items()):
        add("platform-mismatch", None,
            f"budgets were recorded on {reference}, measurement is from "
            f"{ {key: measured_platform.get(key) for key in reference} }")
    measured = measurement.get("workloads", {})
    budgeted = {workload["id"]: workload for workload in budgets.get("workloads", [])}
    for ident in sorted(set(measured) - set(budgeted)):
        add("unbudgeted-workload", ident, "measured workload has no entry in the budgets file")
    for ident, workload in budgeted.items():
        result = measured.get(ident)
        if result is None:
            add("missing-workload", ident, "budgeted workload is absent from the measurement")
            continue
        if result.get("status") != "ok":
            add("failed-workload", ident, f"workload failed: {result.get('error', 'unknown error')}")
            continue
        budget = workload.get("budget")
        if budget is None:
            add("pending", ident, "no baseline recorded; budget pending")
            continue
        expected = budget.get("output", {})
        actual = result.get("output", {})
        if expected.get("sha256") != actual.get("sha256"):
            add("output-changed", ident,
                f"emitted Lean changed ({expected.get('sha256', '?')[:12]} -> "
                f"{str(actual.get('sha256', '?'))[:12]}); definitions are not preserved. "
                "Rebaseline only with preservation evidence (docs/perf-budgets.md).")
        phases = result.get("phases", {})
        for phase, limits in sorted(budget.get("phases", {}).items()):
            got = phases.get(phase)
            if got is None:
                add("missing-phase", ident, "budgeted phase is absent from the measurement", phase)
                continue
            if "max_seconds" in limits:
                seconds = got.get("seconds")
                if not isinstance(seconds, (int, float)):
                    add("missing-phase", ident, "phase has no wall time", phase)
                elif seconds > limits["max_seconds"]:
                    add("time-regression", ident,
                        f"{seconds:.3f}s exceeds budget {limits['max_seconds']:.3f}s "
                        f"(baseline {limits.get('baseline_seconds', 0):.3f}s)", phase)
            if "max_peak_rss_kib" in limits:
                rss = got.get("peak_rss_kib")
                if not isinstance(rss, int):
                    add("missing-phase", ident, "phase has no peak RSS", phase)
                elif rss > limits["max_peak_rss_kib"]:
                    add("memory-regression", ident,
                        f"peak RSS {rss} KiB exceeds budget {limits['max_peak_rss_kib']} KiB "
                        f"(baseline {limits.get('baseline_peak_rss_kib', 0)} KiB)", phase)
    failures = [item for item in findings if item["kind"] != "pending"]
    if failures:
        return 1, findings
    if any(item["kind"] == "pending" for item in findings) and not allow_pending:
        return EXIT_PENDING, findings
    return 0, findings


# ---------------------------------------------------------------------------
# Baseline


def required_phases(workload):
    """Phases a full `record` run measures for one workload."""
    phases = ["translate.cold", "translate.warm", *INTERNAL_PHASES, "elaborate"]
    if workload.get("proof_modules"):
        phases += ["proof.cold", "proof.warm"]
    return phases


def limit(value, ratio, slack):
    return max(value * ratio, value + slack)


def derive(budgets, measurement, only=None, allow_dirty=False):
    """Return new budgets with limits derived from a successful measurement."""
    problems = []
    if measurement.get("schema") != MEASUREMENT_SCHEMA:
        problems.append(f"measurement schema must be {MEASUREMENT_SCHEMA}")
    if measurement.get("lean_num_threads") != "1":
        problems.append("baseline requires a LEAN_NUM_THREADS=1 measurement")
    revision = measurement.get("revision", {})
    if not allow_dirty and (revision.get("tracked_dirty") or "head" not in revision):
        problems.append("baseline requires a clean tracked tree (or --allow-dirty)")
    reference = budgets.get("reference_platform")
    if reference and reference != measurement.get("platform", {}) and only:
        problems.append("a partial rebaseline must use the reference platform")
    if problems:
        raise ValueError("; ".join(problems))
    updated = copy.deepcopy(budgets)
    selected = set(only) if only else {workload["id"] for workload in updated["workloads"]}
    unknown = selected - {workload["id"] for workload in updated["workloads"]}
    if unknown:
        raise ValueError(f"unknown workloads: {', '.join(sorted(unknown))}")
    recorded = {"revision": revision.get("head"), "recorded_at": measurement.get("recorded_at"),
                "translator_sha256": measurement.get("translator", {}).get("sha256")}
    for workload in updated["workloads"]:
        if workload["id"] not in selected:
            continue
        result = measurement.get("workloads", {}).get(workload["id"])
        if not result or result.get("status") != "ok":
            raise ValueError(f"{workload['id']}: no successful measurement to baseline")
        if result.get("output", {}).get("matches_reference") is False:
            raise ValueError(f"{workload['id']}: emitted definitions differ from "
                             f"{workload.get('reference_gen')}; refusing to baseline them")
        missing = sorted(set(required_phases(workload)) - set(result["phases"]))
        if missing:
            raise ValueError(f"{workload['id']}: measurement lacks phases {', '.join(missing)} "
                             "(recorded with --skip-elaborate/--skip-proof?)")
        phases = {}
        for phase, got in sorted(result["phases"].items()):
            tolerance = budgets["tolerance"][phase_class(phase)]
            entry = {}
            if isinstance(got.get("seconds"), (int, float)):
                entry["baseline_seconds"] = got["seconds"]
                entry["max_seconds"] = round(limit(got["seconds"], tolerance["time_ratio"],
                                                   tolerance["time_slack_seconds"]), 3)
            if isinstance(got.get("peak_rss_kib"), int):
                entry["baseline_peak_rss_kib"] = got["peak_rss_kib"]
                entry["max_peak_rss_kib"] = int(limit(got["peak_rss_kib"], tolerance["rss_ratio"],
                                                      tolerance["rss_slack_kib"]))
            if entry:
                phases[phase] = entry
        workload["budget"] = {"recorded": recorded, "output": result["output"], "phases": phases}
    updated["reference_platform"] = measurement.get("platform")
    if all(workload.get("budget") for workload in updated["workloads"]):
        updated["status"] = "recorded"
        updated.pop("note", None)
    return updated


# ---------------------------------------------------------------------------
# Record


def air_identity(path):
    """Version/schema/profile fields that the translator requires to agree across files."""
    try:
        doc = load_json(path)
    except (OSError, ValueError) as error:
        raise RuntimeError(f"unreadable AIR {path.name}: {error}") from error
    if not isinstance(doc, dict):
        raise RuntimeError(f"AIR {path.name} is not a JSON object")
    return (doc.get("zig_version"), doc.get("schema"),
            json.dumps(doc.get("profile"), sort_keys=True))


def air_set(root, directories, expected_version=None):
    """Overlay AIR directories in order (later names replace earlier ones).

    Golden directories are comparison artifacts (scripts/check.sh compares fresh dumps
    against them after normalization), so a shared folder plus a version overlay can
    mix Zig versions or profiles. Only a uniform set is a valid translation input.
    Returns {file name: source path}.
    """
    files = {}
    for directory in directories:
        for path in sorted((root / directory).glob("*.json")):
            files[path.name] = path
    if not files:
        raise RuntimeError(f"no AIR JSON in {directories}")
    identities = {}
    for name, path in sorted(files.items()):
        identities.setdefault(air_identity(path), []).append(name)
    if len(identities) != 1:
        summary = "; ".join(f"zig {version} schema {schema}: {len(names)} files (e.g. {names[0]})"
                            for (version, schema, _), names in identities.items())
        raise RuntimeError(f"mixed AIR versions/profiles in {directories}: {summary}")
    version = next(iter(identities))[0]
    if expected_version is not None and version != expected_version:
        raise RuntimeError(f"AIR in {directories} is Zig {version}, expected {expected_version}")
    return files


def stage_air(root, directories, destination, expected_version=None):
    """Copy one uniform AIR set (`air_set`) into `destination`."""
    files = air_set(root, directories, expected_version)
    destination.mkdir(parents=True, exist_ok=True)
    for name, path in files.items():
        shutil.copyfile(path, destination / name)
    return destination


def lean_body(data):
    """Generated Lean without its first-line profile record (scripts/normalize-generated.py)."""
    first, newline, body = data.partition(b"\n")
    return body if newline and first.startswith(b"-- air2lean-profile: ") else data


def matches_reference(generated, reference):
    """Definitions equal to the reference translation, ignoring only the profile record."""
    if reference is None:
        return None
    path = ROOT / reference
    return path.is_file() and lean_body(generated.read_bytes()) == lean_body(path.read_bytes())


def maxrss_kib(usage):
    # ru_maxrss is bytes on macOS and KiB on Linux.
    return usage.ru_maxrss // 1024 if sys.platform == "darwin" else usage.ru_maxrss


def measure(command, cwd, log, timeout, env=None):
    """Run one step to completion; wall seconds and the kernel peak RSS (KiB).

    `wait4` reports the largest single-process high-water mark among the step and its
    reaped descendants, not a sum across processes.
    """
    with open(log, "ab") as stream:
        stream.write(("$ " + " ".join(map(str, command)) + "\n").encode())
        stream.flush()
        start = time.monotonic()
        child = subprocess.Popen([str(part) for part in command], cwd=cwd, env=env,
                                 stdin=subprocess.DEVNULL, stdout=stream, stderr=stream,
                                 start_new_session=True)
        expired = threading.Event()

        def expire():
            expired.set()
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        timer = threading.Timer(timeout, expire)
        timer.start()
        try:
            _, status, usage = os.wait4(child.pid, 0)
        finally:
            timer.cancel()
        child.returncode = os.waitstatus_to_exitcode(status)
        seconds = time.monotonic() - start
    return {"seconds": round(seconds, 4), "peak_rss_kib": maxrss_kib(usage),
            "exit_code": child.returncode, "timed_out": expired.is_set()}


def require_success(step, what):
    if step["timed_out"]:
        raise RuntimeError(f"{what} timed out")
    if step["exit_code"] != 0:
        raise RuntimeError(f"{what} exited {step['exit_code']}")


def wall_and_rss(step):
    return {"seconds": step["seconds"], "peak_rss_kib": step["peak_rss_kib"]}


def remove_module_artifacts(root, modules):
    """Delete build outputs of the given modules only (module-local cold build)."""
    removed = 0
    for module in modules:
        parts = module.split(".")
        for base in (root / ".lake/build/lib/lean", root / ".lake/build/ir"):
            directory = base.joinpath(*parts[:-1])
            if not directory.is_dir():
                continue
            for path in directory.iterdir():
                if path.is_file() and path.name.startswith(parts[-1] + "."):
                    path.unlink()
                    removed += 1
    return removed


def run_workload(workload, args, work, log):
    ident = workload["id"]
    phases = {}
    staged = stage_air(ROOT, workload["air"], work / ident / "air", workload["air_zig_version"])
    command_base = [args.air2lean, staged, "--namespace", workload["namespace"],
                    "--prefix", workload["prefix"], *workload["translate_args"]]
    outputs = []
    runs = []
    for attempt in range(args.repeat + 1):
        output = work / ident / f"Gen-{attempt}.lean"
        timing = work / ident / f"timing-{attempt}.json"
        step = measure([*command_base, "-o", output, "--timing-json", timing], ROOT, log, args.timeout)
        require_success(step, f"translator (attempt {attempt})")
        report = load_json(timing)
        if report.get("schema") != TIMING_SCHEMA:
            raise RuntimeError("translator timing report has an unexpected schema")
        outputs.append(output)
        runs.append((step, report))
    hashes = {digest(path) for path in outputs}
    if len(hashes) != 1:
        raise RuntimeError("translator output differs between repeated runs")
    cold, warm = runs[0], runs[1:]
    phases["translate.cold"] = wall_and_rss(cold[0])
    phases["translate.warm"] = {
        "seconds": round(statistics.median(step["seconds"] for step, _ in warm), 4),
        "peak_rss_kib": max(step["peak_rss_kib"] for step, _ in warm)}
    for phase in INTERNAL_PHASES:
        phases[phase] = {"seconds": round(statistics.median(
            report["phases_ns"][phase] for _, report in warm) / 1e9, 6)}
    generated = outputs[0]
    output = {"bytes": generated.stat().st_size, "sha256": digest(generated),
              "matches_reference": matches_reference(generated, workload.get("reference_gen")),
              "functions": runs[0][1].get("functions"), "input_bytes": runs[0][1].get("input_bytes")}
    if not args.skip_elaborate:
        step = measure([args.lake, "env", "lean", generated], ROOT, log, args.timeout)
        require_success(step, "elaboration of the generated Lean")
        phases["elaborate"] = wall_and_rss(step)
    modules = workload.get("proof_modules", [])
    if modules and not args.skip_proof:
        removed = remove_module_artifacts(ROOT, modules)
        for cache in ("cold", "warm"):
            step = measure([args.lake, "build", *modules], ROOT, log, args.timeout)
            require_success(step, f"proof build ({cache})")
            phases[f"proof.{cache}"] = wall_and_rss(step)
        phases["proof.cold"]["artifacts_removed"] = removed
        if args.per_module:
            result_modules = {}
            for module in modules:
                remove_module_artifacts(ROOT, [module])
                step = measure([args.lake, "build", module], ROOT, log, args.timeout)
                require_success(step, f"cold build of {module}")
                result_modules[module] = wall_and_rss(step)
            return {"status": "ok", "phases": phases, "output": output, "modules": result_modules}
    return {"status": "ok", "phases": phases, "output": output}


def git(*args):
    try:
        return subprocess.run(["git", "-C", str(ROOT), *args], stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, text=True, timeout=10,
                              check=True).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return None


def record(args):
    budgets = load_json(args.budgets)
    errors = validate_budgets(budgets)
    if errors:
        raise SystemExit("invalid budgets:\n  " + "\n  ".join(errors))
    if os.environ.get("LEAN_NUM_THREADS") != "1" and not args.allow_unserialized:
        raise SystemExit("record must run under scripts/build-guard.py (LEAN_NUM_THREADS=1); "
                         "see docs/perf-budgets.md")
    selected = [workload for workload in budgets["workloads"]
                if not args.workload or workload["id"] in args.workload]
    missing = set(args.workload or ()) - {workload["id"] for workload in selected}
    if missing:
        raise SystemExit(f"unknown workloads: {', '.join(sorted(missing))}")
    work = Path(tempfile.mkdtemp(prefix="air2lean-perf-"))
    log = Path(args.log) if args.log else work / "record.log"
    head = git("rev-parse", "HEAD")
    dirty = git("status", "--porcelain", "--untracked-files=no")
    measurement = {
        "schema": MEASUREMENT_SCHEMA,
        "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "platform": platform_key(), "host": platform.node(),
        "revision": {"head": head, "tracked_dirty": bool(dirty)} if head else {"unavailable": True},
        "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
        "budgets_sha256": digest(args.budgets), "repeat": args.repeat,
        "workloads": {}}
    try:
        if not args.no_build:
            step = measure([args.lake, "build", "ZigLean", "air2lean"], ROOT, log, args.timeout)
            measurement["setup_build"] = step
            if step["exit_code"] != 0:
                raise SystemExit(f"setup build failed (exit {step['exit_code']}); log: {log}")
        translator = Path(args.air2lean)
        measurement["translator"] = {"path": str(translator),
                                     "sha256": digest(translator) if translator.is_file() else None}
        for workload in selected:
            print(f"== {workload['id']} ==", file=sys.stderr, flush=True)
            try:
                result = run_workload(workload, args, work, log)
            except (RuntimeError, OSError, KeyError, ValueError) as error:
                result = {"status": "failed", "error": str(error)}
            measurement["workloads"][workload["id"]] = result
        write_json(args.out, measurement)
    finally:
        if args.keep:
            print(f"kept work directory {work}", file=sys.stderr)
        else:
            if args.log is None and log.exists():
                shutil.copyfile(log, Path(args.out).with_suffix(".log"))
            shutil.rmtree(work, ignore_errors=True)
    failed = [ident for ident, result in measurement["workloads"].items() if result["status"] != "ok"]
    for ident in failed:
        print(f"error: {ident}: {measurement['workloads'][ident]['error']}", file=sys.stderr)
    return 1 if failed else 0


def print_findings(code, findings):
    for item in findings:
        where = item["workload"] or "*"
        if item.get("phase"):
            where += f" [{item['phase']}]"
        print(f"{item['kind']}: {where}: {item['message']}")
    verdict = {0: "pass", 1: "FAIL", EXIT_PENDING: "pending (no recorded baseline)"}[code]
    print(f"perf-budgets gate: {verdict}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("record", help="measure the workload suite (heavy; run serially)")
    rec.add_argument("--out", type=Path, required=True)
    rec.add_argument("--budgets", type=Path, default=BUDGETS)
    rec.add_argument("--workload", action="append")
    rec.add_argument("--repeat", type=int, default=3, help="warm translator runs (median)")
    rec.add_argument("--timeout", type=float, default=1800, help="per step, seconds")
    rec.add_argument("--air2lean", default=str(ROOT / ".lake/build/bin/air2lean"))
    rec.add_argument("--lake", default="lake")
    rec.add_argument("--log", type=Path)
    rec.add_argument("--no-build", action="store_true")
    rec.add_argument("--skip-elaborate", action="store_true")
    rec.add_argument("--skip-proof", action="store_true")
    rec.add_argument("--per-module", action="store_true",
                     help="also time each proof module's module-local cold build (informational)")
    rec.add_argument("--keep", action="store_true")
    rec.add_argument("--allow-unserialized", action="store_true", help=argparse.SUPPRESS)
    base = sub.add_parser("baseline", help="write limits derived from a measurement")
    base.add_argument("--measurement", type=Path, required=True)
    base.add_argument("--budgets", type=Path, default=BUDGETS)
    base.add_argument("--workload", action="append")
    base.add_argument("--allow-dirty", action="store_true")
    gat = sub.add_parser("gate", help="compare a measurement with the budgets")
    gat.add_argument("--measurement", type=Path, required=True)
    gat.add_argument("--budgets", type=Path, default=BUDGETS)
    gat.add_argument("--allow-pending", action="store_true")
    gat.add_argument("--allow-platform-mismatch", action="store_true")
    gat.add_argument("--json", type=Path, help="also write findings as JSON")
    val = sub.add_parser("validate", help="check the budgets file structure")
    val.add_argument("--budgets", type=Path, default=BUDGETS)
    args = parser.parse_args(argv)
    if args.command == "record":
        if args.repeat < 1:
            parser.error("--repeat must be at least 1")
        return record(args)
    budgets = load_json(args.budgets)
    errors = validate_budgets(budgets)
    if errors:
        print("invalid budgets:\n  " + "\n  ".join(errors), file=sys.stderr)
        return 1
    if args.command == "validate":
        pending = sum(workload.get("budget") is None for workload in budgets["workloads"])
        print(f"{len(budgets['workloads'])} workloads, {pending} pending; status {budgets['status']}")
        return 0
    measurement = load_json(args.measurement)
    if args.command == "baseline":
        try:
            updated = derive(budgets, measurement, args.workload, args.allow_dirty)
        except ValueError as error:
            print(f"error: {error}", file=sys.stderr)
            return 1
        write_json(args.budgets, updated)
        print(f"wrote {args.budgets} (status {updated['status']})")
        return 0
    code, findings = gate(budgets, measurement, args.allow_pending, args.allow_platform_mismatch)
    if args.json:
        write_json(args.json, {"exit_code": code, "findings": findings})
    print_findings(code, findings)
    return code


if __name__ == "__main__":
    sys.exit(main())
