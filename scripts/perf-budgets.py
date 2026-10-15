#!/usr/bin/env python3
"""Record, baseline and gate translation/proof performance budgets on real modules.

Subcommands (docs/perf-budgets.md):
  record    run the workload suite serially and write a measurement JSON
  baseline  derive per-phase limits from a measurement into the budgets file
  gate      compare a measurement against the budgets; nonzero on a regression
            (--portable: any platform, translator and elaboration; --normalized: also proofs)
  heartbeats check|record FILE…|show
            the heartbeat budgets of proofs that raise `maxHeartbeats` (the budgets file's
            `heartbeats` section): `check` (static, preflight) that every raise of a gated file is
            exactly its recorded budget; `record` elaborates a measuring copy of each file (run it
            under scripts/build-guard.py) and rewrites its entries; `show` lists them, worst first

`record` starts the translator and Lake; run it once under scripts/build-guard.py so
the whole suite holds the shared build lock with LEAN_NUM_THREADS=1. `baseline`
and `gate` only read JSON and never start a process.
"""

import argparse
import copy
import datetime
import hashlib
import json
import math
import os
import platform
import re
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
# Phases a portable (any-platform) gate checks by default: everything that needs no cold Lake build.
PORTABLE_PHASES = ("translate.cold", "translate.warm", *INTERNAL_PHASES, "elaborate")
# The calibration workload (pure Lean, no imports) and the phases a normalized gate compares as
# multiples of it: Lean time, unlike translator time, differs between machines by far more than
# any fixed slack can absorb, and proofs take minutes.
CALIBRATION = "tests/roadmap/perf-budgets/Calibration.lean"
CALIBRATION_RUNS = 3
NORMALIZED_PHASES = LEAN_PHASES
HOTSPOT_SECONDS = 2.0


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
    for name in ("translator", "lean"):
        portable = data.get("portable_tolerance", {}).get(name)
        if not isinstance(portable, dict) or not all(
                isinstance(portable.get(key), (int, float)) and portable[key] >= 0 for key in
                ("time_ratio", "time_slack_seconds", "rss_ratio", "rss_slack_kib")):
            errors.append(f"portable_tolerance.{name} needs nonnegative time/rss ratio and slack")
        elif portable["time_ratio"] < 1 or portable["rss_ratio"] < 1:
            errors.append(f"portable_tolerance.{name} ratios must be at least 1")
        elif isinstance(data.get("tolerance", {}).get(name), dict) and any(
                portable[key] < data["tolerance"][name].get(key, 0) for key in portable):
            errors.append(f"portable_tolerance.{name} must be at least as loose as tolerance.{name}")
    calibration = data.get("calibration")
    if calibration is not None:
        normalized = data.get("normalized_tolerance", {}).get("lean")
        if not isinstance(normalized, dict) or not all(
                isinstance(normalized.get(key), (int, float)) and normalized[key] >= 0 for key in
                ("time_ratio", "time_slack_units", "module_slack_units")) or normalized.get("time_ratio", 0) < 1:
            errors.append("normalized_tolerance.lean needs time_ratio >= 1 and nonnegative time_slack_units "
                          "and module_slack_units")
        if not (isinstance(calibration, dict) and calibration.get("file") == CALIBRATION
                and isinstance(calibration.get("sha256"), str)
                and isinstance(calibration.get("baseline_seconds"), (int, float)) and calibration["baseline_seconds"] > 0):
            errors.append(f"calibration needs file {CALIBRATION}, its sha256 and a positive baseline_seconds")
        elif (root / CALIBRATION).is_file() and digest(root / CALIBRATION) != calibration["sha256"]:
            errors.append("calibration file changed since the baseline was recorded; rebaseline")
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
        for phase, limits in sorted(budget["phases"].items()) if isinstance(budget.get("phases"), dict) else ():
            for key in ("max_seconds", "max_peak_rss_kib"):
                if key in limits and "portable_" + key not in limits:
                    errors.append(f"{ident}: phase {phase} has {key} but no portable_{key}; "
                                  "rebaseline it so the portable gate cannot skip it")
            if calibration is not None and phase in NORMALIZED_PHASES and "max_ratio" not in limits:
                errors.append(f"{ident}: phase {phase} has no max_ratio although the budgets are calibrated; "
                              "rebaseline it so the normalized gate cannot skip it")
        modules = budget.get("modules")
        for module, limits in sorted(modules.items()) if isinstance(modules, dict) else ():
            if module not in workload.get("proof_modules", []) or not isinstance(limits.get("max_ratio"), (int, float)):
                errors.append(f"{ident}: module budget {module} must name a proof module and carry max_ratio")
        output = budget.get("output", {})
        if not isinstance(output.get("sha256"), str):
            errors.append(f"{ident}: budget.output.sha256 is required")
    if data.get("status") == "recorded" and not data.get("reference_platform"):
        errors.append("a recorded budget needs reference_platform")
    return errors


# ---------------------------------------------------------------------------
# Gate


def gate(budgets, measurement, allow_pending=False, allow_platform_mismatch=False,
         portable=False, only_phases=None, normalized=False, only_workloads=None):
    """Compare one measurement with the budgets.

    `portable` checks the generous `portable_*` limits instead of the reference-platform
    ones, on any platform (CI runners), over `only_phases` (default PORTABLE_PHASES).

    `normalized` is `portable` plus the Lean phases (elaboration and proofs) and the budgeted
    hotspot proof modules, whose time is compared as a multiple of the calibration workload
    measured in the same run (`max_ratio`), so a slower or faster machine cancels. The
    measurement must carry the budgets' calibration file; memory uses the portable limits.

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
    portable = portable or normalized
    unit = None
    if normalized:
        only_phases = set(only_phases or (*PORTABLE_PHASES, *NORMALIZED_PHASES))
        expected = budgets.get("calibration")
        calibration = measurement.get("calibration")
        if not expected:
            add("missing-calibration", None, "the budgets file has no calibration; record and rebaseline with it")
        elif not isinstance(calibration, dict) or not isinstance(calibration.get("seconds"), (int, float)) \
                or calibration["seconds"] <= 0:
            add("missing-calibration", None, "the measurement has no calibration run (record it again)")
        elif calibration.get("sha256") != expected["sha256"]:
            add("missing-calibration", None, "the measurement ran another calibration file than the budgets")
        else:
            unit = calibration["seconds"]
        if unit is None:
            return 1, findings
    elif portable:
        only_phases = set(only_phases or PORTABLE_PHASES)
    prefix = "portable_" if portable else ""
    time_key, rss_key = prefix + "max_seconds", prefix + "max_peak_rss_kib"
    if reference and not portable and not allow_platform_mismatch and any(
            measured_platform.get(key) != value for key, value in reference.items()):
        add("platform-mismatch", None,
            f"budgets were recorded on {reference}, measurement is from "
            f"{ {key: measured_platform.get(key) for key in reference} }")
    measured = measurement.get("workloads", {})
    budgeted = {workload["id"]: workload for workload in budgets.get("workloads", [])}
    if only_workloads:
        unknown = set(only_workloads) - set(budgeted)
        if unknown:
            add("missing-workload", ", ".join(sorted(unknown)), "gated workload is not in the budgets file")
        budgeted = {ident: workload for ident, workload in budgeted.items() if ident in only_workloads}
        measured = {ident: result for ident, result in measured.items() if ident in only_workloads}
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
            if only_phases is not None and phase not in only_phases:
                continue
            got = phases.get(phase)
            if got is None:
                add("missing-phase", ident, "budgeted phase is absent from the measurement", phase)
                continue
            if normalized and phase in NORMALIZED_PHASES:
                seconds = got.get("seconds")
                if not isinstance(seconds, (int, float)):
                    add("missing-phase", ident, "phase has no wall time", phase)
                elif "max_ratio" not in limits:
                    add("missing-phase", ident, "phase has no calibrated budget (rebaseline)", phase)
                elif seconds / unit > limits["max_ratio"]:
                    add("time-regression", ident,
                        f"{seconds / unit:.2f} calibration units ({seconds:.2f}s) exceed budget "
                        f"{limits['max_ratio']:.2f} (baseline {limits.get('baseline_ratio', 0):.2f}); "
                        f"1 unit = {unit:.2f}s on this machine", phase)
            elif time_key in limits:
                seconds = got.get("seconds")
                if not isinstance(seconds, (int, float)):
                    add("missing-phase", ident, "phase has no wall time", phase)
                elif seconds > limits[time_key]:
                    add("time-regression", ident,
                        f"{seconds:.3f}s exceeds budget {limits[time_key]:.3f}s "
                        f"(baseline {limits.get('baseline_seconds', 0):.3f}s)", phase)
            if rss_key in limits:
                rss = got.get("peak_rss_kib")
                if not isinstance(rss, int):
                    add("missing-phase", ident, "phase has no peak RSS", phase)
                elif rss > limits[rss_key]:
                    add("memory-regression", ident,
                        f"peak RSS {rss} KiB exceeds budget {limits[rss_key]} KiB "
                        f"(baseline {limits.get('baseline_peak_rss_kib', 0)} KiB)", phase)
        if normalized:
            for module, limits in sorted((budget.get("modules") or {}).items()):
                got = (result.get("modules") or {}).get(module)
                if got is None:
                    add("missing-phase", ident, f"hotspot module {module} has no timing "
                        "(record with --per-module)")
                    continue
                seconds = got.get("seconds")
                if not isinstance(seconds, (int, float)):
                    add("missing-phase", ident, f"module {module} has no wall time")
                elif seconds / unit > limits["max_ratio"]:
                    add("time-regression", ident,
                        f"module {module}: {seconds / unit:.2f} calibration units ({seconds:.2f}s) exceed "
                        f"budget {limits['max_ratio']:.2f} (baseline {limits.get('baseline_ratio', 0):.2f})")
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
    calibration = measurement.get("calibration")
    unit = None
    if calibration is not None:
        if not isinstance(calibration.get("seconds"), (int, float)) or calibration["seconds"] <= 0 \
                or calibration.get("sha256") != digest(ROOT / CALIBRATION):
            raise ValueError("the measurement's calibration is invalid or ran another calibration file")
        unit = calibration["seconds"]
        # A partial rebaseline keeps the recorded unit of the other workloads (same reference platform).
        kept = updated.get("calibration") if only else None
        updated["calibration"] = kept or {"file": CALIBRATION, "sha256": calibration["sha256"],
                                          "baseline_seconds": unit, "runs": calibration.get("runs")}
        updated.setdefault("normalized_tolerance", {"lean": {"time_ratio": 2.0, "time_slack_units": 2.0,
                                                             "module_slack_units": 1.0}})
    elif updated.get("calibration") and only:
        # A partial rebaseline keeps its unit: ratios of different units would not be comparable.
        raise ValueError("a calibrated budgets file needs a measurement with a calibration run")
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
            portable = budgets["portable_tolerance"][phase_class(phase)]
            entry = {}
            if isinstance(got.get("seconds"), (int, float)):
                entry["baseline_seconds"] = got["seconds"]
                entry["max_seconds"] = round(limit(got["seconds"], tolerance["time_ratio"],
                                                   tolerance["time_slack_seconds"]), 3)
                entry["portable_max_seconds"] = round(limit(got["seconds"], portable["time_ratio"],
                                                            portable["time_slack_seconds"]), 3)
            if isinstance(got.get("peak_rss_kib"), int):
                entry["baseline_peak_rss_kib"] = got["peak_rss_kib"]
                entry["max_peak_rss_kib"] = int(limit(got["peak_rss_kib"], tolerance["rss_ratio"],
                                                      tolerance["rss_slack_kib"]))
                entry["portable_max_peak_rss_kib"] = int(limit(got["peak_rss_kib"], portable["rss_ratio"],
                                                               portable["rss_slack_kib"]))
            if unit is not None and phase in NORMALIZED_PHASES and "baseline_seconds" in entry:
                normalized = updated["normalized_tolerance"]["lean"]
                entry["baseline_ratio"] = round(got["seconds"] / unit, 3)
                entry["max_ratio"] = round(limit(got["seconds"] / unit, normalized["time_ratio"],
                                                 normalized["time_slack_units"]), 3)
            if entry:
                phases[phase] = entry
        workload["budget"] = {"recorded": recorded, "output": result["output"], "phases": phases}
        # Hotspot proof modules (module-local cold builds, `record --per-module`) keep their own limit.
        if unit is not None and result.get("modules"):
            normalized = updated["normalized_tolerance"]["lean"]
            workload["budget"]["modules"] = {
                module: {"baseline_seconds": got["seconds"], "baseline_ratio": round(got["seconds"] / unit, 3),
                         "max_ratio": round(limit(got["seconds"] / unit, normalized["time_ratio"],
                                                  normalized["module_slack_units"]), 3)}
                for module, got in sorted(result["modules"].items())
                if isinstance(got.get("seconds"), (int, float)) and got["seconds"] >= HOTSPOT_SECONDS}
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


def run_calibration(args, log):
    """Median wall time of a fixed pure-Lean elaboration (`CALIBRATION`): the unit of the normalized gate."""
    file = ROOT / CALIBRATION
    times = []
    for _ in range(CALIBRATION_RUNS):
        step = measure([args.lake, "env", "lean", file], ROOT, log, args.timeout)
        require_success(step, "calibration run")
        times.append(step["seconds"])
    return {"file": CALIBRATION, "sha256": digest(file), "runs": times, "seconds": statistics.median(times)}


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
    # The guard admits several workloads at once; a timing run must hold it alone.
    if os.environ.get("AIR2LEAN_GUARD_MODE", "exclusive") != "exclusive" and not args.allow_unserialized:
        raise SystemExit("record must run alone: scripts/build-guard.py --exclusive; see docs/perf-budgets.md")
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
        if not args.skip_calibration and not args.skip_proof:
            measurement["calibration"] = run_calibration(args, log)
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


# Heartbeat budgets (`heartbeats`): Lean's heartbeats count elaboration work deterministically, so
# a proof's budget is an exact gate. Every `set_option maxHeartbeats N in` of a gated file is the
# recorded budget of the declaration it precedes, `N = ceil(measured * tolerance / step) * step`
# (Lean's units of 1000 heartbeats).
HB_RAISE = re.compile(r"^set_option maxHeartbeats (\d+) in\s*$")
HB_DECL = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[]+)")
# Lines between a raise and its declaration: other `… in` prefixes, docstrings, attributes.
HB_PREFIX = re.compile(r"^(?:set_option \S+ \S+ in|omit .* in|attribute \[.*\] .* in|include .* in|@\[.*\]|/--.*|.*-/|\s*)$")
HB_MEASURE = '''
set_option Elab.async false
open Lean Elab Command in
elab "air2lean_count_heartbeats " n:str " in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  logInfo m!"AIR2LEAN_HEARTBEATS {n.getString} {(← IO.getNumHeartbeats) - h0}"
'''


def hb_section(budgets):
    section = budgets.get("heartbeats")
    if not isinstance(section, dict) or not all(key in section for key in ("policy", "files", "budgets")):
        raise ValueError(f"{BUDGETS.relative_to(ROOT)}: no `heartbeats` section with policy, files, budgets")
    return section


def hb_budget_of(measured, policy):
    """The budget of a declaration measured at `measured` (units of 1000 heartbeats)."""
    step = policy["step"]
    return max(policy["default"], math.ceil(measured * policy["tolerance"] / step) * step)


def hb_declarations(text):
    """(declaration, its raise or None, line of its first prefix) for every declaration, in order.
    Inside a docstring, only its last line (`-/`) ends it."""
    out, start, raise_, in_doc = [], None, None, False
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if in_doc:
            in_doc = "-/" not in stripped
            continue
        if stripped.startswith("/--") and "-/" not in stripped:
            in_doc = True
            start = start or number
            continue
        m = HB_RAISE.match(line)
        if m:
            raise_, start = int(m.group(1)), start or number
            continue
        d = HB_DECL.match(line)
        if d:
            out.append((d.group(1), raise_, start or number))
            start, raise_ = None, None
            continue
        if stripped and HB_PREFIX.match(line):
            start = start or number
        else:
            start, raise_ = None, None
    return out


def hb_check(root, section):
    policy, errors = section["policy"], []
    listed = {(e["file"], e["declaration"]): e for e in section["budgets"]}
    for name in section["files"]:
        path = root / name
        if not path.is_file():
            errors.append(f"{name}: gated file is missing")
            continue
        seen = set()
        for decl, raised, _ in hb_declarations(path.read_text()):
            entry = listed.get((name, decl))
            if raised is None:
                if entry:
                    errors.append(f"{name}: `{decl}` is listed but does not raise maxHeartbeats")
                continue
            seen.add(decl)
            if entry is None:
                errors.append(f"{name}: `{decl}` raises maxHeartbeats to {raised} without a recorded "
                              f"budget (scripts/perf-budgets.py heartbeats record {name})")
            elif raised != entry["budget"]:
                errors.append(f"{name}: `{decl}` raises maxHeartbeats to {raised}, its budget is "
                              f"{entry['budget']}")
        errors += [f"{name}: `{decl}` is listed but has no raise in the file"
                   for file, decl in listed if file == name and decl not in seen]
    for entry in section["budgets"]:
        if entry["file"] not in section["files"]:
            errors.append(f"{entry['file']}: listed but not a gated file")
        if entry["budget"] != hb_budget_of(entry["measured"], policy):
            errors.append(f"{entry['file']}: `{entry['declaration']}` budget {entry['budget']} does not "
                          f"follow the policy for {entry['measured']} measured "
                          f"({hb_budget_of(entry['measured'], policy)})")
        if entry["budget"] <= policy["default"]:
            errors.append(f"{entry['file']}: `{entry['declaration']}` fits the default budget; drop the raise")
    return sorted(set(errors))


def hb_measure(root, name):
    """{declaration: measured} for every declaration of a gated file (units of 1000)."""
    text = (root / name).read_text()
    lines = text.splitlines()
    starts = {start: decl for decl, _, start in hb_declarations(text)}
    first = next(i for i, line in enumerate(lines) if not line.startswith(("import", "--")) and line.strip())
    body = list(lines[:first]) + HB_MEASURE.splitlines()
    for number, line in enumerate(lines[first:], first + 1):
        if number in starts:
            body.append(f"air2lean_count_heartbeats {json.dumps(starts[number])} in")
        body.append(HB_RAISE.sub("set_option maxHeartbeats 0 in", line))
    with tempfile.TemporaryDirectory(dir=root / ".lake") as work:
        measuring = Path(work) / Path(name).name
        measuring.write_text("\n".join(body) + "\n")
        run = subprocess.run(["lake", "env", "lean", str(measuring)], cwd=root, text=True,
                             capture_output=True)
    if run.returncode != 0:
        raise RuntimeError(f"{name}: the measuring copy does not elaborate:\n{run.stdout}{run.stderr}")
    found = {m.group(1): int(m.group(2)) // 1000
             for m in re.finditer(r"AIR2LEAN_HEARTBEATS (\S+) (\d+)", run.stdout)}
    if set(found) != set(starts.values()):
        raise RuntimeError(f"{name}: measured {sorted(found)}, expected {sorted(starts.values())}")
    return found


def hb_record(root, budgets, names):
    section = hb_section(budgets)
    policy = section["policy"]
    for name in names:
        if name not in section["files"]:
            raise ValueError(f"{name} is not a gated file of the heartbeats section")
        found = hb_measure(root, name)
        section["budgets"] = [e for e in section["budgets"] if e["file"] != name] + [
            {"file": name, "declaration": decl, "measured": hb, "budget": hb_budget_of(hb, policy)}
            for decl, hb in found.items() if hb > policy["default"] / policy["tolerance"]]
    section["budgets"].sort(key=lambda e: (e["file"], e["declaration"]))


def heartbeats(args):
    budgets = load_json(args.budgets)
    try:
        section = hb_section(budgets)
        if args.action == "check":
            errors = hb_check(ROOT, section)
            for error in errors:
                print(f"error: {error}")
            return 1 if errors else 0
        if args.action == "record":
            hb_record(ROOT, budgets, args.files)
            write_json(args.budgets, budgets)
            return 0
    except (ValueError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    for e in sorted(section["budgets"], key=lambda e: -e["measured"]):
        print(f"{e['measured']:>9}  budget {e['budget']:>8}  {e['file']}  {e['declaration']}")
    return 0


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
    rec.add_argument("--skip-calibration", action="store_true",
                     help="no calibration run (implied by --skip-proof); such a measurement cannot pass the normalized gate")
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
    gat.add_argument("--portable", action="store_true",
                     help="check the generous platform-independent limits (CI runners)")
    gat.add_argument("--normalized", action="store_true",
                     help="like --portable, plus elaboration, proofs and hotspot modules as multiples of the "
                          "calibration run of the same measurement (any machine; needs `record` with calibration)")
    gat.add_argument("--phase", action="append",
                     help="with --portable/--normalized: restrict to these phases (default: translator and elaborate)")
    gat.add_argument("--workload", action="append",
                     help="gate only these workloads (a partial `record --workload` measurement)")
    gat.add_argument("--json", type=Path, help="also write findings as JSON")
    val = sub.add_parser("validate", help="check the budgets file structure")
    val.add_argument("--budgets", type=Path, default=BUDGETS)
    hb = sub.add_parser("heartbeats", help="heartbeat budgets of proofs that raise maxHeartbeats")
    hb.add_argument("--budgets", type=Path, default=BUDGETS)
    hb_sub = hb.add_subparsers(dest="action", required=True)
    hb_sub.add_parser("check", help="static: every raise of a gated file is its recorded budget")
    hb_rec = hb_sub.add_parser("record", help="measure the gated FILEs and rewrite their entries")
    hb_rec.add_argument("files", nargs="+")
    hb_sub.add_parser("show", help="the recorded entries, worst first")
    args = parser.parse_args(argv)
    if args.command == "heartbeats":
        return heartbeats(args)
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
    code, findings = gate(budgets, measurement, args.allow_pending, args.allow_platform_mismatch,
                          args.portable, args.phase, args.normalized, args.workload)
    if args.json:
        write_json(args.json, {"exit_code": code, "findings": findings})
    print_findings(code, findings)
    return code


if __name__ == "__main__":
    sys.exit(main())
