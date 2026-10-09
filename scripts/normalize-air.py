#!/usr/bin/env python3
"""Normalize compiler identities and writer metadata for AIR golden comparison."""

import argparse
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path
import runpy
import re
import sys


HASHED_NAME = re.compile(r"~air2lean-sha256-[0-9a-f]{64}\.json")


IDENTITY_MARKER = re.compile(r"__(anon|enum|opaque|union|struct)_[0-9]+")


def storage_name(name, document):
    """The exporter's storage identity of a function: `name` in the `root` and `std` modules
    (and in a legacy export without `module`), else `<module>:<name>`."""
    module = document.get("module")
    return name if module in (None, "root", "std") else f"{module}:{name}"


def canonical_filename(name):
    """Portable naming for normalized identities, reserving legacy collision suffix space."""
    stem = name.split(".", 1)[0].upper()
    reserved = stem in {"CON", "PRN", "AUX", "NUL"} or re.fullmatch(r"(COM|LPT)[1-9]", stem)
    if (re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*", name) and
            len(name.encode("utf-8")) + 5 + 13 <= 255 and not reserved):
        return name + ".json"
    return "~air2lean-sha256-" + hashlib.sha256(name.encode("utf-8")).hexdigest() + ".json"


@cache
def load_helpers():
    return runpy.run_path(str(Path(__file__).with_name("normalize-generated.py")))


def normalize(value, root=True, type_entry=False, checked_profile=None, actual=False, helpers=None):
    if root and checked_profile is not None:
        helpers = helpers if helpers is not None else load_helpers()
        profile = helpers["profile_for_air"](value)
        if actual and profile != checked_profile:
            raise ValueError("AIR profile differs from validated translation report")
        # The only schema compatibility transition is 12 (mandatory metadata) to
        # 11 (the same AIR semantic payload). Older schemas remain observable.
        if value["schema"] == 12:
            value = {k: v for k, v in value.items() if k != "profile"}
            value["schema"] = 11

    # Match Air2Lean.Anon.renameIdentities: only the root/type-entry name and
    # function references are identities. Nested names and all other data remain
    # observable, even when they contain compiler-looking markers.
    if isinstance(value, list):
        return [normalize(item, False, type_entry) for item in value]
    if not isinstance(value, dict):
        return value
    result = {}
    for key, item in value.items():
        if root and (key == "zig_version" or (key == "target_endian" and item == "little")):
            continue
        # A packed field bit-pointer's `"vector_index": null` (the exporter's explicit "not a
        # lane pointer") is the same AIR as a golden that predates the field. A lane number or
        # "runtime" stays observable.
        if type_entry and key == "vector_index" and item is None:
            continue
        # Module identity (B1, docs/air-json.md §Identity) is checked by translating the
        # actual export: the generated names and std model bindings depend on it, and the
        # generated file is compared with its golden. Goldens that predate it compare equal.
        if key == "comptime_fn_module" or (key == "module" and (root or "func" in value or "name" in value)):
            continue
        identity = key in ("func", "comptime_fn") or (key == "name" and (root or type_entry))
        if identity:
            result[key] = IDENTITY_MARKER.sub(r"__\1_N", item) if isinstance(item, str) else item
        else:
            result[key] = normalize(item, False, root and key == "types")
    return result


class ValidationContext:
    """Load the helpers and receipt once, with constant-time AIR filename lookup."""
    def __init__(self, report_path=None, actual=False):
        self.helpers = load_helpers()
        self.actual = actual
        self.profile = None
        self.inputs = {}
        if report_path:
            report = self.helpers["load_report"](report_path)
            self.profile = report["metadata"]["profile"]
            for entry in report["air"]:
                if not isinstance(entry, dict) or not isinstance(entry.get("file"), str):
                    raise ValueError("malformed AIR receipt entry")
                name = entry["file"]
                if name in self.inputs:
                    raise ValueError(f"duplicate AIR receipt filename {name!r}")
                self.inputs[name] = entry["sha256"]
        elif actual:
            raise ValueError("--actual requires a validated --check-report")

    def file_entry(self, path):
        path = Path(path)
        raw = path.read_bytes()
        if self.actual and self.inputs.get(path.name) != self.helpers["digest"](raw):
            raise ValueError(f"{path}: AIR artifact does not match validated translation report")
        document = self.helpers["parse_json"](raw.decode("utf-8"))
        value = normalize(document, checked_profile=self.profile, actual=self.actual, helpers=self.helpers)
        if not isinstance(document, dict) or not isinstance(document.get("name"), str):
            raise ValueError(f"{path}: AIR filename requires a full JSON name")
        if path.name.startswith("~air2lean-sha256-"):
            if not HASHED_NAME.fullmatch(path.name):
                raise ValueError(f"{path}: malformed reserved AIR filename")
            expected = "~air2lean-sha256-" + hashlib.sha256(storage_name(document["name"], document).encode("utf-8")).hexdigest() + ".json"
            if path.name != expected:
                raise ValueError(f"{path}: reserved AIR filename does not match full JSON name")
        name = canonical_filename(storage_name(value["name"], document))
        data = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode("utf-8")
        return name, data

    def file(self, path):
        return self.file_entry(path)[1]


def add_directory(source, destination, context):
    """Apply a validated directory overlay, preserving the legacy collision filenames."""
    source, destination = Path(source), Path(destination)
    if not source.is_dir():
        raise ValueError(f"not an AIR directory: {source}")
    # Validate every input before removing an earlier overlay or writing any new file.
    entries = [context.file_entry(p) for p in sorted(source.glob("*.json")) if p.is_file()]
    counts = Counter(name for name, _ in entries)
    destination.mkdir(parents=True, exist_ok=True)
    # Inspect existing files once, rather than scanning the directory for each basename.
    for previous in destination.iterdir():
        if not previous.name.endswith(".json"):
            continue
        stem = previous.name.removesuffix(".json")
        while True:
            if stem + ".json" in counts:
                previous.unlink()
                break
            if "." not in stem:
                break
            stem = stem.rsplit(".", 1)[0]
    for name, data in entries:
        if counts[name] > 1:
            # This is the old shasum hash of the exact pretty JSON, including its newline.
            name = name.removesuffix(".json") + "." + hashlib.sha1(data).hexdigest()[:12] + ".json"
        (destination / name).write_bytes(data)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source")
    parser.add_argument("--check-report")
    parser.add_argument("--actual", action="store_true")
    parser.add_argument("--output-dir", help="normalize a whole AIR directory as one overlay")
    args = parser.parse_args()
    try:
        context = ValidationContext(args.check_report, args.actual)
        if args.output_dir:
            add_directory(args.source, args.output_dir, context)
        else:
            sys.stdout.buffer.write(context.file(args.source))
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"error: {error}\n")
