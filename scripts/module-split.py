#!/usr/bin/env python3
"""Invalidation keys for `air2lean --split-modules` output (`docs/modular-output.md`).

`air2lean AIR -o Proofs/Ex/Gen.lean --namespace Ex --split-modules Proofs.Ex.Gen` writes one
Lean module per call group plus `Gen.modules.json` (`air2lean-module-split-v1`). Each
module's key hashes its own Lean text, the profile metadata, the semantic fingerprints of its
functions (`scripts/semantic-fingerprints.py`, when a source map is given) and the keys of the
generated modules it imports. A changed key means the module, and hence every module importing
it, must be rebuilt; an unchanged key means its inputs are identical.

`keys MANIFEST [--source-map MAP]` prints every module's key. `compare OLD NEW` (manifests,
with `--old-source-map`/`--new-source-map`) reports which modules changed text, which are
invalidated and which are unaffected; `invalidated` is exactly the changed modules plus every
module that imports one of them, transitively.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

FORMAT = "air2lean-module-split-v1"
KEYS = "air2lean-module-keys-v1"
COMPARISON = "air2lean-module-comparison-v1"
KINDS = {"types", "group", "dispatch", "umbrella"}
MODULE_FIELDS = {"module", "file", "kind", "functions", "definitions", "imports"}

sys.dont_write_bytecode = True  # importing the sibling script must not leave __pycache__
_spec = importlib.util.spec_from_file_location(
    "semantic_fingerprints", Path(__file__).resolve().parent / "semantic-fingerprints.py")
fp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fp)


def load_manifest(path):
    path = Path(path)
    doc = fp.parse_json(path.read_text(encoding="utf-8"))
    if (not isinstance(doc, dict) or doc.get("format") != FORMAT or
            set(doc) != {"format", "namespace", "root", "metadata", "modules"} or
            not isinstance(doc["modules"], list)):
        raise ValueError(f"{path}: not an {FORMAT} manifest")
    names = set()
    for m in doc["modules"]:
        if (not isinstance(m, dict) or set(m) != MODULE_FIELDS or m["kind"] not in KINDS or
                not isinstance(m["module"], str) or not isinstance(m["file"], str) or
                any(not isinstance(m[k], list) or any(not isinstance(v, str) for v in m[k])
                    for k in ("functions", "definitions", "imports"))):
            raise ValueError(f"{path}: malformed module record")
        if m["module"] in names:
            raise ValueError(f"{path}: duplicate module {m['module']!r}")
        names.add(m["module"])
        file = (path.parent / m["file"]).resolve()
        if path.parent.resolve() not in file.parents:
            raise ValueError(f"{path}: module file {m['file']!r} escapes the manifest directory")
        m["text_sha256"] = hashlib.sha256(file.read_bytes()).hexdigest()
    return doc


def keys(manifest, source_map=None):
    """`module -> entry` with the text digest and the invalidation key, imports first."""
    modules = {m["module"]: m for m in manifest["modules"]}
    prints = {}
    if source_map is not None:
        if (source_map["namespace"] != manifest["namespace"] or
                source_map["metadata"] != manifest["metadata"]):
            raise ValueError("source map and module manifest describe different translations")
        prints = fp.fingerprints(source_map)
        listed = [s for m in modules.values() for s in m["functions"]]
        if sorted(listed) != sorted(prints):
            raise ValueError("source map and module manifest list different functions")
        for m in modules.values():
            if [prints[s]["definition"] for s in m["functions"]] != m["definitions"]:
                raise ValueError(f"{m['module']}: declarations differ from the source map")
    edges = {name: sorted(i for i in m["imports"] if i in modules) for name, m in modules.items()}
    result = {}
    for members in fp.components(sorted(modules), edges):
        if len(members) > 1 or members[0] in edges[members[0]]:
            raise ValueError(f"import cycle: {members}")
        name = members[0]
        m = modules[name]
        key = fp.digest(dict(
            format=KEYS, module=name, kind=m["kind"], text=m["text_sha256"],
            metadata=manifest["metadata"],
            functions=[[s, prints[s]["fingerprint"] if prints else None] for s in m["functions"]],
            imports=[[i, result[i]["key"] if i in result else None] for i in sorted(m["imports"])]))
        result[name] = dict(module=name, kind=m["kind"], file=m["file"], functions=m["functions"],
                            imports=edges[name], text_sha256=m["text_sha256"], key=key)
    return result


def dependents(entries, roots):
    """`roots` and every module that imports one of them, transitively."""
    importers = {}
    for name, entry in entries.items():
        for i in entry["imports"]:
            importers.setdefault(i, set()).add(name)
    seen, todo = set(roots), list(roots)
    while todo:
        for user in importers.get(todo.pop(), ()):
            if user not in seen:
                seen.add(user); todo.append(user)
    return seen


def compare(old, new):
    report = dict(format=COMPARISON, changed=[], invalidated=[], unaffected=[], added=[], removed=[])
    for name in sorted(set(old) | set(new)):
        if name not in new:
            report["removed"].append(name)
        elif name not in old:
            report["added"].append(name)
        else:
            if old[name]["text_sha256"] != new[name]["text_sha256"]:
                report["changed"].append(name)
            report["invalidated" if old[name]["key"] != new[name]["key"] else "unaffected"].append(name)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("keys", help="print every module's invalidation key")
    p.add_argument("manifest"); p.add_argument("--source-map")
    p = sub.add_parser("compare", help="classify modules between two split translations")
    p.add_argument("old"); p.add_argument("new")
    p.add_argument("--old-source-map"); p.add_argument("--new-source-map")
    args = parser.parse_args()

    def load(manifest, source_map):
        return keys(load_manifest(manifest), fp.load_sidecar(source_map) if source_map else None)
    try:
        if args.command == "keys":
            entries = load(args.manifest, args.source_map)
            result = dict(format=KEYS, modules=[entries[n] for n in sorted(entries)])
        else:
            result = compare(load(args.old, args.old_source_map), load(args.new, args.new_source_map))
    except (ValueError, OSError, UnicodeDecodeError) as error:
        parser.exit(2, f"error: {error}\n")
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
