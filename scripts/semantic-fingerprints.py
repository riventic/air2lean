#!/usr/bin/env python3
"""Semantic fingerprints and proof-interface invalidation from translator source maps.

`air2lean ... --source-map-json Gen.source-map.json` writes a sidecar with one canonical,
renumbering-invariant AIR body per function (`docs/stable-generation.md`). This script
hashes each body with the checked profile metadata and translator options, then folds in
callee fingerprints over the call graph. Mutually recursive functions share one
strongly connected component digest, so a change anywhere in a cycle invalidates
the whole cycle and every caller.

`index` prints the per-function fingerprints. `compare OLD NEW` reports which proof
interfaces are unaffected, invalidated (semantic change), renamed (same semantics,
different Lean names), added or removed. A fingerprint is an invalidation key, not a
semantic-equivalence proof: equal fingerprints mean that the translated inputs agree.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

SIDECAR = "air2lean-source-map-v1"
INDEX = "air2lean-semantic-fingerprint-v1"
COMPARISON = "air2lean-proof-interface-comparison-v1"
FIELDS = {"source", "air_name", "air_file", "definition", "proof_api", "callees", "canonical", "lines"}

sys.dont_write_bytecode = True  # importing the sibling script must not leave __pycache__
_spec = importlib.util.spec_from_file_location(
    "normalize_generated", Path(__file__).resolve().parent / "normalize-generated.py")
_normalize = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_normalize)
parse_json = _normalize.parse_json


def digest(value):
    encoded = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
                         allow_nan=False).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def load_sidecar(path, generated=None):
    doc = parse_json(Path(path).read_text(encoding="utf-8"))
    if (not isinstance(doc, dict) or doc.get("format") != SIDECAR or
            set(doc) != {"format", "namespace", "metadata", "options", "functions"} or
            not isinstance(doc["functions"], list)):
        raise ValueError(f"{path}: not an {SIDECAR} sidecar")
    seen = set()
    for record in doc["functions"]:
        if (not isinstance(record, dict) or set(record) != FIELDS or
                not isinstance(record["source"], str) or not record["source"] or
                not isinstance(record["callees"], list) or
                any(not isinstance(c, str) for c in record["callees"])):
            raise ValueError(f"{path}: malformed function record")
        if record["source"] in seen:
            raise ValueError(f"{path}: duplicate function {record['source']!r}")
        seen.add(record["source"])
    if generated is not None:
        metadata, _ = _normalize.split_generated(Path(generated).read_bytes(), required=True)
        if metadata != doc["metadata"]:
            raise ValueError(f"{generated}: profile header differs from the source map")
    return doc


def components(nodes, edges):
    """Tarjan's SCCs (iterative), callees before callers."""
    index, low, on_stack, stack, order = {}, {}, set(), [], []
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(edges[root]))]
        index[root] = low[root] = len(index)
        stack.append(root); on_stack.add(root)
        while work:
            node, children = work[-1]
            child = next(children, None)
            if child is None:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[node])
                if low[node] == index[node]:
                    members = []
                    while True:
                        member = stack.pop(); on_stack.discard(member); members.append(member)
                        if member == node:
                            break
                    order.append(sorted(members))
            elif child not in index:
                index[child] = low[child] = len(index)
                stack.append(child); on_stack.add(child)
                work.append((child, iter(edges[child])))
            elif child in on_stack:
                low[node] = min(low[node], index[child])
    return order


def fingerprints(doc):
    """`source -> entry` with local, component and call-graph fingerprints."""
    context = digest(dict(format=INDEX, metadata=doc["metadata"], options=doc["options"]))
    records = {r["source"]: r for r in doc["functions"]}
    local = {s: digest(dict(context=context, canonical=r["canonical"])) for s, r in records.items()}
    edges = {s: sorted(set(c for c in r["callees"] if c in records)) for s, r in records.items()}
    result = {}
    for members in components(sorted(records), edges):
        inside = set(members)
        outside = sorted({c for m in members for c in edges[m] if c not in inside})
        cyclic = len(members) > 1 or members[0] in edges[members[0]]
        component = digest(dict(
            members=[[m, local[m], [c for c in edges[m] if c in inside]] for m in members],
            callees=[[c, result[c]["fingerprint"]] for c in outside]))
        for m in members:
            record = records[m]
            result[m] = dict(
                source=m, definition=record["definition"], proof_api=record["proof_api"],
                air_name=record["air_name"], air_file=record["air_file"],
                local_sha256=local[m], fingerprint=digest(dict(component=component, source=m)),
                callees=edges[m], boundaries=sorted(set(record["callees"]) - set(records)),
                recursive_group=members if cyclic else [])
    return result


def interface(doc, entry):
    return dict(namespace=doc["namespace"], definition=entry["definition"], proof_api=entry["proof_api"])


def index(doc):
    entries = fingerprints(doc)
    return dict(format=INDEX, namespace=doc["namespace"],
                functions=[entries[s] for s in sorted(entries)])


def compare(old, new):
    before, after = fingerprints(old), fingerprints(new)
    report = dict(format=COMPARISON, unaffected=[], invalidated=[], renamed=[], added=[], removed=[])
    for source in sorted(set(before) | set(after)):
        if source not in after:
            report["removed"].append(source)
        elif source not in before:
            report["added"].append(source)
        elif before[source]["fingerprint"] != after[source]["fingerprint"]:
            report["invalidated"].append(source)
        elif interface(old, before[source]) != interface(new, after[source]):
            report["renamed"].append(source)
        else:
            report["unaffected"].append(source)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("index", help="print per-function semantic fingerprints")
    p.add_argument("source_map"); p.add_argument("--generated", help="bind to this generated Lean file")
    p = sub.add_parser("compare", help="classify proof interfaces between two translations")
    p.add_argument("old"); p.add_argument("new")
    p.add_argument("--old-generated"); p.add_argument("--new-generated")
    p.add_argument("--fail-on-change", action="store_true",
                   help="exit 1 unless every old interface is unaffected")
    args = parser.parse_args()
    try:
        if args.command == "index":
            result = index(load_sidecar(args.source_map, args.generated))
        else:
            result = compare(load_sidecar(args.old, args.old_generated),
                             load_sidecar(args.new, args.new_generated))
    except (ValueError, OSError, UnicodeDecodeError) as error:
        parser.exit(2, f"error: {error}\n")
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    if args.command == "compare" and args.fail_on_change and (
            result["invalidated"] or result["renamed"] or result["removed"]):
        sys.exit(1)


if __name__ == "__main__":
    main()
