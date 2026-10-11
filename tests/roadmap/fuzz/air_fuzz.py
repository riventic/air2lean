#!/usr/bin/env python3
"""Q01 seeded malformed-AIR-JSON fuzzer with delta-debugging shrinking.

Drives a previously built translator; never builds it or invokes a compiler.

  air_fuzz.py run BINARY [--seeds N] [--start S] [--save DIR] [--report FILE]
  air_fuzz.py replay BINARY            # committed regressions/ must pass the oracle
  air_fuzz.py show SEED [--out DIR]    # write the generated input for one seed

A case is reproducible from (seed, corpus): the corpus is the sorted list of committed
`tests/golden/**/*.json` files under CORPUS_MAX_BYTES plus the in-file seeds below.
Each case is run in emission mode and with `--diagnostics-json`. The oracle accepts only:
exit 0 with a profile header and no emitter placeholder, or exit 1 with a non-empty
diagnostic and an untouched output path; diagnostics mode must print schema JSON whose
status matches its exit code, with codes from the fixed vocabulary, and must agree with
emission mode on accept/reject. Anything else (signal, timeout, other exit, Lean PANIC,
placeholder, untyped rejection, disagreement) is a failure and is shrunk to a minimal
input that keeps the same failure signature.
"""
import argparse
import copy
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from shrink import ddmin, nodes, shrink_bytes, shrink_json  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
REGRESSIONS = HERE / "regressions"
CORPUS_MAX_BYTES = 16 * 1024
TIMEOUT = 10
SENTINEL = "sentinel\n"
# `Emit.lean`'s `placeholder`: an arm the checker should exclude (MM-6). The CLI rejects output
# that contains one (`EMITTER_PLACEHOLDER`, a checker gap, so a finding); the oracle also catches
# one that slipped through into written output.
PLACEHOLDER = re.compile(r'air2lean_emitter_placeholder "')
PLACEHOLDER_CODE = "EMITTER_PLACEHOLDER"
CRASH_MARKERS = ("PANIC at", "INTERNAL PANIC", "uncaught exception", "Stack overflow",
                 "stack overflow", "Segmentation fault")
CODES = {"CLI_ARGUMENTS", "INPUT_READ", "INPUT_LIMIT", "JSON_SYNTAX", "AIR_DECODE",
         "EXPORTER_UNSUPPORTED", "OPTIMIZED_UNSUPPORTED", "CANONICAL_FAILURE",
         "NORMALIZATION_FAILURE", "STRUCTURE_FAILURE", "TYPE_FAILURE", "GLOBAL_FAILURE",
         "MEMORY_FAILURE", "INSTRUCTION_FAILURE", "CONSTANT_FAILURE", "SIGNATURE_FAILURE",
         "MODEL_FAILURE", "PROGRAM_FAILURE", "PROFILE_FAILURE", "DUPLICATE_FUNCTION",
         "CALLEE_MISSING", "CALLEE_BLOCKED", "CALLEE_AMBIGUOUS", "CALLEE_EXTERN_UNBOUND",
         "PREREQUISITE_SKIPPED",
         "VOLATILE_ACCESS", "PACKED_LAYOUT", "PADDED_ATOMIC",
         "ASM_VOLATILE_EFFECT", "EMITTER_PLACEHOLDER"}


# --- corpus ------------------------------------------------------------------------------

def _int(bits=32, signed=False):
    return dict(k="int", signed=signed, bits=bits, abi_size=(bits + 7) // 8, abi_align=(bits + 7) // 8)


def _builtin_seeds():
    void, noret = dict(k="void", abi_size=0, abi_align=1), dict(k="noreturn")
    ident = dict(schema=11, zig_version="0.16.0", target_endian="little", name="seed.ident",
                 types=[void, _int(), noret], params=[1], ret=1, globals=[], body=[
                     dict(id=0, tag="arg", ty=1, args=[], param=0),
                     dict(id=1, tag="ret", ty=2, args=[dict(inst=0)])])
    caller = dict(ident, name="seed.caller", body=[
        dict(id=0, tag="arg", ty=1, args=[], param=0),
        dict(id=1, tag="call", ty=1, args=[dict(inst=0)], callee=dict(func="seed.ident", noreturn=False)),
        dict(id=2, tag="ret", ty=2, args=[dict(inst=1)])])
    pointer = dict(k="ptr", size="one", const=False, child=1, abi_size=8, abi_align=8, ptr_align=4)
    glob = dict(schema=11, zig_version="0.16.0", target_endian="little", name="seed.global",
                types=[void, _int(), noret, pointer], params=[], ret=1, body=[
                    dict(id=0, tag="load", ty=1, args=[dict(ty=3, ptr={"global": 0, "off": 0})]),
                    dict(id=1, tag="ret", ty=2, args=[dict(inst=0)])],
                globals=[dict(name="seed.state", ty=1, const=False, threadlocal=False, extern=False,
                              init=dict(ty=1, val="7"))])
    return [("builtin:ident", [ident]), ("builtin:call", [caller, ident]), ("builtin:global", [glob])]


def load_corpus():
    corpus = _builtin_seeds()
    for path in sorted((ROOT / "tests/golden").rglob("*.json")):
        if path.stat().st_size <= CORPUS_MAX_BYTES:
            try:
                corpus.append((str(path.relative_to(ROOT)), [json.loads(path.read_text())]))
            except (ValueError, UnicodeDecodeError):
                continue
    return corpus


def _vocabulary(corpus):
    tags, kinds, keys = set(), set(), set()
    for _, docs in corpus:
        for doc in docs:
            stack = [doc]
            while stack:
                node = stack.pop()
                if isinstance(node, dict):
                    keys.update(node)
                    if isinstance(node.get("tag"), str):
                        tags.add(node["tag"])
                    if isinstance(node.get("k"), str):
                        kinds.add(node["k"])
                    stack.extend(node.values())
                elif isinstance(node, list):
                    stack.extend(node)
    return sorted(tags), sorted(kinds), sorted(keys)


# --- generator ---------------------------------------------------------------------------

WEIRD = [None, True, False, -1, 0, 1, 2 ** 31, 2 ** 32, 2 ** 63, 2 ** 64, -(2 ** 63) - 1,
         10 ** 30, 1.5, -0.0, "", "x", "0", "-1", "9" * 40, "{}", "undefined", [], {}, [[]],
         {"inst": 0}, {"ty": 0, "val": "0"}, {"ty": 99999, "val": "1"}, {"inst": -1},
         {"func": "", "noreturn": True}, {"global": 0, "off": -8}]


def _replace(doc, path, new):
    if not path:
        return new
    parent = doc
    for key in path[:-1]:
        parent = parent[key]
    parent[path[-1]] = new
    return doc


def _structural(rng, doc, corpus, vocab):
    tags, kinds, keys = vocab
    tree = list(nodes(doc))
    path, node = rng.choice(tree)
    op = rng.randrange(10)
    if op == 0 and path:  # delete a key / element
        parent = doc
        for key in path[:-1]:
            parent = parent[key]
        del parent[path[-1]]
        return doc, f"delete {list(path)}"
    if op == 1:
        new = copy.deepcopy(rng.choice(WEIRD))
        return _replace(doc, path, new), f"replace {list(path)} with {json.dumps(new)}"
    if op == 2:
        ints = [(p, v) for p, v in tree if isinstance(v, int) and not isinstance(v, bool)]
        if ints:
            path, value = rng.choice(ints)
            new = rng.choice([value + 1, value - 1, -value - 1, value + 1000, 0, 2 ** 32 + value])
            return _replace(doc, path, new), f"int {list(path)} {value}->{new}"
    if op == 3:
        tagged = [(p, v) for p, v in tree if isinstance(v, dict) and ("tag" in v or "k" in v)]
        if tagged:
            path, value = rng.choice(tagged)
            field = "tag" if "tag" in value else "k"
            new = rng.choice(tags if field == "tag" else kinds) if rng.random() < 0.8 else "fuzz_unknown"
            value[field] = new
            return doc, f"{field} {list(path)} -> {new}"
    if op == 4:
        lists = [(p, v) for p, v in tree if isinstance(v, list) and v]
        if lists:
            path, value = rng.choice(lists)
            i, j = rng.randrange(len(value)), rng.randrange(len(value))
            action = rng.randrange(3)
            if action == 0:
                value.insert(j, copy.deepcopy(value[i]))
            elif action == 1:
                value[i], value[j] = value[j], value[i]
            else:
                del value[i:]
            return doc, f"list {list(path)} op{action} {i} {j}"
    if op == 5:  # splice a subtree from the corpus
        _, donor_docs = rng.choice(corpus)
        _, donor = rng.choice(list(nodes(rng.choice(donor_docs))))
        return _replace(doc, path, copy.deepcopy(donor)), f"splice into {list(path)}"
    if op == 6 and isinstance(node, dict):
        key = rng.choice(keys + ["fuzz_extra"])
        node[key] = copy.deepcopy(rng.choice(WEIRD))
        return doc, f"set key {key} at {list(path)}"
    if op == 7 and isinstance(node, str):
        new = rng.choice(["", node + node, node[::-1], node.upper(), node + "\u0000",
                          "a" * 1100, "\ud800", "é", "«x»", node.replace(".", "..")])
        return _replace(doc, path, new), f"string {list(path)}"
    if op == 8:  # deep nesting
        depth = rng.choice([8, 64, 127, 129, 300])
        new = 0
        for _ in range(depth):
            new = [new]
        return _replace(doc, path, new), f"nest {depth} at {list(path)}"
    # default: wrong-type swap of a node
    flip = {dict: [], list: {}, str: 0, int: "0", float: "0.0", bool: 1, type(None): {}}
    new = flip.get(type(node), None)
    return _replace(doc, path, new), f"flip type at {list(path)}"


def _textual(rng, data):
    op = rng.randrange(9)
    n = len(data)
    i = rng.randrange(n + 1)
    if op == 0:
        return data[:i], f"truncate {i}"
    if op == 1:
        j = min(n, i + rng.randrange(1, 16))
        return data[:i] + data[j:], f"cut {i}:{j}"
    if op == 2:
        token = rng.choice([b"{", b"}", b"[", b"]", b",", b":", b'"', b"\\", b"\x00", b"-",
                            b"e", b".", b" ", b"\n", b"01", b"NaN", b"Infinity", b"true", b"null"])
        return data[:i] + token + data[i:], f"insert {token!r} at {i}"
    if op == 3:
        token = rng.choice([b"\xff", b"\xc0\x80", b"\xed\xa0\x80", b"\xe2\x82", b"\xf4\x90\x80\x80"])
        return data[:i] + token + data[i:], f"bad utf8 at {i}"
    if op == 4:
        return b"\xef\xbb\xbf" + data, "bom"
    if op == 5:
        return data.replace(b'"schema": 11', b'"schema": 1e999999', 1), "huge exponent"
    if op == 6:
        m = re.search(rb'"[a-z_]+": ', data[i:])
        if m:
            return data[:i + m.end()] + b'0, ' + m.group(0) + data[i + m.end():], "duplicate key"
        return data + b" ", "trailing space"
    if op == 7:
        return data + rng.choice([b"x", b"{}", b",", b"\x00"]), "trailing garbage"
    return data.replace(b'"', b"'", 1), "quote swap"


def _dump(doc):
    # A lone surrogate is written as its JSON escape rather than as invalid UTF-8.
    return json.dumps(doc, indent=1, ensure_ascii=False).encode("utf-8", "backslashreplace")


def generate(seed, corpus, vocab):
    """Return (files, description): files is a list of bytes, one per AIR file."""
    rng = random.Random(seed)
    origin, docs = corpus[rng.randrange(len(corpus))]
    docs = copy.deepcopy(docs)
    steps = []
    if rng.random() < 0.1:
        extra_origin, extra = corpus[rng.randrange(len(corpus))]
        docs = docs + copy.deepcopy(extra)
        steps.append(f"add {extra_origin}")
    for _ in range(rng.randint(1, 3)):
        k = rng.randrange(len(docs))
        if not isinstance(docs[k], (dict, list)):
            continue
        docs[k], step = _structural(rng, docs[k], corpus, vocab)
        steps.append(f"doc{k}: {step}")
    files = [_dump(doc) for doc in docs]
    if rng.random() < 0.3:
        k = rng.randrange(len(files))
        files[k], step = _textual(rng, files[k])
        steps.append(f"doc{k}: text {step}")
    return files, {"seed": seed, "origin": origin, "steps": steps}


# --- oracle ------------------------------------------------------------------------------

def _write(directory, files):
    air = directory / "air"
    if air.exists():
        shutil.rmtree(air)
    air.mkdir()
    for k, data in enumerate(files):
        (air / f"{k:02d}.json").write_bytes(data)
    return air


def _exec(argv, timeout):
    try:
        r = subprocess.run(argv, capture_output=True, timeout=timeout, check=False)
        return r.returncode, r.stdout.decode("utf-8", "replace"), r.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return None, "", ""


def classify_emit(code, stderr, output):
    """Failure kind for emission mode, or None when the outcome is predictable."""
    if code is None:
        return "emit:timeout"
    if any(m in stderr for m in CRASH_MARKERS):
        return "emit:internal-panic"
    if code == 0:
        if not output.startswith("-- air2lean-profile: "):
            return "emit:bad-output"
        if PLACEHOLDER.search(output):
            return "emit:placeholder"
        return None
    if code == 1:
        if output != SENTINEL:
            return "emit:partial-output"
        if not stderr.strip():
            return "emit:untyped-rejection"
        if PLACEHOLDER_CODE in stderr:
            return "emit:placeholder"
        return None
    return f"emit:exit-{code}"


def diagnostic_codes(stdout):
    """Non-skipped codes of a diagnostics report, or an empty set."""
    try:
        report = json.loads(stdout)
        return {d["code"] for d in report["diagnostics"]} - {"PREREQUISITE_SKIPPED"}
    except (ValueError, KeyError, TypeError):
        return set()


def disagreement(emit_code, diag_code, codes):
    """Emission and diagnostics must agree, except for diagnostics-only input limits
    (docs/diagnostics.md: 1024-character names, 256 files, aggregate bytes)."""
    if emit_code == diag_code:
        return None
    if emit_code == 0 and diag_code == 1 and codes == {"INPUT_LIMIT"}:
        return None
    return "mode-disagreement"


def classify_diagnostics(code, stdout, stderr):
    if code is None:
        return "diag:timeout"
    if any(m in stderr for m in CRASH_MARKERS):
        return "diag:internal-panic"
    if code not in (0, 1):
        return f"diag:exit-{code}"
    try:
        report = json.loads(stdout)
    except ValueError:
        return "diag:not-json"
    if not isinstance(report, dict) or report.get("kind") != "air2lean-check-diagnostics":
        return "diag:schema"
    expected = "checked" if code == 0 else "rejected"
    if report.get("status") != expected:
        return "diag:status-mismatch"
    diagnostics = report.get("diagnostics")
    if not isinstance(diagnostics, list):
        return "diag:schema"
    if any(not isinstance(d, dict) or d.get("code") not in CODES for d in diagnostics):
        return "diag:unknown-code"
    if code == 1 and not any(d.get("code") != "PREREQUISITE_SKIPPED" for d in diagnostics):
        return "diag:untyped-rejection"
    if any(d.get("code") == PLACEHOLDER_CODE for d in diagnostics):
        return "diag:placeholder"
    return None


def evaluate(binary, files, modes=("emit", "diag"), timeout=TIMEOUT):
    """Return (failure kind or None, observation dict)."""
    with tempfile.TemporaryDirectory(prefix="air2lean-q01-") as tmp:
        tmp = Path(tmp)
        air = _write(tmp, files)
        observed = {}
        failure = None
        if "emit" in modes:
            out = tmp / "Gen.lean"
            out.write_text(SENTINEL)
            code, _, stderr = _exec([str(binary), str(air), "-o", str(out), "--namespace", "Fuzz"], timeout)
            output = out.read_text(errors="replace") if out.exists() else ""
            observed["emit"] = code
            observed["emit_stderr"] = stderr.strip()[:300]
            failure = classify_emit(code, stderr, output)
        if failure is None and "diag" in modes:
            code, stdout, stderr = _exec([str(binary), "--diagnostics-json", str(air)], timeout)
            observed["diag"] = code
            failure = classify_diagnostics(code, stdout, stderr)
            if failure is None and "emit" in modes:
                failure = disagreement(observed["emit"], code, diagnostic_codes(stdout))
        return failure, observed


def shrink_case(binary, files, kind):
    """Reduce files to a minimal list that still produces `kind`."""
    modes = ("emit", "diag") if kind == "mode-disagreement" else (kind.split(":")[0],)

    def fails(candidate):
        return evaluate(binary, candidate, modes)[0] == kind

    files = ddmin(files, fails)
    for k in range(len(files)):
        try:
            doc = json.loads(files[k])
        except (ValueError, UnicodeDecodeError):
            doc = None
        if doc is not None:
            files[k] = _dump(shrink_json(doc, lambda d: fails(files[:k] + [_dump(d)] + files[k + 1:])))
        else:
            files[k] = shrink_bytes(files[k], lambda b: fails(files[:k] + [b] + files[k + 1:]))
    return files


# --- commands ----------------------------------------------------------------------------

def save_regression(directory, seed, kind, files, description):
    case = directory / f"seed-{seed}"
    if case.exists():
        shutil.rmtree(case)
    case.mkdir(parents=True)
    for k, data in enumerate(files):
        (case / f"{k:02d}.json").write_bytes(data)
    (case / "case.json").write_text(json.dumps(
        # expected_exit stays null until a fix decides the outcome; test_fuzz.py rejects null.
        {"seed": seed, "original_failure": kind, "expected_exit": None, "generator": description},
        indent=1) + "\n")
    return case


def cmd_run(args):
    binary = Path(args.binary).resolve(strict=True)
    corpus = load_corpus()
    vocab = _vocabulary(corpus)
    failures, outcomes = [], {}
    for seed in range(args.start, args.start + args.seeds):
        files, description = generate(seed, corpus, vocab)
        kind, observed = evaluate(binary, files)
        outcome = kind or f"ok:{observed.get('emit')}"
        outcomes[outcome] = outcomes.get(outcome, 0) + 1
        if kind is None:
            continue
        print(f"seed {seed}: {kind} ({description['origin']}; {description['steps']})", flush=True)
        shrunk = shrink_case(binary, files, kind) if args.shrink else files
        entry = {"seed": seed, "failure": kind, "generator": description,
                 "shrunk_bytes": sum(len(f) for f in shrunk)}
        if args.save:
            entry["fixture"] = str(save_regression(Path(args.save), seed, kind, shrunk, description))
        failures.append(entry)
    report = {"seeds": args.seeds, "start": args.start, "corpus": len(corpus),
              "outcomes": dict(sorted(outcomes.items())), "failures": failures}
    if args.report:
        Path(args.report).write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in ("seeds", "start", "corpus", "outcomes")}))
    print(f"{len(failures)} failing seeds")
    return 1 if failures else 0


def cmd_replay(args):
    binary = Path(args.binary).resolve(strict=True)
    cases = sorted(p for p in REGRESSIONS.iterdir() if p.is_dir()) if REGRESSIONS.is_dir() else []
    bad = 0
    for case in cases:
        meta = json.loads((case / "case.json").read_text())
        files = [p.read_bytes() for p in sorted(case.glob("[0-9][0-9].json"))]
        kind, observed = evaluate(binary, files)
        expected = meta.get("expected_exit")
        if kind is not None or (expected is not None and observed.get("emit") != expected):
            bad += 1
            print(f"{case.name}: {kind or 'exit'} {observed}")
    print(f"{len(cases) - bad}/{len(cases)} committed fuzz regressions pass the oracle")
    return 1 if bad else 0


def cmd_show(args):
    corpus = load_corpus()
    files, description = generate(args.seed, corpus, _vocabulary(corpus))
    print(json.dumps(description, indent=1))
    if args.out:
        out = Path(args.out)
        out.mkdir(parents=True, exist_ok=True)
        for k, data in enumerate(files):
            (out / f"{k:02d}.json").write_bytes(data)
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("run")
    run.add_argument("binary")
    run.add_argument("--seeds", type=int, default=200)
    run.add_argument("--start", type=int, default=0)
    run.add_argument("--save", help="write shrunk failures as regression directories here")
    run.add_argument("--report")
    run.add_argument("--no-shrink", dest="shrink", action="store_false")
    replay = sub.add_parser("replay")
    replay.add_argument("binary")
    show = sub.add_parser("show")
    show.add_argument("seed", type=int)
    show.add_argument("--out")
    args = parser.parse_args(argv)
    return {"run": cmd_run, "replay": cmd_replay, "show": cmd_show}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
