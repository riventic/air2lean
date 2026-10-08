#!/usr/bin/env python3
"""C front-end coverage harness: C -> zig translate-c -> Zig -> AIR -> air2lean -> Lean.

  run.py heavy --out DIR [--files NAME ...] [--record FILE] [--no-build]
      Run every stage for the corpus (or the named files) and write the coverage record.
      Needs AIR2LEAN_ZIG_NATIVE (stock Zig 0.16.0), AIR2LEAN_ZIG_AIR (patched 0.16.0) and
      optionally AIR2LEAN_ZIG_NATIVE_0152 (stock 0.15.2, translate-c comparison only).
      Runs compilers and Lean sequentially; wrap the whole call in one scripts/build-guard.py.
  run.py check [--record FILE]
      Offline record check (CI): the record covers exactly the committed corpus with matching
      source hashes, its summary is recomputed from the per-file stages, and docs/c-frontend.md
      contains the generated tables verbatim. No compiler, translator or Lean run.
  run.py tables [--record FILE]
      Print the generated markdown tables (stage results and histograms).

Every corpus file defines `unsigned entry(unsigned a, unsigned b)`; it must be deterministic
and reset any state it uses (the C driver calls each input twice and compares). Expected
values come from the C program compiled natively by `zig cc` with UBSan traps. Stages:

  c_native     zig cc (host, -fsanitize=undefined trap): expected results per input
  translate_c  zig translate-c -target x86_64-linux-musl; warnings, demoted C functions
  zig_native   zig test of the translated Zig plus expectEqual against the C results
  air_export   patched Zig build-obj (x86_64-linux, ReleaseSafe) with the AIR JSON filter
  air2lean     air2lean --diagnostics-json; checked or rejected with diagnostic codes
  lean         emit Gen.lean, append the Q01 #guard checks of `entry`, elaborate with Lean
"""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CORPUS = HERE / "corpus"
RECORD = HERE / "record.json"
DOC = ROOT / "docs" / "c-frontend.md"
sys.path.insert(0, str(ROOT / "tests" / "roadmap" / "fuzz"))
from zig_gen import INPUTS, lean_checks  # noqa: E402  (Q01 inputs and #guard emitter)

SCHEMA = 1
TC_TARGET = "x86_64-linux-musl"
AIR_TARGET = ["-target", "x86_64-linux", "-mcpu=baseline"]
# std code that translate-c output calls is translated from its AIR like user code.
STD_FILTER = ["zig.c_translation."]
STAGES = ["c_native", "translate_c", "zig_native", "air_export", "air2lean", "lean"]
TIMEOUT = {"c": 300, "tc": 600, "zig": 900, "air": 900, "diag": 600, "emit": 900, "lean": 3600}
WARNING = re.compile(r"^// (?P<loc>[^\n]*?:\d+:\d+): warning: (?P<msg>.*)$", re.M)
EXTERN_FN = re.compile(r"^pub extern fn (\w+)\(", re.M)
BODY_FN = re.compile(r"^(?:pub )?(?:export )?fn (\w+)\(.*\{$", re.M)

# Construct families each corpus file targets (the histogram's "by C construct" axis).
CONSTRUCTS = {
    "arrays_2d": ["multi-dim arrays"],
    "bitfield_packet": ["bitfields", "libc string"],
    "bitfields": ["bitfields"],
    "bool_logic": ["short-circuit/_Bool"],
    "casts": ["integer casts", "object-representation casts"],
    "enums": ["enums", "switch"],
    "expressions": ["side-effecting expressions"],
    "float_basic": ["floating point"],
    "func_pointers": ["function pointers"],
    "globals": ["globals"],
    "goto_cleanup": ["goto"],
    "goto_state_machine": ["goto"],
    "hash_table": ["realistic", "structs+pointers"],
    "initializers": ["designated/compound initializers"],
    "inline_static": ["static inline"],
    "int_promotion": ["integer promotions"],
    "libc_stdio": ["libc stdio", "variadic call"],
    "libc_stdlib": ["libc stdlib", "function pointers"],
    "libc_string": ["libc string"],
    "linked_list": ["realistic", "structs+pointers"],
    "loops": ["loops/break/continue"],
    "macros": ["macros"],
    "malloc_vec": ["libc stdlib", "realistic"],
    "memcpy_loops": ["realistic", "void* byte loops"],
    "ptr_arith": ["pointer arithmetic"],
    "ptr_int_casts": ["pointer<->integer casts"],
    "recursion": ["recursion"],
    "ring_buffer": ["realistic", "structs+pointers"],
    "setjmp_longjmp": ["setjmp/longjmp"],
    "signed_ops": ["signed arithmetic"],
    "sort_callback": ["realistic", "function pointers", "void* byte loops"],
    "static_locals": ["static locals"],
    "string_literals": ["string literals"],
    "strings_loops": ["realistic", "pointer arithmetic"],
    "struct_layout": ["struct layout"],
    "switch_fallthrough": ["switch fallthrough"],
    "switch_simple": ["switch"],
    "unions": ["unions"],
    "varargs_sum": ["variadic definition"],
    "wide_ints": ["64-bit arithmetic"],
}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def corpus_files(corpus=CORPUS):
    return sorted(p.stem for p in Path(corpus).glob("*.c"))


def run(cmd, timeout, cwd=None, env=None):
    """Run cmd; return (code, combined output). Timeouts and missing tools are code -1."""
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=timeout, text=True, errors="replace")
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        return -1, out + f"\n[timeout after {timeout}s]"
    except OSError as e:
        return -1, str(e)


def tail(text, n=1500):
    return text if len(text) <= n else "..." + text[-n:]


# --- stages ------------------------------------------------------------------------------

def driver_source():
    calls = "\n".join(f"    {{ unsigned r1 = entry({a}u, {b}u), r2 = entry({a}u, {b}u); "
                      f'printf("%u %u\\n", r1, r2); }}' for a, b in INPUTS)
    return ("#include <stdio.h>\nunsigned entry(unsigned a, unsigned b);\n"
            f"int main(void) {{\n{calls}\n    return 0;\n}}\n")


def stage_c_native(zig, src, work):
    (work / "driver.c").write_text(driver_source())
    exe = work / "c_native"
    code, out = run([zig, "cc", "-std=c11", "-O0", "-g0", "-fsanitize=undefined",
                     "-fsanitize-trap=undefined", str(src), str(work / "driver.c"), "-o", str(exe)],
                    TIMEOUT["c"])
    if code != 0:
        return {"status": "compile_error", "log": tail(out)}, None
    code, out = run([str(exe)], TIMEOUT["c"])
    if code != 0:
        return {"status": "runtime_error", "exit": code, "log": tail(out)}, None
    values = []
    for line in out.split():
        values.append(int(line))
    pairs = list(zip(values[0::2], values[1::2]))
    if len(pairs) != len(INPUTS):
        return {"status": "runtime_error", "log": tail(out)}, None
    if any(x != y for x, y in pairs):
        return {"status": "nondeterministic", "results": pairs}, None
    expected = [x for x, _ in pairs]
    return {"status": "ok", "expected": expected}, expected


def c_symbols(zig, src, work):
    """Defined and undefined symbols of the C object for the AIR target (no sanitizers)."""
    obj = work / "c_target.o"
    code, out = run([zig, "cc", "-target", TC_TARGET, "-std=c11", "-O0", "-g0", "-fno-sanitize=all",
                     "-fno-stack-protector", "-c", str(src), "-o", str(obj)], TIMEOUT["c"])
    if code != 0:
        return None, None
    nm = shutil.which("nm") or "nm"
    code, out = run([nm, str(obj)], 60)
    if code != 0:
        return None, None
    defined, undefined = set(), set()
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == "U":
            undefined.add(parts[1])
        elif len(parts) == 3 and parts[1] in ("T", "t"):
            defined.add(parts[2])
    return sorted(defined), sorted(undefined)


def stage_translate_c(zig, src, work, out_name, defined):
    zig_file = work / out_name
    # stdout must be a regular file: Zig 0.16 copies its result to stdout with fcopyfile,
    # which spins forever when stdout is a pipe on macOS 27.
    try:
        with open(zig_file, "w") as stdout:
            p = subprocess.run([zig, "translate-c", "-target", TC_TARGET, "-lc", str(src)], stdout=stdout,
                               stderr=subprocess.PIPE, timeout=TIMEOUT["tc"], text=True, errors="replace")
        code, err = p.returncode, p.stderr
    except subprocess.TimeoutExpired:
        code, err = -1, f"[timeout after {TIMEOUT['tc']}s]"
    if code != 0:
        return {"status": "failed", "log": tail(err)}, None
    out = zig_file.read_text()
    warnings = sorted({re.sub(r"^.*/", "", m["loc"]) + ": " + m["msg"] for m in WARNING.finditer(out)
                       if str(src.name) in m["loc"]})
    externs = set(EXTERN_FN.findall(out))
    demoted = sorted(f for f in (defined or []) if f in externs)
    record = {"status": "ok" if not demoted else "demoted", "lines": out.count("\n"),
              "warnings": warnings, "demoted_functions": demoted}
    return record, zig_file


def stage_zig_native(zig, zig_file, expected, work):
    test_file = work / (zig_file.stem + "_native.zig")
    checks = "\n".join(f"    try std.testing.expectEqual(@as(c_uint, {v}), entry({a}, {b}));"
                       for (a, b), v in zip(INPUTS, expected))
    test_file.write_text(zig_file.read_text() +
                         f'\ntest "c_frontend_native" {{\n    const std = @import("std");\n{checks}\n}}\n')
    code, out = run([zig, "test", str(test_file), "-OReleaseSafe", "-lc"], TIMEOUT["zig"], cwd=work)
    if code == 0:
        return {"status": "ok"}
    if "expected " in out and ", found " in out:
        status = "mismatch"
    elif "error:" in out and ("All 1 tests passed" not in out) and ("panic" not in out.lower()):
        status = "compile_error"
    else:
        status = "runtime_error"
    return {"status": status, "log": tail(out)}


def stage_air_export(zig_air, zig_file, stem, work):
    air = work / "air"
    shutil.rmtree(air, ignore_errors=True)
    air.mkdir()
    env = dict(os.environ, ZIG_AIR_JSON_DIR=str(air), ZIG_AIR_JSON_FILTER=",".join([stem + "."] + STD_FILTER))
    code, out = run([zig_air, "build-obj", "-fno-emit-bin", "-OReleaseSafe", "-fno-error-tracing",
                     *AIR_TARGET, str(zig_file)], TIMEOUT["air"], cwd=work, env=env)
    files = sorted(air.glob("*.json"))
    incomplete = re.search(r"air2lean: (cannot open|name too long for a file|no JSON for|incomplete JSON for)", out)
    if code != 0 or incomplete or not files:
        return {"status": "failed", "files": len(files), "log": tail(out)}, None
    callees, names = set(), set()
    for f in files:
        doc = json.loads(f.read_text())
        names.add(doc.get("name", f.stem))
        stack = [doc.get("body", [])]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                callee = node.get("callee")
                if isinstance(callee, dict) and isinstance(callee.get("func"), str):
                    callees.add(callee["func"])
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)
    external = sorted(c for c in callees - names)
    std = sorted(n for n in names if not n.startswith(stem + "."))
    return {"status": "ok", "functions": len(files), "std_functions": std,
            "unexported_callees": external}, air


def stage_air2lean(binary, air):
    code, out = run([binary, "--diagnostics-json", str(air), "--diagnostic-limit", "256"], TIMEOUT["diag"])
    try:
        doc = json.loads(out)
    except ValueError:
        return {"status": "crash", "exit": code, "log": tail(out)}
    items = []
    for d in doc.get("diagnostics", []):
        fn = d.get("function")
        if isinstance(fn, dict):
            fn = fn.get("name") or fn.get("identity") or json.dumps(fn, sort_keys=True)
        items.append({"code": d.get("code"), "phase": d.get("phase"), "category": d.get("category"),
                      "function": fn, "message": (d.get("message") or "")[:400]})
    status = doc.get("status")
    return {"status": "checked" if status == "checked" and code == 0 else "rejected",
            "codes": dict(sorted(collections.Counter(i["code"] for i in items).items())),
            "diagnostics": items[:40], "diagnostic_count": len(items)}


def stage_lean(binary, air, stem, expected, work):
    namespace = "CFront" + "".join(part.capitalize() for part in stem.split("_"))
    gen = work / "Gen.lean"
    code, out = run([binary, str(air), "-o", str(gen), "--namespace", namespace, "--prefix", stem + "."],
                    TIMEOUT["emit"])
    if code != 0 or not gen.exists():
        return {"status": "emit_failed", "log": tail(out)}
    text = gen.read_text()
    try:
        guards = lean_checks(text, namespace, expected)
    except ValueError as e:
        return {"status": "no_entry", "log": str(e)}
    check = work / "Check.lean"
    check.write_text(text + guards)
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    code, out = run(["lake", "env", "lean", str(check)], TIMEOUT["lean"], cwd=ROOT, env=env)
    if code == 0:
        return {"status": "ok", "gen_lines": text.count("\n")}
    status = "guard_failed" if "#guard" in out or "guard" in out.split("error", 1)[-1][:200] else "elab_failed"
    return {"status": status, "log": tail(out)}


def run_file(stem, tools, out_dir, corpus=CORPUS):
    src = Path(corpus) / f"{stem}.c"
    work = out_dir / stem
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    entry = {"source_sha256": sha256(src), "constructs": CONSTRUCTS.get(stem, ["generated" if stem.startswith("gen_") else "unclassified"]),
             "stages": {}}
    stages = entry["stages"]
    stages["c_native"], expected = stage_c_native(tools["native"], src, work)
    defined, undefined = c_symbols(tools["native"], src, work)
    entry["c_defined_functions"] = defined
    entry["libc_symbols"] = undefined
    stages["translate_c"], zig_file = stage_translate_c(tools["native"], src, work, f"{stem}.zig", defined)
    if tools.get("native_0152"):
        entry["translate_c_0.15.2"] = stage_translate_c(tools["native_0152"], src, work,
                                                        f"{stem}_0152.zig", defined)[0]
    if zig_file is None:
        return entry
    if expected is not None:
        stages["zig_native"] = stage_zig_native(tools["native"], zig_file, expected, work)
    stages["air_export"], air = stage_air_export(tools["air"], zig_file, stem, work)
    if air is None:
        return entry
    stages["air2lean"] = stage_air2lean(tools["air2lean"], air)
    if (stages["air2lean"]["status"] == "checked" and expected is not None
            and stages.get("zig_native", {}).get("status") == "ok"):
        stages["lean"] = stage_lean(tools["air2lean"], air, stem, expected, work)
    return entry


def outcome(entry):
    """First failing stage (or 'lean_ok') — the file's single headline outcome."""
    s = entry["stages"]
    if s.get("c_native", {}).get("status") != "ok":
        return "c_native"
    if s.get("translate_c", {}).get("status") == "failed":
        return "translate_c"
    if s.get("air_export", {}).get("status") != "ok":
        return "air_export" if "air_export" in s else "translate_c"
    if s.get("air2lean", {}).get("status") != "checked":
        return "air2lean"
    if s.get("zig_native", {}).get("status") != "ok":
        return "zig_native"
    if s.get("lean", {}).get("status") != "ok":
        return "lean"
    return "lean_ok"


def summarize(files):
    stage_counts = {st: dict(sorted(collections.Counter(
        f["stages"][st]["status"] for f in files.values() if st in f["stages"]).items())) for st in STAGES}
    headline = dict(sorted(collections.Counter(outcome(f) for f in files.values()).items()))
    by_code, by_construct, libc = collections.Counter(), collections.defaultdict(collections.Counter), collections.Counter()
    for f in files.values():
        codes = f["stages"].get("air2lean", {}).get("codes", {})
        for code in codes:
            by_code[code] += 1
        result = outcome(f)
        for c in f["constructs"]:
            by_construct[c][result] += 1
        for sym in f.get("libc_symbols") or []:
            libc[sym] += 1
    return {"files": len(files), "stage_status": stage_counts, "headline": headline,
            "rejection_codes_by_file": dict(sorted(by_code.items())),
            "outcome_by_construct": {k: dict(sorted(v.items())) for k, v in sorted(by_construct.items())},
            "libc_symbols": dict(sorted(libc.items()))}


# --- tables ------------------------------------------------------------------------------

def tables(record):
    files, summary = record["files"], record["summary"]
    lines = ["<!-- c-frontend tables: generated by tests/roadmap/c-frontend/run.py tables; do not edit -->",
             "", "| file | C native | translate-c 0.16 | translate-c 0.15.2 | Zig native | AIR export | air2lean | Lean | codes |",
             "|---|---|---|---|---|---|---|---|---|"]
    for stem, f in sorted(files.items()):
        s = f["stages"]
        cell = lambda st: s.get(st, {}).get("status", "–")  # noqa: E731
        tc = cell("translate_c")
        if s.get("translate_c", {}).get("demoted_functions"):
            tc += " (" + ", ".join(s["translate_c"]["demoted_functions"]) + ")"
        old = f.get("translate_c_0.15.2", {}).get("status", "–")
        codes = ", ".join(f"{k}×{v}" for k, v in s.get("air2lean", {}).get("codes", {}).items()) or "–"
        lines.append(f"| {stem} | {cell('c_native')} | {tc} | {old} | {cell('zig_native')} | "
                     f"{cell('air_export')} | {cell('air2lean')} | {cell('lean')} | {codes} |")
    lines += ["", "Headline outcome (first failing stage; `lean_ok` = translated and #guard-checked):", "",
              "| outcome | files |", "|---|---|"]
    lines += [f"| {k} | {v} |" for k, v in summary["headline"].items()]
    lines += ["", "Rejection histogram (files whose diagnostics contain the code):", "",
              "| code | files |", "|---|---|"]
    lines += [f"| {k} | {v} |" for k, v in summary["rejection_codes_by_file"].items()]
    lines += ["", "Outcome by C construct family:", "", "| construct | outcomes |", "|---|---|"]
    lines += [f"| {k} | " + ", ".join(f"{o}: {n}" for o, n in v.items()) + " |"
              for k, v in summary["outcome_by_construct"].items()]
    lines += ["", "<!-- end c-frontend tables -->"]
    return "\n".join(lines) + "\n"


# --- commands ----------------------------------------------------------------------------

def cmd_heavy(args):
    tools = {"native": os.environ.get("AIR2LEAN_ZIG_NATIVE"), "air": os.environ.get("AIR2LEAN_ZIG_AIR"),
             "native_0152": os.environ.get("AIR2LEAN_ZIG_NATIVE_0152")}
    if not tools["native"] or not tools["air"]:
        print("set AIR2LEAN_ZIG_NATIVE (stock 0.16.0) and AIR2LEAN_ZIG_AIR (patched 0.16.0)", file=sys.stderr)
        return 2
    if not args.no_build:
        code, out = run(["lake", "build", "ZigLean", "air2lean"], 10800, cwd=ROOT)
        if code != 0:
            print(tail(out, 4000), file=sys.stderr)
            return 1
    tools["air2lean"] = str(ROOT / ".lake" / "build" / "bin" / "air2lean")
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    record_path = Path(args.record)
    old = json.loads(record_path.read_text()) if record_path.exists() and args.files else None
    files = dict(old["files"]) if old else {}
    names = corpus_files(args.corpus)
    for stem in args.files or names:
        try:
            files[stem] = run_file(stem, tools, out_dir, args.corpus)
        except Exception as error:  # a harness bug must not lose the other files' results
            files[stem] = {"source_sha256": sha256(Path(args.corpus) / f"{stem}.c"),
                           "constructs": CONSTRUCTS.get(stem, ["generated"]),
                           "stages": {}, "harness_error": repr(error)[:500]}
        print(f"{stem}: {outcome(files[stem])}", flush=True)
    files = {k: files[k] for k in sorted(files) if k in names}
    version = lambda z: run([z, "version"], 60)[1].strip() if z else None  # noqa: E731
    record = {"schema": SCHEMA, "kind": "air2lean-c-frontend-coverage",
              "inputs": INPUTS, "translate_c_target": TC_TARGET, "air_target": " ".join(AIR_TARGET),
              "std_filter": STD_FILTER,
              "tools": {"zig_native": version(tools["native"]), "zig_air": version(tools["air"]),
                        "zig_native_0152": version(tools["native_0152"])},
              "files": files}
    record["summary"] = summarize(files)
    record_path.write_text(json.dumps(record, indent=1, sort_keys=False) + "\n")
    print(json.dumps(record["summary"]["headline"]))
    return 0


def cmd_check(args):
    record = json.loads(Path(args.record).read_text())
    errors = []
    if record.get("schema") != SCHEMA or record.get("kind") != "air2lean-c-frontend-coverage":
        errors.append("unexpected record schema/kind")
    if record.get("inputs") != [list(x) for x in INPUTS]:
        errors.append("record inputs differ from tests/roadmap/fuzz/zig_gen.py INPUTS")
    names = corpus_files()
    if sorted(record["files"]) != names:
        errors.append(f"record files {sorted(record['files'])} != corpus {names}")
    for stem in names:
        f = record["files"].get(stem)
        if f is None:
            continue
        if f["source_sha256"] != sha256(CORPUS / f"{stem}.c"):
            errors.append(f"{stem}: corpus source changed since the record; rerun run.py heavy --files {stem}")
        if stem not in CONSTRUCTS or f["constructs"] != CONSTRUCTS[stem]:
            errors.append(f"{stem}: construct classification differs from run.py CONSTRUCTS")
        unknown = set(f["stages"]) - set(STAGES)
        if unknown:
            errors.append(f"{stem}: unknown stages {sorted(unknown)}")
        if f["stages"].get("lean", {}).get("status") == "ok" and f["stages"]["air2lean"]["status"] != "checked":
            errors.append(f"{stem}: Lean ok without an accepted translation")
    if record.get("summary") != summarize(record["files"]):
        errors.append("record summary is stale; regenerate it from the per-file stages")
    if DOC.exists():
        if tables(record) not in DOC.read_text():
            errors.append("docs/c-frontend.md does not contain the current generated tables (run.py tables)")
    else:
        errors.append("docs/c-frontend.md is missing")
    for e in errors:
        print("error:", e, file=sys.stderr)
    if not errors:
        print(f"c-frontend record ok: {len(names)} files, headline {record['summary']['headline']}")
    return 1 if errors else 0


def cmd_tables(args):
    sys.stdout.write(tables(json.loads(Path(args.record).read_text())))
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    heavy = sub.add_parser("heavy")
    heavy.add_argument("--out", required=True)
    heavy.add_argument("--files", nargs="*")
    heavy.add_argument("--record", default=str(RECORD))
    heavy.add_argument("--no-build", action="store_true")
    heavy.add_argument("--corpus", default=str(CORPUS), help="directory of .c files (default: corpus/)")
    for name in ("check", "tables"):
        p = sub.add_parser(name)
        p.add_argument("--record", default=str(RECORD))
    args = parser.parse_args(argv)
    return {"heavy": cmd_heavy, "check": cmd_check, "tables": cmd_tables}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
