#!/usr/bin/env python3
"""C front-end coverage harness: C -> zig translate-c -> Zig -> AIR -> air2lean -> Lean.

  run.py heavy --out DIR [--files NAME ...] [--record FILE] [--no-build] [--defer-lean]
      Run every stage for the corpus (or the named files) and write the coverage record.
      Needs AIR2LEAN_ZIG_NATIVE (stock Zig 0.17.1), AIR2LEAN_ZIG_AIR (patched 0.17.1) and
      optionally AIR2LEAN_ZIG_NATIVE_0152 (stock 0.15.2, translate-c comparison only).
      Runs compilers and Lean sequentially; wrap the whole call in one scripts/build-guard.py.
      --defer-lean writes each Check.lean but leaves its elaboration to `run.py lean`.
  run.py lean --out DIR [--record FILE]
      Elaborate the deferred Check.lean files under DIR (Lean only) and rewrite the record.
  run.py check [--record FILE]
      Offline record check (CI): the record covers exactly the committed corpus with matching
      source hashes, its summary is recomputed from the per-file stages, and docs/c-frontend.md
      contains the generated tables verbatim. No compiler, translator or Lean run.
  run.py tables [--record FILE] [--write]
      Print the generated markdown tables (stage results and histograms); --write replaces
      them in docs/c-frontend.md.

Every corpus file defines `unsigned entry(unsigned a, unsigned b)`; it must be deterministic
and reset any state it uses (the C driver calls each input twice and compares). Expected
values come from the C program compiled natively by `zig cc` with UBSan traps. Stages:

  c_native     zig cc (host, -fsanitize=undefined trap): expected results per input
  translate_c  zig translate-c -target x86_64-linux-musl; warnings, demoted C functions
  zig_native   zig test of the translated Zig plus expectEqual against the C results
  air_export   patched Zig build-obj (x86_64-linux-musl -lc with Zig's libc as the module
               `zigc`, ReleaseSafe) with the AIR JSON filter
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
GENERATED = HERE / "generated-record.json"
DOC = ROOT / "docs" / "c-frontend.md"
sys.path[:0] = [str(HERE), str(ROOT / "tests" / "roadmap" / "fuzz")]
import cgen  # noqa: E402
from zig_gen import INPUTS, lean_checks  # noqa: E402  (Q01 inputs and #guard emitter)

SCHEMA = 1
TC_TARGET = "x86_64-linux-musl"
# The AIR is that of the program as `zig build-exe -OReleaseSafe -target x86_64-linux-musl -lc`
# compiles it. For a static musl target that compilation holds Zig's libc (`lib/c.zig`) as its
# module `zigc` (`src/Compilation.zig`: `zigc_strat == .zcu`, with `stack_check`,
# `stack_protector` and `no_builtin` set as below), so the libc functions that are Zig are
# translated from the same compilation as the program (`zigc_module`).
AIR_TARGET = ["-target", TC_TARGET, "-mcpu=baseline", "-lc"]
ZIGC_MODULE = ["-fno-stack-check", "-fno-stack-protector", "-fno-builtin"]
# std code that translate-c output calls is translated from its AIR like user code. The first
# export asks for these prefixes; `stage_air_export` adds the other std callees by name, and the
# libc functions by the symbols the program calls (the compilation's export table).
STD_FILTER = ["zig.c_translation."]
EXPORT_TABLE = "export-table.air2lean"
# The libc definitions are weak (`lib/c.zig` `symbol`): the translator binds them under premise
# EXT-07 (the image links no other definition of the symbol), which the header records.
LINK_PREMISES = ["--assume-weak-exports"]
# The translator runs in the allocator model the project is moving to (docs/allocator-model.md):
# translated C has no `std.mem.Allocator`, and only this mode admits the recovery of a typed
# pointer from `void *` (`?*anyopaque`), which it checks to be free of error storage.
ALLOCATOR_MODEL = ["--allocator-model", "translated"]
# Named gates (docs/c-frontend.md §Gates). A translate-c gate: its warning on a C function that
# it demoted to `extern fn`, so the program reaches the translator without that function.
TC_GATES = {
    "TC-GOTO": "TODO goto",
    "TC-BITFIELD": "has bitfield",
    "TC-VARIADIC-DEF": "unable to translate variadic function",
    "TC-COMPLEX-SWITCH": "TODO complex switch",
}
SETJMP_SYMBOLS = {"setjmp", "_setjmp", "sigsetjmp", "__sigsetjmp", "longjmp", "_longjmp", "siglongjmp"}
VARIADIC_EXTERN = re.compile(r"extern function '(\w+)' is variadic")
EXPORT_ROUNDS = 8 # export/closure rounds, as `project.py export`'s default `max_iterations`
# `Air2Lean/Air/Op.lean` `panicErrorFor?`: the safety-check handlers, modelled by the translator.
PANIC_PREFIX = "debug.FullPanic((function 'defaultPanic'))."
STAGES = ["c_native", "translate_c", "zig_native", "air_export", "air2lean", "lean"]
TIMEOUT = {"c": 300, "tc": 600, "zig": 900, "air": 900, "diag": 600, "emit": 900, "lean": 3600}
WARNING = re.compile(r"// (?P<loc>[^\n]*?:\d+:\d+): warning: (?P<msg>.*)$", re.M)
MISMATCH = re.compile(r"expected \d+, found \d+")
COMPILE_ERROR = re.compile(r"(\.zig:\d+:\d+: error:|error: undefined symbol)")
EXTERN_FN = re.compile(r"^pub extern fn (\w+)\(", re.M)
BODY = re.compile(r"^(?:pub )?(?:export )?fn \w+\([^\n]*\{$.*?^\}$", re.M | re.S)  # translated bodies

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


def module_name(stem):
    """The Zig root module of a translated corpus file. Not the bare stem: a root module named
    like a std file (`enums`, `linked_list`) shares its name prefix with std's own functions."""
    return "c_" + stem


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


SCRUBBED = []


def scrub(text):
    """Host-independent logs: the repository and home directories become placeholders."""
    for var in ("AIR2LEAN_ZIG_AIR", "AIR2LEAN_ZIG_NATIVE", "AIR2LEAN_ZIG_NATIVE_0152"):
        if os.environ.get(var):  # <prefix>/bin/zig or <prefix>/zig
            prefix = Path(os.environ[var]).parent
            text = text.replace(str(prefix.parent if prefix.name == "bin" else prefix), "$" + var)
    for path, name in SCRUBBED:  # the run's work directory (`cmd_heavy`)
        text = text.replace(path, name)
    return text.replace(str(ROOT), "$REPO").replace(str(Path.home()), "$HOME")


def tail(text, n=1500):
    text = scrub(text)
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
    # stdout must be a regular file: Zig (0.16, 0.17) copies its result to stdout with fcopyfile,
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
    bodies = "\n".join(m.group(0) for m in BODY.finditer(out))
    used = sorted(e for e in externs - set(demoted) if re.search(rf"\b{re.escape(e)}\(", bodies))
    record = {"status": "ok" if not demoted else "demoted", "lines": out.count("\n"),
              "warnings": warnings, "demoted_functions": demoted, "extern_calls": used}
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
    (work / "zig_native.log").write_text(out)
    if MISMATCH.search(out):
        status = "mismatch"
    elif COMPILE_ERROR.search(out):
        status = "compile_error"
    else:
        status = "runtime_error"  # a ReleaseSafe panic / signal of the translated program
    return {"status": status, "log": tail(out)}


def function_refs(doc, definitions):
    """Every function a function's AIR names: direct callees and function values, in the body
    and in the initial values of its globals (`{"func": <fully qualified name>}`), and the
    function that defines each extern symbol it names (`{"extern": <symbol>}`), if the
    compilation has one (`definitions`, from its export table)."""
    refs, stack = set(), [doc.get("body", []), doc.get("globals", [])]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if isinstance(node.get("func"), str):
                refs.add(node["func"])
            if isinstance(node.get("extern"), str):
                refs.update(definitions.get(node["extern"], ()))
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return refs


def symbol_definitions(air):
    """The functions that define each linker symbol in the exported compilation (its export
    table, docs/air-json.md §Export table), by symbol. Empty without a table. The translator
    decides which of them binds; the harness only exports them."""
    table = air / EXPORT_TABLE
    definitions = collections.defaultdict(set)
    if table.exists():
        for record in json.loads(table.read_text())["exports"]:
            if record["function"]:
                definitions[record["name"]].add(record["function"]["name"])
    return definitions


def zigc_module(zig_air):
    """The compiler's `lib/c.zig`: the root file of the module `zigc`."""
    code, out = run([zig_air, "env"], 60)
    found = re.search(r'\.lib_dir = "([^"]+)"', out)
    if code != 0 or not found:
        raise RuntimeError(f"zig env does not name lib_dir: {tail(out, 300)}")
    return Path(found.group(1)) / "c.zig"


def stage_air_export(zig_air, zig_file, module, work):
    """Export the C module's functions and the closure of what they reference (G6): the
    exporter's filter is a list of name prefixes, so each round adds the exact names of the
    referenced functions without AIR and exports again (the fixed point of
    docs/project-workflow.md §Dependency closure); afterwards every exported function that
    the C module does not reach (another instance sharing a prefix) is removed. An extern
    symbol references the function of the compilation that defines it, so the libc functions
    that are Zig (`AIR_TARGET`) join the closure like std callees. Panic handlers are the
    translator's own boundary and are never exported."""
    air = work / "air"
    prefixes, log = [module + "."] + STD_FILTER, ""
    command = [zig_air, "build-obj", "-fno-emit-bin", "-OReleaseSafe", "-fno-error-tracing", *AIR_TARGET,
               "--dep", "zigc", f"-Mroot={zig_file}", *ZIGC_MODULE, f"-Mzigc={zigc_module(zig_air)}"]
    for _ in range(EXPORT_ROUNDS):
        shutil.rmtree(air, ignore_errors=True)
        air.mkdir()
        env = dict(os.environ, ZIG_AIR_JSON_DIR=str(air), ZIG_AIR_JSON_FILTER=",".join(prefixes))
        code, out = run(command, TIMEOUT["air"], cwd=work, env=env)
        log += out
        (work / "air_export.log").write_text(log)
        files = sorted(air.glob("*.json"))
        incomplete = re.search(r"air2lean: (cannot open|name too long for a file|no JSON for|incomplete JSON for)", out)
        if code != 0 or incomplete or not files:
            return {"status": "failed", "files": len(files), "log": tail(out)}, None
        docs = {f: json.loads(f.read_text()) for f in files}
        definitions = symbol_definitions(air)
        refs = {doc.get("name", f.stem): function_refs(doc, definitions) for f, doc in docs.items()}
        reached = {n for n in refs if n.startswith(module + ".")}
        pending = sorted(reached)
        while pending:
            for callee in refs.get(pending.pop(), ()):
                if callee not in reached:
                    reached.add(callee)
                    pending.append(callee)
        missing = sorted(n for n in reached - set(refs) if not n.startswith(PANIC_PREFIX))
        if all(any(n.startswith(p) for p in prefixes) for n in missing):
            break  # nothing more to ask for: what is still missing has no AIR under its name
        prefixes += [n for n in missing if not any(n.startswith(p) for p in prefixes)]
    for f, doc in docs.items():
        if doc.get("name", f.stem) not in reached:
            f.unlink()
    exported = sorted(n for n in refs if n in reached)
    return {"status": "ok", "functions": len(exported), "filter": prefixes,
            "std_functions": [n for n in exported if not n.startswith(module + ".")],
            "unexported_callees": sorted(reached - set(refs))}, air


def stage_air2lean(binary, air):
    code, out = run([binary, "--diagnostics-json", str(air), "--diagnostic-limit", "256", *ALLOCATOR_MODEL,
                     *LINK_PREMISES], TIMEOUT["diag"])
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
                      "function": fn, "message": scrub(d.get("message") or "")[:400]})
    status = doc.get("status")
    return {"status": "checked" if status == "checked" and code == 0 else "rejected",
            "codes": dict(sorted(collections.Counter(i["code"] for i in items).items())),
            "diagnostics": items[:40], "diagnostic_count": len(items)}


def stage_lean(binary, air, stem, expected, work, defer=False):
    """Emit Gen.lean plus the #guard checks (Check.lean) and elaborate it. With `defer`, stop
    after writing Check.lean (status `deferred`): `run.py lean` elaborates it later, possibly
    on another host."""
    namespace = "CFront" + "".join(part.capitalize() for part in stem.split("_"))
    gen = work / "Gen.lean"
    code, out = run([binary, *ALLOCATOR_MODEL, *LINK_PREMISES, str(air), "-o", str(gen), "--namespace", namespace,
                     "--prefix", module_name(stem) + "."],
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
    if defer:
        return {"status": "deferred", "gen_lines": text.count("\n"), "check_sha256": sha256(check)}
    return elaborate(check, text.count("\n"))


def elaborate(check, gen_lines):
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    code, out = run(["lake", "env", "lean", str(check)], TIMEOUT["lean"], cwd=ROOT, env=env)
    (check.parent / "lean.log").write_text(out)
    if code == 0:
        return {"status": "ok", "gen_lines": gen_lines}
    status = "guard_failed" if "did not evaluate to `true`" in out else "elab_failed"
    return {"status": status, "log": tail(out)}


def run_file(stem, tools, out_dir, corpus=CORPUS, defer_lean=False):
    src = Path(corpus) / f"{stem}.c"
    work = out_dir / stem
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    default = ["generated" if stem.startswith("gen_") else "unclassified"]
    entry = {"source_sha256": sha256(src), "constructs": CONSTRUCTS.get(stem, default), "stages": {}}
    stages = entry["stages"]
    stages["c_native"], expected = stage_c_native(tools["native"], src, work)
    defined, undefined = c_symbols(tools["native"], src, work)
    entry["c_defined_functions"] = defined
    entry["libc_symbols"] = undefined
    stages["translate_c"], zig_file = stage_translate_c(tools["native"], src, work,
                                                        module_name(stem) + ".zig", defined)
    if tools.get("native_0152"):
        entry["translate_c_0.15.2"] = stage_translate_c(tools["native_0152"], src, work,
                                                        f"{stem}_0152.zig", defined)[0]
    if zig_file is None:
        return entry
    if expected is not None:
        stages["zig_native"] = stage_zig_native(tools["native"], zig_file, expected, work)
    stages["air_export"], air = stage_air_export(tools["air"], zig_file, module_name(stem), work)
    if air is None:
        return entry
    stages["air2lean"] = stage_air2lean(tools["air2lean"], air)
    if (stages["air2lean"]["status"] == "checked" and expected is not None
            and stages.get("zig_native", {}).get("status") == "ok"):
        stages["lean"] = stage_lean(tools["air2lean"], air, stem, expected, work, defer_lean)
    return entry


def gates(entry):
    """The named gates that reject the file (docs/c-frontend.md §Gates), each with the evidence
    in the stage records it is derived from."""
    s = entry["stages"]
    tc, found = s.get("translate_c", {}), []
    if tc.get("status") == "demoted":
        for gate, fragment in TC_GATES.items():
            hits = [w for w in tc.get("warnings", []) if fragment in w]
            if hits:
                found.append({"id": gate, "evidence": hits[0]})
    symbols = sorted(SETJMP_SYMBOLS & set(tc.get("extern_calls", [])))
    if symbols:
        found.append({"id": "LIBC-SETJMP", "evidence": ", ".join(symbols)})
    variadic = {m.group(1) for d in s.get("air2lean", {}).get("diagnostics", [])
                for m in VARIADIC_EXTERN.finditer(d["message"])} - set(tc.get("demoted_functions", []))
    if variadic:
        found.append({"id": "EXT-VARIADIC", "evidence": ", ".join(sorted(variadic))})
    native = s.get("zig_native", {}).get("status")
    if native in ("mismatch", "runtime_error"):
        found.append({"id": "NATIVE-DIVERGENCE", "evidence": native})
    return found


def outcome(entry):
    """`gated` for a file a named gate rejects, else the first failing stage (or 'lean_ok') —
    the file's single headline outcome."""
    result = stage_outcome(entry)
    return "gated" if result != "lean_ok" and entry.get("gates") else result


def stage_outcome(entry):
    s = entry["stages"]
    if s.get("c_native", {}).get("status") != "ok":
        return "c_native"
    if s.get("translate_c", {}).get("status") in ("failed", "demoted", None):
        return "translate_c"  # a demoted C function leaves the program incompletely translated
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
    by_code, by_construct = collections.Counter(), collections.defaultdict(collections.Counter)
    libc, zig_externs = collections.Counter(), collections.Counter()
    by_gate = collections.defaultdict(list)
    for stem, f in sorted(files.items()):
        for gate in f.get("gates", []):
            by_gate[gate["id"]].append(stem)
    for f in files.values():
        codes = f["stages"].get("air2lean", {}).get("codes", {})
        for code in codes:
            by_code[code] += 1
        result = outcome(f)
        for c in f["constructs"]:
            by_construct[c][result] += 1
        for sym in f.get("libc_symbols") or []:
            libc[sym] += 1
        for sym in f["stages"].get("translate_c", {}).get("extern_calls", []):
            zig_externs[sym] += 1
    return {"files": len(files), "stage_status": stage_counts, "headline": headline,
            "gates": dict(sorted(by_gate.items())),
            "rejection_codes_by_file": dict(sorted(by_code.items())),
            "outcome_by_construct": {k: dict(sorted(v.items())) for k, v in sorted(by_construct.items())},
            "libc_symbols": dict(sorted(libc.items())),
            "zig_extern_calls": dict(sorted(zig_externs.items()))}


# --- tables ------------------------------------------------------------------------------

def tables(record):
    files, summary = record["files"], record["summary"]
    lines = ["<!-- c-frontend tables: generated by tests/roadmap/c-frontend/run.py tables; do not edit -->",
             "", f"| file | C native | translate-c {record['tools']['zig_native']} | translate-c 0.15.2 | "
             "Zig native | AIR export | air2lean | Lean | codes | gates |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for stem, f in sorted(files.items()):
        s = f["stages"]
        cell = lambda st: s.get(st, {}).get("status", "–")  # noqa: E731
        tc = cell("translate_c")
        if s.get("translate_c", {}).get("demoted_functions"):
            tc += " (" + ", ".join(s["translate_c"]["demoted_functions"]) + ")"
        old = f.get("translate_c_0.15.2", {}).get("status", "–")
        codes = ", ".join(f"{k}×{v}" for k, v in s.get("air2lean", {}).get("codes", {}).items()) or "–"
        named = ", ".join(g["id"] for g in f.get("gates", [])) or "–"
        lines.append(f"| {stem} | {cell('c_native')} | {tc} | {old} | {cell('zig_native')} | "
                     f"{cell('air_export')} | {cell('air2lean')} | {cell('lean')} | {codes} | {named} |")
    lines += ["", "Headline outcome (`lean_ok` = translated and #guard-checked; `gated` = rejected by a "
              "named gate; else the first failing stage):", "", "| outcome | files |", "|---|---|"]
    lines += [f"| {k} | {v} |" for k, v in summary["headline"].items()]
    lines += ["", "Gates (files each named gate rejects):", "", "| gate | files |", "|---|---|"]
    lines += [f"| {k} | {', '.join(v)} |" for k, v in summary["gates"].items()]
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
        print("set AIR2LEAN_ZIG_NATIVE (stock 0.17.1) and AIR2LEAN_ZIG_AIR (patched 0.17.1)", file=sys.stderr)
        return 2
    if not args.no_build:
        code, out = run(["lake", "build", "ZigLean", "air2lean"], 10800, cwd=ROOT)
        if code != 0:
            print(tail(out, 4000), file=sys.stderr)
            return 1
    tools["air2lean"] = str(ROOT / ".lake" / "build" / "bin" / "air2lean")
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    SCRUBBED.append((str(out_dir), "$WORK"))
    record_path = Path(args.record)
    old = json.loads(record_path.read_text()) if record_path.exists() and args.files else None
    files = dict(old["files"]) if old else {}
    names = corpus_files(args.corpus)
    for stem in args.files or names:
        try:
            files[stem] = run_file(stem, tools, out_dir, args.corpus, args.defer_lean)
        except Exception as error:  # a harness bug must not lose the other files' results
            files[stem] = {"source_sha256": sha256(Path(args.corpus) / f"{stem}.c"),
                           "constructs": CONSTRUCTS.get(stem, ["unclassified"]),
                           "stages": {}, "harness_error": repr(error)[:500]}
        files[stem]["gates"] = gates(files[stem])
        print(f"{stem}: {outcome(files[stem])}", flush=True)
    files = {k: files[k] for k in sorted(files) if k in names}
    version = lambda z: run([z, "version"], 60)[1].strip() if z else None  # noqa: E731
    record = {"schema": SCHEMA, "kind": "air2lean-c-frontend-coverage",
              "inputs": INPUTS, "translate_c_target": TC_TARGET, "air_target": " ".join(AIR_TARGET),
              "std_filter": STD_FILTER, "allocator_model": ALLOCATOR_MODEL[1],
              "link_premises": LINK_PREMISES,
              "tools": {"zig_native": version(tools["native"]), "zig_air": version(tools["air"]),
                        "zig_native_0152": version(tools["native_0152"])},
              "files": files}
    record["summary"] = summarize(files)
    record_path.write_text(json.dumps(record, indent=1, sort_keys=False) + "\n")
    print(json.dumps(record["summary"]["headline"]))
    return 0


def cmd_lean(args):
    """Finish a `heavy --defer-lean` run: elaborate every deferred Check.lean under --out (the
    file the deferred stage hashed) and rewrite the record. Needs only Lean and the built
    ZigLean library, so it can run on a build host that has no patched compiler."""
    record_path, out_dir = Path(args.record), Path(args.out).resolve()
    record = json.loads(record_path.read_text())
    for stem, f in sorted(record["files"].items()):
        lean = f["stages"].get("lean", {})
        if lean.get("status") != "deferred":
            continue
        check = out_dir / stem / "Check.lean"
        if not check.exists() or sha256(check) != lean.get("check_sha256"):
            f["stages"]["lean"] = {"status": "elab_failed", "log": "deferred Check.lean missing or changed"}
        else:
            f["stages"]["lean"] = elaborate(check, lean["gen_lines"])
        print(f"{stem}: {outcome(f)}", flush=True)
    record["summary"] = summarize(record["files"])
    record_path.write_text(json.dumps(record, indent=1, sort_keys=False) + "\n")
    print(json.dumps(record["summary"]["headline"]))
    return 0


def check_generated(path):
    """The committed cgen.py record: every seed regenerates to the recorded source, its
    summary recomputes, and the doc states its headline."""
    if not path.exists():
        return [f"{path.relative_to(ROOT)} is missing"]
    record, errors = json.loads(path.read_text()), []
    for stem, f in record["files"].items():
        seed = int(stem.removeprefix("gen_s"))
        digest = hashlib.sha256(cgen.Gen(seed).program().encode()).hexdigest()
        if f["source_sha256"] != digest:
            errors.append(f"generated {stem}: cgen.py no longer produces the recorded program")
    if record.get("summary") != summarize(record["files"]):
        errors.append("generated record summary is stale")
    line = f"generated headline: {json.dumps(record['summary']['headline'], sort_keys=True)}"
    if DOC.exists() and line not in DOC.read_text():
        errors.append(f"docs/c-frontend.md does not state `{line}`")
    return errors


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
        if f.get("gates") != gates(f):
            errors.append(f"{stem}: recorded gates differ from the gates its stage records give")
        unknown = set(f["stages"]) - set(STAGES)
        if unknown:
            errors.append(f"{stem}: unknown stages {sorted(unknown)}")
        if f["stages"].get("lean", {}).get("status") == "ok" and f["stages"]["air2lean"]["status"] != "checked":
            errors.append(f"{stem}: Lean ok without an accepted translation")
    if record.get("summary") != summarize(record["files"]):
        errors.append("record summary is stale; regenerate it from the per-file stages")
    errors += check_generated(Path(args.generated))
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
    text = tables(json.loads(Path(args.record).read_text()))
    if not args.write:
        sys.stdout.write(text)
        return 0
    first, last = text.splitlines()[0], text.splitlines()[-1]
    doc = DOC.read_text()
    start, end = doc.find(first), doc.find(last)
    if start < 0 or end < start:
        print(f"{DOC.relative_to(ROOT)} has no generated tables block to replace", file=sys.stderr)
        return 1
    DOC.write_text(doc[:start] + text + doc[end + len(last) + 1:])
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
    heavy.add_argument("--defer-lean", action="store_true",
                       help="write Check.lean but leave its elaboration to `run.py lean`")
    for name in ("check", "tables", "lean"):
        p = sub.add_parser(name)
        p.add_argument("--record", default=str(RECORD))
    sub.choices["check"].add_argument("--generated", default=str(GENERATED))
    sub.choices["lean"].add_argument("--out", required=True, help="the heavy run's work directory")
    sub.choices["tables"].add_argument("--write", action="store_true",
                                       help="replace the generated tables in docs/c-frontend.md")
    args = parser.parse_args(argv)
    return {"heavy": cmd_heavy, "check": cmd_check, "tables": cmd_tables, "lean": cmd_lean}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
