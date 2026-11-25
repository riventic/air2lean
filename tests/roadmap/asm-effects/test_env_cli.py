#!/usr/bin/env python3
"""CLI regressions for A01's environment reads, memory inputs and memory-region contracts.

`air-env/<version>` are fresh exports of `asm_env.zig` (exports.json). The 0.17.1 translation
is the retained `AsmEnv/Gen.lean`; 0.16.0 and 0.15.2 translate to the same text apart from the
profile header. Mutations outside the reviewed allowlist entries (`Air2Lean/AsmAllowlist.lean`)
are rejected, and a device contract that declares `rdtsc` keeps it a device event (L13).
Never builds or invokes compilers.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ARGS = ["--namespace", "AsmEnv", "--prefix", "asm_env.", "--profile", "abi64-le-v1"]
TSC = HERE.parent / "volatile-effects" / "tsc.json"


def load(version):
    return {p.name: json.loads(p.read_text()) for p in sorted((HERE / "air-env" / version).glob("*.json"))}


def run(binary, documents, extra=()):
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-env-") as d:
        air = Path(d) / "air"
        air.mkdir()
        for name, document in documents.items():
            (air / name).write_text(json.dumps(document))
        out = Path(d) / "Gen.lean"
        out.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS, *extra], text=True,
                                capture_output=True, check=False, timeout=120)
        return result, out.read_text()


def body(text):
    return "\n".join(text.splitlines()[1:])


def asm_inst(doc):
    stack = list(doc["body"])
    while stack:
        i = stack.pop()
        if i["tag"] == "assembly":
            return i
        for k in ("body", "then", "else"):
            stack.extend(i.get(k, []))
    raise AssertionError("no assembly")


def reject(binary, docs, name, mutate, marker):
    docs = json.loads(json.dumps(docs))
    mutate(asm_inst(docs[name]), docs[name])
    result, text = run(binary, {name: docs[name]})
    assert result.returncode == 1 and text == "sentinel\n", (name, marker, result.stderr)
    assert marker in result.stderr, (marker, result.stderr)
    return 1


def main(binary):
    checks = 0
    retained = (HERE / "AsmEnv" / "Gen.lean").read_text()
    for version in ("0.17.1", "0.16.0", "0.15.2"):
        result, text = run(binary, load(version))
        assert result.returncode == 0, (version, result.stderr)
        if version == "0.17.1":
            assert text == retained, "AsmEnv/Gen.lean is not the fresh 0.17.1 translation"
        assert body(text) == body(retained), version
        checks += 1
    docs = load("0.17.1")
    # Environment reads are oracle queries, never opaques; region contracts read and write.
    for token in ("Zig.Asm.envWord 64", "Zig.Asm.readRegion", "Zig.Asm.writeRegion", "Zig.Asm.movePtr"):
        assert token in retained, token
        checks += 1
    # A pointer operand whose block no allowlisted region names.
    checks += reject(binary, docs, "asm_env.fill.json",
                     lambda i, _: i.update(source="rep stosw"), "nor an allowlist entry declares its memory regions")
    # A `memory` clobber with pointer operands needs the region entry: dropping it is another block.
    checks += reject(binary, docs, "asm_env.copy.json",
                     lambda i, _: i.update(clobbers=[]), "nor a read-write pointer that an allowlisted memory region uses")
    # The region's base must be read-write: a write-only pointer output would make a pointer.
    def write_only(i, _):
        i["outputs"][0]["constraint"] = "={rdi}"
    checks += reject(binary, docs, "asm_env.fill.json", write_only,
                     "nor an allowlist entry declares its memory regions")
    # A memory clobber on an entry without regions stays rejected.
    def clobber(i, _):
        i["clobbers"] = ["cc", "memory"]
    checks += reject(binary, docs, "asm_env.random.json", clobber, "'memory' clobber is outside the subset")
    # An `m` input of a pointer (the operand itself, not a value) is no memory-value input.
    def ptr_input(i, d):
        i["inputs"][0]["ref"] = {"inst": 0}
    checks += reject(binary, docs, "asm_env.loadm.json", ptr_input, "not an integer register value")
    # A write region through a const pointer, and a count narrower than rcx.
    def alloc_child(d, ref):
        alloc = next(i for i in d["body"] if i["id"] == ref["inst"])
        return d["types"][alloc["ty"]]["child"]
    def const_base(i, d):
        d["types"][alloc_child(d, i["outputs"][0]["ref"])]["const"] = True
    checks += reject(binary, docs, "asm_env.fill.json", const_base, "writes through a const pointer")
    def narrow_count(i, d):
        d["types"].append({"k": "int", "signed": False, "bits": 32, "abi_size": 4, "abi_align": 4})
        alloc = next(x for x in d["body"] if x["id"] == i["outputs"][1]["ref"]["inst"])
        ptr = dict(d["types"][alloc["ty"]], child=len(d["types"]) - 1)
        d["types"].append(ptr)
        alloc["ty"] = len(d["types"]) - 1
    checks += reject(binary, docs, "asm_env.fill.json", narrow_count, "64-bit integer operand")
    # The noalias analysis does not see region accesses: no regions next to noalias parameters.
    def noalias(i, d):
        d["noalias"] = [0]
    checks += reject(binary, docs, "asm_env.fill.json", noalias, "noalias")
    # A device contract that declares the rdtsc template keeps it a device event (L13).
    result, text = run(binary, {k: v for k, v in docs.items() if k in ("asm_env.ticks.json", "asm_env.elapsed.json")},
                       ("--device-contract", str(TSC)))
    assert result.returncode == 0, result.stderr
    assert "Zig.vasm air2lean_device" in text and "Zig.Asm.envWord" not in text, text
    checks += 1
    checks += check_cpu_features(binary, docs)
    checks += check_isa_coverage(binary, retained)
    print(f"{checks} asm environment/region CLI checks passed")


def check_isa_coverage(binary, retained):
    """A02 decision 1: an allowlist entry is a defined function over the instruction model
    (`isa`, premise ASM-07) exactly when the model covers its block; only an uncovered entry
    stays uninterpreted (`opaque`, premises ASM-01/02) (`--print-asm-isa-table`)."""
    table = json.loads(subprocess.run([str(binary), "--print-asm-isa-table"], text=True, capture_output=True,
                                      check=True, timeout=60).stdout)
    assert table["model"] == "ZigLean/Isa/X86.lean" and table["allowlist"], table
    for entry in table["allowlist"]:
        assert entry["covered"] == (entry["semantics"] == "isa"), entry
        assert ("reason" in entry) != entry["covered"], entry
    by_semantics = {}
    for entry in table["allowlist"]:
        by_semantics.setdefault(entry["semantics"], []).append(entry["template"])
    assert by_semantics["opaque"] == ["rep stosb", "rep movsb"], by_semantics
    assert len(by_semantics["isa"]) == 12, by_semantics
    # The retained translation: the two region blocks are the only uninterpreted functions; the
    # memory-value input (`movq %[x], %[ret]`) is a definition with its footprint theorem.
    opaques = [line for line in retained.splitlines() if line.startswith("opaque ")]
    assert len(opaques) == 2 and all(line.startswith("opaque airAsmFx_") for line in opaques), opaques
    assert retained.count(".check = none := by decide") == 1 and "def airIsa_" in retained, retained
    return 3


def header(text):
    return json.loads(text.splitlines()[0].split("-- air2lean-profile: ", 1)[1])


def check_cpu_features(binary, docs):
    """The CPU features of asm instructions come from the profile (A02 decision D1, premise
    ASM-09; `Air2Lean/AsmFeatures.lean`, `checkAsmCpuFeatures`)."""
    checks = 0
    assume = "--assume-asm-cpu-features"
    # `rdrand` needs `rdrnd`. With the feature in `profile.features` the block translates (the
    # retained translation above, whose header has no admission); without it the block is
    # rejected by instruction and feature; the admission of exactly that feature accepts it and
    # the header records the admission and the feature.
    assert "admission" not in header((HERE / "AsmEnv" / "Gen.lean").read_text())
    for name in ("asm_env.random.json", "asm_env.rand64.json"):
        bare = json.loads(json.dumps(docs[name]))
        bare["profile"]["features"].remove("rdrnd")
        result, text = run(binary, {name: bare})
        assert result.returncode == 1 and text == "sentinel\n", (name, result.stderr)
        assert "instruction 'rdrand' needs the CPU feature(s) [rdrnd]" in result.stderr, result.stderr
        assert "ASM-09" in result.stderr and f"{assume} rdrnd" in result.stderr, result.stderr
        # Another feature admits nothing here.
        result, text = run(binary, {name: bare}, (assume, "lzcnt,popcnt"))
        assert result.returncode == 1 and text == "sentinel\n" and "[rdrnd]" in result.stderr, result.stderr
        result, text = run(binary, {name: bare}, (assume, "rdrnd"))
        assert result.returncode == 0, result.stderr
        record = header(text)
        assert record["admission"] == "asm-cpu-features" and record["asm_cpu_features"] == ["rdrnd"], record
        checks += 3
    # The documented counterexample: `lzcnt` at a CPU without LZCNT runs as `bsr` (lzcnt(1) = 63,
    # bsr(1) = 0; tests/roadmap/asm-semantics/expected_x86_64.txt), so the model's value would
    # be wrong there. Rejected on the legacy profile (it lists no feature) and on the baseline
    # x86_64 CPU; accepted when the profile's CPU has `lzcnt`, or under the admission.
    golden = HERE.parent.parent / "golden/asm/air"
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-lzcnt-") as d:
        air = Path(d) / "air"
        air.mkdir()
        out = Path(d) / "Gen.lean"
        (air / "asm.lzcnt64.json").write_bytes((golden / "asm.lzcnt64.json").read_bytes())
        base = [str(binary), str(air), "-o", str(out), "--namespace", "L", "--prefix", "asm."]
        def translate(*extra):
            return subprocess.run([*base, *extra], text=True, capture_output=True, check=False, timeout=60)
        legacy = ("--profile", "legacy-abi64-le")
        result = translate(*legacy)
        assert result.returncode == 1 and not out.exists(), result.stderr
        assert "instruction 'lzcnt' needs the CPU feature(s) [lzcnt]" in result.stderr, result.stderr
        result = translate(*legacy, assume, "popcnt,lzcnt,popcnt")
        assert result.returncode == 0, result.stderr
        record = header(out.read_text())
        # Sorted, without duplicates.
        assert record["admission"] == "asm-cpu-features" and record["asm_cpu_features"] == ["lzcnt", "popcnt"], record
        checks += 2
        # The same instruction under a schema-12 profile (the `loadm` export with its block
        # replaced by the allowlisted `lzcnt` entry): the baseline CPU, one with `lzcnt`, and one
        # with other bit-manipulation features only.
        document = json.loads(json.dumps(docs["asm_env.loadm.json"]))
        block = asm_inst(document)
        block.update(source="lzcnt %[x], %[ret]", clobbers=["cc"])
        block["inputs"][0]["constraint"] = "r"
        baseline = [f for f in document["profile"]["features"] if f != "rdrnd"]
        for extra, accepted in (([], False), (["lzcnt"], True), (["popcnt", "bmi"], False)):
            document["profile"]["features"] = baseline + extra
            result, text = run(binary, {"asm_env.loadm.json": document})
            if accepted:
                assert result.returncode == 0 and "admission" not in header(text), result.stderr
                assert "def airIsa_" in text and "opaque" not in text, text
            else:
                assert result.returncode == 1 and text == "sentinel\n", result.stderr
                assert "instruction 'lzcnt' needs the CPU feature(s) [lzcnt]" in result.stderr, result.stderr
                assert "the profile's CPU 'x86_64' on target 'x86_64' does not list" in result.stderr, result.stderr
            checks += 1
        # The admission is a list of table features: a bare flag, an empty item and a name outside
        # the table are usage errors (a misspelt name would admit nothing and hide that).
        for value, marker in (((), "missing value for --assume-asm-cpu-features"),
                              (("--proof-api",), "needs a comma-separated list"),
                              (("lzcnt,",), "needs a comma-separated list"),
                              (("lzcnt,avx1024",), "'avx1024' is not a CPU feature of the asm feature table"),
                              (("lzcnt", assume, "popcnt"), "duplicate --assume-asm-cpu-features")):
            result = translate(*legacy, assume, *value)
            assert result.returncode == 1 and marker in result.stderr, (value, result.stderr)
            checks += 1
        # Check-only mode agrees with translation.
        (air / "asm.lzcnt64.json").write_bytes((golden / "asm.lzcnt64.json").read_bytes())
        check = [str(binary), "--diagnostics-json", str(air), *legacy]
        report = json.loads(subprocess.run(check, text=True, capture_output=True, check=False, timeout=60).stdout)
        found = [x for x in report["diagnostics"] if "needs the CPU feature(s) [lzcnt]" in x["message"]]
        assert report["status"] == "rejected" and len(found) == 1 and found[0]["code"] == "MODEL_FAILURE", report
        report = json.loads(subprocess.run([*check, assume, "lzcnt"], text=True, capture_output=True, check=False,
                                           timeout=60).stdout)
        assert report["status"] == "checked" and not report["diagnostics"], report
        checks += 2
    # The table (`--print-asm-feature-table`): every instruction of every allowlist entry is in
    # it (an entry with an instruction outside it could never translate), the feature-gated
    # entries are exactly these, and an unknown instruction is an error, never feature-free.
    table = json.loads(subprocess.run([str(binary), "--print-asm-feature-table"], text=True, capture_output=True,
                                      check=True, timeout=60).stdout)
    assert table["unknown_instructions"] == "rejected" and set(table["targets"]) == {"x86_64", "aarch64"}, table
    needs = {}
    for entry in table["allowlist"]:
        assert "error" not in entry, entry
        for instr in entry["instructions"]:
            if instr["features"]:
                needs.setdefault(entry["template"], set()).update(instr["features"])
    assert needs == {"lzcnt %[x], %[ret]": {"lzcnt"}, "popcnt %[x], %[ret]": {"popcnt"},
                     "rdrand %[ret]": {"rdrnd"}, "rdrand %[v]\n\tsetc %[ok]": {"rdrnd"}}, needs
    for arch, rows in table["targets"].items():
        names = [m for row in rows for m in row["mnemonics"]]
        assert len(names) == len(set(names)), (arch, "a mnemonic has two rows")
        assert all(set(row["features"]) <= set(table["features"]) for row in rows), arch
        # A prefix names only instructions of its own table.
        assert all(set(row["prefix_of"]) <= set(names) for row in rows), arch
    checks += 2
    # An allowlisted template whose instruction has no table row cannot be built by a mutation
    # (the allowlist matches the exact template), so the unknown-instruction rejection is tested
    # with a device asm in tests/roadmap/volatile-effects/test_cli.py.
    # aarch64: the `random` export retargeted, its block a device asm. `crc32b` needs `crc`; a
    # template with `%%` is rejected whatever the CPU has, as `%%` separates statements on Apple
    # targets (`nop %%%% crc32b …` would hide `crc32b` behind `nop`).
    document = json.loads(json.dumps(docs["asm_env.random.json"]))
    document["profile"].update(target_triple="aarch64-linux.5.10...6.16-gnu.2.31", abi="gnu", cpu="generic")
    block = asm_inst(document)
    constraints = [o["constraint"] for o in block["outputs"]] + [i["constraint"] for i in block["inputs"]]
    with tempfile.TemporaryDirectory(prefix="air2lean-asm-a64-") as d:
        contract = Path(d) / "cpu.json"
        for source, features, marker in (
                ("crc32b w0, w0, w0", [], "instruction 'crc32b' needs the CPU feature(s) [crc]"),
                ("nop %%%% crc32b w0, w0, w0", [], "an aarch64 template with '%%'"),
                ("nop %%%% crc32b w0, w0, w0", ["crc"], "an aarch64 template with '%%'"),
                ("crc32b w0, w0, w0", ["crc"], None)):
            block["source"] = source
            document["profile"]["features"] = features
            contract.write_text(json.dumps({"schema": 1, "device": "cpu", "registers": [], "asm": [
                {"template": source, "constraints": constraints, "clobbers": block["clobbers"]}]}))
            result, text = run(binary, {"asm_env.random.json": document}, ("--device-contract", str(contract)))
            if marker is None:
                assert result.returncode == 0 and "Zig.vasm air2lean_device" in text, result.stderr
            else:
                assert result.returncode == 1 and text == "sentinel\n" and marker in result.stderr, result.stderr
            checks += 1
    return checks


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
