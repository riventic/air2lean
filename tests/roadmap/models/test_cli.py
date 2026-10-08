#!/usr/bin/env python3
"""Run with the built translator; creates exact binding templates then mutates them."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def proved_fields(implementation="identity", contract="contract", proof="evidence"):
    return {"import": "tests.roadmap.models.Model", "implementation": f"RegistryExample.{implementation}",
            "contract": f"RegistryExample.{contract}", "trust": "proved", "proof": f"RegistryExample.{proof}",
            "termination": "total", "errors": [], "effects": "preserves", "dependencies": []}


def run_cli(argv, *, cwd=None, success=True, diagnostic=None):
    result = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=10)
    assert result.returncode == (0 if success else 1), (result.returncode, result.stderr)
    if not success:
        assert result.stderr.strip(), "missing failure diagnostic"
    if diagnostic is not None:
        assert diagnostic in result.stderr, (diagnostic, result.stderr)
    return result


def main(executable):
    exe = Path(executable).resolve()
    fixture = Path(__file__).with_name("client.json")
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        air = tmp / "air"
        air.mkdir()
        (air / "client.json").write_text(fixture.read_text())
        out = tmp / "output.lean"
        registry = tmp / "registry.json"
        base = [str(exe), str(air), "-o", str(out), "--namespace", "ExternalClient"]
        def invoke(extra=(), success=True, diagnostic=None):
            return run_cli(base + list(extra), success=success, diagnostic=diagnostic)
        invoke(["--model-registry-template"])
        data = json.loads(out.read_text())
        m = data["models"][0]
        m.update(proved_fields())
        def write(data):
            registry.write_text(json.dumps(data))
        def fail(data, diagnostic):
            write(data)
            out.write_text("KEEP")
            invoke(["--model-registry", str(registry)], False, diagnostic)
            assert out.read_text() == "KEEP"
        write(data)
        invoke(["--model-registry", str(registry)])
        text = out.read_text()
        marker = next(line for line in text.splitlines() if line.startswith("-- air2lean-models: "))
        report = json.loads(marker.split(": ", 1)[1])
        assert report["assumptions"] == []
        assert "theorem air2lean_model_0_evidence" in text and "def client (p0 : BitVec 8) : Zig.MemM" in text
        # Qualified std models and Lean declarations are admitted semantic dependencies.
        dependent = copy.deepcopy(data)
        dependent["models"][0]["dependencies"] = ["mem.Allocator.allocSentinel", "RegistryExample.identity"]
        write(dependent)
        invoke(["--model-registry", str(registry)])
        dependent_report = json.loads(out.read_text().split("-- air2lean-models: ")[1].splitlines()[0])
        assert dependent_report["bindings"][0]["dependencies"] == dependent["models"][0]["dependencies"]
        write(data)
        registry_symlink = tmp / "registry-link.json"
        registry_symlink.symlink_to(registry)
        invoke(["--model-registry", str(registry_symlink)])
        assert out.read_text() == text, "regular-file registry symlink changed output"
        # No writer is attached: pre-open rejection must finish within run_cli's timeout.
        registry_fifo = tmp / "registry.fifo"
        os.mkfifo(registry_fifo)
        out.write_text("KEEP")
        invoke(["--model-registry", str(registry_fifo)], False, "must be a regular file")
        assert out.read_text() == "KEEP", "FIFO registry rejection overwrote output"
        assumed = copy.deepcopy(data)
        assumed["models"][0]["trust"] = "assumed"
        assumed["models"][0].pop("proof")
        write(assumed)
        invoke(["--model-registry", str(registry)])
        text = out.read_text()
        assert "axiom air2lean_model_0_evidence" in text
        assert json.loads(text.split("-- air2lean-models: ")[1].splitlines()[0])["assumptions"] == ["project.identity"]
        for key in ["signature", "profile", "contract", "implementation", "import", "termination", "errors", "effects", "dependencies"]:
            bad = copy.deepcopy(data)
            bad["models"][0].pop(key)
            fail(bad, f"property not found: {key}")
        for key, value, diagnostic in [("symbol", "missing", "has no supported direct call"),
                           ("termination", "unspecified", "unsupported termination"),
                           ("effects", "empty", "unsupported effects"), ("errors", ["Bad"], "unknown safety error"),
                           ("implementation", "X; axiom injected : False", "invalid Lean identifier"),
                           ("signature", {"params": [], "return": None}, "incompatible signature/layout"),
                           ("symbol", "mem.Allocator.create", "conflicts with translated AIR or a built-in model"),
                           ("dependencies", ["Io.futexWaitTimeout"], "is outside the subset"),
                           ("dependencies", ["project.identity"], "cyclic semantic dependency"),
                           ("dependencies", ["Zig.x", "Zig.x"], "duplicate semantic dependency")]:
            bad = copy.deepcopy(data)
            bad["models"][0][key] = value
            fail(bad, diagnostic)
        bad = copy.deepcopy(data)
        bad["models"] *= 2
        fail(bad, "duplicate model symbol")
        for key, value in [("zig_version", "0.15.2"), ("cpu", "baseline"), ("features", []), ("error_tracing", True)]:
            bad = copy.deepcopy(data)
            bad["models"][0]["profile"][key] = value
            fail(bad, "profile")
        for contents, diagnostic in [
            ('{"schema":1e1000000000,"models":[]}', "exponent exceeds"),
            ('{"schema":1,"schema":1,"models":[]}', "duplicate JSON object key"),
            ('[' * 529 + '0' + ']' * 529, "JSON nesting exceeds"),
        ]:
            registry.write_text(contents)
            out.write_text("KEEP")
            result = invoke(["--model-registry", str(registry)], False, diagnostic)
            assert diagnostic in result.stderr and out.read_text() == "KEEP", result.stderr
        # A sparse file checks the pre-read metadata guard without constructing 64 MiB text.
        with registry.open("wb") as oversized:
            oversized.truncate(64 * 1024 * 1024 + 1)
        result = invoke(["--model-registry", str(registry)], False, "UTF-8 bytes")
        assert "UTF-8 bytes" in result.stderr and out.read_text() == "KEEP", result.stderr
        invoke([], False, "has no AIR file and no model")
        invoke(["--model-registry-template", "--model-registry", str(registry)], False, "cannot be combined")
        # Value-taking options consume their next token even when it looks like a flag.
        write(data)
        prefix = run_cli(base + ["--prefix", "--model-registry-template", "--model-registry", str(registry)])
        assert prefix.returncode == 0, prefix.stderr
        flagfile = tmp / "--model-registry-template"
        output_name = run_cli([str(exe), str(air), "-o", "--model-registry-template", "--namespace", "ExternalClient",
                               "--model-registry", str(registry)], cwd=tmp)
        assert output_name.returncode == 0 and flagfile.read_text().startswith("-- air2lean-profile:"), output_name.stderr
        flagfile.write_text(json.dumps(data))
        registry_name = run_cli(base + ["--model-registry", "--model-registry-template"], cwd=tmp)
        assert registry_name.returncode == 0, registry_name.stderr
        for option in ["-o", "--prefix", "--model-registry", "--namespace"]:
            run_cli(base + [option], success=False, diagnostic=f"missing value for {option}")
        ordinary = json.loads(fixture.read_text())
        ordinary["body"] = [ordinary["body"][0], ordinary["body"][2]]
        ordinary["body"][1]["args"] = [{"inst": 0}]
        (air / "client.json").write_text(json.dumps(ordinary))
        invoke()
        text = out.read_text()
        assert text.startswith("-- air2lean-profile:") and "-- air2lean-models:" not in text
        write({"schema": 1, "models": []})
        invoke(["--model-registry", str(registry)])
        assert out.read_text() == text
        deep = json.loads(fixture.read_text())
        deep["types"] = [deep["types"][0]] + [{"k": "optional", "child": i - 1} for i in range(1, 65)] + [{"k": "noreturn"}]
        deep["params"], deep["ret"] = [64], 64
        deep["body"][0]["ty"] = deep["body"][1]["ty"] = 64
        deep["body"][2]["ty"] = 65
        (air / "client.json").write_text(json.dumps(deep))
        invoke(["--model-registry-template"])
        deep_data = json.loads(out.read_text())
        deep_data["models"][0].update(proved_fields("polyIdentity", "polyContract", "polyEvidence"))
        write(deep_data)
        invoke(["--model-registry", str(registry)])
        assert "-- air2lean-models:" in out.read_text()
        # A tuple argument followed by a scalar must remain grouped as (A × B) × C.
        (air / "client.json").write_text(Path(__file__).with_name("tuple-client.json").read_text())
        invoke(["--model-registry-template"])
        tuple_data = json.loads(out.read_text())
        tuple_data["models"][0].update(proved_fields("tupleSelect", "tupleContract", "tupleEvidence"))
        write(tuple_data)
        invoke(["--model-registry", str(registry)])
        assert "Contract ((BitVec 8 × BitVec 8) × (BitVec 8))" in out.read_text()
        # A source AIR mutation of only the byte qualifier must reject the old binding.
        sentinel = json.loads(fixture.read_text())
        sentinel["types"].append({"k": "ptr", "size": "slice", "const": False,
            "child": 0, "abi_size": 16, "abi_align": 8, "ptr_align": 1,
            "sentinel": True, "sentinel_byte": "0"})
        sentinel["params"], sentinel["ret"] = [2], 2
        sentinel["body"][0]["ty"] = sentinel["body"][1]["ty"] = 2
        (air / "client.json").write_text(json.dumps(sentinel))
        invoke(["--model-registry-template"])
        sentinel_data = json.loads(out.read_text())
        sentinel_model = sentinel_data["models"][0]
        assert sentinel_model["signature"]["params"][0]["layout"]["sentinel_byte"] == 0
        assert sentinel_model["signature"]["return"]["layout"]["sentinel_byte"] == 0
        sentinel_model.update(proved_fields("polyIdentity", "polyContract", "polyEvidence"))
        write(sentinel_data)
        invoke(["--model-registry", str(registry)])
        assert '\"sentinel_byte\":0' in out.read_text()
        for value in ("42", None):
            mutated = copy.deepcopy(sentinel)
            if value is None:
                del mutated["types"][2]["sentinel_byte"]
            else:
                mutated["types"][2]["sentinel_byte"] = value
            (air / "client.json").write_text(json.dumps(mutated))
            fail(sentinel_data, "incompatible signature/layout")

    print("external model CLI regressions passed")


if __name__ == "__main__":
    main(sys.argv[1])
