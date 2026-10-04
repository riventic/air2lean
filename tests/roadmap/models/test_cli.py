#!/usr/bin/env python3
"""Run with the built translator; creates exact binding templates then mutates them."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

exe = Path(sys.argv[1]).resolve()
fixture = Path(__file__).with_name("client.json")
with tempfile.TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    air = tmp / "air"
    air.mkdir()
    (air / "client.json").write_text(fixture.read_text())
    out = tmp / "output.lean"
    registry = tmp / "registry.json"
    base = [str(exe), str(air), "-o", str(out), "--namespace", "ExternalClient"]
    def invoke(extra=(), success=True):
        result = subprocess.run(base + list(extra), capture_output=True, text=True)
        assert (result.returncode == 0) == success, result.stderr
        return result
    invoke(["--model-registry-template"])
    data = json.loads(out.read_text())
    m = data["models"][0]
    m.update({"import": "tests.roadmap.models.Model", "implementation": "RegistryExample.identity",
              "contract": "RegistryExample.contract", "trust": "proved", "proof": "RegistryExample.evidence",
              "termination": "total", "errors": [], "effects": "preserves", "dependencies": []})
    def write(data):
        registry.write_text(json.dumps(data))
    def fail(data):
        write(data)
        out.write_text("KEEP")
        invoke(["--model-registry", str(registry)], False)
        assert out.read_text() == "KEEP"
    write(data)
    invoke(["--model-registry", str(registry)])
    text = out.read_text()
    marker = next(line for line in text.splitlines() if line.startswith("-- air2lean-models: "))
    report = json.loads(marker.split(": ", 1)[1])
    assert report["assumptions"] == []
    assert "theorem air2lean_model_0_evidence" in text and "def client (p0 : BitVec 8) : Zig.MemM" in text
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
        fail(bad)
    for key, value in [("symbol", "missing"), ("termination", "unspecified"), ("effects", "empty"),
                       ("errors", ["Bad"]), ("implementation", "X; axiom injected : False"),
                       ("signature", {"params": [], "return": None})]:
        bad = copy.deepcopy(data)
        bad["models"][0][key] = value
        fail(bad)
    bad = copy.deepcopy(data)
    bad["models"] *= 2
    fail(bad)
    for key, value in [("zig_version", "0.15.2"), ("cpu", "baseline"), ("features", []), ("error_tracing", True)]:
        bad = copy.deepcopy(data)
        bad["models"][0]["profile"][key] = value
        fail(bad)
    invoke([], False)
    invoke(["--model-registry-template", "--model-registry", str(registry)], False)
    # Value-taking options consume their next token even when it looks like a flag.
    write(data)
    prefix = subprocess.run(base + ["--prefix", "--model-registry-template", "--model-registry", str(registry)],
                            capture_output=True, text=True)
    assert prefix.returncode == 0, prefix.stderr
    flagfile = tmp / "--model-registry-template"
    output_name = subprocess.run([str(exe), str(air), "-o", "--model-registry-template", "--namespace", "ExternalClient",
                                  "--model-registry", str(registry)], cwd=tmp, capture_output=True, text=True)
    assert output_name.returncode == 0 and flagfile.read_text().startswith("-- air2lean-profile:"), output_name.stderr
    flagfile.write_text(json.dumps(data))
    registry_name = subprocess.run(base + ["--model-registry", "--model-registry-template"], cwd=tmp,
                                  capture_output=True, text=True)
    assert registry_name.returncode == 0, registry_name.stderr
    for option in ["-o", "--prefix", "--model-registry", "--namespace"]:
        result = subprocess.run(base + [option], capture_output=True, text=True)
        assert result.returncode != 0 and "missing value" in result.stderr
    # A tuple argument followed by a scalar must remain grouped as (A × B) × C.
    (air / "client.json").write_text(Path(__file__).with_name("tuple-client.json").read_text())
    invoke(["--model-registry-template"])
    tuple_data = json.loads(out.read_text())
    tuple_data["models"][0].update({"import": "tests.roadmap.models.Model", "implementation": "RegistryExample.tupleSelect",
              "contract": "RegistryExample.tupleContract", "trust": "proved", "proof": "RegistryExample.tupleEvidence",
              "termination": "total", "errors": [], "effects": "preserves", "dependencies": []})
    write(tuple_data)
    invoke(["--model-registry", str(registry)])
    assert "Contract ((BitVec 8 × BitVec 8) × (BitVec 8))" in out.read_text()

print("external model CLI regressions passed")
