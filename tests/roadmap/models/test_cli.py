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
print("external model CLI regressions passed")
