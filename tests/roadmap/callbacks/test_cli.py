#!/usr/bin/env python3
"""CLI regressions for function-pointer call sites bound to registry contracts (E02).

`air/<version>` and `air-async/<version>` are fresh exports of `callbacks.zig` and
`async_cb.zig` (provenance.json). Usage: test_cli.py <air2lean>. Never invokes a compiler.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
VERSIONS = ("0.17.0", "0.16.0", "0.15.2", "0.14.1")


def run(exe, air, out, *extra):
    return subprocess.run([str(exe), str(air), "-o", str(out), "--namespace", "T",
                           "--prefix", "callbacks.", "--profile", "abi64-le-v1", *extra],
                          capture_output=True, text=True, timeout=120)


def registry_file(tmp, registry):
    path = Path(tempfile.mkstemp(dir=tmp, suffix=".json")[1])
    path.write_text(json.dumps(registry))
    return str(path)


def main(exe):
    checks = 0
    with tempfile.TemporaryDirectory(prefix="air2lean-callbacks-") as tmp:
        out = Path(tmp) / "Out.lean"
        for version in VERSIONS:
            air = HERE / "air" / version
            registry = json.loads((HERE / f"registry-{version}.json").read_text())
            # Without a binding the address of `ext_visit` fails closed.
            result = run(exe, air, out)
            assert result.returncode == 1 and "CALLEE_EXTERN_UNBOUND" in result.stderr and \
                "(its address is taken)" in result.stderr, result.stderr
            # The template offers the address-taken symbol, typed by its indirect call sites.
            result = run(exe, air, out, "--model-registry-template")
            assert result.returncode == 0, result.stderr
            template = json.loads(out.read_text())
            assert [m["symbol"] for m in template["models"]] == ["extern:ext_visit"], template
            assert template["models"][0]["signature"] == registry["models"][0]["signature"]
            # Bound: every call through the pointer type dispatches the model's block.
            result = run(exe, air, out, "--model-registry", registry_file(tmp, registry))
            assert result.returncode == 0, result.stderr
            text = out.read_text()
            assert "Zig.callM (air2lean_model_0 " in text and text.count("then Zig.callM (sumVisit") >= 3
            # A signature that differs from a call through the pointer is rejected.
            bad = json.loads(json.dumps(registry))
            bad["models"][0]["signature"]["params"] = bad["models"][0]["signature"]["params"][:1]
            result = run(exe, air, out, "--model-registry", registry_file(tmp, bad))
            assert result.returncode == 1 and "incompatible signature" in result.stderr, result.stderr
            # The AIR global records no library and no direct call declares one, so the
            # binding's library is not checked (docs/air-json.md §Extern calls).
            other = json.loads(json.dumps(registry))
            other["models"][0]["extern"]["library"] = "c"
            result = run(exe, air, out, "--model-registry", registry_file(tmp, other))
            assert result.returncode == 0, result.stderr
            checks += 5
            # Asynchronous callbacks: a concurrent program needs the footprint (EXT-04).
            air = HERE / "air-async" / version
            registry = json.loads((HERE / f"registry-async-{version}.json").read_text())
            result = subprocess.run([str(exe), str(air), "-o", str(out), "--namespace", "T",
                                     "--prefix", "async_cb.", "--profile", "abi64-le-v1",
                                     "--model-registry", registry_file(tmp, registry)],
                                    capture_output=True, text=True, timeout=120)
            assert result.returncode == 0, result.stderr
            assert "Zig.External.claim p0 .write *> _root_.CallbackModel.visit" in out.read_text()
            del registry["models"][0]["footprint"]
            result = subprocess.run([str(exe), str(air), "-o", str(out), "--namespace", "T",
                                     "--prefix", "async_cb.", "--profile", "abi64-le-v1",
                                     "--model-registry", registry_file(tmp, registry)],
                                    capture_output=True, text=True, timeout=120)
            assert result.returncode == 1 and "needs a declared 'footprint'" in result.stderr
            checks += 2
    print(f"callbacks CLI checks: {checks}")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
