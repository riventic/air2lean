#!/usr/bin/env python3
"""CLI rejections for error return tracing (L14), for a root-built translator.

`air/<version>` is a compiler export (provenance.json); each case below mutates one exported file
into a shape that `Canon.errTraces` must refuse, and checks the exact diagnostic. Never builds or
invokes compilers. usage: test_cli.py TRANSLATOR
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
VERSIONS = ("0.17.0", "0.16.0", "0.15.2", "0.14.1")
TRANSLATOR = None


def walk(body):
    for i in body:
        yield i
        for key in ("body", "then", "else"):
            yield from walk(i.get(key, []))
        for case in i.get("cases", []):
            yield from walk(case["body"])


def run(files):
    with tempfile.TemporaryDirectory() as d:
        for name, doc in files.items():
            (Path(d) / name).write_text(json.dumps(doc))
        done = subprocess.run([TRANSLATOR, d, "-o", str(Path(d) / "Gen.lean"), "--namespace", "T"],
                              capture_output=True, text=True)
        return done.returncode, done.stdout + done.stderr


class Rejections(unittest.TestCase):
    def files(self, version):
        return {p.name: json.loads(p.read_text()) for p in sorted((HERE / "air" / version).glob("*.json"))}

    def reject(self, files, message):
        code, out = run(files)
        self.assertNotEqual(code, 0, out)
        self.assertIn(message, out)

    def test_exports_translate(self):
        for version in VERSIONS:
            code, out = run(self.files(version))
            self.assertEqual(code, 0, (version, out))

    def test_unresolved_stack_trace(self):
        for version in VERSIONS:
            files = self.files(version)
            doc = files["error_tracing.pass.json"]
            del doc["err_trace"]
            doc["err_trace_unresolved"] = True
            self.reject(files, "could not resolve `std.builtin.StackTrace`")

    def test_trace_without_one(self):
        # A function that passes a trace it neither receives nor sets.
        for version in VERSIONS:
            files = self.files(version)
            del files["error_tracing.pass.json"]["err_trace"]
            self.reject(files, "without an error return trace (a function that neither receives one nor sets one)")

    def test_nested_set(self):
        for version in VERSIONS:
            files = self.files(version)
            doc = files["error_tracing.traced.json"]
            body = doc["body"]
            k = next(n for n, i in enumerate(body) if i["tag"] == "set_err_return_trace")
            block = next(i for i in body[k:] if i.get("body") or i.get("then"))
            nested = dict(copy.deepcopy(body[k]), id=100000)
            block["body" if block.get("body") else "then"].insert(0, nested)
            self.reject(files, "`set_err_return_trace` outside the top-level body")

    def test_return_address_value(self):
        # `@returnAddress()` read as a number, not stored: outside the memory model.
        for version in VERSIONS:
            files = self.files(version)
            name = next(n for n in files if n.endswith("returnError.json"))
            doc = files[name]
            ra = next(i for i in walk(doc["body"]) if i["tag"] == "ret_addr")
            boolean = next(k for k, t in enumerate(doc["types"]) if t["k"] == "bool")
            body = doc["body"] if ra in doc["body"] else next(
                i[key] for i in walk(doc["body"]) for key in ("body", "then", "else") if ra in i.get(key, []))
            k = body.index(ra)
            body.insert(k + 1, {"id": 100000, "tag": "cmp_eq", "ty": boolean,
                                "args": [{"inst": ra["id"]}, {"inst": ra["id"]}]})
            self.reject(files, "`@returnAddress()` is a machine address outside the memory model")


if __name__ == "__main__":
    TRANSLATOR = sys.argv.pop(1)
    unittest.main()
