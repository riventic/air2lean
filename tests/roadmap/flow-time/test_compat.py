#!/usr/bin/env python3
"""Bounded synthetic profile/receipt regressions; no Zig, Lean, Lake, or translator."""
import copy
import json
from pathlib import Path
import runpy
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
CHECK = runpy.run_path(str(ROOT / "tests/roadmap/flow-time/compare-air.py"))
HELPER = CHECK["helpers"]()
BODY = b"import ZigLean\nnamespace FlowTime\ndef synthetic : Nat := 7\nend FlowTime\n"


class Compatibility(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.old = self.root / "old"; self.old.mkdir()
        self.air = self.root / "air"; self.air.mkdir()
        self.gen = self.root / "Gen.lean"
        self.baseline = self.root / "Historic.lean"; self.baseline.write_bytes(BODY)
        self.report = self.root / "report.json"
        self.docs = {}
        for name in sorted(CHECK["NAMES"]):
            doc = dict(schema=11, zig_version="0.16.0", target_endian="little",
                       name=name.removesuffix(".json"), params=[0], ret=0,
                       types=[dict(k="int", bits=32, signed=False, abi_size=4, abi_align=4)],
                       body=[dict(id=1, tag="ret", ty=0, args=[dict(ty=0, val="7")])])
            self.write(self.old / name, doc)
            doc.update(schema=12, profile=copy.deepcopy(CHECK["PROFILE"]))
            self.docs[name] = doc
        self.publish()

    @staticmethod
    def write(path, doc):
        path.write_text(json.dumps(doc))

    def publish(self, body=BODY, metadata=None):
        for name, doc in self.docs.items(): self.write(self.air / name, doc)
        metadata = metadata or dict(profile=dict(CHECK["PROFILE"], schema=12),
                                    float_semantics="ieee", correspondence="model")
        self.gen.write_bytes(HELPER["PREFIX"] + json.dumps(metadata).encode() + b"\n" + body)
        HELPER["write_report"](self.gen, self.air, self.report)

    def check(self):
        CHECK["compare"](self.old, self.air, self.gen, self.report)
        HELPER["compare"](self.baseline, self.gen, self.report)

    def test_valid_profile_transition_and_full_body(self):
        CHECK["compare"](self.old, self.air, validate_fresh=True)
        self.check()
        self.assertTrue(self.gen.read_bytes().startswith(HELPER["PREFIX"]))
        with self.assertRaisesRegex(ValueError, "Flow AIR changed"):
            CHECK["compare"](self.old, self.air)  # No receipt means no schema normalization.

    def test_each_profile_fact_is_required_before_comparison(self):
        name = sorted(self.docs)[0]
        for key, value in CHECK["PROFILE"].items():
            with self.subTest(key=key):
                changed = copy.deepcopy(self.docs[name])
                changed["profile"][key] = {"features": CHECK["PROFILE"]["features"] + ["avx"], "error_tracing": True,
                                           "pointer_bits": 32, "error_set_bits": 32}.get(key, "wrong")
                self.write(self.air / name, changed)
                with self.assertRaises(ValueError):
                    CHECK["compare"](self.old, self.air, validate_fresh=True)
        self.publish()
        for key in ("profile", "target_endian"):
            changed = copy.deepcopy(self.docs[name]); del changed[key]
            self.write(self.air / name, changed)
            with self.assertRaises(ValueError):
                CHECK["compare"](self.old, self.air, validate_fresh=True)

    def test_uniform_profile_and_exact_inventory(self):
        name = sorted(self.docs)[0]
        changed = copy.deepcopy(self.docs[name]); changed["profile"]["build_mode"] = "Debug"
        self.write(self.air / name, changed)
        with self.assertRaises(ValueError): CHECK["compare"](self.old, self.air, validate_fresh=True)
        self.publish()
        # GNU is a valid general ABI profile, but outside this observed musl contract.
        gnu = dict(CHECK["PROFILE"], abi="gnu", target_triple="x86_64-linux.5.10...6.19-gnu.2.31")
        for doc in self.docs.values():
            doc["profile"] = gnu
            self.assertEqual(HELPER["profile_for_air"](doc)["abi"], "gnu")
        self.publish(metadata=dict(profile=dict(gnu, schema=12), float_semantics="ieee", correspondence="model"))
        with self.assertRaisesRegex(ValueError, "unqualified profile"):
            CHECK["compare"](self.old, self.air, validate_fresh=True)
        with self.assertRaisesRegex(ValueError, "unqualified profile"): self.check()
        for doc in self.docs.values(): doc["profile"] = copy.deepcopy(CHECK["PROFILE"])
        self.publish()
        (self.air / name).unlink()
        with self.assertRaisesRegex(ValueError, "exactly both"):
            CHECK["compare"](self.old, self.air, self.gen, self.report)
        self.publish()
        self.write(self.air / "extra.json", self.docs[name])
        with self.assertRaisesRegex(ValueError, "exactly both"):
            CHECK["compare"](self.old, self.air, validate_fresh=True)

    def test_all_semantic_fields_remain_observable_after_rebinding(self):
        name = sorted(self.docs)[0]
        original = copy.deepcopy(self.docs[name])
        changes = [("body", [dict(id=1, tag="ret", ty=0, args=[dict(ty=0, val="8")])]),
                   ("types", [dict(k="int", bits=64, signed=False, abi_size=8, abi_align=8)]),
                   ("params", []), ("ret", 1), ("name", "flow_time.wrong"),
                   ("globals", []), ("target_endian", "big")]
        for key, value in changes:
            with self.subTest(key=key):
                self.docs[name] = copy.deepcopy(original); self.docs[name][key] = value
                try:
                    self.publish()
                    with self.assertRaises(ValueError): self.check()
                except ValueError:  # The shared helper may reject before receipt publication.
                    self.assertEqual(key, "target_endian")
        self.docs[name] = copy.deepcopy(original)
        self.docs[name]["body"][0]["profile"] = {"schema": 11}
        self.publish()
        with self.assertRaisesRegex(ValueError, "Flow AIR changed"): self.check()
        self.docs[name] = copy.deepcopy(original)
        self.docs[name]["body"][0]["id"] = True  # Python equality must not hide True vs 1.
        self.publish()
        with self.assertRaisesRegex(ValueError, "Flow AIR changed"): self.check()

    def test_schema_and_historic_envelope_cannot_be_relabelled(self):
        name = sorted(self.docs)[0]
        for version in (11, 13, True):
            self.docs[name]["schema"] = version
            self.write(self.air / name, self.docs[name])
            with self.assertRaises(ValueError):
                CHECK["compare"](self.old, self.air, validate_fresh=True)
        self.docs[name]["schema"] = 12; self.publish()
        historic = json.loads((self.old / name).read_text()); historic["schema"] = 10
        self.write(self.old / name, historic)
        with self.assertRaisesRegex(ValueError, "historical AIR envelope"):
            self.check()

    def test_raw_air_and_receipt_tampering(self):
        name = sorted(self.docs)[0]
        self.docs[name]["body"][0]["args"][0]["val"] = "8"
        self.write(self.air / name, self.docs[name])
        with self.assertRaisesRegex(ValueError, "raw AIR does not match"): self.check()
        for key, value in [("generated_sha256", "0" * 64), ("body_sha256", "0" * 64),
                           ("air", []), ("air", [dict(file=name, sha256="0" * 64)] * 2)]:
            self.docs[name]["body"][0]["args"][0]["val"] = "7"; self.publish()
            report = json.loads(self.report.read_text()); report[key] = value
            self.write(self.report, report)
            with self.subTest(key=key), self.assertRaises(ValueError): self.check()
        self.publish()
        report = json.loads(self.report.read_text()); report["metadata"]["float_semantics"] = "compiler-rt"
        self.write(self.report, report)
        with self.assertRaises(ValueError): self.check()

    def test_missing_malformed_nonfirst_and_changed_headers(self):
        for data in (BODY, HELPER["PREFIX"] + b"{}\n" + BODY,
                     b"-- preceding comment\n" + self.gen.read_bytes()):
            self.gen.write_bytes(data)
            with self.assertRaises(ValueError): self.check()
        self.publish(); self.gen.write_bytes(self.gen.read_bytes() + b"-- changed\n")
        with self.assertRaisesRegex(ValueError, "generated artifact"): self.check()
        self.publish(body=BODY.replace(b"7", b"8"))
        with self.assertRaisesRegex(ValueError, "generated semantics changed"): self.check()
        metadata = dict(profile=dict(CHECK["PROFILE"], schema=12),
                        float_semantics="compiler-rt", correspondence="model")
        self.publish(metadata=metadata)
        with self.assertRaisesRegex(ValueError, "profile/body"): self.check()

    def test_duplicate_json_keys_bounds_and_required_pair(self):
        name = sorted(self.docs)[0]
        self.write(self.air / name, self.docs[name])
        data = (self.air / name).read_text().replace('"schema": 12', '"schema": 12, "schema": 12')
        (self.air / name).write_text(data)
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            CHECK["compare"](self.old, self.air, validate_fresh=True)
        self.publish()
        self.gen.write_bytes(b"x" * (CHECK["MAX_BYTES"] + 1))
        with self.assertRaisesRegex(ValueError, "byte bound"): self.check()
        with self.assertRaisesRegex(ValueError, "requires both"):
            CHECK["compare"](self.old, self.air, generated=self.gen)


if __name__ == "__main__":
    unittest.main()
