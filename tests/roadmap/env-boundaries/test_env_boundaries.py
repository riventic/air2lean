#!/usr/bin/env python3
"""E03 boundary documentation checks: every `Zig.Env.Ops` operation has a documented row
with a defined premise ID, every contract field is documented, and the not-claimed list
names CPython, browser host imports and the operating system."""
import json
from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
ENV = ROOT / "ZigLean/Env.lean"
DOC = ROOT / "docs/env-boundaries.md"
CATALOG = ROOT / "docs/premises.md"
CONFIG = ROOT / "assurance/premises.json"

NOT_CLAIMED = ("CPython", "Browser host imports", "The operating system")
PREMISE_RE = re.compile(r"\b[A-Z]{3}-\d{2}\b")


def structure_fields(lean: str, name: str) -> list[str]:
    """Field names of `structure <name>` up to the next blank line."""
    match = re.search(rf"^structure {name}\b.*?\bwhere\n(.*?)(?:\n\n|\Z)", lean, re.M | re.S)
    if not match:
        return []
    return re.findall(r"^  ([a-zA-Z][A-Za-z0-9_']*) :", match.group(1), re.M)


def section(doc: str, heading: str) -> str | None:
    match = re.search(rf"^## {re.escape(heading)}\n(.*?)(?=^## |\Z)", doc, re.M | re.S)
    return match.group(1) if match else None


def operation_rows(doc: str) -> dict[str, tuple[str, str]]:
    body = section(doc, "Operations") or ""
    rows = {}
    for line in body.splitlines():
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) == 3 and cells[0].startswith("`"):
            rows[cells[0].strip("`")] = (cells[1], cells[2])
    return rows


def check(lean: str, doc: str, catalog: str, config: dict) -> list[str]:
    errors = []
    ops = structure_fields(lean, "Ops")
    contract = structure_fields(lean, "Contract")
    if not ops or not contract:
        return ["ZigLean/Env.lean: Ops or Contract fields not found"]
    defined = set(re.findall(r"^### ([A-Z]{3}-\d{2}) — ", catalog, re.M))
    rows = operation_rows(doc)
    documented = set()
    for op in ops:
        if op not in rows:
            errors.append(f"operation {op}: no row in docs/env-boundaries.md#operations")
            continue
        fields, premise = rows[op]
        ids = PREMISE_RE.findall(premise)
        if not ids:
            errors.append(f"operation {op}: no premise ID")
        errors += [f"operation {op}: premise {pid} is not defined in docs/premises.md"
                   for pid in ids if pid not in defined]
        for name in re.findall(r"`([^`]+)`", fields):
            if name not in contract:
                errors.append(f"operation {op}: {name} is not a Contract field")
            documented.add(name)
    errors += [f"operation row {op}: not an Ops field" for op in rows if op not in ops]
    errors += [f"Contract field {name}: not documented in any operation row"
               for name in contract if name not in documented]
    if config.get("runtime_modules", {}).get("ZigLean.Env") != ["ENV-01"]:
        errors.append("assurance/premises.json: ZigLean.Env must map to ENV-01")
    if not any(rule.get("premise") == "ENV-02" for rule in config.get("rules", [])):
        errors.append("assurance/premises.json: no ENV-02 rule")
    claims = section(doc, "Not claimed")
    if claims is None:
        errors.append("docs/env-boundaries.md: no '## Not claimed' section")
    else:
        errors += [f"not-claimed list: missing {item}" for item in NOT_CLAIMED
                   if f"- **{item}.**" not in claims]
    return errors


class EnvBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.lean = ENV.read_text()
        self.doc = DOC.read_text()
        self.catalog = CATALOG.read_text()
        self.config = json.loads(CONFIG.read_text())

    def run_check(self, lean=None, doc=None, catalog=None, config=None):
        return check(self.lean if lean is None else lean, self.doc if doc is None else doc,
                     self.catalog if catalog is None else catalog,
                     self.config if config is None else config)

    def test_repository_passes(self):
        self.assertEqual(self.run_check(), [])
        self.assertEqual(structure_fields(self.lean, "Ops"),
                         ["monotonicNow", "wallNow", "isOpen", "read", "write", "close"])

    def test_missing_not_claimed_section_fails(self):
        doc = self.doc.replace("## Not claimed", "## Claimed")
        self.assertIn("docs/env-boundaries.md: no '## Not claimed' section",
                      self.run_check(doc=doc))

    def test_each_not_claimed_item_is_required(self):
        for item in NOT_CLAIMED:
            doc = self.doc.replace(f"- **{item}.**", "- **Something else.**")
            self.assertIn(f"not-claimed list: missing {item}", self.run_check(doc=doc))

    def test_new_operation_without_row_fails(self):
        lean = self.lean.replace("  close : σ → Handle → σ\n",
                                 "  close : σ → Handle → σ\n  sync : σ → Handle → σ\n")
        self.assertIn("operation sync: no row in docs/env-boundaries.md#operations",
                      self.run_check(lean=lean))

    def test_row_without_premise_fails(self):
        doc = self.doc.replace("| `close` | `closeReleases`, `closeFrame`, `closeMonotone` | ENV-01 |",
                               "| `close` | `closeReleases`, `closeFrame`, `closeMonotone` | none |")
        self.assertIn("operation close: no premise ID", self.run_check(doc=doc))

    def test_undefined_premise_fails(self):
        catalog = self.catalog.replace("### ENV-02 — ", "### ENV-09 — ")
        errors = self.run_check(catalog=catalog)
        self.assertIn("operation monotonicNow: premise ENV-02 is not defined in docs/premises.md",
                      errors)

    def test_undocumented_contract_field_fails(self):
        lean = self.lean.replace("  closeMonotone :", "  closeMonotone' : True\n  closeMonotone :")
        self.assertIn("Contract field closeMonotone': not documented in any operation row",
                      self.run_check(lean=lean))

    def test_premise_mapping_is_required(self):
        config = dict(self.config, runtime_modules={})
        self.assertIn("assurance/premises.json: ZigLean.Env must map to ENV-01",
                      self.run_check(config=config))


if __name__ == "__main__":
    unittest.main()
