#!/usr/bin/env python3
"""Require actual audited creation/FAdmit evidence for the named allocator contracts."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('claims', ROOT / 'scripts/claims.py')
claims = importlib.util.module_from_spec(spec)
spec.loader.exec_module(claims)
report = json.loads(Path(sys.argv[1]).read_text())
audited = claims.audited_theorems(report)
for name in sys.argv[2:]:
    theorem = audited[name]
    assert theorem.get('allowed') is True, theorem.get('violations')
    found = claims.assess(theorem, claims.load_heads(), audited=audited)
    evidence = found['allocator_creation']
    assert evidence['status'] == 'verified', (name, evidence)
    own = [entry for entry in evidence['contracts'] if entry['contract'] == name]
    assert len(own) == 1 and own[0]['status'] == 'verified', (name, own)
    print(f'allocator creation: {name}: verified total triple, positive fee, inhabited request and FAdmit')
