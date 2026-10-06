#!/usr/bin/env python3
"""Bind observation pointers to the freshly emitted named global blocks."""
import re
import sys
from pathlib import Path

generated = Path(sys.argv[1]).read_text()
template = Path(sys.argv[2]).read_text()
for name, marker in (("global_status", "@STATUS_BLOCK@"), ("statuses", "@SLOTS_BLOCK@")):
    blocks = [index for index, label in re.findall(r"^  -- (\d+): (.+)$", generated, re.M)
              if label == name or label.endswith("." + name)]
    if len(blocks) != 1 or template.count(marker) != 1:
        raise SystemExit(f"ambiguous or absent fresh global {name}")
    template = template.replace(marker, blocks[0])
Path(sys.argv[3]).write_text(generated + template)
