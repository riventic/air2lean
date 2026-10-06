#!/usr/bin/env python3
"""Only the pinned semantic refutation at this mutant's oracle counts."""
import importlib.util
import sys
from pathlib import Path

helper = Path(__file__).resolve().parent.parent / "dispatch" / "mutations.py"
spec = importlib.util.spec_from_file_location("dispatch_classifier", helper)
classifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(classifier)
status = int(sys.argv[1]); source = Path(sys.argv[2]); log = Path(sys.argv[3]).read_text()
proof_line = next(i for i, line in enumerate(source.read_text().splitlines(), 1)
                  if line.startswith("theorem semantic_oracle"))
if not classifier.is_semantic_rejection(status, log):
    raise SystemExit("nonsemantic mutant failure")
for line in log.splitlines():
    header = classifier.HEADER.fullmatch(line)
    if header is not None and header.group(4) == "error":
        if Path(header.group(1)).resolve() != source.resolve() or int(header.group(2)) != proof_line:
            raise SystemExit("mutant did not fail solely at its semantic oracle")
print("killed", source.stem)
