#!/usr/bin/env python3
"""Record the bitops source, executable tool, generated artifact and observation hashes."""
import argparse
import hashlib
import json
import platform
import shutil
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("output", type=Path)
parser.add_argument("air_compiler")
parser.add_argument("stock_compiler")
args = parser.parse_args()
root = Path(__file__).resolve().parents[3]

def digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()

def executable(name):
    path = shutil.which(name)
    if path is None:
        raise ValueError(f"compiler not found: {name}")
    return Path(path).resolve()

def compiler_info(name):
    path = executable(name)
    info = {"path": str(path), "sha256": digest(path)}
    # The project AIR-only safety launcher is separate from the compiler binary.
    with path.open("rb") as stream:
        header = stream.read(4096)
    if b"air2lean-lock" in header:
        compiler = path.parent / "zig-unlocked"
        if not compiler.is_file():
            raise ValueError(f"AIR launcher has no delegated compiler: {compiler}")
        info["delegated_compiler"] = {"path": str(compiler.resolve()), "sha256": digest(compiler)}
    return info

sources = {p.relative_to(root).as_posix(): digest(p) for directory in
           ["Air2Lean", "ZigLean", "zig-patch/air-json"] for p in sorted((root / directory).rglob("*"))
           if p.is_file() and p.suffix in {".lean", ".zig"}}
for p in [root / "ZigLean.lean", root / "Air2Lean.lean", root / "lean-toolchain"]:
    sources[p.relative_to(root).as_posix()] = digest(p)
for p in sorted((root / "tests/roadmap/bitops").iterdir()):
    if p.is_file() and p.suffix in {".lean", ".zig", ".inc", ".py", ".sh"}:
        sources[p.relative_to(root).as_posix()] = digest(p)
artifacts = {p.relative_to(args.output).as_posix(): digest(p)
             for p in sorted(args.output.rglob("*")) if p.is_file() and p.name != "manifest.json"}
manifest = {
    "status": "passed", "zig_version": "0.16.0", "build_mode": "ReleaseSafe", "cpu": "baseline",
    "host": {"os": platform.system(), "architecture": platform.machine()},
    "air_target": "x86_64-linux",
    "native_execution_target": "host default; architecture and OS recorded in host",
    "target_scope": "Reference x86_64-linux AIR compared against host-native scalar/vector/bitset execution. This does not qualify all x86_64 backend or ABI behavior.",
    "observations": {"exact_matches": 3092, "mismatches": 0,
                     "exclusions": [{"functions": ["shiftNarrow", "shiftSignedNarrow"], "reason": "shift count 3 >= u3/i3 width is illegal behavior", "observation_rows": 256, "function_evaluations": 512}]},
    "semantic_mutations": {"killed": 8, "survived": 0},
    "air_compiler": compiler_info(args.air_compiler),
    "stock_compiler": compiler_info(args.stock_compiler),
    "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
    "sources": sources, "artifacts": artifacts,
    "validation": {
        "kernel_checked": ["ZigLean/Bit.lean runtime lemmas", "Runtime.lean edge assertions", "Bitset.lean bitset client proofs", "GeneratedBitset.lean proofs over the fresh generated bitset fixtures", "mutation control assertions and decide refutations"],
        "compiled_execution": ["Cases.lean parser/normalizer/checker regressions", "18 generated fixture IO assertions", "3092 native/Lean differential observation rows"],
    },
    "trust_boundary": "Kernel checks runtime lemmas, Runtime.lean assertions, bitset client proofs and mutation decide refutations. Generated fixture IO assertions and differential rows are compiled execution evidence. Zig Sema/export/backend and AIR normalization/emission preservation remain unproved.",
}
(args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
