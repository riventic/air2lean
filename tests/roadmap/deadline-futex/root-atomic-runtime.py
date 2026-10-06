#!/usr/bin/env python3
"""ROOT-only v5 atomic-compare qualification, reusing bounded process supervision."""
import importlib.util
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("deadline_atomic_recipe", Path(__file__).with_name("root-runtime.py"))
recipe = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(recipe)
recipe.FILES += (
    "tests/roadmap/deadline-futex/AtomicKernel.lean",
    "tests/roadmap/deadline-futex/RuntimeAtomic.lean",
    "tests/roadmap/deadline-futex/root-atomic-runtime.py",
    "tests/roadmap/deadline-futex/test_atomic_recipe.py",
    "docs/deadline-atomic-compare.md",
    "tests/roadmap/deadline-futex/foundation-qualified-v4.json",
)
foundation_commands = recipe.commands


def commands(root):
    base = foundation_commands(root)
    return base[:2] + [("build-atomic-laws", ["lake", "build", "ZigLean.Conc.Lemmas"])] + base[2:] + [
        ("atomic-kernel", ["lake", "env", "lean", "-R", str(root),
                           str(root / "tests/roadmap/deadline-futex/AtomicKernel.lean")]),
        ("atomic-runtime", ["lake", "env", "lean", "-R", str(root), "--run",
                            str(root / "tests/roadmap/deadline-futex/RuntimeAtomic.lean")]),
    ]


recipe.commands = commands

if __name__ == "__main__":
    raise SystemExit(recipe.main())
