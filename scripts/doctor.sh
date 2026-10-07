#!/usr/bin/env bash
# Diagnose dependency/target prerequisites without downloads, builds or AIR export.
# The checks live in scripts/doctor.py (Python 3.8+); see `scripts/doctor.sh --help`.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
python=${AIR2LEAN_PYTHON:-python3}
if ! command -v "$python" >/dev/null 2>&1; then
  printf 'error: the doctor needs python3 (3.8 or newer); install it with the system package manager\n' >&2
  printf 'hint: committed proofs need only elan: lake build Proofs.Basic.Proofs\n' >&2
  exit 1
fi
exec "$python" "$repo_root/scripts/doctor.py" "$@"
