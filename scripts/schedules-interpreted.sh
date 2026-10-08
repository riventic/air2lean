#!/usr/bin/env bash
# Run tests/diff/Schedules.lean through the Lean interpreter: no native executable, no libm archive.
# Needs `lake build Concurrent ScheduleSearch` in tests/diff once.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root/tests/diff"
exec lake env lean --run Schedules.lean "$@"
