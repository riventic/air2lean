"""Peak-RSS budget shared by the offline proof-receipt suites.

`ru_maxrss` is a high-water mark in BYTES on macOS but KiB on Linux; `peak_rss_bytes` normalises it (that unit
handling was already right).  The old absolute 32 MiB cap was the real defect: a bare `python3 -c pass` already peaks
at ~15 MB on macOS (Python 3.14) versus ~9-10 MB on Linux, so the cap measured the interpreter instead of the suite.
test_receipt.py peaked at 27.1 MB on Linux CI and 34.0 MB on macOS, i.e. ~17-19.5 MB of growth on both.

The budget therefore bounds growth over a bare interpreter of the same build (`baseline()`, measured in a child), so
one number catches a real regression on both platforms: GROWTH_BUDGET leaves ~20% headroom over the observed ~19.5 MB.
Do not raise it without a measured reason; test_rss_budget.py proves a deliberate large allocation trips it.

2026-10-20, raised from 24 to 32 MiB: test_receipt.py grew 24.3-25.9 MB on macOS (Python 3.14.8, 4 of 4 standalone
runs), over the 24 MiB budget. About 11 MB of it is importing the suite (bare interpreter 15.0 MB, after the suite's
imports 25.7 MB). These are the standard modules the code under test needs: unittest alone adds 4.4 MB, and with
tempfile, subprocess, json, pathlib, dataclasses, argparse, hashlib and shutil the total is 10.4 MB. No cheap lazy import
removes them. The tests themselves add about 8 MB, the largest being test_audit_module_checks_cache_success_locally_and_reset
at 4 MB. 32 MiB leaves ~20% headroom over the measured 25.9 MB.
"""
import resource
import subprocess
import sys

MIB = 1024 * 1024
GROWTH_BUDGET = 32 * MIB
_PROBE = 'import resource,sys; r=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss; ' \
         'print(r if sys.platform=="darwin" else r*1024)'


def peak_rss_bytes():
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak if sys.platform == 'darwin' else peak * 1024


def baseline():
    """Peak RSS of a bare interpreter of this build, so imports and test work count as growth."""
    return int(subprocess.run([sys.executable, '-c', _PROBE], check=True, capture_output=True, text=True).stdout)


def enforce(start, label='offline test'):
    """Print the measurement; exit non-zero when peak growth over `start` exceeds the budget."""
    used = peak_rss_bytes() - start
    print('%s peak RSS bytes: %d (bare interpreter %d, growth %d, budget %d)' % (
        label, peak_rss_bytes(), start, used, GROWTH_BUDGET))
    if used > GROWTH_BUDGET:
        raise SystemExit('%s RSS growth exceeded %d MiB' % (label, GROWTH_BUDGET // MIB))
