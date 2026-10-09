"""Peak-RSS budget shared by the offline proof-receipt suites.

`ru_maxrss` is a high-water mark in BYTES on macOS but KiB on Linux; `peak_rss_bytes` normalises it (that unit
handling was already right).  The old absolute 32 MiB cap was the real defect: a bare `python3 -c pass` already peaks
at ~15 MB on macOS (Python 3.14) versus ~9-10 MB on Linux, so the cap measured the interpreter instead of the suite.
test_receipt.py peaked at 27.1 MB on Linux CI and 34.0 MB on macOS, i.e. ~17-19.5 MB of growth on both.

The budget therefore bounds growth over a bare interpreter of the same build (`baseline()`, measured in a child), so
one number catches a real regression on both platforms: GROWTH_BUDGET leaves ~20% headroom over the observed ~19.5 MB.
Do not raise it without a measured reason; test_rss_budget.py proves a deliberate large allocation trips it.
"""
import resource
import subprocess
import sys

MIB = 1024 * 1024
GROWTH_BUDGET = 24 * MIB
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
