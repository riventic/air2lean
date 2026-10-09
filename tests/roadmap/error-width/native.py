#!/usr/bin/env python3
"""L10 native error-width observations with a stock Zig.

usage: native.py ZIG [OUT]

Builds `probe.zig` with `ZIG build-exe -lc -OReleaseSafe -fno-error-tracing --error-limit N` for
each configuration below, runs it, and writes what it observed (one section per configuration)
to OUT or stdout. `Model.lean` prints the same lines from `ZigLean/Mem/ErrWidth.lean` and
compares them with a recorded output (`native/<arch>-<os>-<version>.txt`).

A configuration is `--error-limit` plus the total number of errors in the compilation. The probe
names that many, minus the errors the compiler's own start code names (`hidden`: none in 0.15.2
and 0.16.0, 12 in 0.14.1, measured first); a configuration smaller than that is `skipped`.
Observed per configuration: whether it compiles, the probe's report
(encoding, error-union layout), the `@errorFromInt` boundary (a panic is a signal exit of a
`probe from C` subprocess) and the names of codes 1..N (all of them up to 1000 errors, else the
first and last three).
"""
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

# (name, --error-limit or None for the default, total errors in the compilation)
CONFIGS = [
    ("lim1", 1, 1),
    ("lim1-over", 1, 2),
    ("lim2", 2, 2),
    ("lim2-over", 2, 3),
    ("lim3", 3, 3),
    ("lim4", 4, 4),
    ("lim7", 7, 7),
    ("lim8", 8, 8),
    ("lim255", 255, 255),
    ("lim255-over", 255, 256),
    ("lim256", 256, 256),
    ("lim1000", 1000, 1000),
    ("default", None, 40),
    ("lim65534", 65534, 65534),
    ("lim65535", 65535, 65535),
    ("lim65536", 65536, 65536),
    ("lim100000", 100000, 70000),
    ("lim8388608", 8388608, 5),
    ("lim16777216", 16777216, 5),
    ("lim2147483647", 2147483647, 5),
    ("lim4294967295", 4294967295, 5),
    ("lim0", 0, 2),
]
# The big configurations take the longest to compile; `--quick` skips them.
BIG = {"lim65534", "lim65535", "lim65536", "lim100000"}


def errs_zig(total):
    """`errs.zig`: `Failure` plus `total - |Failure|` extra errors, the last one `top`."""
    if total == 1:
        return ("pub const Failure = error{Bad};\npub const single = true;\n"
                "pub const a: Failure = error.Bad;\npub const b: Failure = error.Bad;\n"
                "pub const top: anyerror = error.Bad;\n")
    head = ("pub const Failure = error{ Bad, Other };\npub const single = false;\n"
            "pub const a: Failure = error.Bad;\npub const b: Failure = error.Other;\n")
    if total == 2:
        return head + "pub const top: anyerror = error.Other;\n"
    names = [f"E{i}" for i in range(3, total)] + ["Top"]
    return (head + "pub const Big = error{" + ",".join(names) + "};\n"
            "pub const top: anyerror = Big.Top;\n")


def run(args, **kw):
    return subprocess.run(args, capture_output=True, text=True, errors="replace", **kw)


def panics(exe, code):
    r = run([str(exe), "from", str(code)])
    return r.returncode != 0


def build(zig, d, limit):
    exe = d / "probe"
    cmd = [zig, "build-exe", "-lc", "-OReleaseSafe", "-fno-error-tracing", f"-femit-bin={exe}"]
    if limit is not None:
        cmd += ["--error-limit", str(limit)]
    return exe, run(cmd + [str(d / "probe.zig")], cwd=d)


def hidden_errors(zig, work):
    """Errors in the compilation beyond the ones `errs.zig` names: probe at the default limit."""
    d = Path(work) / "calibrate"
    d.mkdir()
    (d / "errs.zig").write_text(errs_zig(2))
    (d / "probe.zig").write_text((HERE / "probe.zig").read_text())
    exe, r = build(zig, d, None)
    if r.returncode != 0:
        raise SystemExit(f"calibration failed:\n{r.stderr}")
    lo, hi = 1, 1 << 16
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if panics(exe, mid):
            hi = mid
        else:
            lo = mid
    return lo - 2


def observe(zig, name, limit, total, hidden, work):
    shown = "default" if limit is None else limit
    head = f"config {name} limit {shown} total {total}"
    if total - hidden < 1:
        return [head + " skipped"]
    d = Path(work) / name
    d.mkdir()
    (d / "errs.zig").write_text(errs_zig(total - hidden))
    (d / "probe.zig").write_text((HERE / "probe.zig").read_text())
    exe, r = build(zig, d, limit)
    if r.returncode != 0:
        if "error:" not in r.stderr:
            raise SystemExit(f"{name}: compiler failed without a diagnostic:\n{r.stderr}")
        return [head + " compile fail"]
    out = [head + " compile ok"]
    rep = run([str(exe)])
    if rep.returncode != 0:
        raise SystemExit(f"{name}: probe failed ({rep.returncode}):\n{rep.stderr}")
    lines = rep.stdout.splitlines()
    out += lines
    bits = int(next(l for l in lines if l.startswith("enc anyerror")).split()[4])
    # @errorFromInt boundary: 0 and everything above the compilation's error count panic;
    # a value that does not fit the error integer panics at the cast.
    assert not panics(exe, 1), f"{name}: code 1 panics"
    lo, hi = 1, 1 << bits
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if panics(exe, mid):
            hi = mid
        else:
            lo = mid
    count = lo
    top = 2**bits - 1
    out.append(f"bound zero {'panic' if panics(exe, 0) else 'ok'}")
    out.append(f"bound count {count}")
    out.append(f"bound above {count + 1} {'panic' if panics(exe, count + 1) else 'ok'}")
    out.append(f"bound max {top} {'panic' if panics(exe, top) else 'ok'}")
    out.append(f"bound over {top + 1} {'panic' if panics(exe, top + 1) else 'ok'}")
    ranges = [(1, count)] if count <= 1000 else [(1, 4), (count - 2, count)]
    for lo_, hi_ in ranges:
        t = run([str(exe), "table", str(lo_), str(hi_)])
        if t.returncode != 0:
            raise SystemExit(f"{name}: table {lo_} {hi_} failed")
        out += t.stdout.splitlines()
    return out


def main():
    args = [a for a in sys.argv[1:] if a != "--quick"]
    quick = "--quick" in sys.argv[1:]
    if not 1 <= len(args) <= 2:
        raise SystemExit(__doc__)
    zig = args[0]
    version = run([zig, "version"]).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="air2lean-error-width-") as work:
        hidden = hidden_errors(zig, work)
        lines = [f"meta zig {version}", f"meta hidden {hidden}"]
        for name, limit, total in CONFIGS:
            if quick and name in BIG:
                continue
            lines += observe(zig, name, limit, total, hidden, work)
    text = "\n".join(lines) + "\n"
    if len(args) == 2:
        Path(args[1]).write_text(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
