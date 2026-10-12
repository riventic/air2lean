#!/usr/bin/env python3
"""Checks the recorded LLVM observations behind the poison-on-use decision (docs/research/V01-V02.md).

For every function of probe.zig the recorded IR (Zig 0.14.1 and 0.15.2, ReleaseSafe, -fllvm) forms
the pointer with `getelementptr inbounds` and feeds the result straight to `icmp`, with no
`freeze` in the module: LLVM's poison reaches the comparison, so a compare of a pointer formed
outside its allocation is poison (undefined behaviour only where it is branched on).
With a stock `zig` of a recorded version on PATH, `--rerun` regenerates the IR and compares."""
import re, subprocess, sys, pathlib, tempfile

HERE = pathlib.Path(__file__).resolve().parent
VERSIONS = ["0.14.1", "0.15.2"]


def check(text: str, label: str) -> list[str]:
    errs = []
    if "freeze" in text:
        errs.append(f"{label}: a freeze instruction appears")
    if len(re.findall(r"= getelementptr inbounds i8, ptr %0, i64 %\d+", text)) < 2:
        errs.append(f"{label}: cmpFar/cmpFarLt do not form the pointer with getelementptr inbounds")
    if not re.search(r"icmp eq ptr %3, %1", text) or not re.search(r"icmp ult ptr %3, %1", text):
        errs.append(f"{label}: the gep result does not feed icmp directly")
    # branchFar tests `@intFromPtr(p + n) == 0`; LLVM folds it: an inbounds gep of a nonnull base
    # is not null (an optimizer fact only poison semantics licenses).
    if not re.search(r"@branchFar.*?ret i8 2", text, re.S):
        errs.append(f"{label}: branchFar was not folded to its null-free result")
    return errs


def main() -> int:
    errs = []
    for v in VERSIONS:
        text = (HERE / f"observed-{v}-llvm.txt").read_text()
        errs += check(text, v)
    if "--rerun" in sys.argv:
        out = subprocess.run(["zig", "version"], capture_output=True, text=True).stdout.strip()
        if out in VERSIONS:
            with tempfile.TemporaryDirectory() as d:
                ll = pathlib.Path(d) / "p.ll"
                subprocess.run(["zig", "build-obj", "-OReleaseSafe", "-fllvm", f"-femit-llvm-ir={ll}",
                                "-fno-emit-bin", str(HERE / "probe.zig")], check=True, cwd=d)
                errs += check(ll.read_text(), f"{out} (fresh)")
        else:
            print(f"--rerun skipped: zig {out} is not a recorded version")
    for e in errs:
        print("FAIL", e)
    print("ok" if not errs else "failed")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
