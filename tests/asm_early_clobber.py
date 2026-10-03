#!/usr/bin/env python3
"""Keep a third-argument divisor out of the EDX register cleared by divmod.

Cross-compiles the actual example for SysV x86_64, so this regression also runs on
arm64 hosts without executing an unsupported instruction. Run with a stock Zig
path as the first argument (defaults to zig).
"""
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
ZIG = sys.argv[1] if len(sys.argv) > 1 else "zig"
with tempfile.TemporaryDirectory(prefix="air2lean-asm-clobber-") as temporary:
    directory = pathlib.Path(temporary)
    wrapper = directory / "wrapper.zig"
    wrapper.write_text('const ex = @import("ex");\nexport fn divmod3(keep: u32, a: u32, b: u32) u64 { return ex.divmod(a, b) + keep; }\n')
    assembly = directory / "wrapper.s"
    subprocess.run([ZIG, "build-obj", "-target", "x86_64-linux", "-OReleaseFast", "-femit-asm=" + str(assembly), "-femit-bin=" + str(directory / "wrapper.o"), "--cache-dir", str(directory / "cache"), "--global-cache-dir", str(directory / "global"), "--dep", "ex", "-Mroot=" + str(wrapper), "-Mex=" + str(ROOT / "examples/asm/asm.zig")], check=True, cwd=ROOT)
    text = assembly.read_text()
    body = text.split("divmod3:", 1)[1].split(".Lfunc_end", 1)[0]
    assert re.search(r"\b(?:div|divl)\s+", body), "divmod was not inlined; regression cannot inspect its register allocation"
    assert not re.search(r"\b(?:div|divl)\s+(?:%?edx)\b", body), "divisor allocated to EDX, which the preceding xor clears"
print("divmod3 divisor survives the early EDX write")
