#!/usr/bin/env python3
"""F03 native observation: run probe.zig's strict/fast case pairs and print the results as JSON.

  observe.py ZIG [--target T] [--mcpu CPU] [--optimize MODE ...]

Builds probe.zig as a shared library with ZIG for the host (the script must run on the target:
x86_64-linux in a `--platform linux/amd64` container, aarch64-macos on the host) and runs each case
in a forked child. A result is the 64-bit result word in hex, or `trap` for a child that died on a
signal (a safety panic). Output: {"zig": ..., "target": ..., "mcpu": ...,
"results": {mode: {case: word|"trap"}}}, one entry per --optimize mode. docs/research/F03.md tabulates the committed records.
"""
import argparse
import ctypes
import json
import os
import platform
import subprocess
import sys
import tempfile
from pathlib import Path

PROBE = Path(__file__).with_name('probe.zig')


def host_target() -> str:
    arch = {'x86_64': 'x86_64', 'AMD64': 'x86_64', 'arm64': 'aarch64', 'aarch64': 'aarch64'}[platform.machine()]
    return f'{arch}-{ {"Darwin": "macos", "Linux": "linux"}[platform.system()]}'


def build(zig: str, optimize: str, mcpu: str | None, out: Path) -> Path:
    binary = out / ('probe.dylib' if platform.system() == 'Darwin' else 'probe.so')
    command = [zig, 'build-lib', '-dynamic', f'-O{optimize}', '--cache-dir', str(out / 'cache'),
               '--global-cache-dir', str(out / 'gcache'), f'-femit-bin={binary}', str(PROBE)]
    if platform.system() == 'Darwin':
        command.insert(3, '-lc')
    if mcpu:
        command[3:3] = [f'-mcpu={mcpu}']
    subprocess.run(command, check=True, cwd=out)
    return binary


def run_case(lib: ctypes.CDLL, index: int) -> str:
    """One case in a forked child; the panic report is not part of the observation."""
    read, write = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(read)
        os.dup2(os.open(os.devnull, os.O_WRONLY), 2)
        with os.fdopen(write, 'w') as pipe:
            pipe.write(f'{lib.fm_run(index):016x}\n')
        os._exit(0)
    os.close(write)
    with os.fdopen(read) as pipe:
        text = pipe.read().strip()
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status) or (os.WIFEXITED(status) and os.WEXITSTATUS(status) != 0 and not text):
        return 'trap'
    return text


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('zig')
    parser.add_argument('--mcpu')
    parser.add_argument('--optimize', nargs='+', default=['Debug', 'ReleaseSafe', 'ReleaseFast'])
    args = parser.parse_args()
    version = subprocess.run([args.zig, 'version'], capture_output=True, text=True, check=True).stdout.strip()
    results = {}
    for optimize in args.optimize:
        with tempfile.TemporaryDirectory() as tmp:
            lib = ctypes.CDLL(str(build(args.zig, optimize, args.mcpu, Path(tmp))))
            lib.fm_count.restype = ctypes.c_size_t
            lib.fm_name.restype = ctypes.c_char_p
            lib.fm_name.argtypes = [ctypes.c_size_t]
            lib.fm_run.restype = ctypes.c_uint64
            lib.fm_run.argtypes = [ctypes.c_size_t]
            results[optimize] = {lib.fm_name(i).decode(): run_case(lib, i) for i in range(lib.fm_count())}
    json.dump({'zig': version, 'target': host_target(), 'mcpu': args.mcpu or 'baseline',
               'results': results}, sys.stdout, indent=1, sort_keys=True)
    print()


if __name__ == '__main__':
    main()
