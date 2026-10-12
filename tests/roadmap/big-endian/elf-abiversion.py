#!/usr/bin/env python3
"""Clear EI_ABIVERSION of a static big-endian ELF64 executable in place.

Zig's mips64 musl executables carry ABI version 1; the qemu-mips64 binfmt handler of the Docker
VM matches version 0 only. The byte names no code or data, so the program runs unchanged.
"""
import sys

path = sys.argv[1]
data = bytearray(open(path, 'rb').read())
if data[:4] != b'\x7fELF' or data[4] != 2 or data[5] != 2:
    sys.exit(f'{path}: not a big-endian ELF64 file')
data[8] = 0
open(path, 'wb').write(data)
