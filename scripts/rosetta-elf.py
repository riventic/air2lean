#!/usr/bin/env python3
"""Make LLD-linked x86_64 ELF executables loadable by Rosetta (docs/rosetta.md).

usage: rosetta-elf.py PATH...

Rosetta for Linux refuses a PT_LOAD whose p_filesz is 0 and p_memsz is not
("rosetta error: bss_size overflow"). LLD emits exactly one such segment, the "empty RELRO"
segment, when nothing but alignment padding is RELRO: sections `.got` (size 0) and
`.relro_padding`, a PT_GNU_RELRO over the same range. A program that is linked by the
compiler under our control gets `-z norelro` instead (AIR2LEAN_ROSETTA_LINK_FLAGS). This tool is for
binaries a stock `zig` builds and runs by itself, where there is no flag to pass: the JIT-compiled
`zig build` runner (`maker`, `configurer`) in Zig's cache.

For each executable x86_64 ELF file under the PATHs (a file or a directory, recursively) it turns the
empty PT_LOAD and the PT_GNU_RELRO inside it into PT_NULL, but only when every allocated section in the
range is empty or `.relro_padding`: the range then holds no program data, and nothing is mapped
differently for the program. Anything else is left alone (and listed on stderr). Idempotent. Prints
the number of patched files.
"""
import os
import struct
import sys

PT_NULL, PT_LOAD, PT_GNU_RELRO = 0, 1, 0x6474E552
SHF_ALLOC = 2


def sections(data, ehdr):
    shoff, = struct.unpack_from('<Q', data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from('<HHH', data, 0x3A)
    if shoff == 0 or shnum == 0 or shoff + shnum * shentsize > len(data):
        return None
    raw = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shentsize) for i in range(shnum)]
    strtab = raw[shstrndx]
    names = data[strtab[4]:strtab[4] + strtab[5]]
    return [(names[s[0]:names.index(b'\0', s[0])].decode('latin-1'), s[2], s[3], s[5]) for s in raw]


def patch(data):
    """The patched bytes, or None when there is nothing to patch; ValueError when it is unsafe."""
    if data[:4] != b'\x7fELF' or data[4] != 2 or data[5] != 1:
        return None
    if struct.unpack_from('<H', data, 0x12)[0] != 62:
        return None
    phoff, = struct.unpack_from('<Q', data, 0x20)
    phentsize, phnum = struct.unpack_from('<HH', data, 0x36)
    phdrs = []
    for i in range(phnum):
        at = phoff + i * phentsize
        t, flags, off, va, pa, filesz, memsz, align = struct.unpack_from('<IIQQQQQQ', data, at)
        phdrs.append((at, t, va, filesz, memsz))
    empty = [h for h in phdrs if h[1] == PT_LOAD and h[3] == 0 and h[4] > 0]
    if not empty:
        return None
    secs = sections(data, None)
    if secs is None:
        raise ValueError('no section headers to check the empty segment against')
    out = bytearray(data)
    for at, _, va, _, memsz in empty:
        for name, flags, addr, size in secs:
            if flags & SHF_ALLOC and size > 0 and va <= addr < va + memsz and name != '.relro_padding':
                raise ValueError(f'empty segment at {va:#x} holds section {name}')
        struct.pack_into('<I', out, at, PT_NULL)
        for rat, t, rva, _, rmem in phdrs:
            if t == PT_GNU_RELRO and va <= rva and rva + rmem <= va + memsz:
                struct.pack_into('<I', out, rat, PT_NULL)
            elif t == PT_GNU_RELRO and rva < va + memsz and va < rva + rmem:
                raise ValueError(f'RELRO at {rva:#x} extends past the empty segment at {va:#x}')
    return bytes(out)


def files(paths):
    for p in paths:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                for n in names:
                    yield os.path.join(root, n)
        elif os.path.exists(p):
            yield p


def main(paths):
    patched = 0
    for path in files(paths):
        try:
            if os.path.islink(path) or not os.path.isfile(path) or not os.access(path, os.X_OK):
                continue
            with open(path, 'rb') as f:
                data = f.read()
            new = patch(data)
            if new is None:
                continue
            tmp = path + '.rosetta-tmp'
            with open(tmp, 'wb') as f:
                f.write(new)
            os.chmod(tmp, os.stat(path).st_mode & 0o7777)
            os.replace(tmp, path)
            patched += 1
        except (ValueError, struct.error, OSError) as error:
            print(f'rosetta-elf: {path}: left alone: {error}', file=sys.stderr)
    print(patched)


if __name__ == '__main__':
    main(sys.argv[1:])
