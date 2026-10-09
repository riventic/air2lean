#!/bin/sh
# Inside a Linux container: build native.zig with stock Zig 0.17.0, compare with the Lean run.
set -e
cd /tmp
echo "host $(uname -m) zig $(/zig/zig version)"
/zig/zig build-exe -OReleaseSafe --dep divceil -Mroot=/out/divceil/native.zig \
  -Mdivceil=/out/divceil/divceil.zig -femit-bin=/tmp/native --cache-dir /tmp/zc --global-cache-dir /tmp/zg
/tmp/native > /tmp/native.txt
python3 - <<'PY'
import subprocess
lean = open('/out/dc-lean.txt').read().splitlines()
native = open('/tmp/native.txt').read().splitlines()
assert len(lean) == len(native) > 0
msg = {'panic:divByZero': 'division by zero', 'panic:overflow': 'integer overflow'}
v = p = 0
for l, n in zip(lean, native):
    lf, nf = l.split(' '), n.split(' ')
    assert lf[:3] == nf[:3], (l, n)
    if nf[3] != 'panic':
        assert l == n, (l, n); v += 1; continue
    r = subprocess.run(['/tmp/native', '--one', *nf[:3]], capture_output=True, text=True)
    assert r.returncode != 0 and msg[lf[3]] in r.stderr, (l, r.returncode, r.stderr[-200:])
    p += 1
print(f'divCeil differential: {v} values equal, {p} safety panics agree ({len(lean)} inputs)')
PY
