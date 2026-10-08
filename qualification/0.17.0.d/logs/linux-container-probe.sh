#!/bin/sh
cd /tmp
echo "host $(uname -m) zig $(/zig/zig version) sha256 $(sha256sum /zig/zig | cut -d' ' -f1)"
for mode in ReleaseSafe ReleaseFast; do
  python3 -B /w/scripts/abi-probe.py observe --zig /zig/zig --profile "/w/tests/roadmap/abi-probes/$1-$mode.json" \
    --output "/out/$1-$mode.json" > "/out/probe_layout_$1-$mode.log" 2>&1
  echo "ABI $1 $mode $?" | tee -a "/out/probe_layout_$1-$mode.log"
done
if [ "$1" = x86_64-linux-gnu ]; then
  AIR2LEAN_ZIG=/zig/zig bash /w/scripts/floatprobe.sh > /out/probe_float.log 2>&1
  echo "FLOAT $?" | tee -a /out/probe_float.log
fi
