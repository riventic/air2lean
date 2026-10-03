#!/usr/bin/env bash
# Safe shell-wrapper/cache regressions. Optional patched compilers exercise JSON fidelity.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-exporter-check.XXXXXX")
trap 'rm -rf "$work"' EXIT
fail() { echo "exporter checks: $*" >&2; exit 1; }
mkdir -p "$work/lock/bin"
cat > "$work/lock/bin/zig" <<'SPY'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$REVIEW_SPY_ARGS"
SPY
chmod +x "$work/lock/bin/zig"
"$repo_root/zig-patch/lock.sh" "$work/lock"
export REVIEW_SPY_ARGS="$work/args"
"$work/lock/bin/zig" build-obj -fno-emit-bin source.zig
[ "$(sed -n '2p' "$work/args")" = -fno-emit-bin ] || fail 'missing guaranteed no-emission option'
"$work/lock/bin/zig" build-obj --cache-dir -fno-emit-bin source.zig
[ "$(sed -n '2p' "$work/args")" = -fno-emit-bin ] || fail 'option value bypassed no-emission guard'
for args in response emit; do
  rm -f "$work/args"
  if [ "$args" = response ]; then arg="@$work/override.rsp"; else arg=-femit-bin; fi
  if "$work/lock/bin/zig" build-obj -fno-emit-bin "$arg" source.zig 2>/dev/null; then
    fail "accepted $args emission override"
  fi
  [ ! -e "$work/args" ] || fail 'rejected command reached compiler'
done
"$repo_root/zig-patch/lock.sh" "$work/lock"
"$work/lock/bin/zig" version
[ "$(cat "$work/args")" = version ] || fail 'idempotent lock broke version command'

# Synthetic pinned source exercises the real download/verify/patch/build code without network.
mkdir -p "$work/build/air-json" "$work/build/hooks" "$work/source/zig/src/Air" "$work/mocks"
cp "$repo_root/zig-patch/build.sh" "$repo_root/zig-patch/toml-get.sh" "$repo_root/zig-patch/lock.sh" "$work/build/"
cp "$repo_root/zig-patch/air-json/json.zig" "$work/build/air-json/"
: > "$work/source/zig/src/Air/.keep"
: > "$work/build/hooks/hook.patch"
tar -cJf "$work/source.tar.xz" -C "$work/source" zig
if command -v shasum >/dev/null 2>&1; then digest=$(shasum -a 256 "$work/source.tar.xz" | awk '{print $1}');
else digest=$(sha256sum "$work/source.tar.xz" | awk '{print $1}'); fi
cat > "$work/build/versions.toml" <<TOML
["0.15.2"]
url = "https://invalid.example/test.tar.xz"
sha256 = "$digest"
hook = "hooks/hook.patch"
TOML
cat > "$work/mocks/curl" <<'CURL'
#!/usr/bin/env bash
set -euo pipefail
while [ "$#" -gt 0 ]; do
  if [ "$1" = --output ]; then shift; out=$1; fi
  shift
done
printf '%s\n' "$out" >> "$REVIEW_DOWNLOAD_LOG"
if [ "${REVIEW_BAD_DOWNLOAD:-0}" = 1 ]; then
  # The digest-failure case has one writer and must not wait at the two-writer barrier.
  printf broken > "$out"
else
  cp "$REVIEW_SOURCE_TARBALL" "$out"
  # Neither valid download may return (and publish its cache entry) until both have
  # arrived. A bounded wait reports setup failure instead of hanging the test.
  : > "$REVIEW_DOWNLOAD_BARRIER/$$"
  for ((attempt = 0; attempt < 600; attempt++)); do
    if [ "$(find "$REVIEW_DOWNLOAD_BARRIER" -type f | wc -l | tr -d ' ')" -ge 2 ]; then
      exit 0
    fi
    sleep 0.05
  done
  echo 'mock curl: timed out waiting for both concurrent downloads' >&2
  exit 1
fi
CURL
cat > "$work/mocks/zig" <<'ZIG'
#!/usr/bin/env bash
if [ "${1:-}" = version ]; then echo 0.15.2; exit 0; fi
for expected in -Doptimize=Debug -Dstrip=true -j1; do
  found=0
  for arg in "$@"; do [ "$arg" != "$expected" ] || found=1; done
  [ "$found" = 1 ] || { echo "missing bootstrap option: $expected" >&2; exit 1; }
done
while [ "$#" -gt 0 ]; do
  if [ "$1" = --prefix ]; then shift; prefix=$1; fi
  shift
done
mkdir -p "$prefix/bin"
printf '#!/usr/bin/env bash\necho 0.15.2\n' > "$prefix/bin/zig"
chmod +x "$prefix/bin/zig"
if [ "${REVIEW_BUILD_MODE:-}" = installed-failure ]; then
  echo 'mock builder failed after installing raw compiler' >&2
  exit 1
fi
ZIG
chmod +x "$work/mocks/"*
export PATH="$work/mocks:$PATH" REVIEW_SOURCE_TARBALL="$work/source.tar.xz" REVIEW_DOWNLOAD_LOG="$work/downloads"
export REVIEW_DOWNLOAD_BARRIER="$work/download-barrier"
mkdir -p "$REVIEW_DOWNLOAD_BARRIER"
export AIR2LEAN_CACHE="$work/cache" AIR2LEAN_LLVM=0 AIR2LEAN_OPTIMIZE=Debug REVIEW_BUILD_MODE= REVIEW_BAD_DOWNLOAD=0
"$work/build/build.sh" 0.15.2 "$work/one" > "$work/one.log" 2>&1 &
a=$!
"$work/build/build.sh" 0.15.2 "$work/two" > "$work/two.log" 2>&1 &
b=$!
wait "$a" || { cat "$work/one.log"; fail 'first concurrent build failed'; }
wait "$b" || { cat "$work/two.log"; fail 'second concurrent build failed'; }
[ "$(sort -u "$work/downloads" | wc -l | tr -d ' ')" = 2 ] || fail 'downloads shared a temporary file'
[ -f "$AIR2LEAN_CACHE/zig-0.15.2.tar.xz" ] || fail 'verified cache entry missing'
[ "$(find "$AIR2LEAN_CACHE" -type f | wc -l | tr -d ' ')" = 1 ] || fail 'temporary download leaked'
"$work/one/bin/zig" version >/dev/null
export AIR2LEAN_CACHE="$work/bad-cache" REVIEW_BAD_DOWNLOAD=1
if "$work/build/build.sh" 0.15.2 "$work/bad" > "$work/bad.log" 2>&1; then fail 'invalid download passed digest'; fi
[ "$(find "$AIR2LEAN_CACHE" -type f | wc -l | tr -d ' ')" = 0 ] || fail 'invalid download published or leaked'

# A failed install never exposes the raw staged compiler or changes a previous prefix.
export AIR2LEAN_CACHE="$work/cache" REVIEW_BAD_DOWNLOAD=0 REVIEW_BUILD_MODE=installed-failure
cp "$work/one/bin/zig" "$work/previous-wrapper"
printf 'caller-owned file\n' > "$work/one/keep.txt"
for prefix in "$work/one" "$work/never-published"; do
  if "$work/build/build.sh" 0.15.2 "$prefix" > "$work/failed-install.log" 2>&1; then
    fail 'failed builder published an installation'
  fi
  grep -q 'failed after installing raw compiler' "$work/failed-install.log" || fail 'builder failure not exercised'
done
cmp "$work/previous-wrapper" "$work/one/bin/zig" || fail 'failed build changed previous compiler'
[ -f "$work/one/keep.txt" ] || fail 'failed build removed caller file'
[ ! -e "$work/never-published" ] || fail 'failed build exposed a compiler'
if "$work/one/bin/zig" build-exe source.zig 2>/dev/null; then fail 'previous compiler lost AIR-only lock'; fi
if find "$work" -maxdepth 1 -name '*.air2lean-stage.*' -o -name '*.air2lean-build.lock' | grep -q .; then
  fail 'failed install leaked staging directory or writer lock'
fi
export REVIEW_BUILD_MODE=
# Fail or interrupt the final rename after the previous installation has been moved.
# The EXIT/signal cleanup must restore it before releasing the writer lock.
real_mv=$(command -v mv)
export REVIEW_REAL_MV="$real_mv"
cat > "$work/mocks/mv" <<'MV'
#!/usr/bin/env bash
for arg in "$@"; do
  case "$arg" in *.air2lean-stage.*)
    [ -d "$arg" ] || continue
    case "${REVIEW_PUBLICATION_MODE:-}" in
      fail) echo 'mock publication failed' >&2; exit 1 ;;
      signal) echo 'mock publication interrupted' >&2; kill -TERM "$PPID"; exit 143 ;;
    esac ;;
  esac
done
exec "$REVIEW_REAL_MV" "$@"
MV
chmod +x "$work/mocks/mv"
for mode in fail signal; do
  if REVIEW_PUBLICATION_MODE="$mode" "$work/build/build.sh" 0.15.2 "$work/one" > "$work/publication-$mode.log" 2>&1; then
    fail "publication $mode unexpectedly passed"
  fi
  grep -q 'mock publication' "$work/publication-$mode.log" || fail "publication $mode not exercised"
  cmp "$work/previous-wrapper" "$work/one/bin/zig" || fail "publication $mode did not restore compiler"
  [ -f "$work/one/keep.txt" ] || fail "publication $mode discarded caller-owned file"
  [ ! -e "$work/.one.air2lean-build.lock" ] || fail "publication $mode leaked writer lock"
done
# An occupied writer lock prevents a same-prefix build from reaching installation.
mkdir "$work/.one.air2lean-build.lock"
if "$work/build/build.sh" 0.15.2 "$work/one" > "$work/locked-install.log" 2>&1; then
  fail 'same-prefix writer bypassed lock'
fi
grep -q 'another build owns' "$work/locked-install.log" || fail 'writer conflict not diagnosed'
[ -d "$work/.one.air2lean-build.lock" ] || fail 'losing writer removed another writer lock'
rmdir "$work/.one.air2lean-build.lock"
"$work/build/build.sh" 0.15.2 "$work/one" > "$work/replacement.log" 2>&1
previous=$(sed -n 's/^previous installation retained: //p' "$work/replacement.log")
[ -n "$previous" ] && [ -f "$previous/keep.txt" ] || fail 'replacement discarded caller-owned previous files'
cmp "$work/previous-wrapper" "$previous/bin/zig" || fail 'previous compiler backup changed'
if "$work/one/bin/zig" build-exe source.zig 2>/dev/null; then fail 'published compiler was not locked'; fi

# Opt-in actual compiler tests. Each compiler must be patched and locked; library paths can
# be supplied for builds using -Dno-lib. AIR2LEAN_REVIEW_TRANSLATOR enables round-trip parsing.
for version in 14 15 16; do
  eval "compiler=\${AIR2LEAN_REVIEW_ZIG${version}:-}"
  eval "lib=\${AIR2LEAN_REVIEW_LIB${version}:-}"
  [ -n "$compiler" ] || continue
  lib_args=(-OReleaseSafe -fno-error-tracing)
  [ -z "$lib" ] || lib_args+=(--zig-lib-dir "$lib")
  out="$work/air$version"
  ZIG_AIR_JSON_DIR="$out" ZIG_AIR_JSON_FILTER=exporter. "$compiler" build-obj -fno-emit-bin \
    "${lib_args[@]}" "$repo_root/tests/review/exporter.zig" \
    --cache-dir "$work/zig-cache$version" --global-cache-dir "$work/zig-global$version"
  python3 - "$out" "$version" <<'PY'
import glob, json, os, sys
files = glob.glob(os.path.join(sys.argv[1], '*.json'))
assert files, 'no JSON functions exported'
for path in files:
    data=json.load(open(path))
    assert data['target_endian']=='little', path
    def walk(value):
        if isinstance(value,dict):
            if 'val' in value:
                assert '@sizeOf' not in value['val'] and '@alignOf' not in value['val'], (path,value)
            for child in value.values(): walk(child)
        elif isinstance(value,list):
            for child in value: walk(child)
    walk(data)
def constant_shape(ref):
    # Type IDs depend on discovery order; the constant's fields and their values do not.
    return {key: [constant_shape(child) for child in value] if key == 'elems' else value
            for key, value in ref.items() if key in ('elems', 'enum', 'val')}

if sys.argv[2] == '16':
    expected_constants = {'packedConstant': {'val': '69'}, 'nestedConstant': {'val': '158'}}
else:
    # Before 0.16 packed structs are aggregates, including their enum and nested fields.
    expected_constants = {
        'packedConstant': {'elems': [{'enum': '1'}, {'val': '17'}]},
        'nestedConstant': {'elems': [{'elems': [{'val': '-2'}, {'val': 'true'}]}, {'val': '9'}]},
    }
for name, expected in expected_constants.items():
    data=json.load(open(os.path.join(sys.argv[1],f'exporter.{name}.json')))
    returns=[i for i in data['body'] if i['tag'] in ('ret','ret_safe')]
    assert len(returns)==1 and constant_shape(returns[0]['args'][0])==expected, (name,returns)
PY
  if [ -n "${AIR2LEAN_REVIEW_TRANSLATOR:-}" ]; then
    "$AIR2LEAN_REVIEW_TRANSLATOR" "$out" -o "$work/Gen$version.lean" --namespace ExporterReview
    [ -f "$work/Gen$version.lean" ] || fail 'translator failed to produce output'
  fi
done
echo 'exporter checks passed'
