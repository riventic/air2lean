#!/usr/bin/env bash
# Native x86_64-linux differential run of one (optimize mode, backend) pair in the pinned
# linux/amd64 local-CI image (emulated on an arm64 host), reusing scripts/local-ci.sh's cache
# volumes. Stock Zig, the Lean model side and the comparison all run inside the container, so the
# float model's reference host (Linux x86_64) applies. Writes the differential summary and cases
# next to the requested output directory (docs/build-modes.md).
#
# The native side (harnesses, libm and asm archives) is cross-compiled on the host for
# x86_64-linux by the host's stock Zig of the same version (`scripts/cas.py host-zig`; with
# AIR2LEAN_CAS_DIR set, through the shared cache) and only run in the container, so no compiler
# runs emulated (`diff.sh --build-only`, AIR2LEAN_DIFF_PREBUILT). AIR2LEAN_BUILD_MODE_CROSS=0 builds
# inside the container instead; both build with `-target x86_64-linux`. zig.sha256 names the
# compiler that built the binaries.
#
# usage: scripts/build-mode-docker.sh <version> <Debug|ReleaseSafe|ReleaseFast|ReleaseSmall> \
#          <llvm|stage2_x86_64> <output-dir> ["<examples>"]
# Run it under scripts/build-guard.py (AIR2LEAN_BUILD_LOCK) like every other Zig/Docker workload.
set -euo pipefail

if [ "${1:-}" = --inside ]; then
  shift
  version=$1 optimize=$2 backend=$3 examples=$4
  mkdir -p /artifacts /work
  cd /work
  tar -xf /snapshot/source.tar -C /work
  sha=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
  hostsha=$(zig-patch/toml-get.sh "[ci.host-zig.\"$version\"]" sha256)
  export ELAN_HOME=/cache/elan-$sha LEAN_NUM_THREADS=2
  export ZIG_GLOBAL_CACHE_DIR=/cache/zig-global
  zig=/cache/host-zig-$hostsha/zig
  [ -x "$zig" ] || { echo "error: no verified stock zig at $zig (run scripts/local-ci.sh once)" >&2; exit 1; }
  export PATH="$ELAN_HOME/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
  lake build
  export AIR2LEAN_ZIG=$zig AIR2LEAN_DIFF_OPTIMIZE=$optimize AIR2LEAN_DIFF_BACKEND=$backend
  export AIR2LEAN_DIFF_REPORT=/work/tests/diff/out/report.json AIR2LEAN_EXAMPLES=$examples
  # Rosetta cannot load the empty RELRO segment of release builds ("bss_size overflow").
  export AIR2LEAN_DIFF_LINK_FLAGS='-z norelro' AIR2LEAN_DIFF_TARGET=x86_64-linux
  if [ -d /snapshot/native ]; then
    export AIR2LEAN_DIFF_PREBUILT=/snapshot/native
    cp /snapshot/native/zig.sha256 /artifacts/zig.sha256
  else
    sha256sum "$zig" | cut -d' ' -f1 >/artifacts/zig.sha256
  fi
  status=0
  bash scripts/diff.sh >/artifacts/diff.log 2>&1 || status=$?
  cp -a /work/tests/diff/out/report.json /work/tests/diff/out/report.json.jsonl /artifacts/ 2>/dev/null || true
  echo "$status" >/artifacts/exit-status
  tail -n 40 /artifacts/diff.log >&2
  exit 0
fi

[ "$#" -ge 4 ] || { sed -n 17,19p "$0" >&2; exit 2; }
version=$1 optimize=$2 backend=$3 out=$4 examples=${5:-}
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
if [ -z "$examples" ]; then
  source scripts/example-selection.sh
  examples=$(air2lean_default_examples "$repo" "$version" x86_64)
fi
snapshot=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-build-mode.XXXXXX")
container=
cleanup() {
  status=$?
  trap - EXIT
  if [ -n "$container" ]; then
    mkdir -p "$out"
    docker cp "$container:/artifacts/." "$out" || status=1
    if [ -f "$snapshot/stage2/excluded-examples.json" ]; then cp "$snapshot/stage2/excluded-examples.json" "$out/"; fi
    # The container always exits 0 so its artifacts are kept; the diff status is the result.
    if [ "$status" -eq 0 ] && [ -f "$out/exit-status" ]; then status=$(cat "$out/exit-status"); fi
    docker rm -f "$container" >/dev/null 2>&1 || true
  fi
  rm -rf "$snapshot"
  exit "$status"
}
trap cleanup EXIT
if [ "$backend" = stage2_x86_64 ]; then
  # The self-hosted backend's own translations (scripts/stage2-translations.py): its AIR export
  # under the stage2_x86_64 profile, translated, must be the translation the run's Lean side
  # builds; an example the stage2_x86_64 rules reject, or that the backend cannot compile
  # (examples/asm), is left out and listed in <output-dir>/excluded-examples.json.
  python3 -B scripts/stage2-translations.py --version "$version" --examples "$examples" --out "$snapshot/stage2"
  examples=$(cat "$snapshot/stage2/examples")
fi
git ls-files -z | while IFS= read -r -d '' path; do
  case "$path" in
    .git|.git/*|.lake|.lake/*|*/.lake|*/.lake/*|zig-air-*/*|host-zig/*) continue ;;
  esac
  if [ -e "$path" ] || [ -L "$path" ]; then printf '%s\0' "$path"; fi
done >"$snapshot/files"
COPYFILE_DISABLE=1 tar -cf "$snapshot/source.tar" --null -T "$snapshot/files"
if [ "${AIR2LEAN_BUILD_MODE_CROSS:-1}" != 0 ]; then
  host_zig=$(python3 -B scripts/cas.py host-zig "$version")
  AIR2LEAN_ZIG=$host_zig AIR2LEAN_DIFF_OPTIMIZE=$optimize AIR2LEAN_DIFF_BACKEND=$backend \
    AIR2LEAN_DIFF_LINK_FLAGS='-z norelro' AIR2LEAN_DIFF_TARGET=x86_64-linux AIR2LEAN_EXAMPLES=$examples \
    bash scripts/diff.sh --build-only "$snapshot/native"
  shasum -a 256 "$host_zig" | cut -d' ' -f1 >"$snapshot/native/zig.sha256"
fi
case "$(docker info --format '{{.Architecture}}')" in
  aarch64|arm64) python_arch=arm64 ;;
  x86_64|amd64) python_arch=amd64 ;;
  *) echo 'error: unsupported Docker engine architecture' >&2; exit 1 ;;
esac
image="air2lean-local-ci:ubuntu24-amd64-python-$python_arch"
lake_key=$(cat lean-toolchain lake-manifest.json | shasum -a 256 | cut -c1-16)
diff_key=$(cat tests/diff/lean-toolchain tests/diff/lake-manifest.json | shasum -a 256 | cut -c1-16)
tool_volume=${AIR2LEAN_LOCAL_TOOL_VOLUME:-air2lean-local-linux-toolchains}
cache_namespace=$(printf '%s' "$tool_volume" | shasum -a 256 | cut -c1-16)
# Sized like scripts/local-ci.sh (AIR2LEAN_LOCAL_CPUS, AIR2LEAN_LOCAL_MEMORY); scripts/diff.sh
# builds and runs that many harnesses at once.
container=$(docker create --platform linux/amd64 --memory="${AIR2LEAN_LOCAL_MEMORY:-8g}" \
  --memory-swap="${AIR2LEAN_LOCAL_MEMORY:-8g}" --cpus="${AIR2LEAN_LOCAL_CPUS:-2}" --pids-limit=512 --init \
  --mount "type=bind,src=$snapshot,dst=/snapshot,readonly" \
  --mount "type=volume,src=$tool_volume,dst=/cache" \
  --mount "type=volume,src=air2lean-linux-amd64-$cache_namespace-lake-$lake_key,dst=/work/.lake" \
  --mount "type=volume,src=air2lean-linux-amd64-$cache_namespace-diff-$diff_key,dst=/work/tests/diff/.lake" \
  "$image" bash -c 'tar -xOf /snapshot/source.tar scripts/build-mode-docker.sh > /tmp/bm.sh; exec bash /tmp/bm.sh --inside "$@"' \
  build-mode "$version" "$optimize" "$backend" "$examples")
docker start -a "$container"
