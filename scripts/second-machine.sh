#!/usr/bin/env bash
# Second-machine project check (I03): reproduce `scripts/project.py check` for one committed
# manifest from a fresh Git clone in a clean Linux container, then compare its record with a
# record produced elsewhere (normally the host checkout).
#
# Usage: scripts/second-machine.sh [--platform linux/arm64|linux/amd64] [--rev REV]
#                                  [--manifest PATH] [--compare RECORD] [--keep-image]
#   --platform  container platform (default: compatibility.json clean_environment.platform)
#   --rev       committed ref (branch, tag or HEAD; default HEAD) to clone; working-tree edits
#               never reach the container
#   --manifest  manifest path inside the clone (default example-project.json)
#   --compare   after a reproduced run, `project.py compare-records RECORD <container record>`
#   --keep-image keep the Docker image afterwards
# The container is Dockerfile.clean-env (Ubuntu 24.04, no Lean/elan/Zig/caches). Inside it
# clones a `git bundle` of REV, installs the sha256-pinned elan for the container architecture
# (zig-patch/versions.toml [ci.elan] or [ci.elan-aarch64]) and the lean-toolchain release,
# builds the translator (`lake build air2lean`), and runs `project.py check`. Zig is not needed:
# the manifest translates committed AIR.
# Results: <results>/check/ (record.json and all check evidence), clone.json, build-air2lean.log.
# Env: AIR2LEAN_SECOND_RESULTS (default .lake/second-machine-results), AIR2LEAN_SECOND_TIMEOUT
# (default 6h), AIR2LEAN_SECOND_MEMORY (default 10g), AIR2LEAN_SECOND_CPUS (default 4).
# Exit status: the container's (`project.py check` exits 1 on a failed record), then compare-records'.
set -euo pipefail

if [ "${1:-}" = --inside ]; then
  rev=$2 manifest=$3
  set -x
  out=/results
  git clone --quiet --no-checkout /snapshot/repo.bundle "$HOME/air2lean"
  cd "$HOME/air2lean"
  git -c advice.detachedHead=false checkout --quiet "$rev"
  test -z "$(git status --porcelain)"
  printf '{"revision": "%s", "machine": "%s"}\n' "$(git rev-parse HEAD)" "$(uname -m)" >"$out/clone.json"
  case "$(uname -m)" in
    x86_64) table='[ci.elan]' ;;
    aarch64) table='[ci.elan-aarch64]' ;;
    *) echo "error: no elan pin for $(uname -m)" >&2; exit 1 ;;
  esac
  url=$(zig-patch/toml-get.sh "$table" url)
  sha=$(zig-patch/toml-get.sh "$table" sha256)
  curl -fsSL --output /tmp/elan.tar.gz "$url"
  echo "$sha  /tmp/elan.tar.gz" | sha256sum -c -
  tar -xzf /tmp/elan.tar.gz -C /tmp
  /tmp/elan-init --default-toolchain none -y
  export PATH="$HOME/.elan/bin:$PATH"
  # The toolchain download is the only unpinned-host fetch; retry transient network failures.
  for attempt in 1 2 3; do
    if elan toolchain install "$(cat lean-toolchain)"; then break; fi
    [ "$attempt" -lt 3 ] || exit 1
    sleep 15
  done
  lake build air2lean >"$out/build-air2lean.log" 2>&1 || { tail -50 "$out/build-air2lean.log" >&2; exit 1; }
  status=0
  python3 scripts/project.py check "$manifest" --translator .lake/build/bin/air2lean --out "$out/check" || status=$?
  test -z "$(git status --porcelain --untracked-files=no)"
  exit "$status"
fi

platform='' rev=HEAD manifest=example-project.json compare='' keep_image=0
while [ $# -gt 0 ]; do
  case "$1" in
    --platform | --rev | --manifest | --compare)
      [ $# -ge 2 ] || { echo "error: $1 needs a value" >&2; exit 2; }
      case "$1" in
        --platform) platform=$2 ;; --rev) rev=$2 ;; --manifest) manifest=$2 ;; --compare) compare=$2 ;;
      esac
      shift 2 ;;
    --keep-image) keep_image=1; shift ;;
    -h | --help) sed -n '2,23p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "error: unknown argument: $1" >&2; exit 2 ;;
  esac
done
case "$platform" in '' | linux/amd64 | linux/arm64) ;; *) echo "error: unsupported platform: $platform" >&2; exit 2 ;; esac
if [ -n "$compare" ]; then
  [ -f "$compare" ] || { echo "error: no record at $compare" >&2; exit 2; }
  compare=$(cd -- "$(dirname -- "$compare")" && pwd)/$(basename -- "$compare")
fi
command -v docker >/dev/null 2>&1 || { echo 'error: Docker is required' >&2; exit 1; }
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
commit=$(git rev-parse --verify "$rev^{commit}")
[ -n "$platform" ] || platform=$(python3 -c 'import json; print(json.load(open("compatibility.json"))["clean_environment"]["platform"])')
snapshot=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-second-machine.XXXXXX")
image="air2lean-second-machine:$$"
cleanup() {
  status=$?
  trap - EXIT HUP INT TERM
  rm -rf "$snapshot"
  [ "$keep_image" = 1 ] || docker image rm -f "$image" >/dev/null 2>&1 || true
  exit "$status"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
# Only the committed history reaches the container: a bundle of the revision, no checkout.
git bundle create --quiet "$snapshot/repo.bundle" "$rev"
git show "$commit:scripts/second-machine.sh" >"$snapshot/second-machine.sh"
results_parent=${AIR2LEAN_SECOND_RESULTS:-"$repo/.lake/second-machine-results"}
mkdir -p "$results_parent"
results=$(mktemp -d "$(cd -- "$results_parent" && pwd -P)/run.XXXXXX")
chmod 777 "$results"
git show "$commit:Dockerfile.clean-env" | docker build --pull --no-cache --platform "$platform" -t "$image" -
bound=${AIR2LEAN_SECOND_TIMEOUT:-6h}
runner=()
if command -v timeout >/dev/null 2>&1; then runner=(timeout --foreground "$bound")
elif command -v gtimeout >/dev/null 2>&1; then runner=(gtimeout --foreground "$bound"); fi
status=0
${runner[@]+"${runner[@]}"} docker run --rm --platform "$platform" --init \
  --memory="${AIR2LEAN_SECOND_MEMORY:-10g}" --cpus="${AIR2LEAN_SECOND_CPUS:-4}" \
  --mount "type=bind,src=$snapshot,dst=/snapshot,readonly" \
  --mount "type=bind,src=$results,dst=/results" \
  "$image" bash /snapshot/second-machine.sh --inside "$commit" "$manifest" || status=$?
printf 'Second-machine results (%s, %s): %s\n' "$platform" "$commit" "$results" >&2
[ "$status" = 0 ] || exit "$status"
if [ -n "$compare" ]; then
  python3 scripts/project.py compare-records "$compare" "$results/check/record.json"
fi
