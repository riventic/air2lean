#!/usr/bin/env bash
# Local Ubuntu 24.04 CI recipes with pinned x86_64 Lean/Zig. No host tools are used.
set -euo pipefail

prepare() {
  local version=$1 url sha host stage key compiler
  url=$(zig-patch/toml-get.sh "[ci.host-zig.\"$version\"]" url)
  sha=$(zig-patch/toml-get.sh "[ci.host-zig.\"$version\"]" sha256)
  host=/cache/host-zig-$sha
  if [ ! -f "$host/.local-ci-verified" ]; then
    curl -fL --output /tmp/host-zig.tar.xz "$url"
    echo "$sha  /tmp/host-zig.tar.xz" | sha256sum -c -
    stage=$(mktemp -d /cache/.host-zig.XXXXXX)
    tar -xJf /tmp/host-zig.tar.xz -C "$stage" --strip-components=1
    [ -x "$stage/zig" ]
    touch "$stage/.local-ci-verified"
    [ ! -e "$host" ] || mv "$host" "$host.incomplete.$$"
    mv "$stage" "$host"
  fi
  export PATH="$host:$ELAN_HOME/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
  key=$(cat zig-patch/versions.toml zig-patch/toml-get.sh zig-patch/build.sh zig-patch/lock.sh \
    zig-patch/air-json/json.zig "zig-patch/$version/hook.patch" | sha256sum | cut -d' ' -f1)
  compiler=/cache/zig-air-$version-$key
  if [ ! -x "$compiler/bin/zig" ]; then
    # FD 9's exclusive flock is inherited by every child, so only an exited
    # previous container can have left this exact prefix's empty mkdir lock.
    rmdir "/cache/.zig-air-$version-$key.air2lean-build.lock" 2>/dev/null || true
    zig-patch/build.sh "$version" "$compiler" || zig-patch/build.sh "$version" "$compiler"
  fi
  # CI's receipt gate requires physical untracked compiler directories. Copy only
  # verified Linux cache installations, never host binaries or symlink these roots.
  if [ ! -f "/work/host-zig/.local-ci-$sha" ]; then
    rm -rf /work/host-zig
    cp -a "$host" /work/host-zig
    touch "/work/host-zig/.local-ci-$sha"
  fi
  if [ "$(cat "/work/zig-air-$version/.local-ci-key" 2>/dev/null)" != "$key" ]; then
    rm -rf "/work/zig-air-$version"
    cp -a "$compiler" "/work/zig-air-$version"
    printf '%s\n' "$key" >"/work/zig-air-$version/.local-ci-key"
  fi
}

if [ "${1:-}" = --prepare ]; then
  flock -n 9 || { echo 'error: preparation requires the owned cache lock' >&2; exit 1; }
  prepare "$2"
  exit 0
fi

if [ "${1:-}" = --inside ]; then
  shift
  mode=$1 version=$2 examples=$3
  # Serialize users of the shared Linux caches; never reuse host native artifacts.
  exec 9>/cache/local-ci.lock
  flock -n 9 || { echo 'error: another local CI run owns the caches' >&2; exit 1; }
  tar -xf /snapshot/source.tar -C /work
  git init -q
  git config user.email local-ci@example.invalid
  git config user.name local-ci
  git --literal-pathspecs add -f --pathspec-from-file=/snapshot/files --pathspec-file-nul
  git commit -qm 'Local tracked-source snapshot'
  sha=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
  export ELAN_HOME=/cache/elan-$sha AIR2LEAN_CACHE=/cache/downloads
  export ZIG_GLOBAL_CACHE_DIR=/cache/zig-global LEAN_NUM_THREADS=1
  export PATH="$ELAN_HOME/bin:$PATH"
  if [ ! -x "$ELAN_HOME/bin/elan" ]; then
    url=$(zig-patch/toml-get.sh '[ci.elan]' url)
    sha=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
    curl -fL --output /tmp/elan.tar.gz "$url"
    echo "$sha  /tmp/elan.tar.gz" | sha256sum -c -
    tar -xzf /tmp/elan.tar.gz -C /tmp
    chmod +x /tmp/elan-init
    /tmp/elan-init --default-toolchain none -y
  fi
  if [ "$mode" != targeted ]; then
    exec python3 scripts/local-ci-steps.py "$mode" "$version"
  fi
  scripts/review-checks.sh
  prepare "$version"
  export PATH="/work/host-zig:$ELAN_HOME/bin:$PATH"
  export AIR2LEAN_ZIG_VERSION=$version AIR2LEAN_ZIG_AIR="/work/zig-air-$version/bin/zig"
  export AIR2LEAN_CI=1 AIR2LEAN_DIFF=1 AIR2LEAN_EXAMPLES=$examples
  if [ "$version" = 0.14.1 ]; then
    export AIR2LEAN_DIFF=0
    allowed='basic recursion options floatops floats errors variants pointers layout'
    for ex in $examples; do
      case " $allowed " in *" $ex "*) ;; *) echo "error: $ex is outside the 0.14.1 CI row" >&2; exit 1 ;; esac
    done
  fi
  lake build
  scripts/check.sh
  lake build Proofs
  exit 0
fi

usage() {
  echo 'usage: scripts/local-ci.sh targeted <version> "<examples>" | full [version] | matrix' >&2
  exit 2
}
mode=${1:-full} version=${2:-0.16.0} examples=${3:-}
case "$mode" in
  targeted) [ "$#" = 3 ] && [ -n "$examples" ] || usage ;;
  full) [ "$#" -le 2 ] || usage ;;
  matrix) [ "$#" = 1 ] || usage ;;
  *) usage ;;
esac
case "$version" in 0.16.0|0.15.2|0.14.1) ;; *) usage ;; esac
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
snapshot=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-local-ci.XXXXXX")
container=
cleanup() {
  status=$?
  trap - EXIT HUP INT TERM
  if [ -n "$container" ]; then
    docker stop --time 30 "$container" >/dev/null 2>&1 || true
    docker rm -f "$container" >/dev/null 2>&1 || true
  fi
  rm -rf "$snapshot"
  exit "$status"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
# Index paths include staged additions; copy their current working-tree content. Deleted
# paths are omitted. Never copy untracked files, Git metadata or host build/cache directories.
git ls-files -z | while IFS= read -r -d '' path; do
  case "$path" in
    .git|.git/*|.lake|.lake/*|*/.lake|*/.lake/*|.aws/*|.codex/*|.agents/*|zig-air-*/*|host-zig/*) continue ;;
  esac
  [ ! -d "$path" ] || { echo "error: tracked directory/submodule unsupported: $path" >&2; exit 1; }
  if [ -e "$path" ] || [ -L "$path" ]; then printf '%s\0' "$path"; fi
done >"$snapshot/files"
COPYFILE_DISABLE=1 tar -cf "$snapshot/source.tar" --null -T "$snapshot/files"
# Build with only this Dockerfile as context: no checkout or private files reach the daemon.
cp Dockerfile.local-ci "$snapshot/Dockerfile"
case "$(docker info --format '{{.Architecture}}')" in
  aarch64|arm64) python_arch=arm64 ;;
  x86_64|amd64) python_arch=amd64 ;;
  *) echo 'error: unsupported Docker engine architecture' >&2; exit 1 ;;
esac
image="air2lean-local-ci:ubuntu24-amd64-python-$python_arch"
docker build --platform linux/amd64 --build-arg "PYTHON_ARCH=$python_arch" \
  -t "$image" - <"$snapshot/Dockerfile"
lake_key=$(cat lean-toolchain lake-manifest.json | shasum -a 256 | cut -c1-16)
diff_key=$(cat tests/diff/lean-toolchain tests/diff/lake-manifest.json | shasum -a 256 | cut -c1-16)
tool_volume=${AIR2LEAN_LOCAL_TOOL_VOLUME:-air2lean-local-linux-toolchains}
cache_namespace=$(printf '%s' "$tool_volume" | shasum -a 256 | cut -c1-16)
container=$(docker create --platform linux/amd64 --memory=8g --memory-swap=8g \
  --cpus=2 --pids-limit=512 --init \
  --mount "type=bind,src=$snapshot,dst=/snapshot,readonly" \
  --mount "type=volume,src=$tool_volume,dst=/cache" \
  --mount "type=volume,src=air2lean-linux-amd64-$cache_namespace-lake-$lake_key,dst=/work/.lake" \
  --mount "type=volume,src=air2lean-linux-amd64-$cache_namespace-diff-$diff_key,dst=/work/tests/diff/.lake" \
  "$image" bash -c 'tar -xOf /snapshot/source.tar scripts/local-ci.sh > /tmp/local-ci.sh; exec bash /tmp/local-ci.sh --inside "$@"' \
  local-ci "$mode" "$version" "$examples")
bound=${AIR2LEAN_LOCAL_TIMEOUT:-6h}
if command -v timeout >/dev/null 2>&1; then
  timeout --foreground "$bound" docker start -a "$container"
elif command -v gtimeout >/dev/null 2>&1; then
  gtimeout --foreground "$bound" docker start -a "$container"
else
  echo 'note: install GNU timeout/coreutils for a bounded host wait' >&2
  docker start -a "$container"
fi
# Attached start may report only Docker's status; preserve the actual recipe exit code.
exit "$(docker inspect --format '{{.State.ExitCode}}' "$container")"
