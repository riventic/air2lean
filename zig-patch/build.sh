#!/usr/bin/env bash
# Download, verify, patch, and build a Zig compiler with the air2lean AIR-JSON exporter
# (docs/air-json.md) for one version listed in versions.toml.
#
# Usage: build.sh <version> [prefix]
#   version   e.g. 0.15.2 — must have an entry in versions.toml.
#   prefix    Install location. Default: ./zig-air-<version>
#
# Env:
#   AIR2LEAN_OPTIMIZE     Build optimize mode. Default: ReleaseFast.
#   AIR2LEAN_CACHE        Download cache dir (tarballs only). Default: $HOME/.cache/air2lean
#   AIR2LEAN_LLVM         1: build with LLVM (the compiler can then also build programs). Needs
#                         LLVM, Clang and LLD of this Zig's LLVM version (versions.toml `llvm`)
#                         and cmake. Default: 0, no LLVM, and lock.sh locks the compiler to
#                         AIR dumps only.
#   AIR2LEAN_LLVM_PREFIX  AIR2LEAN_LLVM=1: `;`-separated install prefixes of LLVM, Clang and LLD.
#                         Default: Homebrew's llvm@<N> and lld@<N>.
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
version=${1:?"usage: build.sh <version> [prefix]"}
prefix=${2:-"./zig-air-${version}"}
optimize=${AIR2LEAN_OPTIMIZE:-ReleaseFast}
cache_dir=${AIR2LEAN_CACHE:-"$HOME/.cache/air2lean"}

# Building this version's compiler needs a same-version host zig to bootstrap.
command -v zig >/dev/null 2>&1 || {
  echo "error: no 'zig' on PATH; build.sh needs a host zig ${version} to bootstrap the build" >&2
  exit 1
}
host_version=$(zig version)
[ "$host_version" = "$version" ] || {
  echo "error: host zig is $host_version, need $version on PATH to build zig $version" >&2
  exit 1
}

url=$("$script_dir/toml-get.sh" "[\"$version\"]" url)
sha256=$("$script_dir/toml-get.sh" "[\"$version\"]" sha256)
hook_rel=$("$script_dir/toml-get.sh" "[\"$version\"]" hook)
llvm=${AIR2LEAN_LLVM:-0}
case "$llvm" in 0 | 1) ;; *) echo "error: AIR2LEAN_LLVM must be 0 or 1, not '$llvm'" >&2; exit 1 ;; esac
hook_file="$script_dir/$hook_rel"
exporter="$script_dir/air-json/json.zig"
[ -f "$hook_file" ] || { echo "error: hook patch not found: $hook_file" >&2; exit 1; }

mkdir -p "$cache_dir"
tarball="$cache_dir/zig-${version}.tar.xz"
download_tmp=
work_dir=
cleanup() {
  [ -z "$download_tmp" ] || rm -f "$download_tmp"
  [ -z "$work_dir" ] || rm -rf "$work_dir"
}
trap cleanup EXIT

verify_tarball() {
  local actual_sha256
  if command -v shasum >/dev/null 2>&1; then
    actual_sha256=$(shasum -a 256 "$1" | awk '{print $1}')
  else
    actual_sha256=$(sha256sum "$1" | awk '{print $1}')
  fi
  if [ "$actual_sha256" != "$sha256" ]; then
    echo "error: sha256 mismatch for $1" >&2
    echo "  expected: $sha256" >&2
    echo "  actual:   $actual_sha256" >&2
    return 1
  fi
}

if [ ! -f "$tarball" ]; then
  echo "downloading $url" >&2
  download_tmp=$(mktemp "$cache_dir/zig-${version}.part.XXXXXX")
  curl -fL --output "$download_tmp" "$url"
  verify_tarball "$download_tmp"
  # Each writer publishes complete verified bytes. Concurrent builds can replace the same
  # cache entry safely, because the pinned digest guarantees identical content.
  mv -f "$download_tmp" "$tarball"
  download_tmp=
else
  # Do not unlink this shared path: another build may publish a valid replacement meanwhile.
  verify_tarball "$tarball" || {
    echo "Remove the invalid cache entry and retry: $tarball" >&2
    exit 1
  }
fi

# Resolve prefix to an absolute path before we cd into the source dir.
case "$prefix" in
  /*) abs_prefix="$prefix" ;;
  *) abs_prefix="$PWD/$prefix" ;;
esac

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-build-${version}.XXXXXX")
src_dir="$work_dir/zig-${version}"
mkdir -p "$src_dir"
tar -xJf "$tarball" -C "$src_dir" --strip-components=1

# The exporter is one source for every version (its `Compat` section holds the differences);
# only the one-line hook that calls it differs per version.
cp "$exporter" "$src_dir/src/Air/json.zig"
echo "applying $hook_file" >&2
(cd "$src_dir" && patch -p1 < "$hook_file")

# With LLVM: cmake only configures (it writes build/config.h with the LLVM, Clang and LLD
# libraries it found); the host zig builds, as without LLVM. No cmake build: that bootstraps
# the compiler from C and takes much longer.
llvm_flags=(-Denable-llvm=false)
if [ "$llvm" = 1 ]; then
  command -v cmake >/dev/null 2>&1 || { echo "error: AIR2LEAN_LLVM=1 needs cmake" >&2; exit 1; }
  llvm_version=$("$script_dir/toml-get.sh" "[\"$version\"]" llvm)
  llvm_prefix=${AIR2LEAN_LLVM_PREFIX:-}
  if [ -z "$llvm_prefix" ]; then
    command -v brew >/dev/null 2>&1 || {
      echo "error: AIR2LEAN_LLVM=1 without Homebrew needs AIR2LEAN_LLVM_PREFIX" >&2; exit 1; }
    llvm_prefix=
    for f in "llvm@$llvm_version" "lld@$llvm_version"; do
      # brew --prefix prints the path also when the formula is not installed.
      d=$(brew --prefix "$f")
      [ -d "$d" ] || { echo "error: $f is not installed (brew install $f)" >&2; exit 1; }
      llvm_prefix="${llvm_prefix:+$llvm_prefix;}$d"
    done
  fi
  echo "configuring LLVM $llvm_version from $llvm_prefix" >&2
  cmake -S "$src_dir" -B "$src_dir/build" -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_PREFIX_PATH="$llvm_prefix" >&2
  llvm_flags=(-Denable-llvm=true -Dconfig_h="$src_dir/build/config.h")
fi

# No -Dno-lib: the build installs lib/ into the prefix alongside the binary, so the
# built zig finds its own lib dir (self-exe-relative lookup) without --zig-lib-dir.
# -Dcpu=baseline: the default is the build machine's CPU, and CI restores a cached build on
# other runners; a newer CPU's instructions then crash it ("Illegal instruction").
echo "building zig $version ($optimize, LLVM: $llvm) -> $abs_prefix" >&2
(cd "$src_dir" && zig build \
  -Doptimize="$optimize" \
  -Dcpu=baseline \
  -Ddebug-extensions=true \
  "${llvm_flags[@]}" \
  --prefix "$abs_prefix")

# Without LLVM, the compiler only writes AIR (lock.sh has the reason). With LLVM, remove the
# compiler of an earlier build without LLVM that lock.sh left in the prefix.
if [ "$llvm" = 1 ]; then
  rm -f "$abs_prefix/bin/zig-unlocked"
else
  "$script_dir/lock.sh" "$abs_prefix"
fi

echo "done: $abs_prefix/bin/zig" >&2
