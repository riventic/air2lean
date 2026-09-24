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
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
version=${1:?"usage: build.sh <version> [prefix]"}
prefix=${2:-"./zig-air-${version}"}
optimize=${AIR2LEAN_OPTIMIZE:-ReleaseFast}
cache_dir=${AIR2LEAN_CACHE:-"$HOME/.cache/air2lean"}

versions_file="$script_dir/versions.toml"
[ -f "$versions_file" ] || { echo "error: $versions_file not found" >&2; exit 1; }

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

# Simple grep/sed TOML read: pull the lines between `["<version>"]` and the next `[`.
section=$(awk -v ver="[\"${version}\"]" '
  $0 == ver { found = 1; next }
  found && /^\[/ { exit }
  found { print }
' "$versions_file")
[ -n "$section" ] || { echo "error: no entry for version '$version' in versions.toml" >&2; exit 1; }

url=$(printf '%s\n' "$section" | sed -n 's/^url *= *"\(.*\)"/\1/p')
sha256=$(printf '%s\n' "$section" | sed -n 's/^sha256 *= *"\(.*\)"/\1/p')
patch_rel=$(printf '%s\n' "$section" | sed -n 's/^patch *= *"\(.*\)"/\1/p')
if [ -z "$url" ] || [ -z "$sha256" ] || [ -z "$patch_rel" ]; then
  echo "error: incomplete entry for version '$version' in versions.toml" >&2
  exit 1
fi
patch_file="$script_dir/$patch_rel"
[ -f "$patch_file" ] || { echo "error: patch file not found: $patch_file" >&2; exit 1; }

mkdir -p "$cache_dir"
tarball="$cache_dir/zig-${version}.tar.xz"

if [ ! -f "$tarball" ]; then
  echo "downloading $url" >&2
  curl -fL --output "$tarball.part" "$url"
  mv "$tarball.part" "$tarball"
fi

if command -v shasum >/dev/null 2>&1; then
  actual_sha256=$(shasum -a 256 "$tarball" | awk '{print $1}')
else
  actual_sha256=$(sha256sum "$tarball" | awk '{print $1}')
fi
if [ "$actual_sha256" != "$sha256" ]; then
  echo "error: sha256 mismatch for $tarball" >&2
  echo "  expected: $sha256" >&2
  echo "  actual:   $actual_sha256" >&2
  rm -f "$tarball"
  exit 1
fi

# Resolve prefix to an absolute path before we cd into the source dir.
case "$prefix" in
  /*) abs_prefix="$prefix" ;;
  *) abs_prefix="$PWD/$prefix" ;;
esac

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-build-${version}.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT
src_dir="$work_dir/zig-${version}"
mkdir -p "$src_dir"
tar -xJf "$tarball" -C "$src_dir" --strip-components=1

echo "applying $patch_file" >&2
(cd "$src_dir" && patch -p1 < "$patch_file")

# No -Dno-lib: the build installs lib/ into the prefix alongside the binary, so the
# built zig finds its own lib dir (self-exe-relative lookup) without --zig-lib-dir.
# -Dcpu=baseline: the default is the build machine's CPU, and CI restores a cached build on
# other runners; a newer CPU's instructions then crash it ("Illegal instruction").
echo "building zig $version ($optimize) -> $abs_prefix" >&2
(cd "$src_dir" && zig build \
  -Doptimize="$optimize" \
  -Dcpu=baseline \
  -Ddebug-extensions=true \
  -Denable-llvm=false \
  --prefix "$abs_prefix")

echo "done: $abs_prefix/bin/zig" >&2
