#!/usr/bin/env bash
# Install the pinned Lean toolchain manager for unrestricted CI preparation steps.
set -euo pipefail
cd "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
scratch=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-elan.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
url=$(zig-patch/toml-get.sh '[ci.elan]' url)
sha256=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
curl -fL --output "$scratch/elan.tar.gz" "$url"
echo "$sha256  $scratch/elan.tar.gz" | sha256sum -c -
tar -xzf "$scratch/elan.tar.gz" -C "$scratch"
chmod +x "$scratch/elan-init"
"$scratch/elan-init" --default-toolchain none -y
echo "$HOME/.elan/bin" >> "${GITHUB_PATH:?GITHUB_PATH is required}"
