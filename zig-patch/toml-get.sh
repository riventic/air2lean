#!/usr/bin/env bash
# Print one `key = "value"` of one table in zig-patch/versions.toml. The one reader for that
# file (build.sh, .github/workflows/ci.yml): exact-match the table's header line, then read up to
# the next `[`. Fails if the table or the key is missing.
#
# Usage: toml-get.sh <table-header> <key>
#   e.g. toml-get.sh '["0.15.2"]' url
#        toml-get.sh '[ci.host-zig."0.15.2"]' sha256
set -euo pipefail

[ $# -eq 2 ] || { echo "usage: toml-get.sh <table-header> <key>" >&2; exit 2; }
versions_file="$(dirname -- "${BASH_SOURCE[0]}")/versions.toml"

value=$(awk -v hdr="$1" '$0 == hdr { f = 1; next } f && /^\[/ { exit } f' "$versions_file" |
  sed -n "s/^$2 *= *\"\(.*\)\"/\1/p")
[ -n "$value" ] || { echo "error: no '$2' in table $1 of $versions_file" >&2; exit 1; }
printf '%s\n' "$value"
