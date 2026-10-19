#!/usr/bin/env bash
# Pinned Linux tool installation shared by the existing Docker wrappers.
# Call from the captured checkout; callers own their cache lifetime and locks.

air2lean_linux_ci_host_zig() (
  set -euo pipefail
  local version=$1 url sha host stage=
  trap '[ -z "$stage" ] || rm -rf "$stage"' EXIT
  url=$(zig-patch/toml-get.sh "[ci.host-zig.\"$version\"]" url)
  sha=$(zig-patch/toml-get.sh "[ci.host-zig.\"$version\"]" sha256)
  host=/cache/host-zig-$sha
  if [ ! -f "$host/.local-ci-verified" ]; then
    curl -fL --output /tmp/host-zig.tar.xz "$url"
    echo "$sha  /tmp/host-zig.tar.xz" | sha256sum -c - >&2
    stage=$(mktemp -d /cache/.host-zig.XXXXXX)
    tar -xJf /tmp/host-zig.tar.xz -C "$stage" --strip-components=1
    [ -x "$stage/zig" ]
    touch "$stage/.local-ci-verified"
    [ ! -e "$host" ] || mv "$host" "$host.incomplete.$$"
    mv "$stage" "$host"
    stage=
  fi
  printf '%s\n' "$host"
)

air2lean_linux_ci_elan() {
  local url sha
  sha=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
  export ELAN_HOME=/cache/elan-$sha
  export PATH="$ELAN_HOME/bin:$PATH"
  if [ ! -x "$ELAN_HOME/bin/elan" ]; then
    url=$(zig-patch/toml-get.sh '[ci.elan]' url)
    curl -fL --output /tmp/elan.tar.gz "$url"
    echo "$sha  /tmp/elan.tar.gz" | sha256sum -c -
    tar -xzf /tmp/elan.tar.gz -C /tmp
    chmod +x /tmp/elan-init
    /tmp/elan-init --default-toolchain none -y
  fi
}
