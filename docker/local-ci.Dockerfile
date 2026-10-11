# Local stand-in for GitHub's ubuntu-24.04 / ubuntu-24.04-arm runners (scripts/local-ci.sh).
# One file, two platforms: build with --platform linux/amd64 (x86_64, Rosetta on Apple silicon) or
# --platform linux/arm64 (native). The apt list is what the CI steps need beyond the hosted image
# (git, curl, python3 with PyYAML, ripgrep, sudo and qemu-user-static for the steps that install
# them, GNU toolchain, libgmp for Lean). Lean (elan), the stock Zig releases and the patched
# compilers are NOT in the image: the runner executes the install recipes from ci.yml into persistent
# volumes, so a version bump needs no image rebuild.
FROM ubuntu:24.04

# On an arm64 Docker engine, an amd64 image takes Python and PyYAML from the native arm64
# architecture: shell, coreutils, Lean and Zig stay x86_64, while the memory gates of the Python
# tests (a 32 MiB growth bound) do not count Rosetta's per-process overhead.
ARG PYTHON_ARCH=amd64
RUN if [ "$PYTHON_ARCH" = arm64 ] && [ "$(dpkg --print-architecture)" = amd64 ]; then \
      dpkg --add-architecture arm64; \
      sed -i '/^Components:/a Architectures: amd64' /etc/apt/sources.list.d/ubuntu.sources; \
      printf '%s\n' \
        'deb [arch=arm64] http://ports.ubuntu.com/ubuntu-ports noble main universe' \
        'deb [arch=arm64] http://ports.ubuntu.com/ubuntu-ports noble-updates main universe' \
        'deb [arch=arm64] http://ports.ubuntu.com/ubuntu-ports noble-security main universe' \
        > /etc/apt/sources.list.d/arm64.list; \
    fi \
    && apt-get update && apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates curl git patch jq sudo \
    "python3:$PYTHON_ARCH" "python3-yaml:$PYTHON_ARCH" ripgrep procps qemu-user-static \
    libgmp-dev libssl-dev perl util-linux xz-utils \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /work /cache
WORKDIR /work
