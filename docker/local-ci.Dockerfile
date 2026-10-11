# Local stand-in for GitHub's ubuntu-24.04 / ubuntu-24.04-arm runners (scripts/local-ci.sh).
# One file, two platforms: build with --platform linux/amd64 (runs under Rosetta on Apple silicon)
# or --platform linux/arm64 (native). The apt list is what the CI steps need beyond the hosted
# image (git, curl, python3 with PyYAML, ripgrep, GNU toolchain, libgmp for Lean). Lean (elan),
# the stock Zig releases and the patched compilers are NOT in the image: the runner installs them
# with the recipes from ci.yml into persistent volumes, so a version bump needs no image rebuild.
FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates curl git patch jq \
    python3 python3-yaml ripgrep procps libgmp-dev libssl-dev perl util-linux xz-utils \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /work /cache
WORKDIR /work
