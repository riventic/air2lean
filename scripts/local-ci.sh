#!/usr/bin/env bash
# Run the checkout's CI recipes on their intended local platforms.
set -euo pipefail
row_transfer=

prepare() {
  local version=$1 sha host key compiler
  source scripts/linux-ci-tools.sh
  host=$(air2lean_linux_ci_host_zig "$version")
  sha=${host##*/host-zig-}
  export PATH="$host:$ELAN_HOME/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
  key=$(cat zig-patch/versions.toml zig-patch/toml-get.sh zig-patch/build.sh zig-patch/lock.sh \
    zig-patch/air-json/json.zig zig-patch/air-json/pointer-offset.zig zig-patch/air-json/identity.zig \
    "zig-patch/$version/hook.patch" | sha256sum | cut -d' ' -f1)
  compiler=/cache/zig-air-$version-$key
  if [ ! -x "$compiler/bin/zig" ]; then
    # /cache belongs only to this container; an empty mkdir lock can be left by
    # this row's interrupted first build before the existing retry.
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
  # The whole-tree generated files CI's rows install (docs/ci.md#whole-tree-generated-files): the
  # coverage inventories and premise index regenerated on this tree (pristine sources in /cache).
  AIR2LEAN_CACHE=/cache python3 -B scripts/generated.py materialize --heavy skip
}

bounded_run() {
  local bound=${AIR2LEAN_LOCAL_TIMEOUT:-6h}
  if command -v timeout >/dev/null 2>&1; then
    timeout --foreground "$bound" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout --foreground "$bound" "$@"
  else
    echo 'note: install GNU timeout/coreutils for a bounded host wait' >&2
    "$@"
  fi
}

drain_owned_container() {
  local identifier=$1 grace=$2 state listed
  owned_container_present=0
  if ! listed=$(bounded_run docker ps -aq --no-trunc --filter "id=$identifier"); then
    echo "error: cannot list owned container $identifier" >&2
    return 1
  fi
  [ -n "$listed" ] || return 0
  if [ "$listed" != "$identifier" ]; then
    echo "error: unexpected owned container identity: $listed" >&2
    return 1
  fi
  owned_container_present=1
  if ! state=$(bounded_run docker inspect --format '{{.State.Running}}' "$identifier"); then
    echo "error: cannot inspect owned container $identifier" >&2
    return 1
  fi
  if [ "$state" = true ]; then
    if ! bounded_run docker stop --time "$grace" "$identifier" >/dev/null; then
      echo "error: cannot stop owned container $identifier" >&2
      return 1
    fi
    if ! state=$(bounded_run docker inspect --format '{{.State.Running}}' "$identifier") || [ "$state" != false ]; then
      echo "error: cannot confirm owned container stopped: $identifier" >&2
      return 1
    fi
  elif [ "$state" != false ]; then
    echo "error: invalid owned container state: $identifier: $state" >&2
    return 1
  fi
}

export_targeted_container() {
  local identifier=$1 stage
  stage=$(mktemp -d "$snapshot/targeted-export.XXXXXX") || return 1
  mkdir -p "$stage/targeted" || return 1
  # Fixed diagnostic transport runs after the worker, with its own bounded calls.
  bounded_run docker logs "$identifier" >"$stage/container.log" 2>&1 || return 1
  bounded_run docker cp "$identifier:/artifacts/targeted/." "$stage/targeted" || return 1
  if [ -e "$artifacts/targeted" ] || [ -L "$artifacts/targeted" ]; then
    echo 'error: targeted diagnostic destination already exists' >&2
    return 1
  fi
  mv "$stage/targeted" "$artifacts/targeted" || return 1
  cp "$stage/container.log" "$artifacts/container-${identifier:0:12}.log" || return 1
  mv "$stage/container.log" "$artifacts/container.log" || return 1
  bounded_run docker rm "$identifier" >/dev/null || return 1
  rm -rf "$stage"
}

cleanup() {
  status=$?
  trap - EXIT HUP INT TERM
  if [ -n "$row_transfer" ]; then
    if ! rm -rf "$row_transfer"; then
      echo "error: cannot remove local CI row metadata: $row_transfer" >&2
      status=1
    fi
    row_transfer=
  fi
  # Docker writes the private registry itself, including when create succeeds but
  # cancellation prevents the shell from reading its result.
  if [ -z "$container" ] && [ -n "${cid_file:-}" ] && [ -f "$cid_file" ]; then
    container=$(<"$cid_file")
    if [[ ! "$container" =~ ^[0-9a-f]{64}$ ]]; then
      echo "error: invalid owned container identity: $cid_file" >&2
      container=
      status=1
    fi
  fi
  if [ -n "$container" ]; then
    # This worker only drains. Its host dispatcher exports after it has exited,
    # outside the caller's process-tree cancellation grace.
    if ! drain_owned_container "$container" 20; then status=1; fi
  fi
  preserve_snapshot=0
  if [ "${owns_snapshot:-0}" = 1 ] && [ -n "$artifacts" ]; then
    # Docker workloads are not host descendants. A cancelled row's cleanup client
    # may have died, so the outer owner independently confirms its recorded CIDs
    # stopped before returning. Preserve stopped recovery containers and exports.
    for cid_file in "$snapshot"/containers/*.id; do
      [ -f "$cid_file" ] || continue
      owned_id=$(<"$cid_file")
      if [[ ! "$owned_id" =~ ^[0-9a-f]{64}$ ]]; then
        echo "error: invalid owned container identity: $cid_file" >&2
        status=1
        preserve_snapshot=1
        continue
      fi
      if ! drain_owned_container "$owned_id" 30; then
        status=1
        preserve_snapshot=1
      elif [ "$owned_container_present" = 1 ]; then
        echo "warning: retained owned container $owned_id for artifact recovery" >&2
        status=1
        preserve_snapshot=1
      fi
    done
    if [ -d "$snapshot/containers" ]; then
      # Exported row artifacts are untrusted as an ownership registry. Publish
      # diagnostic copies only after all rows finish, from the private host data.
      rm -rf "$artifacts/containers"
      cp -R "$snapshot/containers" "$artifacts/containers"
    fi
  fi
  if [ -n "$snapshot" ] && [ "${owns_snapshot:-0}" = 1 ]; then
    if [ "$preserve_snapshot" = 1 ]; then
      echo "warning: retained private local CI snapshot for recovery: $snapshot" >&2
      printf '%s\n' "$snapshot" >"$artifacts/recovery-snapshot"
    else
      rm -rf "$snapshot"
    fi
  fi
  if [ -n "$artifacts" ] && [ "${owns_snapshot:-0}" = 1 ]; then
    printf '%s\n' "$status" >"$artifacts/exit-status"
    printf 'Local CI results: %s\n' "$artifacts" >&2
  fi
  exit "$status"
}

if [ "${1:-}" = --container-row ]; then
  # The host owns the archive and dependency graph. A stopped fresh container gets
  # files, metadata and declared producer outputs; never the host snapshot mount.
  part=$2
  artifacts=$AIR2LEAN_LOCAL_ARTIFACTS snapshot= container= owns_snapshot=0
  trap cleanup EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  safe_part=${part//\//-}
  producer_refs=${AIR2LEAN_LOCAL_PRODUCERS:-}
  if [ -z "$producer_refs" ]; then producer_refs='{}'; fi
  mkdir -p "$AIR2LEAN_LOCAL_SNAPSHOT/containers"
  cid_file=$AIR2LEAN_LOCAL_SNAPSHOT/containers/$safe_part.id
  job_payload=${AIR2LEAN_LOCAL_JOB_PAYLOAD:-}
  job_payload_sha=${AIR2LEAN_LOCAL_JOB_PAYLOAD_SHA256:-}
  if [ "$AIR2LEAN_LOCAL_MODE" != targeted ]; then
    if [ ! -f "$job_payload" ] || [[ ! "$job_payload_sha" =~ ^[0-9a-f]{64}$ ]]; then
      echo 'error: a local CI row needs its captured job payload and digest' >&2
      exit 1
    fi
  fi
  root_cache=0 diff_cache=0
  if [ "$AIR2LEAN_LOCAL_MODE" != targeted ]; then
    root_cache=${AIR2LEAN_LOCAL_ROOT_CACHE:-0}
    diff_cache=${AIR2LEAN_LOCAL_DIFF_CACHE:-0}
  fi
  case "$root_cache:$diff_cache" in
    0:0|0:1|1:0|1:1) ;;
    *) echo 'error: invalid declared local CI cache flags' >&2; exit 1 ;;
  esac
  cache_args=(--env "AIR2LEAN_LOCAL_ROOT_CACHE=$root_cache" --env "AIR2LEAN_LOCAL_DIFF_CACHE=$diff_cache")
  # Persist only Lake paths declared by the captured job's cache actions. Their
  # existing toolchain/manifest keys and Lake traces bind incremental facets to
  # inputs; initialization removes cached source copies before restriction.
  if [ "$root_cache" = 1 ]; then
    cache_args+=(--mount "type=volume,src=air2lean-linux-$AIR2LEAN_LOCAL_TARGET_ARCH-$AIR2LEAN_LOCAL_CACHE_NAMESPACE-lake-$AIR2LEAN_LOCAL_LAKE_KEY,dst=/work/.lake")
  fi
  if [ "$diff_cache" = 1 ]; then
    cache_args+=(--mount "type=volume,src=air2lean-linux-$AIR2LEAN_LOCAL_TARGET_ARCH-$AIR2LEAN_LOCAL_CACHE_NAMESPACE-diff-$AIR2LEAN_LOCAL_DIFF_KEY,dst=/work/tests/diff/.lake")
  fi
  # HOME, Zig's global cache, compilers and downloads stay in this fresh rootfs.
  docker create --cidfile "$cid_file" --platform "$AIR2LEAN_LOCAL_PLATFORM" \
    --memory="${AIR2LEAN_LOCAL_MEMORY:-8g}" --memory-swap="${AIR2LEAN_LOCAL_MEMORY:-8g}" \
    --cpus="${AIR2LEAN_LOCAL_CPUS:-2}" --pids-limit=512 --init \
    --env "AIR2LEAN_LOCAL_IMAGE_ID=$AIR2LEAN_LOCAL_IMAGE_ID" \
    --env "AIR2LEAN_LOCAL_PRODUCERS=$producer_refs" \
    --env "AIR2LEAN_LOCAL_JOB_PAYLOAD_SHA256=$job_payload_sha" \
    "${cache_args[@]}" \
    "$AIR2LEAN_LOCAL_IMAGE_ID" bash -c 'exec bash /snapshot/bootstrap.sh --inside "$@"' \
    local-ci "$AIR2LEAN_LOCAL_MODE" "$part" "${AIR2LEAN_LOCAL_EXAMPLES:-}" >/dev/null
  container=$(<"$cid_file")
  if [[ ! "$container" =~ ^[0-9a-f]{64}$ ]]; then
    echo "error: invalid owned container identity: $cid_file" >&2
    container=
    exit 1
  fi
  # Docker's host/daemon transport extracts this stream into the stopped rootfs.
  # Neither PID 1 nor the later row interpreter ever sees the archive bytes.
  bounded_run docker cp - "$container:/work" <"$AIR2LEAN_LOCAL_SNAPSHOT/source.tar"
  row_transfer=$(mktemp -d "$AIR2LEAN_LOCAL_SNAPSHOT/row-metadata.XXXXXX")
  mkdir -p "$row_transfer/snapshot" "$row_transfer/imports"
  cp "$AIR2LEAN_LOCAL_SNAPSHOT/source-revision" "$row_transfer/snapshot/source-revision"
  cp "$AIR2LEAN_LOCAL_SNAPSHOT/files" "$row_transfer/snapshot/files"
  cp "$AIR2LEAN_LOCAL_BOOTSTRAP" "$row_transfer/snapshot/bootstrap.sh"
  if [ "$AIR2LEAN_LOCAL_MODE" != targeted ]; then
    cp "$job_payload" "$row_transfer/snapshot/job.json"
  fi
  if [ "$part" = preflight ]; then
    cp "$AIR2LEAN_LOCAL_SNAPSHOT/main.bundle" "$row_transfer/snapshot/main.bundle"
  fi
  python3 -B -c 'import json,sys; from pathlib import Path; d=json.loads(Path(sys.argv[1]).read_text()); print(json.dumps({name:"/imports/"+name for name in d}))' \
    "$AIR2LEAN_LOCAL_IMPORTS" >"$row_transfer/imports/manifest.json"
  bounded_run docker cp "$row_transfer/snapshot" "$container:/snapshot"
  bounded_run docker cp "$row_transfer/imports" "$container:/imports"
  rm -rf "$row_transfer"
  row_transfer=
  while IFS=$'\t' read -r name path; do
    bounded_run docker cp "$path/." "$container:/imports/$name"
  done < <(python3 -B -c 'import json,sys; from pathlib import Path; d=json.loads(Path(sys.argv[1]).read_text()); [print(name+"\t"+path) for name,path in d.items()]' "$AIR2LEAN_LOCAL_IMPORTS")
  bounded_run docker start -a "$container"
  exit "$(docker inspect --format '{{.State.ExitCode}}' "$container")"
fi

if [ "${1:-}" = --prepare ]; then
  flock -n 9 || { echo 'error: preparation requires the owned cache lock' >&2; exit 1; }
  prepare "$2"
  exit 0
fi

if [ "${1:-}" = --inside ]; then
  shift
  mode=$1 version=$2 examples=$3
  mkdir -p /artifacts
  cp /snapshot/source-revision /artifacts/source-revision
  # Lock each declared shared cache in root-then-diff order. FD 9 also anchors
  # --prepare when both caches are private; children inherit both owned locks.
  if [ "${AIR2LEAN_LOCAL_ROOT_CACHE:-0}" = 1 ]; then
    exec 9>/work/.lake/local-ci.lock
  else
    exec 9>/cache/local-ci.lock
  fi
  flock -n 9 || { echo 'error: another local CI run owns the root cache' >&2; exit 1; }
  if [ "${AIR2LEAN_LOCAL_DIFF_CACHE:-0}" = 1 ]; then
    exec 8>/work/tests/diff/.lake/local-ci.lock
    flock -n 8 || { echo 'error: another local CI run owns the diff cache' >&2; exit 1; }
  fi
  export HOME=/tmp/air2lean-home
  export ZIG_GLOBAL_CACHE_DIR=$HOME/.cache/zig
  mkdir -p "$HOME"
  [ ! -e /snapshot/source.tar ] || { echo 'error: source archive must stay outside the container' >&2; exit 1; }
  python3 -B scripts/local-ci-steps.py --initialize /snapshot/files
  # Under Rosetta: AIR2LEAN_ROSETTA_LINK_FLAGS for every native build below (docs/rosetta.md).
  source scripts/rosetta.sh
  export AIR2LEAN_LOCAL_BOOTSTRAP=/snapshot/bootstrap.sh
  export AIR2LEAN_LOCAL_MODE=$mode
  if [ "$mode" != targeted ]; then
    case "$version" in
      test/*) ;;
      *)
        # Native/support installers run from the workflow, not the Linux test setup.
        export ELAN_HOME=$HOME/.elan
        export AIR2LEAN_CACHE=/cache/downloads LEAN_NUM_THREADS=1
        exec python3 -B scripts/local-ci-steps.py --row "$mode" "$version"
        ;;
    esac
  fi
  source scripts/linux-ci-tools.sh
  air2lean_linux_ci_elan
  export AIR2LEAN_CACHE=/cache/downloads
  export LEAN_NUM_THREADS=1
  if [ "$mode" != targeted ]; then
    exec python3 -B scripts/local-ci-steps.py --row "$mode" "$version"
  fi
  export RUNNER_TEMP=/artifacts/targeted TMPDIR=/artifacts/targeted
  export AIR2LEAN_OUT_DIR=/artifacts/targeted/air-out
  mkdir -p "$RUNNER_TEMP"
  python3 scripts/local-ci-steps.py --prune-cache
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
  tree=$(cat ".lake/check-reports/$version/build-tree")
  cd "$tree"
  lake build Proofs
  exit 0
fi

usage() {
  echo 'usage: scripts/local-ci.sh targeted <version> "<examples>" | full [version] | part|discover <job/part id> | matrix | mutations' >&2
  exit 2
}
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
. "$repo/scripts/zig-default.sh"
mode=${1:-full} version=${2:-$(air2lean_default_zig_version "$repo")} examples=${3:-}
case "$mode" in
  targeted) [ "$#" = 3 ] && [ -n "$examples" ] || usage ;;
  full) [ "$#" -le 2 ] || usage ;;
  part|discover) [ "$#" = 2 ] || usage ;;
  matrix|mutations) [ "$#" = 1 ] || usage ;;
  *) usage ;;
esac
if [ "$mode" = part ] || [ "$mode" = discover ]; then
  case "$version" in *[!a-zA-Z0-9_./-]*|'') usage ;; esac
else
  case "$version" in 0.17.0|0.16.0|0.15.2|0.14.1) ;; *) usage ;; esac
fi
snapshot=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-local-ci.XXXXXX")
container=
artifacts=
owns_snapshot=1
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
artifact_parent=${AIR2LEAN_LOCAL_RESULTS:-"$repo/.lake/local-ci-results"}
mkdir -p "$artifact_parent"
artifact_parent=$(cd -- "$artifact_parent" && pwd -P)
artifacts=$(mktemp -d "$artifact_parent/run.XXXXXX")
printf 'Local CI results: %s\n' "$artifacts" >&2
# Compare the actual archived bytes/modes with one pinned revision before issuing a stamp.
# A failed comparison stops here, before any local verification runtime is launched.
python3 -B scripts/local-ci-steps.py --snapshot-runner "$snapshot" "$artifacts" "$mode" "$version"
# Preflight's ledger ratchet reads origin/main history. Supply that exact local ref,
# never the caller's .git or credentials; other jobs cannot access this bundle after sealing.
if [ "$version" = preflight ]; then
  git init --bare -q "$snapshot/base.git"
  git -C "$snapshot/base.git" fetch --no-tags "$repo" origin/main:refs/heads/main
  git -C "$snapshot/base.git" bundle create "$snapshot/main.bundle" main
  rm -rf "$snapshot/base.git"
fi
platform=linux/amd64
local_python=${AIR2LEAN_LOCAL_PYTHON:-python3}
mkdir -p "$artifacts/bootstrap"
snapshot_sha=$(awk -F= '$1 == "snapshot_sha256" { print $2 }' "$snapshot/source-revision")
[[ "$snapshot_sha" =~ ^[0-9a-f]{64}$ ]] || { echo 'error: invalid snapshot archive digest' >&2; exit 1; }
printf '%s  %s\n' "$snapshot_sha" "$snapshot/source.tar" | shasum -a 256 -c -
COPYFILE_DISABLE=1 tar -xf "$snapshot/source.tar" -C "$artifacts/bootstrap"
if [ "$mode" = part ] || [ "$mode" = discover ]; then
  # The existing interpreter owns runner selection, including unknown-job diagnostics.
  platform=$(cd "$artifacts/bootstrap" && "$local_python" scripts/local-ci-steps.py --placement "$version")
fi
if [ "$platform" = host ]; then
  [ "$(uname -s)/$(uname -m)" = Darwin/arm64 ] || {
    echo 'error: macOS rows require an Apple silicon macOS host' >&2; exit 1;
  }
  # Use the standard host cache, with a nonblocking lock just like the Linux cache.
  host_tools="$HOME/.cache/air2lean/local-ci/tools-macos"
  mkdir -p "$host_tools"
  mv "$artifacts/bootstrap" "$artifacts/work"
  export AIR2LEAN_LOCAL_ARTIFACTS=$artifacts AIR2LEAN_LOCAL_SNAPSHOT=$snapshot AIR2LEAN_LOCAL_MODE=$mode
  export AIR2LEAN_LOCAL_BOOTSTRAP=$snapshot/bootstrap.sh
  export AIR2LEAN_LOCAL_HOST_TOOLS=$host_tools
  cd "$artifacts/work"
  bounded_run "$local_python" scripts/local-ci-steps.py --host "$mode" "$version"
  exit 0
fi
# Build with only this Dockerfile as context: no checkout or private files reach the daemon.
lake_key=$(<"$snapshot/lake-key")
diff_key=$(<"$snapshot/diff-key")
rm "$snapshot/lake-key" "$snapshot/diff-key"
case "$(docker info --format '{{.Architecture}}')" in
  aarch64|arm64) python_arch=arm64 ;;
  x86_64|amd64) python_arch=amd64 ;;
  *) echo 'error: unsupported Docker engine architecture' >&2; exit 1 ;;
esac
target_arch=${platform#linux/}
if [ "$target_arch" = arm64 ] && [ "$python_arch" != arm64 ]; then
  echo 'error: native aarch64-linux rows require an arm64 Docker engine; emulation is not qualification' >&2
  exit 1
fi
image="air2lean-local-ci:ubuntu24-$target_arch-python-$python_arch"
docker build --platform "$platform" --build-arg "PYTHON_ARCH=$python_arch" --iidfile "$snapshot/image-id" \
  -t "$image" - <"$snapshot/Dockerfile"
image_id=$(<"$snapshot/image-id")
[[ "$image_id" =~ ^sha256:[0-9a-f]{64}$ ]] || { echo 'error: invalid built image ID' >&2; exit 1; }
rm "$snapshot/Dockerfile"
if [ -n "${AIR2LEAN_LOCAL_TOOL_VOLUME:-}" ]; then
  tool_volume=$AIR2LEAN_LOCAL_TOOL_VOLUME-$target_arch
elif [ "$target_arch" = arm64 ]; then
  tool_volume=air2lean-local-linux-arm64-toolchains
else
  tool_volume=air2lean-local-linux-toolchains
fi
# Keep the established override-derived namespace for declared Lake volumes;
# the former broad tool volume itself is never mounted into a verification row.
cache_namespace=$(printf '%s' "$tool_volume" | shasum -a 256 | cut -c1-16)
# AIR2LEAN_LOCAL_CPUS (default 2) and AIR2LEAN_LOCAL_MEMORY (default 8g) size the container; a
# GitHub runner has 4 CPUs and 16 GB. scripts/par.py takes its worker count from the CPU quota.
export AIR2LEAN_LOCAL_ARTIFACTS=$artifacts AIR2LEAN_LOCAL_SNAPSHOT=$snapshot
export AIR2LEAN_LOCAL_BOOTSTRAP=$snapshot/bootstrap.sh
export AIR2LEAN_LOCAL_IMAGE_ID=$image_id AIR2LEAN_LOCAL_PLATFORM=$platform
export AIR2LEAN_LOCAL_TARGET_ARCH=$target_arch AIR2LEAN_LOCAL_EFFECTIVE_TOOL_VOLUME=$tool_volume
export AIR2LEAN_LOCAL_CACHE_NAMESPACE=$cache_namespace AIR2LEAN_LOCAL_LAKE_KEY=$lake_key AIR2LEAN_LOCAL_DIFF_KEY=$diff_key
export AIR2LEAN_LOCAL_MODE=$mode AIR2LEAN_LOCAL_EXAMPLES=$examples
if [ "$mode" = targeted ]; then
  printf '{}\n' >"$snapshot/imports.json"
  export AIR2LEAN_LOCAL_IMPORTS=$snapshot/imports.json
  targeted_status=0
  bash "$snapshot/bootstrap.sh" --container-row "$version" || targeted_status=$?
  targeted_cid_file=$snapshot/containers/$version.id
  if [ -f "$targeted_cid_file" ]; then
    targeted_id=$(<"$targeted_cid_file")
    if [[ "$targeted_id" =~ ^[0-9a-f]{64}$ ]]; then
      if ! export_targeted_container "$targeted_id"; then
        echo "warning: targeted diagnostic export failed; retained container $targeted_id for recovery" >&2
        [ "$targeted_status" -ne 0 ] || targeted_status=1
      fi
    else
      echo "error: invalid owned container identity: $targeted_cid_file" >&2
      targeted_status=1
    fi
  else
    echo 'error: targeted run did not record its container identity' >&2
    [ "$targeted_status" -ne 0 ] || targeted_status=1
  fi
  exit "$targeted_status"
else
  cd "$artifacts/bootstrap"
  "$local_python" -B scripts/local-ci-steps.py --dispatch "$mode" "$version"
fi
