#!/usr/bin/env bash
# Clean-environment acceptance recipe: run the first proof end to end in a fresh Ubuntu 24.04
# container from tracked files only. No host toolchains, caches, volumes or build outputs reach
# the container; elan and (with --translate) Zig come from sha256 pins, Lean from the version
# pinned in lean-toolchain (installed by elan).
#
# Usage: scripts/clean-env.sh [--translate] [--keep-image]
#   default      install elan + pinned Lean, run the doctor (--require proofs), build
#                Proofs.Basic.Proofs, check tutorials/first-proof, the exercise and its
#                negative control (docs/getting-started.md, first half)
#   --translate  additionally bootstrap the pinned Zig 0.16.0, build the AIR-only patched
#                compiler (no LLVM), verify the lock refuses native output, translate the
#                getting-started demo and check its separate proof (needs ~12 GiB disk, 8 GiB RAM)
# Env: AIR2LEAN_CLEAN_RESULTS (default .lake/clean-env-results), AIR2LEAN_CLEAN_TIMEOUT (default 3h).
# Network access is required for the pinned downloads. Requires Docker.
set -euo pipefail

if [ "${1:-}" = --inside ]; then
  translate=$2
  set -x
  mkdir -p "$HOME/air2lean"
  cd "$HOME/air2lean"
  tar -xf /snapshot/source.tar
  out=/results
  # 1. elan from the pin in zig-patch/versions.toml (sha256-verified).
  url=$(zig-patch/toml-get.sh '[ci.elan]' url)
  sha=$(zig-patch/toml-get.sh '[ci.elan]' sha256)
  curl -fsSL --output /tmp/elan.tar.gz "$url"
  echo "$sha  /tmp/elan.tar.gz" | sha256sum -c -
  tar -xzf /tmp/elan.tar.gz -C /tmp
  /tmp/elan-init --default-toolchain none -y
  export PATH="$HOME/.elan/bin:$PATH"
  # 2. Pinned Lean toolchain, then the doctor must report proofs ready.
  elan toolchain install "$(cat lean-toolchain)"
  python3 scripts/compat.py check
  scripts/doctor.sh --require proofs --no-docker --json >"$out/doctor-proofs.json"
  scripts/doctor.sh --require proofs --no-docker
  # 3. The first proof, exactly as docs/getting-started.md documents it.
  lake build Proofs.Basic.Proofs
  lake env lean tutorials/first-proof/Main.lean
  # 4. The exercise, and the negative control Lean must reject.
  mkdir -p work/first
  awk '/^end FirstProof/ { print "theorem exactly_on_time (endTime due : BitVec 32)\n    (sameTime : endTime.toNat = due.toNat) :\n    tardiness endTime due = pure 0 := by\n  exact on_time_zero endTime due (Nat.le_of_eq sameTime)\n" } { print }' \
    tutorials/first-proof/Main.lean >work/first/Exercise.lean
  grep -q 'theorem exactly_on_time' work/first/Exercise.lean
  lake env lean work/first/Exercise.lean
  sed 's/tardiness endTime due = pure 0 := by/tardiness endTime due = pure 1 := by/' \
    tutorials/first-proof/Main.lean >work/first/Wrong.lean
  if lake env lean work/first/Wrong.lean >"$out/negative-control.log" 2>&1; then
    echo 'error: Lean accepted the false negative-control theorem' >&2
    exit 1
  fi
  echo 'OK: first proof, exercise and negative control' | tee "$out/proofs.ok"
  if [ "$translate" = 1 ]; then
    # 5. Stock host Zig 0.16.0 from its pin, then the default (no-LLVM, AIR-only locked) build.
    url=$(zig-patch/toml-get.sh '[ci.host-zig."0.16.0"]' url)
    sha=$(zig-patch/toml-get.sh '[ci.host-zig."0.16.0"]' sha256)
    curl -fsSL --output /tmp/zig.tar.xz "$url"
    echo "$sha  /tmp/zig.tar.xz" | sha256sum -c -
    mkdir -p "$HOME/host-zig"
    tar -xJf /tmp/zig.tar.xz -C "$HOME/host-zig" --strip-components=1
    export PATH="$HOME/host-zig:$PATH"
    zig-patch/build.sh 0.16.0
    scripts/doctor.sh --no-docker --json >"$out/doctor-translate.json"
    scripts/doctor.sh --no-docker
    python3 - "$out/doctor-translate.json" <<'PY'
import json, sys
report = json.load(open(sys.argv[1]))
lock = [c for c in report['checks'] if c['id'] == 'patched-zig-0.16.0'][0]
assert report['ready']['translate'] and lock['details']['lock'] == 'locked', lock
PY
    # 6. The AIR-only lock must refuse native output when LLVM is absent.
    printf 'pub fn main() void {}\n' >/tmp/lock-probe.zig
    if zig-air-0.16.0/bin/zig build-exe /tmp/lock-probe.zig >"$out/lock-probe.log" 2>&1; then
      echo 'error: the AIR-only compiler accepted build-exe' >&2
      exit 1
    fi
    grep -q 'only writes AIR' "$out/lock-probe.log"
    # 7. Translate the getting-started demo and check its separate proof.
    mkdir -p Proofs/MyProgram
    printf 'export fn tardiness(end: u32, due: u32) u32 {\n    return if (end > due) end - due else 0;\n}\n' \
      >work/first/demo.zig
    scripts/translate.sh work/first/demo.zig -o Proofs/MyProgram/Gen.lean --namespace MyProgram
    lake build Proofs.MyProgram.Gen
    cat >work/first/Proof.lean <<'LEAN'
import Proofs.MyProgram.Gen

open MyProgram

example (endTime due : BitVec 32)
    (onTime : endTime.toNat ≤ due.toNat) :
    tardiness endTime due = pure 0 := by
  unfold tardiness
  have notLate : ¬ due.toNat < endTime.toNat := Nat.not_lt.mpr onTime
  simp [zig_unfold, notLate]
LEAN
    lake env lean work/first/Proof.lean
    echo 'OK: translation, lock and separate proof' | tee "$out/translate.ok"
  fi
  exit 0
fi

translate=0 keep_image=0
for arg in "$@"; do
  case "$arg" in
    --translate) translate=1 ;;
    --keep-image) keep_image=1 ;;
    -h | --help) sed -n '2,15p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "error: unknown argument: $arg" >&2; exit 2 ;;
  esac
done
command -v docker >/dev/null 2>&1 || { echo 'error: Docker is required (scripts/doctor.sh reports its state)' >&2; exit 1; }
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
python3 scripts/compat.py check
platform=$(python3 -c 'import json; print(json.load(open("compatibility.json"))["clean_environment"]["platform"])')
snapshot=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-clean-env.XXXXXX")
image="air2lean-clean-env:$$"
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
# Tracked files only (working-tree content); never untracked files, .lake, compilers or caches.
git ls-files -z | while IFS= read -r -d '' path; do
  case "$path" in .lake/* | */.lake/* | zig-air-*/* | host-zig/*) continue ;; esac
  if [ -f "$path" ] || [ -L "$path" ]; then printf '%s\0' "$path"; fi
done >"$snapshot/files"
COPYFILE_DISABLE=1 tar -cf "$snapshot/source.tar" --null -T "$snapshot/files"
results_parent=${AIR2LEAN_CLEAN_RESULTS:-"$repo/.lake/clean-env-results"}
mkdir -p "$results_parent"
results=$(mktemp -d "$(cd -- "$results_parent" && pwd -P)/run.XXXXXX")
chmod 777 "$results"
cp scripts/clean-env.sh "$snapshot/clean-env.sh"
# The Dockerfile is the only build context: no checkout reaches the daemon at build time.
docker build --pull --no-cache --platform "$platform" -t "$image" - <Dockerfile.clean-env
bound=${AIR2LEAN_CLEAN_TIMEOUT:-3h}
runner=()
if command -v timeout >/dev/null 2>&1; then runner=(timeout --foreground "$bound")
elif command -v gtimeout >/dev/null 2>&1; then runner=(gtimeout --foreground "$bound"); fi
status=0
${runner[@]+"${runner[@]}"} docker run --rm --platform "$platform" --memory=8g --cpus=2 --init \
  --mount "type=bind,src=$snapshot,dst=/snapshot,readonly" \
  --mount "type=bind,src=$results,dst=/results" \
  -e LEAN_NUM_THREADS=1 \
  "$image" bash /snapshot/clean-env.sh --inside "$translate" || status=$?
printf 'Clean-environment results: %s\n' "$results" >&2
exit "$status"
