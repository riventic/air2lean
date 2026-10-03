#!/usr/bin/env bash
# Regressions for shell checks that previously reported success without doing their checks.
# All fake tools, generated sources and mutations live in an isolated temporary repository.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
test_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-review-checks.XXXXXX")
trap 'rm -rf "$test_dir"' EXIT
passed=0
expect_pass() {
  local name=$1
  shift
  if ! "$@" >"$test_dir/output.log" 2>&1; then
    echo "FAILED: $name" >&2; cat "$test_dir/output.log" >&2; exit 1
  fi
  passed=$((passed + 1))
}
expect_failure() {
  local name=$1 pattern=$2
  shift 2
  if "$@" >"$test_dir/output.log" 2>&1; then
    echo "FAILED: $name unexpectedly succeeded" >&2; cat "$test_dir/output.log" >&2; exit 1
  fi
  if ! grep -Fq "$pattern" "$test_dir/output.log"; then
    echo "FAILED: $name did not report $pattern" >&2; cat "$test_dir/output.log" >&2; exit 1
  fi
  passed=$((passed + 1))
}

# Exercise the actual comparison loop without the costly Zig/Lean builds before it.
compare="$test_dir/compare"
mkdir -p "$compare/tests/diff/basic/inputs" "$compare/tests/diff/out/zig/basic" \
  "$compare/tests/diff/out/lean/basic" "$compare/bin"
cat >"$compare/run.sh" <<'EOF'
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
examples=basic
build_dir=$PWD
EOF
sed -n '/^functions_of()/,/^}/p' "$repo_root/scripts/diff.sh" >>"$compare/run.sh"
sed -n '/^# Classifies one JSONL/,$p' "$repo_root/scripts/diff.sh" >>"$compare/run.sh"
printf '[1]\n[2]\n' >"$compare/tests/diff/basic/inputs/foo.jsonl"
printf '{"ok":1}\n{"ok":2}\n' >"$compare/tests/diff/out/zig/basic/foo.jsonl"
cp "$compare/tests/diff/out/zig/basic/foo.jsonl" "$compare/tests/diff/out/lean/basic/foo.jsonl"
expect_pass "healthy comparison" bash "$compare/run.sh"
printf '{"ok":9}\n{"ok":2}\n' >"$compare/tests/diff/out/lean/basic/foo.jsonl"
expect_failure "real mismatch" "MISMATCH basic.foo" bash "$compare/run.sh"
real_paste=$(command -v paste)
cat >"$compare/bin/paste" <<'EOF'
#!/usr/bin/env bash
if [ "$PASTE_MODE" = fail ]; then echo "paste failed" >&2; exit 1; fi
"$REAL_PASTE" "$@" | head -n 1
EOF
chmod +x "$compare/bin/paste"
expect_failure "failed comparison producer" "paste failed" env PATH="$compare/bin:$PATH" \
  PASTE_MODE=fail REAL_PASTE="$real_paste" bash "$compare/run.sh"
cp "$compare/tests/diff/out/zig/basic/foo.jsonl" "$compare/tests/diff/out/lean/basic/foo.jsonl"
expect_failure "truncated comparison producer" "compared 1 rows" env PATH="$compare/bin:$PATH" \
  PASTE_MODE=truncate REAL_PASTE="$real_paste" bash "$compare/run.sh"

# Execute the entire float probe with a fake compiler that emits the selected probe output.
probe="$test_dir/probe"
mkdir -p "$probe/scripts" "$probe/tests/floatprobe" "$probe/bin"
cp "$repo_root/scripts/floatprobe.sh" "$probe/scripts/"
cat >"$probe/bin/zig" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = version ]; then echo test; exit 0; fi
for arg in "$@"; do
  case "$arg" in -femit-bin=*)
    printf '#!/usr/bin/env bash\ncat "$PROBE_OUTPUT"\n' >"${arg#-femit-bin=}"
    chmod +x "${arg#-femit-bin=}"
  esac
done
EOF
chmod +x "$probe/bin/zig"
printf 'f16 sqrt 1\n' >"$probe/tests/floatprobe/expected.txt"
printf 'f16 sqrt 2\n' >"$probe/tests/floatprobe/expected.test.txt"
printf 'f16 sqrt 2\n' >"$probe/actual.txt"
expect_pass "valid float override" env AIR2LEAN_ZIG="$probe/bin/zig" PROBE_OUTPUT="$probe/actual.txt" \
  bash "$probe/scripts/floatprobe.sh"
printf 'f16 sqrt 2\nf16 sqrt 3\n' >"$probe/tests/floatprobe/expected.test.txt"
printf 'f16 sqrt 3\n' >"$probe/actual.txt"
expect_failure "duplicate float override" "duplicate override key" env AIR2LEAN_ZIG="$probe/bin/zig" \
  PROBE_OUTPUT="$probe/actual.txt" bash "$probe/scripts/floatprobe.sh"

# A fake translator emits bad Lean; the generated-module build must reject it even with diff0.
check="$test_dir/check"
mkdir -p "$check/scripts" "$check/examples/basic" "$check/tests/golden/basic/air" \
  "$check/Proofs/Basic" "$check/bin"
cp "$repo_root/scripts/check.sh" "$check/scripts/"
printf '{\n  "instructions": []\n}\n' >"$check/tests/golden/basic/air/basic.foo.json"
touch "$check/examples/basic/basic.zig"
cat >"$check/bin/zig" <<'EOF'
#!/usr/bin/env bash
awk 'NR == 1 {
  print
  if (ENVIRON["EXPORTED_ENDIAN"] != "") print "  \"target_endian\": \"" ENVIRON["EXPORTED_ENDIAN"] "\","
  next
} { print }' tests/golden/basic/air/basic.foo.json >"$ZIG_AIR_JSON_DIR/basic.foo.json"
EOF
cat >"$check/bin/lake" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = exe ]; then
  while [ "$#" -gt 0 ]; do
    if [ "$1" = -o ]; then printf '%s\n' "$GENERATED_SOURCE" >"$2"; shift 2; else shift; fi
  done
else
  for arg in "$@"; do
    if [ "$arg" = Proofs.Basic.Gen ] && grep -q invalid Proofs/Basic/Gen.lean; then
      echo 'invalid generated Lean rejected' >&2; exit 1
    fi
  done
fi
EOF
chmod +x "$check/bin/zig" "$check/bin/lake"
expect_failure "generated Lean checked with diff disabled" "invalid generated Lean rejected" \
  env PATH="$check/bin:$PATH" AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=basic \
  AIR2LEAN_CI=0 AIR2LEAN_DIFF=0 AIR2LEAN_OUT_DIR= GENERATED_SOURCE=invalid bash "$check/scripts/check.sh"
expect_pass "valid generation with diff disabled" env PATH="$check/bin:$PATH" \
  AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=basic AIR2LEAN_CI=0 AIR2LEAN_DIFF=0 \
  AIR2LEAN_OUT_DIR= GENERATED_SOURCE='def valid := 1' bash "$check/scripts/check.sh"
expect_pass "little-endian metadata compatible with legacy goldens" env PATH="$check/bin:$PATH" \
  AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=basic AIR2LEAN_CI=0 AIR2LEAN_DIFF=0 \
  AIR2LEAN_OUT_DIR= EXPORTED_ENDIAN=little GENERATED_SOURCE='def valid := 1' bash "$check/scripts/check.sh"
expect_failure "big-endian metadata remains visible" "does not match its golden files" env PATH="$check/bin:$PATH" \
  AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=basic AIR2LEAN_CI=0 AIR2LEAN_DIFF=0 \
  AIR2LEAN_OUT_DIR= EXPORTED_ENDIAN=big GENERATED_SOURCE='def valid := 1' bash "$check/scripts/check.sh"

# Execute mutation w on copies of every source the script backs up. No live source is touched.
mutate="$test_dir/mutate"
mkdir -p "$mutate/scripts" "$mutate/examples/atomics" "$mutate/examples/recursion" "$mutate/bin"
cp "$repo_root/scripts/mutate.sh" "$mutate/scripts/"
# Two shards: w alone in shard2; all other real labels in shard1, maintaining complete coverage.
awk '{ for (i = 1; i <= NF; i++) if ($i != "w") printf "%s ", $i } END { print ""; print "w" }' \
  "$repo_root/scripts/mutation-shards.txt" >"$mutate/scripts/mutation-shards.txt"
touch "$mutate/examples/atomics/atomics.zig" "$mutate/examples/recursion/recursion.zig"
for path in Proofs/Basic/Gen.lean Proofs/Options/Gen.lean Proofs/Variants/Gen.lean \
  Proofs/Layout/Gen.lean Proofs/Slices/Gen.lean ZigLean/Basic.lean ZigLean/Lemmas.lean \
  ZigLean/Float/Round.lean ZigLean/Mem/Basic.lean ZigLean/Mem/Enc.lean ZigLean/Mem/Alloc.lean \
  tests/diff/asm/asm.zig ZigLean/Vec.lean ZigLean/Mem/Thread.lean ZigLean/Conc/Sched.lean; do
  mkdir -p "$mutate/$(dirname "$path")"
  cp "$repo_root/$path" "$mutate/$path"
done
cp "$mutate/ZigLean/Mem/Thread.lean" "$mutate/original-thread.lean"
cat >"$mutate/bin/lake" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = env ]; then exit 0; fi
if [ ! -f "$BASELINE_MARKER" ]; then
  touch "$BASELINE_MARKER"
  if [ "$PROOF_MODE" = baseline-error ]; then echo 'broken unmutated proof' >&2; exit 1; fi
  exit 0
fi
case "$PROOF_MODE" in
  setup-error) echo 'broken lake invocation' >&2; exit 127 ;;
  resource-error) echo 'Lean killed: out of memory' >&2; exit 1 ;;
  signal-error) echo 'interrupting mutant build' >&2; kill -TERM "$PPID"; exit 143 ;;
  undetected) exit 0 ;;
  *) echo 'error: ZigLean/Mem/Thread.lean:1:0: unsolved goals'; exit 1 ;;
esac
EOF
chmod +x "$mutate/bin/lake"
run_mutant() {
  local mode=$1 marker=$2
  env PATH="$mutate/bin:$PATH" AIR2LEAN_ZIG_AIR="$check/bin/zig" \
    AIR2LEAN_EXAMPLES=atomics AIR2LEAN_MUTATION_SHARD=2 AIR2LEAN_MUTATION_SHARDS=2 \
    PROOF_MODE="$mode" BASELINE_MARKER="$mutate/$marker" bash "$mutate/scripts/mutate.sh"
}
expect_failure "unknown mutation example" "unknown example" env AIR2LEAN_ZIG_AIR="$check/bin/zig" \
  AIR2LEAN_EXAMPLES=typo bash "$mutate/scripts/mutate.sh"
expect_failure "whitespace-only selection" "no examples selected" env AIR2LEAN_ZIG_AIR="$check/bin/zig" \
  AIR2LEAN_EXAMPLES=' ' bash "$mutate/scripts/mutate.sh"
expect_failure "empty shard/example intersection" "selection ran no mutations" env PATH="$mutate/bin:$PATH" \
  AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=recursion AIR2LEAN_MUTATION_SHARD=2 \
  AIR2LEAN_MUTATION_SHARDS=2 bash "$mutate/scripts/mutate.sh"
expect_failure "broken unmutated proof" "broken unmutated proof" run_mutant baseline-error baseline1
expect_failure "broken proof tool" "proof build setup failed (exit=127)" run_mutant setup-error baseline2
expect_pass "source restored after proof setup failure" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_failure "proof resource failure" "proof build setup failed (exit=1)" run_mutant resource-error baseline3
expect_pass "source restored after proof resource failure" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_failure "interrupted mutant proof" "mutation interrupted by TERM" run_mutant signal-error baseline-signal
expect_pass "source restored after interruption" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_failure "undetected proof mutation fails the run" "NOT detected" run_mutant undetected baseline-undetected
expect_pass "source restored after undetected mutation" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_pass "genuine mutant proof error" run_mutant mutant-error baseline4
expect_pass "mutation source restored" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"

echo "shell review checks: $passed passed"
