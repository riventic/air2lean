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
mkdir -p "$compare/scripts"
cp "$repo_root/scripts/panic-policy.tsv" "$compare/scripts/"
cat >"$compare/run.sh" <<'EOF'
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
examples=basic
build_dir=$PWD
repo_root=$PWD
# This isolated fixture tests the legacy comparison loop, with no typed producers.
unset AIR2LEAN_DIFF_REPORT
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
cp "$repo_root/scripts/check.sh" "$repo_root/scripts/normalize-air.py"   "$repo_root/scripts/normalize-generated.py" \
  "$repo_root/scripts/workflow-common.sh" "$repo_root/scripts/safe-output.py" "$check/scripts/"
cat >"$check/tests/golden/basic/air/basic.foo.json" <<'EOF'
{
  "schema": 11,
  "zig_version": "0.16.0",
  "name": "basic.foo__anon_1",
  "types": [{"name": "basic.Choice__enum_1", "fields": [{"name": "visible__anon_1"}]}],
  "body": [{
    "callee": {"func": "basic.helper__anon_1"},
    "callback": {"comptime_fn": "basic.task__anon_1"},
    "string": "literal__anon_1",
    "error": {"name": "error__anon_1"},
    "asm": "asm__anon_1",
    "zig_version": "nested__anon_1",
    "target_endian": "nested__anon_1",
    "__anon_1": "key__anon_1"
  }]
}
EOF
touch "$check/examples/basic/basic.zig"
cat >"$check/bin/zig" <<'EOF'
#!/usr/bin/env bash
python3 - <<'PY'
import json
import os
from pathlib import Path

data = json.loads(Path("tests/golden/basic/air/basic.foo.json").read_text())
data["zig_version"] = "0.16.0"
endian = os.environ.get("EXPORTED_ENDIAN", "")
if endian:
    data["target_endian"] = endian
case = os.environ.get("EXPORTED_CASE", "")
body = data["body"][0]
if case == "identities":
    data["name"] = "basic.foo__anon_987"
    data["types"][0]["name"] = "basic.Choice__enum_654"
    body["callee"]["func"] = "basic.helper__anon_321"
    body["callback"]["comptime_fn"] = "basic.task__anon_456"
elif case == "enum-field":
    data["types"][0]["fields"][0]["name"] = "visible__anon_2"
elif case == "error-name":
    body["error"]["name"] = "error__anon_2"
elif case == "key":
    body["__anon_2"] = body.pop("__anon_1")
elif case:
    body[case] = body[case].replace("__anon_1", "__anon_2")
Path(os.environ["ZIG_AIR_JSON_DIR"], "basic.foo.json").write_text(json.dumps(data))
PY
EOF
cat >"$check/bin/lake" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = exe ]; then
  python3 - "$@" <<'PYFAKE'
import json
import os
from pathlib import Path
import runpy
import sys
helpers = runpy.run_path("scripts/normalize-generated.py")
args = sys.argv[1:]
source = sorted(Path(args[2]).glob("*.json"))[0]
profile = helpers["profile_for_air"](json.loads(source.read_text()))
metadata = dict(profile=profile, float_semantics="ieee", correspondence="model")
Path(args[args.index("-o") + 1]).write_text("-- air2lean-profile: " + json.dumps(metadata) + "\n" +
                                         os.environ["GENERATED_SOURCE"] + "\n")
PYFAKE
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
expect_failure "big-endian metadata fails before comparison" "little-endian memory model" env PATH="$check/bin:$PATH" \
  AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=basic AIR2LEAN_CI=0 AIR2LEAN_DIFF=0 \
  AIR2LEAN_OUT_DIR= EXPORTED_ENDIAN=big GENERATED_SOURCE='def valid := 1' bash "$check/scripts/check.sh"
run_identity_check() {
  env PATH="$check/bin:$PATH" AIR2LEAN_ZIG_AIR="$check/bin/zig" AIR2LEAN_EXAMPLES=basic \
    AIR2LEAN_CI=0 AIR2LEAN_DIFF=0 AIR2LEAN_OUT_DIR= EXPORTED_ENDIAN= EXPORTED_CASE="$1" \
    GENERATED_SOURCE='def valid := 1' bash "$check/scripts/check.sh"
}
expect_pass "compiler identity renumbering remains compatible" run_identity_check identities
for change in string enum-field error-name asm zig_version target_endian key; do
  expect_failure "observable $change spelling remains visible" "does not match its golden files" \
    run_identity_check "$change"
done

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
  tests/diff/asm/asm.zig ZigLean/Vec.lean ZigLean/Mem/Thread.lean ZigLean/Conc/Sched.lean \
  ZigLean/Conc.lean; do
  mkdir -p "$mutate/$(dirname "$path")"
  cp "$repo_root/$path" "$mutate/$path"
done
cp "$mutate/ZigLean/Mem/Thread.lean" "$mutate/original-thread.lean"
cp "$mutate/ZigLean/Conc.lean" "$mutate/original-conc.lean"
cat >"$mutate/bin/lake" <<'EOF'
#!/usr/bin/env bash
cmp original-conc.lean ZigLean/Conc.lean || exit 1
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
expect_pass "Conc restored after proof baseline failure" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_failure "broken proof tool" "proof build setup failed (exit=127)" run_mutant setup-error baseline2
expect_pass "source restored after proof setup failure" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_pass "Conc restored after proof setup failure" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_failure "proof resource failure" "proof build setup failed (exit=1)" run_mutant resource-error baseline3
expect_pass "source restored after proof resource failure" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_pass "Conc restored after proof resource failure" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_failure "interrupted mutant proof" "mutation interrupted by TERM" run_mutant signal-error baseline-signal
expect_pass "source restored after interruption" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_pass "Conc restored after proof interruption" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_failure "undetected proof mutation fails the run" "NOT detected" run_mutant undetected baseline-undetected
expect_pass "source restored after undetected mutation" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_pass "Conc restored after undetected proof mutation" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_pass "genuine mutant proof error" run_mutant mutant-error baseline4
expect_pass "mutation source restored" cmp "$mutate/original-thread.lean" "$mutate/ZigLean/Mem/Thread.lean"
expect_pass "Conc restored after detected proof mutation" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"

# The emitter must elaborate every generated/caller fixture and propagate list failures.
emitter="$test_dir/emitter"
mkdir -p "$emitter/tests/review" "$emitter/bin" "$emitter/-fixtures"
cp "$repo_root/tests/review/emitter.sh" "$emitter/tests/review/"
cat > "$emitter/bin/lake" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [ "${3:-}" = --run ]; then
  output=$5
  mkdir -p "$output"
  for name in pointerCasts tuples names indirectCapture blockLoopExits unionTagCapture spawnedSlice floatIeee floatCompilerRt legacyUnionTag escapingSafetyCheck derivedInstanceNames binderTypeNames classNames underscoreName ctorIndexNames generatedBinderTypeNames indexedBinderTypeNames generatedBinderFunctionNames reservedKeywordNames; do
    [ "${EMITTER_MODE:-}" != missing ] || [ "$name" != tuples ] || continue
    : > "$output/$name.lean"
  done
else
  printf '%s\n' "$3" >> "$EMITTER_LOG"
fi
EOF
real_find=$(command -v find)
real_sort=$(command -v sort)
cat > "$emitter/bin/find" <<'EOF'
#!/usr/bin/env bash
if [ "${LIST_MODE:-}" = find-failure ]; then echo 'find failed' >&2; exit 1; fi
if [ "${LIST_MODE:-}" = truncated ]; then "$REAL_FIND" "$@" | head -n 1; else "$REAL_FIND" "$@"; fi
EOF
cat > "$emitter/bin/sort" <<'EOF'
#!/usr/bin/env bash
if [ "${LIST_MODE:-}" = sort-failure ]; then echo 'sort failed' >&2; exit 1; fi
if [ "${LIST_MODE:-}" = sort-truncated ]; then "$REAL_SORT" "$@" | head -n 1; else "$REAL_SORT" "$@"; fi
EOF
chmod +x "$emitter/bin/"*
run_emitter() {
  env PATH="$emitter/bin:$PATH" REAL_FIND="$real_find" REAL_SORT="$real_sort" \
    EMITTER_LOG="$emitter/checked" LIST_MODE="$1" EMITTER_MODE="${2:-}" \
    bash "$emitter/tests/review/emitter.sh" -fixtures
}
for name in parser1 parser2 parser3 parser4 parser5 parser6; do : > "$emitter/-fixtures/$name.lean"; done
expect_pass "emitter checks 26 fixtures in leading-hyphen directory" run_emitter healthy
expect_pass "all 26 emitter and caller fixtures elaborated" test "$(wc -l < "$emitter/checked" | tr -d ' ')" -eq 26
expect_failure "failed emitter find" "find failed" run_emitter find-failure
expect_failure "failed emitter sort" "sort failed" run_emitter sort-failure
expect_failure "truncated emitter find" "listing incomplete" run_emitter truncated
expect_failure "truncated emitter sort" "listing incomplete" run_emitter sort-truncated
# tuples.lean remains from the healthy run: it must not mask a missing fresh output.
expect_failure "stale fixture cannot mask a missing emitter case" "missing emitter fixture: tuples" run_emitter healthy missing
rm "$emitter/-fixtures/tuples.lean"
expect_failure "missing emitter semantic fixture" "missing emitter fixture: tuples" run_emitter healthy missing

# Focused mutation s: verify the real semantic edit, baseline rejection, and restoration.
mkdir -p "$mutate/examples/lists"
touch "$mutate/examples/lists/lists.zig"
awk '{ for (i = 1; i <= NF; i++) if ($i != "s") printf "%s ", $i } END { print ""; print "s" }' \
  "$repo_root/scripts/mutation-shards.txt" > "$mutate/scripts/mutation-shards.txt"
cp "$mutate/ZigLean/Mem/Alloc.lean" "$mutate/original-alloc.lean"
cat > "$mutate/scripts/diff.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [ ! -f "$DIFF_BASELINE_MARKER" ]; then
  touch "$DIFF_BASELINE_MARKER"
  cmp original-conc.lean ZigLean/Conc.lean || exit 1
  if [ "$DIFF_MODE" = baseline-error ]; then echo 'TOTAL: mismatch=1'; exit 1; fi
  cmp original-alloc.lean ZigLean/Mem/Alloc.lean || exit 1
  exit 0
fi
python3 - <<'PYTEST'
from pathlib import Path
before = Path('original-alloc.lean').read_text()
after = Path('ZigLean/Mem/Alloc.lean').read_text()
old = 'poisonFree s.ptr (size * (s.len.toNat + 1))'
new = 'poisonFree s.ptr (size * s.len.toNat)'
assert before.count(old) == 1 and after == before.replace(old, new), 'mutation changed more than sentinel byte count'
proof_import = 'import ZigLean.Conc.WeakCas\n'
before_conc = Path('original-conc.lean').read_text()
assert before_conc.count(proof_import) == 1
assert Path('ZigLean/Conc.lean').read_text() == before_conc.replace(proof_import, ''), 'wrong proof import window'
PYTEST
if [ "$DIFF_MODE" = undetected ]; then echo 'TOTAL: mismatch=0'; exit 0; fi
echo 'TOTAL: mismatch=1'
exit 1
EOF
run_sentinel() {
  env PATH="$mutate/bin:$PATH" AIR2LEAN_ZIG_AIR="$check/bin/zig" \
    AIR2LEAN_EXAMPLES=lists AIR2LEAN_MUTATION_SHARD=2 AIR2LEAN_MUTATION_SHARDS=2 \
    DIFF_MODE="$1" DIFF_BASELINE_MARKER="$mutate/$2" \
    bash "$mutate/scripts/mutate.sh"
}
expect_failure "unmutated differential mismatch cannot detect a mutant" "unmutated differential baseline failed" run_sentinel baseline-error diff-baseline-fail
expect_pass "baseline failure preserves allocator source" cmp "$mutate/original-alloc.lean" "$mutate/ZigLean/Mem/Alloc.lean"
expect_pass "Conc restored after differential baseline failure" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_pass "sentinel mutation changes only sentinel byte count and is detected" run_sentinel detected diff-baseline-pass
expect_pass "sentinel mutation restores allocator source" cmp "$mutate/original-alloc.lean" "$mutate/ZigLean/Mem/Alloc.lean"
expect_pass "Conc restored after detected differential mutation" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"
expect_failure "undetected sentinel mutation fails" "NOT detected" run_sentinel undetected diff-baseline-undetected
expect_pass "undetected sentinel mutation restores source" cmp "$mutate/original-alloc.lean" "$mutate/ZigLean/Mem/Alloc.lean"
expect_pass "Conc restored after undetected differential mutation" cmp "$mutate/original-conc.lean" "$mutate/ZigLean/Conc.lean"

echo "shell review checks: $passed passed"
