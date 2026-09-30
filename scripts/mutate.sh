#!/usr/bin/env bash
# Mutation testing for the differential test's panic-kind comparison (docs/generated-code.md
# §Panics). Each mutation below must make scripts/diff.sh FAIL (exit 1, and mismatch>0 or a changed pinned count); this script
# exits 0 only if every mutation was detected. Guards against a diff test that always passes.
# Each mutation runs diff.sh over its own example only, so a mismatch elsewhere cannot count as
# a detection.
#
# (a) Zig-source mutation: `scale`'s checked `a * b` becomes wrapping `a *% b` in a temp copy of
#     examples/basic/basic.zig, re-translated to Lean. The Zig side keeps checked semantics (it
#     always builds from the real examples/basic/basic.zig — untouched here), so `scale`'s
#     overflow inputs now disagree: Zig fails, Lean's regenerated `scale` does not. Exercises the
#     plain ok-vs-fail comparison — a baseline sanity check.
# (b) Lean-runtime mutation: `Zig.add` (ZigLean/Basic.lean) throws `.panic` instead of
#     `.overflow` for the same failing inputs. Both sides still fail, but with different
#     `Zig.Error` kinds — this exercises the kind comparison in diff.sh/Emit.lean/harness.zig;
#     the plain ok/fail check alone would miss it. `ZigLean.Lemmas`'s `add_unsigned` states
#     `add`'s result in terms of `.overflow`, so it stops type-checking under this mutation (a
#     real, expected proof failure, not a bug); `ZigLean.lean` imports `ZigLean.Lemmas`
#     unconditionally, and `Proofs/Basic/Gen.lean` imports `ZigLean`, so this mutation also drops
#     that one theorem for the duration of the rebuild.
# (c) Zig-source mutation, options: `findOr`'s `orelse xs.len` becomes `orelse 0` in a temp copy
#     of examples/options/options.zig, re-translated to Lean — same shape as (a), but for the
#     optional-result protocol (a not-found search now returns 0 instead of xs.len).
# (d) Lean-runtime mutation: `roundQuot` (ZigLean/Float/Round.lean) rounds ties away from zero
#     instead of to even. `Float.roundRat`'s domain is nonnegative, so "away from zero" is
#     "always round up": the tie branch `else if m % 2 = 0 then (m : Int) else (m : Int) + 1`
#     becomes `else (m : Int) + 1`. Every float op that rounds (`+ - * /`, `@sqrt`,
#     `@floatFromInt`, …) goes through it, so `scripts/diff.sh` must catch it via mismatches,
#     not a build failure: the one lemma that unfolds `roundQuot` (`roundQuot_le`) is written to
#     hold for both forms.
# (e) Emitter-output mutation, variants: the generated `Light.ofInt?` (Proofs/Variants/Gen.lean) also
#     accepts the unnamed value 3. `lightOf(3)` then returns `.red`, where Zig panics
#     (`invalidEnumValue`): the conversion an enum's generated defs do must match Zig's.
# (f) Lean-runtime mutation, pointers: `Zig.store` (ZigLean/Mem/Basic.lean) writes one byte too
#     few (the last byte of the value stays as it was). `swap`, `delay` and `copyJob` then leave
#     other bytes in the buffers than Zig: the diff test compares the buffers after each call.
# (g) Lean-runtime mutation, slices: `Zig.memmove` (ZigLean/Mem/Basic.lean) writes one byte too
#     few (the last byte of the destination stays as it was). `copy` and `copyWithin` then leave
#     other bytes in the buffers than Zig.
# (h) Lean-runtime mutation, lists: `Zig.rawAlloc` (ZigLean/Mem/Alloc.lean) never fails at
#     `Mem.failAt`. Every lists function then returns a value where Zig returns
#     `error.OutOfMemory`.
# (i) Diff-test-archive mutation, asm: `tests/diff/asm/asm.zig`'s `air2lean_asm_bswap32` returns
#     `x` unchanged instead of `@byteSwap(x)`. This archive (docs/generated-code.md §Inline asm)
#     is the diff test's own stand-in for `Asm.airAsm_*`'s opaque behaviour (M21: no defining
#     equation exists to mutate on the Lean side, unlike (b)/(d)/(f)/(g)/(h) above) -- mutating
#     it and comparing against `examples/asm/asm.zig`'s real inline asm checks that the
#     comparison is live, not vacuous. x86_64 only, same as `asm` itself.
# (j) Lean-runtime mutation, vectors: `Vec.reduce` (ZigLean/Vec.lean) folds only lanes
#     `1..n-1`, dropping the last lane. `maxLane`'s `@reduce(.Max)` then ignores the vector's
#     last lane, so an input whose max is in that lane disagrees with Zig.
# (k) Lean-runtime mutation, threads: `racePair` (ZigLean/Mem/Basic.lean) makes two atomic
#     accesses race, as the eager model did. `parallelCounter` and `xchgRace` then throw
#     `.illegal` -- tests/diff/threads/unspecified.txt's pinned counts change.
# (l) Lean-runtime mutation, threads: `recordAccess` (ZigLean/Mem/Basic.lean) never checks for a
#     race (`raceAt`'s result ignored; every access recorded race-free). `race` then returns a
#     value instead of throwing `.illegal` -- tests/diff/threads/unspecified.txt's pinned count
#     drops to 0.
# (m) Emitter-output mutation, layout: the generated `Zig.Packed Flags 8` instance
#     (Proofs/Layout/Gen.lean) reads `ready` from bit 1 and `err` from bit 0 in `ofBits` (two
#     fields swapped). `byteToFlags`, `isOk` and the `@bitCast` round trip in `setMode` then
#     differ from Zig.
# (n) Lean-runtime mutation, layout: `Mem.accessW` (ZigLean/Mem/Basic.lean) does not check for a
#     `const` global. `writeTable` then writes to the read-only `table` and returns a value
#     instead of throwing `.illegal`: tests/diff/layout/unspecified.txt's pinned count for it
#     (3) drops to 0.
# (o) Lean-runtime mutation, layout: `byteBits` (ZigLean/Mem/Enc.lean) rejects every `Byte.part`
#     byte. `nibArg` and `setNib` then throw `.unspecified` for their `u4` fields instead of
#     returning a value: tests/diff/layout/unspecified.txt expects 0 for them.
# (p) Lean-runtime mutation, layout: `byteBits` (ZigLean/Mem/Enc.lean) accepts a set bit above an
#     `N`-bit integer in its last byte (the old truncation). `numInt` then reads the tag byte 2
#     of its 1-bit hidden tag as tag 0: tests/diff/layout/unspecified.txt's pinned count for it
#     (30) drops to 0.
# (q) Lean-runtime mutation, vectors: `Zig.mod` (ZigLean/Basic.lean) throws `.panic` for a
#     negative divisor (the old model; Sema checks only `b ≠ 0`). `sMod` and `vMod` then
#     fail where Zig returns the floored modulo.
# (r) Emitter-output mutation, slices: the generated constant `"xyz".*` in `sentinelArr`
#     (Proofs/Slices/Gen.lean) has no sentinel item (`Vector (BitVec 8) 3`), as when the emitter
#     drops the sentinel of a `[N:s]T` value. `sentinelArr(3)` then panics where Zig returns.
# (s) Lean-runtime mutation, lists: `Allocator.freeSentinel` (ZigLean/Mem/Alloc.lean) frees `len`
#     items, not `len + 1`: the free of `dupeZLen`'s `[:0]u8` then misses the sentinel byte and
#     throws `.illegal` (a free that is not the whole block).
# (t) Emitter-output mutation, layout: the generated `Zig.Packed Mode 2` instance
#     (Proofs/Layout/Gen.lean) calls every value `valid`, as when the emitter drops the check of
#     an enum field of a packed struct. `ctlSum` and `ctlMode` then read mode 3 as `off`.
# (u) Lean-runtime mutation, layout: the `Enc (Vec Bool n)` instance (ZigLean/Vec.lean) puts lane
#     `i` in bit `n - 1 - i`. `maskStore` then writes the wrong byte and counts wrong lanes.
# (v) Lean-runtime mutation, threads: `cmpxchgAs` (ZigLean/Mem/Thread.lean) compares with the
#     new value, not the expected one. In `claimOnce` no thread wins the claim.
# (w) Lean-runtime mutation, atomics: `acquireClock` (ZigLean/Mem/Thread.lean) adopts no clock:
#     an acquire read gives no happens-before edge. Detected by the proof build: in
#     `mp_sees_data` (Proofs/Atomics/Proofs.lean) the data read after the flag is then a race.
# (x) Lean-runtime mutation, atomics: `writeSlots` offers only the end: a relaxed write never
#     goes before a newer message. Detected by the proof build: `twoPlusTwoW_weak` needs it.
#     A weak-memory result is rare on real hardware, so the diff test seldom sees one; the
#     proofs show each one under a fixed schedule.
# (y) Lean-runtime mutation, sync: a futex `wait` (ZigLean/Mem/Thread.lean) never blocks.
#     Detected by the proof build: `wait_alone_deadlock` (Proofs/Sync/Proofs.lean).
# (z) Lean-runtime mutation, sync: the scheduler's deadlock check is off (no result instead of
#     `.deadlock`). Detected by the proof build: `wait_alone_deadlock`.
# (aa) Lean-runtime mutation, threads: an RMW (ZigLean/Mem/Thread.lean's `readOpts`) can read any
#     message, also one with an RMW after it: a lost update. Detected by the proof build:
#     `readOpts_chain` (ZigLean/Conc/Lemmas.lean), which `parallelCounter_spec`
#     (Proofs/Threads/Counter.lean) needs. The diff test does not see it: the newest message is
#     still option 0.
# (ab) Lean-runtime mutation, threads: a spawned thread (`Thread.fork`) gets an empty clock: it
#     no longer happens after its spawner's writes. Detected by the proof build:
#     `parallelCounter_safe` (Proofs/Threads/Counter.lean; a kid's read of its context would race).
#     The diff test does not see it: a schedule with a race matches any Zig result.
# (ac) Lean-runtime mutation, sync: a futex wake (ZigLean/Mem/Thread.lean's `futexWake`) wakes no
#     thread. Detected by the proof build: `mutexCounter_safe` (Proofs/Sync/Mutex.lean; a waiter
#     stays in the queue: a deadlock).
# (ad) Lean-runtime mutation, atomics: a `cmpxchg` (ZigLean/Mem/Thread.lean's `casPrep`) can
#     succeed on a message with an RMW after it: two pushes read the same head, one is lost.
#     Detected by the proof build: `casOpts_pos` (ZigLean/Conc/Lemmas.lean), which
#     `stackPush_spec` (Proofs/Atomics/Stack.lean) needs. The diff test does not see it: the
#     newest message is still option 0.
#
# Usage: mutate.sh
# Env:
#   AIR2LEAN_ZIG_AIR      Patched zig for translation (same as check.sh), needed for (a)/(c).
#   AIR2LEAN_ZIG_VERSION  Zig version: selects the default patched zig. Default: 0.16.0 (same as check.sh).
#   AIR2LEAN_EXAMPLES     Space-separated example dirs. A mutation runs only if its example
#                         (basic for (a)/(b), options for (c), floatops for (d), variants for (e),
#                         pointers (f), slices (g), lists (h), asm (i), vectors (j),
#                         threads (k)/(l), layout (m)/(n)/(o)/(p), vectors (q), slices (r), lists (s), layout (t)/(u), threads (v), atomics (w)/(x), sync (y)/(z), threads (aa)/(ab))
#                         is in the list.
#                         Default: every dir in examples/.
#   AIR2LEAN_MUTATION_SHARD   Run only the mutations of line N (from 1) of
#                         scripts/mutation-shards.txt (CI runs one job per line). Default: all.
#   AIR2LEAN_MUTATION_SHARDS  The number of shard jobs. If set, the file must have that many lines.
#                         Each run checks that the lines name every mutation exactly once, so a
#                         new mutation that is in no line fails.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

zig_version=${AIR2LEAN_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_ZIG_AIR:-zig-air-$zig_version/bin/zig}
[ -x "$zig_air" ] || {
  echo "error: patched zig not found/executable at $zig_air" >&2
  echo "hint: build one with zig-patch/build.sh $zig_version (see zig-patch/README.md)" >&2
  exit 1
}

examples=${AIR2LEAN_EXAMPLES:-$(cd examples && for d in */; do printf '%s ' "${d%/}"; done)}
has_example() {
  local needle=$1 e
  for e in $examples; do
    [ "$e" = "$needle" ] && return 0
  done
  return 1
}

# The shards (scripts/mutation-shards.txt): every mutation of this script in exactly one line.
shards_file="scripts/mutation-shards.txt"
all_labels=$(sed -n 's/^echo "== mutation (\([a-z]*\)).*/\1/p' scripts/mutate.sh | sort)
shard_labels=$(tr ' ' '\n' < "$shards_file" | sed '/^$/d' | sort)
if [ "$all_labels" != "$shard_labels" ]; then
  echo "error: $shards_file must name every mutation exactly once" >&2
  diff <(echo "$all_labels") <(echo "$shard_labels") >&2 || true
  exit 1
fi
if [ -n "${AIR2LEAN_MUTATION_SHARDS:-}" ] && [ "$(sed '/^$/d' "$shards_file" | wc -l)" -ne "$AIR2LEAN_MUTATION_SHARDS" ]; then
  echo "error: $shards_file has not $AIR2LEAN_MUTATION_SHARDS lines (one per CI shard job)" >&2
  exit 1
fi
selected=""
if [ -n "${AIR2LEAN_MUTATION_SHARD:-}" ]; then
  selected=$(sed '/^$/d' "$shards_file" | sed -n "${AIR2LEAN_MUTATION_SHARD}p")
  [ -n "$selected" ] || { echo "error: $shards_file has no line $AIR2LEAN_MUTATION_SHARD" >&2; exit 1; }
fi
want_mutation() {
  local l
  [ -z "$selected" ] && return 0
  for l in $selected; do [ "$l" = "$1" ] && return 0; done
  return 1
}

gen_file="Proofs/Basic/Gen.lean"
options_gen="Proofs/Options/Gen.lean"
variants_gen="Proofs/Variants/Gen.lean"
layout_gen="Proofs/Layout/Gen.lean"
slices_gen="Proofs/Slices/Gen.lean"
basic_lean="ZigLean/Basic.lean"
lemmas_lean="ZigLean/Lemmas.lean"
round_lean="ZigLean/Float/Round.lean"
mem_lean="ZigLean/Mem/Basic.lean"
enc_lean="ZigLean/Mem/Enc.lean"
alloc_lean="ZigLean/Mem/Alloc.lean"
asm_zig="tests/diff/asm/asm.zig"
vec_lean="ZigLean/Vec.lean"
thread_lean="ZigLean/Mem/Thread.lean"
sched_lean="ZigLean/Conc/Sched.lean"
gen_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-gen.XXXXXX")
options_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-options-gen.XXXXXX")
variants_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-variants-gen.XXXXXX")
layout_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-layout-gen.XXXXXX")
slices_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-slices-gen.XXXXXX")
basic_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-basic.XXXXXX")
lemmas_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-lemmas.XXXXXX")
round_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-round.XXXXXX")
mem_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-mem.XXXXXX")
enc_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-enc.XXXXXX")
alloc_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-alloc.XXXXXX")
asm_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-asm.XXXXXX")
vec_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-vec.XXXXXX")
thread_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-thread.XXXXXX")
sched_backup=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-sched.XXXXXX")
cp "$gen_file" "$gen_backup"
cp "$options_gen" "$options_backup"
cp "$variants_gen" "$variants_backup"
cp "$layout_gen" "$layout_backup"
cp "$slices_gen" "$slices_backup"
cp "$basic_lean" "$basic_backup"
cp "$lemmas_lean" "$lemmas_backup"
cp "$round_lean" "$round_backup"
cp "$mem_lean" "$mem_backup"
cp "$enc_lean" "$enc_backup"
cp "$alloc_lean" "$alloc_backup"
cp "$asm_zig" "$asm_backup"
cp "$vec_lean" "$vec_backup"
cp "$thread_lean" "$thread_backup"
cp "$sched_lean" "$sched_backup"

mutate_tmp=""
air_dir=""
cleanup() {
  # Capture the exit status that triggered this trap first — cleanup's own commands would
  # otherwise overwrite it, and bash uses whatever $? is left when the script exits.
  local ec=$?
  cp "$gen_backup" "$gen_file"
  cp "$options_backup" "$options_gen"
  cp "$variants_backup" "$variants_gen"
  cp "$layout_backup" "$layout_gen"
  cp "$slices_backup" "$slices_gen"
  cp "$basic_backup" "$basic_lean"
  cp "$lemmas_backup" "$lemmas_lean"
  cp "$round_backup" "$round_lean"
  cp "$mem_backup" "$mem_lean"
  cp "$enc_backup" "$enc_lean"
  cp "$alloc_backup" "$alloc_lean"
  cp "$asm_backup" "$asm_zig"
  cp "$vec_backup" "$vec_lean"
  cp "$thread_backup" "$thread_lean"
  cp "$sched_backup" "$sched_lean"
  rm -f "$gen_backup" "$options_backup" "$variants_backup" "$layout_backup" "$slices_backup" "$basic_backup" "$lemmas_backup" "$round_backup" \
    "$mem_backup" "$enc_backup" "$alloc_backup" "$asm_backup" "$vec_backup" "$thread_backup" "$sched_backup"
  [ -n "$mutate_tmp" ] && rm -rf "$mutate_tmp"
  [ -n "$air_dir" ] && rm -rf "$air_dir"
  exit "$ec"
}
trap cleanup EXIT

# translate_mutated <ex> <sed-expr> <grep-pattern>: apply <sed-expr> to a temp copy of
# examples/<ex>/<ex>.zig, check with <grep-pattern> that it changed, and translate the copy to
# Proofs/<Ex>/Gen.lean (the same steps as check.sh). The Zig harness keeps the real source.
translate_mutated() {
  local ex=$1 expr=$2 pattern=$3
  local Ex
  Ex="$(printf '%s' "${ex:0:1}" | tr '[:lower:]' '[:upper:]')${ex:1}"
  mutate_tmp=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-mutate-src.XXXXXX")
  cp "examples/$ex/$ex.zig" "$mutate_tmp/$ex.zig"
  sed -i.bak "$expr" "$mutate_tmp/$ex.zig"
  grep -q "$pattern" "$mutate_tmp/$ex.zig" || {
    echo "error: sed '$expr' did not change examples/$ex/$ex.zig" >&2
    exit 1
  }
  air_dir=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-mutate-air.XXXXXX")
  ZIG_AIR_JSON_DIR="$air_dir" ZIG_AIR_JSON_FILTER="$ex." "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing "$mutate_tmp/$ex.zig"
  lake exe air2lean "$air_dir" -o "Proofs/$Ex/Gen.lean" --namespace "$Ex" --prefix "$ex."
  rm -rf "$air_dir" "$mutate_tmp"
  air_dir=""
  mutate_tmp=""
}

# run_and_report <label> <ex>: runs scripts/diff.sh over <ex>, prints "<label>: detected/NOT
# detected (mismatch=N)" and sets $detected (1/0). A diff.sh crash with no TOTAL line at all (not
# even a mismatch report) is a broken test setup, not an undetected mutation, so that case
# aborts the whole script instead.
# proof_report <label> <module>: `lake build <module>` fails with the mutation (a detection).
proof_report() {
  local label=$1 mod=$2
  if lake build "$mod" >/dev/null 2>&1; then
    echo "$label: NOT detected (lake build $mod succeeded)"
    detected=0
  else
    echo "$label: detected (lake build $mod failed)"
    detected=1
  fi
}

run_and_report() {
  local label=$1 ex=$2
  local out
  out=$(mktemp "${TMPDIR:-/tmp}/air2lean-mutate-diff.XXXXXX")
  local status=0
  AIR2LEAN_EXAMPLES=$ex bash scripts/diff.sh >"$out" 2>&1 || status=$?
  local total_line
  total_line=$(grep '^TOTAL:' "$out" || true)
  if [ -z "$total_line" ]; then
    echo "error: $label: diff.sh produced no TOTAL line (setup broke, not just undetected)" >&2
    cat "$out" >&2
    rm -f "$out"
    exit 1
  fi
  local mismatch counts
  mismatch=$(echo "$total_line" | sed -n 's/.*mismatch=\([0-9]*\).*/\1/p')
  # A pinned `unspecified`/`capped` count that changed is a detection too (threads: a mutation
  # that removes a race result changes no value, only the count).
  counts=$(grep -c '^\(UNSPECIFIED\|CAPPED\) COUNT' "$out" || true)
  rm -f "$out"
  if [ "$status" -ne 0 ] && { [ "${mismatch:-0}" -gt 0 ] || [ "${counts:-0}" -gt 0 ]; }; then
    echo "$label: detected (exit=$status mismatch=$mismatch count_changes=$counts)"
    detected=1
  else
    echo "$label: NOT detected (exit=$status mismatch=$mismatch count_changes=$counts)"
    detected=0
  fi
}

all_detected=1

echo "== mutation (a): scale a*b -> a*%b (Zig source) ==" >&2
if ! want_mutation a; then
  echo "mutation (a): skipped (not in this shard)"
elif ! has_example basic; then
  echo "mutation (a): skipped (AIR2LEAN_EXAMPLES excludes basic)"
else
  translate_mutated basic 's/return a \* b;/return a *% b;/' 'a \*% b'
  # No top-level `lake build` here: scripts/diff.sh's own `(cd tests/diff && lake build
  # difftest)` already rebuilds Proofs.Basic.Gen as a dependency of Diff.lean.
  run_and_report "mutation (a)" basic
  [ "$detected" -eq 1 ] || all_detected=0
  # Restore Gen.lean before mutation (b) so the two mutations don't compound.
  cp "$gen_backup" "$gen_file"
fi

echo "== mutation (b): Zig.add throws .panic instead of .overflow (Lean runtime) ==" >&2
if ! want_mutation b; then
  echo "mutation (b): skipped (not in this shard)"
elif ! has_example basic; then
  echo "mutation (b): skipped (AIR2LEAN_EXAMPLES excludes basic)"
else
  sed -i.bak 's/a\.uaddOverflow b) then throw \.overflow/a.uaddOverflow b) then throw .panic/' "$basic_lean"
  rm -f "$basic_lean.bak"
  grep -q 'a.uaddOverflow b) then throw .panic' "$basic_lean" || {
    echo "error: mutation (b): sed did not change Zig.add" >&2
    exit 1
  }

  # `Proofs/Basic/Gen.lean` imports `ZigLean`, and `ZigLean.lean` imports `ZigLean.Lemmas`
  # unconditionally, so building `difftest` always builds `ZigLean.Lemmas` too. Its
  # `add_unsigned` states `add`'s result in terms of `.overflow`, which no longer holds once
  # `add` throws `.panic` instead — a genuine, expected proof failure. Drop just that theorem
  # for this mutation's window.
  awk '/@\[simp\] theorem add_unsigned/,/simp \[add, BitVec\.uaddOverflow\]/{next} {print}' \
    "$lemmas_lean" >"$lemmas_lean.tmp" && mv "$lemmas_lean.tmp" "$lemmas_lean"
  grep -q 'theorem add_unsigned' "$lemmas_lean" && {
    echo "error: mutation (b): failed to remove add_unsigned from $lemmas_lean" >&2
    exit 1
  }

  run_and_report "mutation (b)" basic
  [ "$detected" -eq 1 ] || all_detected=0
  # Restore ZigLean before mutation (c) so the mutations don't compound.
  cp "$basic_backup" "$basic_lean"
  cp "$lemmas_backup" "$lemmas_lean"
fi

echo "== mutation (c): findOr orelse xs.len -> orelse 0 (Zig source) ==" >&2
if ! want_mutation c; then
  echo "mutation (c): skipped (not in this shard)"
elif ! has_example options; then
  echo "mutation (c): skipped (AIR2LEAN_EXAMPLES excludes options)"
else
  translate_mutated options 's/orelse xs\.len/orelse 0/' 'orelse 0'
  run_and_report "mutation (c)" options
  [ "$detected" -eq 1 ] || all_detected=0
fi

echo "== mutation (d): roundQuot ties away from zero (Lean runtime) ==" >&2
if ! want_mutation d; then
  echo "mutation (d): skipped (not in this shard)"
elif ! has_example floatops; then
  echo "mutation (d): skipped (AIR2LEAN_EXAMPLES excludes floatops)"
else
  sed -i.bak 's/else if m % 2 = 0 then (m : Int) else (m : Int) + 1/else (m : Int) + 1/' "$round_lean"
  rm -f "$round_lean.bak"
  ! grep -q 'if m % 2 = 0 then' "$round_lean" || {
    echo "error: mutation (d): sed did not change roundQuot" >&2
    exit 1
  }

  run_and_report "mutation (d)" floatops
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$round_backup" "$round_lean"
fi

echo "== mutation (e): Light.ofInt? accepts the unnamed value 3 (emitter output) ==" >&2
if ! want_mutation e; then
  echo "mutation (e): skipped (not in this shard)"
elif ! has_example variants; then
  echo "mutation (e): skipped (AIR2LEAN_EXAMPLES excludes variants)"
else
  sed -i.bak 's/else if v = 2 then Option.some .green else Option.none/else if v = 2 then Option.some .green else if v = 3 then Option.some .red else Option.none/' "$variants_gen"
  rm -f "$variants_gen.bak"
  grep -q 'if v = 3 then Option.some .red' "$variants_gen" || {
    echo "error: mutation (e): sed did not change Light.ofInt?" >&2
    exit 1
  }

  run_and_report "mutation (e)" variants
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$variants_backup" "$variants_gen"
fi

echo "== mutation (f): Zig.store writes one byte too few (Lean runtime) ==" >&2
if ! want_mutation f; then
  echo "mutation (f): skipped (not in this shard)"
elif ! has_example pointers; then
  echo "mutation (f): skipped (AIR2LEAN_EXAMPLES excludes pointers)"
else
  sed -i.bak 's/storeBytes p align (Enc.encode v)$/storeBytes p align (Enc.encode v).pop/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q 'storeBytes p align (Enc.encode v).pop' "$mem_lean" || {
    echo "error: mutation (f): sed did not change Zig.store" >&2
    exit 1
  }

  run_and_report "mutation (f)" pointers
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (g): Zig.memmove writes one byte too few (Lean runtime) ==" >&2
if ! want_mutation g; then
  echo "mutation (g): skipped (not in this shard)"
elif ! has_example slices; then
  echo "mutation (g): skipped (AIR2LEAN_EXAMPLES excludes slices)"
else
  sed -i.bak 's/^  storeBytes dst dstAlign bs$/  storeBytes dst dstAlign bs.pop/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q 'storeBytes dst dstAlign bs.pop' "$mem_lean" || {
    echo "error: mutation (g): sed did not change Zig.memmove" >&2
    exit 1
  }

  run_and_report "mutation (g)" slices
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (h): Zig.rawAlloc never fails at Mem.failAt (Lean runtime) ==" >&2
if ! want_mutation h; then
  echo "mutation (h): skipped (not in this shard)"
elif ! has_example lists; then
  echo "mutation (h): skipped (AIR2LEAN_EXAMPLES excludes lists)"
else
  sed -i.bak 's/  if m.failAt = some m.allocs ∨ maxAllocBytes < n then return none/  if maxAllocBytes < n then return none/' "$alloc_lean"
  rm -f "$alloc_lean.bak"
  grep -q '  if maxAllocBytes < n then return none' "$alloc_lean" || {
    echo "error: mutation (h): sed did not change Zig.rawAlloc" >&2
    exit 1
  }

  run_and_report "mutation (h)" lists
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$alloc_backup" "$alloc_lean"
fi

echo "== mutation (i): air2lean_asm_bswap32 returns x unchanged (diff-test archive) ==" >&2
if ! want_mutation i; then
  echo "mutation (i): skipped (not in this shard)"
elif ! has_example asm; then
  echo "mutation (i): skipped (AIR2LEAN_EXAMPLES excludes asm)"
else
  sed -i.bak 's/return @byteSwap(x);/return x;/' "$asm_zig"
  rm -f "$asm_zig.bak"
  grep -q 'return x;' "$asm_zig" || {
    echo "error: mutation (i): sed did not change air2lean_asm_bswap32" >&2
    exit 1
  }

  run_and_report "mutation (i)" asm
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$asm_backup" "$asm_zig"
fi

echo "== mutation (j): Vec.reduce drops the last lane (Lean runtime) ==" >&2
if ! want_mutation j; then
  echo "mutation (j): skipped (not in this shard)"
elif ! has_example vectors; then
  echo "mutation (j): skipped (AIR2LEAN_EXAMPLES excludes vectors)"
else
  sed -i.bak 's/(v\.lanes\.toArray\.extract 1 n)\.foldl f v\.lanes\.toArray\[0\]!/(v.lanes.toArray.extract 1 (n - 1)).foldl f v.lanes.toArray[0]!/' "$vec_lean"
  rm -f "$vec_lean.bak"
  grep -q 'extract 1 (n - 1)).foldl f' "$vec_lean" || {
    echo "error: mutation (j): sed did not change Vec.reduce" >&2
    exit 1
  }

  run_and_report "mutation (j)" vectors
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$vec_backup" "$vec_lean"
fi

echo "== mutation (k): two atomic accesses race (Lean runtime) ==" >&2
if ! want_mutation k; then
  echo "mutation (k): skipped (not in this shard)"
elif ! has_example threads; then
  echo "mutation (k): skipped (AIR2LEAN_EXAMPLES excludes threads)"
else
  sed -i.bak 's/^  if (a\.isWrite || b\.isWrite) \&\& !(a\.isAtomic \&\& b\.isAtomic) then some \.illegal else none$/  if a.isWrite || b.isWrite then some .illegal else none/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q '^  if a.isWrite || b.isWrite then some .illegal else none$' "$mem_lean" || {
    echo "error: mutation (k): sed did not change racePair" >&2
    exit 1
  }

  run_and_report "mutation (k)" threads
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (l): recordAccess never checks for a race (Lean runtime) ==" >&2
if ! want_mutation l; then
  echo "mutation (l): skipped (not in this shard)"
elif ! has_example threads; then
  echo "mutation (l): skipped (AIR2LEAN_EXAMPLES excludes threads)"
else
  sed -i.bak 's/match raceAt m.footprint clock block off len kind with/match (none : Option Error) with/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q 'match (none : Option Error) with' "$mem_lean" || {
    echo "error: mutation (l): sed did not change recordAccess" >&2
    exit 1
  }

  run_and_report "mutation (l)" threads
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (m): Flags.ofBits swaps ready and err (emitter output) ==" >&2
if ! want_mutation m; then
  echo "mutation (m): skipped (not in this shard)"
elif ! has_example layout; then
  echo "mutation (m): skipped (AIR2LEAN_EXAMPLES excludes layout)"
else
  sed -i.bak 's/ready := Zig.Packed.get b 0, err := Zig.Packed.get b 1,/ready := Zig.Packed.get b 1, err := Zig.Packed.get b 0,/' "$layout_gen"
  rm -f "$layout_gen.bak"
  grep -q 'ready := Zig.Packed.get b 1, err := Zig.Packed.get b 0,' "$layout_gen" || {
    echo "error: mutation (m): sed did not change Flags.ofBits" >&2
    exit 1
  }

  run_and_report "mutation (m)" layout
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$layout_backup" "$layout_gen"
fi

echo "== mutation (n): Mem.accessW does not check for a const global (Lean runtime) ==" >&2
if ! want_mutation n; then
  echo "mutation (n): skipped (not in this shard)"
elif ! has_example layout; then
  echo "mutation (n): skipped (AIR2LEAN_EXAMPLES excludes layout)"
else
  sed -i.bak 's/if r\.2\.1\.kind = \.constGlobal then throw \.illegal else pure r/if false then throw .illegal else pure r/' "$mem_lean"
  rm -f "$mem_lean.bak"
  grep -q 'if false then throw .illegal else pure r' "$mem_lean" || {
    echo "error: mutation (n): sed did not change Mem.accessW" >&2
    exit 1
  }

  run_and_report "mutation (n)" layout
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$mem_backup" "$mem_lean"
fi

echo "== mutation (o): byteBits rejects every Byte.part (Lean runtime) ==" >&2
if ! want_mutation o; then
  echo "mutation (o): skipped (not in this shard)"
elif ! has_example layout; then
  echo "mutation (o): skipped (AIR2LEAN_EXAMPLES excludes layout)"
else
  sed -i.bak 's/^    if n - 8 \* i ≤ m ∧ (trunc ∨ x\.toNat < 2 ^ (n - 8 \* i)) then some x else none$/    none/' "$enc_lean"
  rm -f "$enc_lean.bak"
  grep -q '^    none$' "$enc_lean" || {
    echo "error: mutation (o): sed did not change byteBits" >&2
    exit 1
  }

  run_and_report "mutation (o)" layout
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$enc_backup" "$enc_lean"
fi

echo "== mutation (p): byteBits accepts a set bit above the integer (Lean runtime) ==" >&2
if ! want_mutation p; then
  echo "mutation (p): skipped (not in this shard)"
elif ! has_example layout; then
  echo "mutation (p): skipped (AIR2LEAN_EXAMPLES excludes layout)"
else
  sed -i.bak 's/| \.int x => if !trunc ∧ n - 8 \* i < 8 ∧ 2 ^ (n - 8 \* i) ≤ x\.toNat then none else some x/| .int x => some x/' "$enc_lean"
  rm -f "$enc_lean.bak"
  grep -q '| .int x => some x' "$enc_lean" || {
    echo "error: mutation (p): sed did not change byteBits" >&2
    exit 1
  }

  run_and_report "mutation (p)" layout
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$enc_backup" "$enc_lean"
fi

echo "== mutation (q): Zig.mod throws .panic for a negative divisor (Lean runtime) ==" >&2
if ! want_mutation q; then
  echo "mutation (q): skipped (not in this shard)"
elif ! has_example vectors; then
  echo "mutation (q): skipped (AIR2LEAN_EXAMPLES excludes vectors)"
else
  sed -i.bak 's/^  else if s then (if remOverflows a b then throw \.illegal else pure (a\.smod b))$/  else if s then (if b.toInt < 0 then throw .panic else pure (a.smod b))/' "$basic_lean"
  rm -f "$basic_lean.bak"
  grep -q 'if b.toInt < 0 then throw .panic else pure (a.smod b)' "$basic_lean" || {
    echo "error: mutation (q): sed did not change Zig.mod" >&2
    exit 1
  }

  run_and_report "mutation (q)" vectors
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$basic_backup" "$basic_lean"
fi

echo "== mutation (r): a [3:0]u8 constant without its sentinel item (emitter output) ==" >&2
if ! want_mutation r; then
  echo "mutation (r): skipped (not in this shard)"
elif ! has_example slices; then
  echo "mutation (r): skipped (AIR2LEAN_EXAMPLES excludes slices)"
else
  sed -i.bak 's/(#v\[(120 : BitVec 8), (121 : BitVec 8), (122 : BitVec 8), (0 : BitVec 8)\] : Vector (BitVec 8) 4)/(#v[(120 : BitVec 8), (121 : BitVec 8), (122 : BitVec 8)] : Vector (BitVec 8) 3)/' "$slices_gen"
  rm -f "$slices_gen.bak"
  grep -q '(122 : BitVec 8)\] : Vector (BitVec 8) 3)' "$slices_gen" || {
    echo "error: mutation (r): sed did not change the constant" >&2
    exit 1
  }

  run_and_report "mutation (r)" slices
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$slices_backup" "$slices_gen"
fi

echo "== mutation (s): Allocator.freeSentinel frees len items, not len + 1 (Lean runtime) ==" >&2
if ! want_mutation s; then
  echo "mutation (s): skipped (not in this shard)"
elif ! has_example lists; then
  echo "mutation (s): skipped (AIR2LEAN_EXAMPLES excludes lists)"
else
  sed -i.bak 's/^  if size = 0 then pure () else rawFree s\.ptr (size \* (s\.len\.toNat + 1))$/  if size = 0 then pure () else rawFree s.ptr (size * s.len.toNat)/' "$alloc_lean"
  rm -f "$alloc_lean.bak"
  grep -q 'rawFree s.ptr (size \* s.len.toNat)$' "$alloc_lean" || {
    echo "error: mutation (s): sed did not change Allocator.freeSentinel" >&2
    exit 1
  }

  run_and_report "mutation (s)" lists
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$alloc_backup" "$alloc_lean"
fi

echo "== mutation (t): every Mode value is valid in a packed struct (emitter output) ==" >&2
if ! want_mutation t; then
  echo "mutation (t): skipped (not in this shard)"
elif ! has_example layout; then
  echo "mutation (t): skipped (AIR2LEAN_EXAMPLES excludes layout)"
else
  sed -i.bak 's/^  valid b := (Mode\.ofInt? (Zig\.val false b))\.isSome$/  valid _ := true/' "$layout_gen"
  rm -f "$layout_gen.bak"
  grep -q '^  valid _ := true$' "$layout_gen" || {
    echo "error: mutation (t): sed did not change the Mode instance" >&2
    exit 1
  }

  run_and_report "mutation (t)" layout
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$layout_backup" "$layout_gen"
fi

echo "== mutation (u): a bool vector in memory has its lanes in reverse bit order (Lean runtime) ==" >&2
if ! want_mutation u; then
  echo "mutation (u): skipped (not in this shard)"
elif ! has_example layout; then
  echo "mutation (u): skipped (AIR2LEAN_EXAMPLES excludes layout)"
else
  sed -i.bak 's/then acc ||| (1#n <<< i) else acc) 0#n))$/then acc ||| (1#n <<< (n - 1 - i)) else acc) 0#n))/' "$vec_lean"
  rm -f "$vec_lean.bak"
  grep -q '(1#n <<< (n - 1 - i))' "$vec_lean" || {
    echo "error: mutation (u): sed did not change the Vec Bool encoding" >&2
    exit 1
  }

  run_and_report "mutation (u)" layout
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$vec_backup" "$vec_lean"
fi

echo "== mutation (v): cmpxchgAs compares with the new value (Lean runtime) ==" >&2
if ! want_mutation v; then
  echo "mutation (v): skipped (not in this shard)"
elif ! has_example threads; then
  echo "mutation (v): skipped (AIR2LEAN_EXAMPLES excludes threads)"
else
  sed -i.bak 's/^  match ← cmpxchgAt c succ fail align p (Packed.toBits expected) (Packed.toBits new) with$/  match ← cmpxchgAt c succ fail align p (Packed.toBits new) (Packed.toBits new) with/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q 'cmpxchgAt c succ fail align p (Packed.toBits new) (Packed.toBits new) with' "$thread_lean" || {
    echo "error: mutation (v): sed did not change cmpxchgAs" >&2
    exit 1
  }

  run_and_report "mutation (v)" threads
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (w): an acquire read adopts no clock (Lean runtime, proof build) ==" >&2
if ! want_mutation w; then
  echo "mutation (w): skipped (not in this shard)"
elif ! has_example atomics; then
  echo "mutation (w): skipped (AIR2LEAN_EXAMPLES excludes atomics)"
else
  sed -i.bak 's/^  { m with clocks := m.clocks.set! m.current (VClock.merge (m.clocks\[m.current\]!) c) }$/  { m with clocks := m.clocks.set! m.current (m.clocks[m.current]!) }/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q '^  { m with clocks := m.clocks.set! m.current (m.clocks\[m.current\]!) }$' "$thread_lean" || {
    echo "error: mutation (w): sed did not change acquireClock" >&2
    exit 1
  }

  proof_report "mutation (w)" Proofs.Atomics.Proofs
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (x): a write goes only at the end (Lean runtime, proof build) ==" >&2
if ! want_mutation x; then
  echo "mutation (x): skipped (not in this shard)"
elif ! has_example atomics; then
  echo "mutation (x): skipped (AIR2LEAN_EXAMPLES excludes atomics)"
else
  sed -i.bak 's/^  ((Array.range (n - f)).map fun k => n - k).filter fun p => p == n || !l.hasRmwAfter (p - 1)$/  ((Array.range (n - f)).map fun k => n - k).filter fun p => p == n/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q 'filter fun p => p == n$' "$thread_lean" || {
    echo "error: mutation (x): sed did not change writeSlots" >&2
    exit 1
  }

  proof_report "mutation (x)" Proofs.Atomics.Proofs
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (y): a futex wait never blocks (Lean runtime, proof build) ==" >&2
if ! want_mutation y; then
  echo "mutation (y): skipped (not in this shard)"
elif ! has_example sync; then
  echo "mutation (y): skipped (AIR2LEAN_EXAMPLES excludes sync)"
else
  sed -i.bak 's/^    if v = e then$/    if false then/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q '^    if false then$' "$thread_lean" || {
    echo "error: mutation (y): sed did not change the futex wait" >&2
    exit 1
  }

  proof_report "mutation (y)" Proofs.Sync.Proofs
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (z): no deadlock check (Lean runtime, proof build) ==" >&2
if ! want_mutation z; then
  echo "mutation (z): skipped (not in this shard)"
elif ! has_example sync; then
  echo "mutation (z): skipped (AIR2LEAN_EXAMPLES excludes sync)"
else
  sed -i.bak 's/^      (if s.anyRunning then some (.error .deadlock) else none, s.trace)$/      (none, s.trace)/' "$sched_lean"
  rm -f "$sched_lean.bak"
  grep -q '^      (none, s.trace)$' "$sched_lean" || {
    echo "error: mutation (z): sed did not change the deadlock check" >&2
    exit 1
  }

  proof_report "mutation (z)" Proofs.Sync.Proofs
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$sched_backup" "$sched_lean"
fi

echo "== mutation (aa): an RMW can read a message with an RMW after it (Lean runtime, proof build) ==" >&2
if ! want_mutation aa; then
  echo "mutation (aa): skipped (not in this shard)"
elif ! has_example threads; then
  echo "mutation (aa): skipped (AIR2LEAN_EXAMPLES excludes threads)"
else
  sed -i.bak 's/^  ((Array.range (n - f)).map fun k => n - 1 - k).filter fun p => !rmw || !l.hasRmwAfter p$/  ((Array.range (n - f)).map fun k => n - 1 - k).filter fun p => !rmw || true/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q 'filter fun p => !rmw || true$' "$thread_lean" || {
    echo "error: mutation (aa): sed did not change readOpts" >&2
    exit 1
  }

  proof_report "mutation (aa)" Proofs.Threads.Counter
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (ab): a spawned thread gets an empty clock (Lean runtime, proof build) ==" >&2
if ! want_mutation ab; then
  echo "mutation (ab): skipped (not in this shard)"
elif ! has_example threads; then
  echo "mutation (ab): skipped (AIR2LEAN_EXAMPLES excludes threads)"
else
  sed -i.bak 's/^    clocks := (m.clocks.set! parent parentClock).push parentClock$/    clocks := (m.clocks.set! parent parentClock).push #[]/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q '^    clocks := (m.clocks.set! parent parentClock).push #\[\]$' "$thread_lean" || {
    echo "error: mutation (ab): sed did not change Thread.fork" >&2
    exit 1
  }

  proof_report "mutation (ab)" Proofs.Threads.Counter
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (ac): a futex wake wakes no thread (Lean runtime, proof build) ==" >&2
if ! want_mutation ac; then
  echo "mutation (ac): skipped (not in this shard)"
elif ! has_example sync; then
  echo "mutation (ac): skipped (AIR2LEAN_EXAMPLES excludes sync)"
else
  sed -i.bak 's/^  let woke := (m.waiters.filter (·.2 == p)).extract 0 n |>.map (·.1)$/  let woke : Array ThreadId := #[]/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q '^  let woke : Array ThreadId := #\[\]$' "$thread_lean" || {
    echo "error: mutation (ac): sed did not change futexWake" >&2
    exit 1
  }

  proof_report "mutation (ac)" Proofs.Sync.Mutex
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

echo "== mutation (ad): a cmpxchg succeeds on a stale message (Lean runtime, proof build) ==" >&2
if ! want_mutation ad; then
  echo "mutation (ad): skipped (not in this shard)"
elif ! has_example atomics; then
  echo "mutation (ad): skipped (AIR2LEAN_EXAMPLES excludes atomics)"
else
  sed -i.bak 's/^    !(l.hasRmwAfter pos && match/    !(false \&\& match/' "$thread_lean"
  rm -f "$thread_lean.bak"
  grep -q '^    !(false && match' "$thread_lean" || {
    echo "error: mutation (ad): sed did not change casPrep" >&2
    exit 1
  }

  proof_report "mutation (ad)" Proofs.Atomics.Stack
  [ "$detected" -eq 1 ] || all_detected=0
  cp "$thread_backup" "$thread_lean"
fi

[ "$all_detected" -eq 1 ]
