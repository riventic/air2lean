set -e
lake build air2lean air2lean-invgen 2>&1 | grep -E "error|Build completed" | head -20
python3 -B scripts/cas.py run -- python3 -B scripts/lean-deps.py --build tests/roadmap/loop-tactics/nested >/dev/null
work=$(mktemp -d); mkdir -p $work/olean/Nested
dir=tests/roadmap/loop-tactics/nested
export LEAN_PATH="$work/olean:$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R "$dir" -o "$work/olean/Nested/Gen.olean" "$dir/Nested/Gen.lean"
lake env .lake/build/bin/air2lean-invgen Nested.Gen Nested -o $dir/Nested/Inv.lean
unset LEAN_PATH
time python3 -B scripts/cas.py run -- bash $dir/check.sh
