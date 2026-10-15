# Gate-dependent clients omitted from the theorem audit

Audit base: `543faecd7`. Found while integrating declaration-based premise attribution.

`scripts/theorem_universe.py universe()` attributed
`tests/roadmap/strength-log/DispatchTemplates.lean` to
`tests/roadmap/dispatch-templates/check.sh` because it imports `TokenizerProof`.
The gate only compiled and audited its copied `TokenizerProof.lean`; it did not compile
the attributed client. The ordinary universe audit excluded every unit with a gate.
Consequently a false anonymous example with `sorry` in this strength log could escape
both audit routes. The existing `test_every_indexed_theorem_file_is_audited` exposed the
extra attributed unit and failed on this base.

The fix computes every transitive client of each registered gate root, compiles its local
dependency closure against the gate's generated modules, and uses the same collision-safe
audit bundling and source classification as the ordinary universe. The copied root must
retain its registered module identity. A compile error or `sorry` warning in an indirect
client fails the gate before audit acceptance; named declarations go through kernel replay.
Anonymous examples remain source-derived in the premise index because they do not survive
in the olean, but their compilation and warning check are covered by the responsible gate.

The regression includes a root, its client, and an indirect outer client; it asserts that
all three reach both compilation and audit, an unrelated module does not, and a compile
failure in the outer client prevents acceptance. The real universe regression checks that
registered roots and their computed client closures cover exactly every gated unit.

The ordinary compiler pool also honors `AIR2LEAN_JOBS` when no universe-specific override
is given. A guarded extraction on this base exceeded 11 GiB with four implicit compiler
workers despite the guard allocating one job. Respecting that existing budget fixes the
resource mismatch without increasing the cap.
