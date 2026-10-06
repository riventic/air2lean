# C04 bounded deadline interpreter handoff

This branch adds an opt-in monotonic-awake environment and resumable timed-wait
interpreter. Ordinary CLI timed source calls remain unsupported. It does not claim
full std.Io backend, OS clock/futex, cancellation, fairness or eventual completion
correspondence. C05 cancellation and E03 broader environment work remain open.

ROOT qualified foundation v4 (Time/TimedSched, eleven kernel proofs and runtime
suite), then selected q3: all four actual retained MUSL Zig16 AIR exports produced
full compiler-emitted Lean, elaborated and passed generated interpreter checks.
Default strict diagnostics still rejected the source calls. The GNU native callback
mock was separate feasibility evidence; the Threaded OS smoke timed out after 300s.

The current v5 candidate replaces the kernel's newest-byte compare with one existing
source atomic read. Explicit readable-option indices update locIdx and seen; unavailable
indices fail without clamping. TimedCompare links the kernel action definitionally to
atomicLoadAt and reuses its existing successful-event theorem. Current-byte agreement
is conditional on the selected message's bytes, not a blanket equivalence to v4.
Generated-body checks exercise older/current messages and seen-floor rejection.
V5 needs ROOT's foundation and composed selected-pipeline gates before publication.

Fresh-agent order: read the composed source freeze and ROOT result receipt, inspect
full generated definitions and source/AIR dependency hashes, preserve default rejection,
and report only the gates actually passed. Resume backend/OS correspondence work as a
separate scope; do not infer it from the interpreter tests or a no-cancellation premise.
The four retained exports are observe, waitZero, waitDeadline and boundaryClient.
BoundaryClient's word is a constant global; the separate TimedClient allocation and
cleanup checks are not its generated source proof.
