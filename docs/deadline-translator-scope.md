# Selected timed emission: acyclic source candidate

Status: ROOT selected q3 passed the bounded acyclic generated interpreter pipeline.
All four retained AIR exports produced actual generated definitions, elaborated and ran
successfully. Ordinary timed source emission remains unsupported; source atomic
correspondence and OS conformance remain open. The separate foundation freeze is unchanged.

The retained source packet is schema 12, Zig 0.16.0, abi64-le-v1,
x86_64 Linux musl, little endian, stage2_llvm. It contains all four bodies:
probe.observe, probe.waitZero, probe.waitDeadline and probe.boundaryClient. Static
inspection finds no loops or indirect calls in these bodies. Observe uses allocation,
store, bitcast, field pointer and load; waits additionally construct the timeout union
and return an error union; boundaryClient calls two exported functions and propagates
the source error union. Its word is a constant global, not an allocated stack local.

## Concrete architectural obstruction

Air2Lean/Emit.lean uses FCtx.monad, callMName, callRName and callOf to select Result,
MemM or ConcM bodies. emitFunctionDef allocates and frees escaped stack blocks in that
selected effect, then runs the generated locals StateT. Merely recognizing a timed
symbol in threadFn? would emit a CM/ConcM call and would not retain a TimedSched
continuation. Registering it as an external model similarly preserves the existing
effect and cannot solve this mismatch.

The current finite Program has Monad but no general exception handler or CCPO/MonoBind
instances. The existing emitter writes throw for traps, invalid indirect dispatch and
invalid exits. Its loops use Zig.loop and recursive groups use partial_fixpoint. These
cannot be accepted in a timed flavor without new semantics and proofs. A broad monad
instance or string replacement of completed generated text would conceal these gaps.

Main.processRaw runs the ordinary check before program checks; therefore opting in only
at program validation or emission is too late. Check's local rejection, program callee
validation, memory/concurrency classification and emission must share the same explicit
validated selection. The ordinary CLI and source rejection must remain unchanged.

## Implemented candidate and remaining qualification

1. TimedEmit.translateSelected is an isolated checked entry point, with no default CLI change, restricted to this
   pinned profile and acyclic direct-call programs. Reject loops, recursive call groups,
   indirect calls, atomics and other concurrency primitives before emission. Reuse
   callGroups/calleesOf for graph checking and the existing type/name/layout machinery.
2. TimedCheck validates selected public API signatures and normalized layout trees.
   Io.Clock.now must return the actual named generated Timestamp; timeout tags and raw
   signed-i96 fields must use the actual generated constructors and projections. Generate
   conversion functions using allocated declaration/member names, not handwritten
   replacement types. Check names plus layout and signatures; names alone are insufficient.
3. TimedBody supplies a locals StateT over Program wrapper. Each ordinary scalar
   instruction runs unchanged shared emitSimple lowering in its existing MM effect,
   then callBody lifts the action and updated locals into a memory node. Escaped
   allocation/free use liftMem; selected and translated direct calls use callProgram.
   Named types, encodings, globals and opcode semantics remain shared with the normal
   emitter. Timed calls bind real observe/wait nodes. No exception-handler or fixed-point
   instance is added. Independent static review and ROOT q3 compiler/interpreter checks passed for this
   bounded candidate; the source correspondence gate below remains open.
4. ROOT must run the compiler-emitted output for all four retained AIR bodies. Retain
   the entire generated file, metadata and source/AIR hashes. Check paused continuation
   and resumption at the public error-union boundary, and default-mode negative cases.
5. Before qualifying std source calls, reconcile the kernel compare with source atomic
   locIdx/seen and read-choice semantics. The kernel's newest-byte tracked read does not
   supply this correspondence. Keep the no-source-writers client scope explicit.

The handwritten TimedCall/TimedClient candidates are interpreter composition examples.
They establish neither completion nor translation acceptance. The mock GNU native PASS
and musl AIR export are separate feasibility steps, not matched-profile qualification.

The ROOT-only Translate.lean driver reads the full retained AIR directory and writes the
entire candidate generated file using translateSelected. It neither substitutes the four
exported bodies by hand nor runs them. The output embeds the checked full profile and an
acyclic-unqualified marker. Qualification must bind the full file, actual AIR, selected
runtime closure and matching source/native profile separately.

ROOT's root-selected.sh recipe requires an extracted source root with an explicitly
attached existing Lake cache, the original retained four-function AIR directory, and
a fresh absolute output directory. It builds the candidate modules, runs Adapter/Client,
emits the entire Gen.lean, elaborates it, and runs Generated.lean against that module.
It also confirms ordinary diagnostics still reject the timed source calls and compares
source/import-closure and AIR hashes before and after. The successful marker is named
interpreter-candidate.passed: it is deliberately not a source/OS-conformance receipt.
No native toolchain/bootstrap work is performed by this recipe.

## Retained bounded result

ROOT selected q3 exited 0. Artifacts are retained at `/artifacts/c04-selected-q3`;
full Gen.lean, generated build/runtime logs, Adapter/Client/Guard logs and default
diagnostics were retained. Before/after source and AIR closure hashes were identical.
The source archive SHA-256 is
`e8783eecc8faefe792ca1d695e71de115ff7c7a30b64b8feaaa4db2c0ddbb636`;
its freeze manifest SHA-256 is
`d250826b4f719508500f93e4f8dd31d47f22824c3142d00e6089271f6587d438`.
The exact successful marker remains `acyclic-unqualified; source atomic coherence and OS conformance remain open`.
These checks qualify the bounded interpreter candidate, not the std backend or a
matched native/source model. The earlier Threaded OS smoke timed out; the GNU mock
was a separate feasibility step from the MUSL retained AIR.

## Runtime v5 source compare candidate

The working v5 candidate replaces the timed kernel compare with exactly one
`atomicLoadAt choice .relaxed 4 p`. `Inputs.readChoice` supplies a readable-option
index, consumed once per accepted wait attempt and retained across resumption; an
unavailable index fails rather than wrapping. `TimedCompare.kernelCompare_sourceAction`
is a definitional identity with that action. Its successful-event contract reuses
`Conc.Proto.atomicLoadAt_ok`: access/race checks, location reconciliation, selected
message and `seen` update all belong to the same source atomic read. Current-byte
agreement additionally requires explicit selected-message byte equality; it does not
assert equality with the previous runtime's memory state.

Generated-body fixtures exercise older/current message choices and the `seen` floor.
This v5 candidate is pending ROOT compiler/runtime qualification. It does not prove
that a particular std.Io vtable backend or OS futex implements this atomic model,
and does not establish cancellation, fairness, eventual completion or clock conformance.
The accepted v4 foundation and q3 generated receipts remain immutable historical results.
