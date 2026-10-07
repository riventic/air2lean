# Your first air2lean proof

This guide is for a Zig developer trying Lean for the first time. Start by checking a small existing proof, then change a theorem, and finally translate your own Zig file. Run every command from the repository root.

## Check a proof before building Zig

Install [elan](https://github.com/leanprover/elan#installation), which provides `lake` and selects the Lean version pinned in `lean-toolchain`. Make sure its binaries are on your `PATH` (you may need a new terminal after installation).

```sh
lake build Proofs.Basic.Proofs
lake env lean tutorials/first-proof/Main.lean
```

The first command builds only the Basic proof module and its dependencies. The first run may download the pinned Lean toolchain. The second command checks the tutorial; success means exit status zero with no Lean errors. You do not need Zig for this step: the generated definitions are already committed.

`scripts/doctor.sh --require proofs` checks these prerequisites (it also reports optional Zig, Docker, disk and memory state and prints a fix for each problem; `--json` gives a machine-readable report). To see the whole first proof succeed in a fresh container from checksum-pinned downloads, run `scripts/clean-env.sh`. See [distribution, doctor and editor workflow](distribution.md), which also covers editor setup and `lake env lean --json` diagnostics.

If `lake` is missing, finish the elan installation and open a new terminal. If Lean reports an unknown `Proofs.Basic.Proofs` module, run the build command above from the repository root before checking the tutorial. An editor can also report missing imports until those dependencies have been built.

## Follow the source, model, and theorem

The Zig function in [`examples/basic/basic.zig`](../examples/basic/basic.zig) is:

```zig
pub fn tardiness(end: u32, due: u32) u32 {
    return if (end > due) end - due else 0;
}
```

There are three separate things to read:

| File | What it means |
|---|---|
| [`examples/basic/basic.zig`](../examples/basic/basic.zig) | The program you want to reason about. |
| [`Proofs/Basic/Gen.lean`](../Proofs/Basic/Gen.lean) | Generated definitions representing the analyzed Zig code. Treat this as translator output. |
| [`Proofs/Basic/Proofs.lean`](../Proofs/Basic/Proofs.lean) | Human-written specifications and proofs about those definitions. |

The generated `Basic.tardiness` accepts two `BitVec 32` values (32-bit words) and returns `Zig.Result (BitVec 32)`. `pure value` represents a successful return; `throw error` represents a modeled safety panic; `none` represents no result. A Zig error-union value is distinct from a safety panic. See [generated code](generated-code.md) for the full representation.

The existing `tardiness_spec` theorem says, for every pair of 32-bit inputs:

```lean
tardiness a b = pure (if b.toNat < a.toNat then a - b else 0)
```

`.toNat` reads an unsigned word as a natural number. The theorem characterizes the returned value and shows that this function never panics or returns no result. The checked subtraction is safe because it runs only when `end > due`.

## Make a small proof your own

Open [`tutorials/first-proof/Main.lean`](../tutorials/first-proof/Main.lean). It imports the built Basic proofs and proves a useful consequence:

```lean
theorem on_time_zero (endTime due : BitVec 32)
    (onTime : endTime.toNat ≤ due.toNat) :
    tardiness endTime due = pure 0 := by
  rw [tardiness_spec]
  simp [Nat.not_lt.mpr onTime]
```

Read this as: for any finish time and due time, assuming the job finishes by its due time, its tardiness returns zero successfully.

`rw [tardiness_spec]` replaces the generated function call with its proved specification. `Nat.not_lt.mpr onTime` says the due time cannot be strictly smaller than the finish time. `simp` uses that fact to select the zero branch. The Lean kernel checks that these steps establish the stated theorem.

**Exercise:** immediately before `end FirstProof`, add a theorem for a job finishing exactly at its due time. Try proving it by applying `on_time_zero`; equality of the natural-number values implies `≤`.

```lean
theorem exactly_on_time (endTime due : BitVec 32)
    (sameTime : endTime.toNat = due.toNat) :
    tardiness endTime due = pure 0 := by
  exact on_time_zero endTime due (Nat.le_of_eq sameTime)
```

Check your edit:

```sh
lake env lean tutorials/first-proof/Main.lean
```

As a useful failure check, temporarily change the conclusion to `pure 1` while leaving the proof unchanged. Lean should reject it. Restore `pure 0` and check again. You have changed a property and seen the checker distinguish a true claim from a false one, without rebuilding a compiler.

## What you have established

This proof covers the generated Lean definition for all inputs satisfying its assumption, not just a set of test cases. Relating it to compiled Zig also trusts Zig's semantic analysis, the AIR export patch, air2lean's translator, and the handwritten runtime model. Differential tests compare the two implementations on sampled inputs; they support that correspondence but do not prove the translator correct.

The memory model uses little-endian, 64-bit pointers. Float and concurrency models have additional target and behavior assumptions. Read [what a proof covers](../README.md#what-a-proof-covers) and [std models](std-models.md) before relying on results for other programs. air2lean generates code, not automatic proofs of arbitrary properties.

## Set up translation

Translation additionally needs a stock Zig **0.16.0** on `PATH` to bootstrap the patched compiler. Install that exact supported version; the bootstrap host version must match the version being built. See [Zig compiler setup](../zig-patch/README.md) for platform and memory requirements, alternative supported versions, and the optional LLVM build.

Check the prerequisites and follow any reported setup hints:

```sh
scripts/doctor.sh
zig-patch/build.sh 0.16.0
scripts/doctor.sh
```

The patched compiler is installed in `zig-air-0.16.0/`. Its default build is locked to AIR export with no emitted binary; the doctor reports this lock state for every installed version. `scripts/clean-env.sh --translate` runs this setup and the translation below in a fresh container. Use a stock Zig compiler to build or run Zig programs. The translation command below builds the runtime library and translator before exporting AIR.

## Translate your own file

Create a small exported function so Zig will analyze it:

```sh
mkdir -p work/first Proofs/MyProgram
cat > work/first/demo.zig <<'ZIG'
export fn tardiness(end: u32, due: u32) u32 {
    return if (end > due) end - due else 0;
}
ZIG
scripts/translate.sh work/first/demo.zig -o Proofs/MyProgram/Gen.lean --namespace MyProgram
```

That single command builds the runtime and translator, exports fresh AIR, translates it, and checks the generated Lean before publishing the output. It uses the reference target `x86_64-linux` with baseline CPU features and `ReleaseSafe`. It requires the toolchain and patched compiler from the setup step; it does not install them or write a property proof. Choose an output path you intend to replace: successful translation replaces that file, while a failed run leaves the existing output intact.

The default AIR filter and Lean name prefix come from the input basename (`demo.` here). Zig analyzes referenced functions; `export fn` ensures this example is included. For a `pub fn`, reference it from a `comptime { _ = &tardiness; }` block. A file requiring translated std functions may need additional filter prefixes; see [std models](std-models.md).

To import the generated code into a separate proof, first build its module. This example uses `Proofs/MyProgram/Gen.lean` because `Proofs` is already a library in this repository's Lake package:

```sh
lake build Proofs.MyProgram.Gen
cat > work/first/Proof.lean <<'LEAN'
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
```

Unlike the first exercise, this proof unfolds the newly generated function directly. Keep it separate from `Gen.lean`, which the translator replaces. Checking a generated file with Lean does not by itself create an importable compiled module: the `lake build Proofs.MyProgram.Gen` step is needed before the separate proof imports it.

Use `scripts/translate.sh --help` for explicit compiler paths, Zig versions, namespace prefixes, AIR filters and float semantics. For example, an already built compiler outside the default directory can be selected with `--zig-air /absolute/path/to/zig`. `--zig-version` must match that compiler. Zig 0.14.1 translation is Linux-only.

If translation reports no AIR files, check that the function is exported or referenced and that the filter matches its name. If it reports unsupported AIR, consult the [subset](../PLAN.md#subset) and [std models](std-models.md); a rejected translation requires a supported construct or model before you can prove anything about it. If the separate proof cannot find its import, confirm the output path and build the corresponding module.

## Go further

- [Generated code and naming](generated-code.md): return values, memory, loops, and generated names.
- [Memory and concurrency proofs](proofs.md): invariants, separation logic, and proofs over schedules.
- [Supported subset](../PLAN.md#subset) and [std models](std-models.md): supported constructs and modeled library calls.
- [Float semantics](floats.md): supported targets and version-specific behavior.
- [Contributor checks](../README.md#before-a-pr): the full translation, differential-test, proof, regression, and mutation workflow. These are broader than the first proof above.
