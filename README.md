# air2lean

[![CI](https://github.com/riventic/air2lean/actions/workflows/ci.yml/badge.svg)](https://github.com/riventic/air2lean/actions/workflows/ci.yml)

Translate a pure subset of Zig into Lean 4, then prove properties of the code in Lean.

**Status:** v0 works for Zig 0.15.2 and 0.14.1. 18 functions in 4 examples (`basic`, `recursion`, `options`, `errors`) translate and match the compiled Zig on 5,400 differential tests, including the panic kind. The 8 `basic` functions have machine-checked proofs, including two loops (`sum`, `totalWeightedTardiness`). See [PLAN.md](PLAN.md).

## How it works

The Zig compiler does semantic analysis (`Sema`) and produces **AIR** (Analyzed Intermediate Representation). In AIR, `comptime` is already evaluated, generics are monomorphized, every type is known, and each safety check is explicit. A small compiler patch writes AIR as JSON. air2lean reads that JSON and writes one Lean definition per function.

```
foo.zig ──patched zig──▶ *.json ──air2lean──▶ Gen.lean ──lean──▶ proofs checked
                                                  ▲
               compiled Zig ◀── differential tests ┘
```

| Part | Where |
|---|---|
| Compiler patch (AIR → JSON) | [`zig-patch/`](zig-patch/README.md), format in [`docs/air-json.md`](docs/air-json.md) |
| Translator | `Air2Lean/` (parser, per-version normalizer, subset checker, emitter) |
| Runtime semantics + lemmas | `ZigLean/` |
| Generated code, proofs | `Proofs/Basic/` ([naming rules](docs/generated-code.md)) |
| Differential tests | `tests/diff/`, `scripts/diff.sh` |

## Example

```zig
pub fn tardiness(end: u32, due: u32) u32 {
    return if (end > due) end - due else 0;
}
```

The generated Lean (`Proofs/Basic/Gen.lean`) has the type `BitVec 32 → BitVec 32 → Zig.Result (BitVec 32)`, where `Zig.Result` is `ExceptT Zig.Error Option`: `throw` is a safety panic, `none` is non-termination. A proof (`Proofs/Basic/Proofs.lean`):

```lean
theorem tardiness_spec (a b : BitVec 32) :
    tardiness a b = pure (if b.toNat < a.toNat then a - b else 0)
```

`end - due` is a checked subtraction in Zig. The proof shows it never panics.

## Quick start

Needs: Zig 0.15.2 on `PATH` (to build the patched compiler), [elan](https://github.com/leanprover/elan).

```sh
zig-patch/build.sh 0.15.2          # patched compiler → ./zig-air-0.15.2/ (a few minutes)
lake build                         # runtime library + translator
scripts/check.sh                   # dump AIR, check goldens, translate, build, differential test
lake build Proofs                  # check the proofs
```

Translate your own file:

```sh
ZIG_AIR_JSON_DIR=out ZIG_AIR_JSON_FILTER=myfile. zig-air-0.15.2/bin/zig \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing myfile.zig
lake exe air2lean out -o MyGen.lean --namespace My --prefix myfile.
```

The Zig compiler only analyzes functions that something references. Use `export fn`, or reference each function in a `comptime { _ = &f; }` block.

### Before a PR

```sh
scripts/check.sh       # goldens, translate, build, differential test
lake build Proofs      # check the proofs
scripts/no-sorry.sh    # no sorry/admit/native_decide
scripts/mutate.sh      # a changed function must fail a test
```

## Scope

| In (v0) | Out (v0) |
|---|---|
| integers of any width, `bool` | floats |
| checked, wrapping (`+%`), saturating (`+\|`) arithmetic | mutable pointers, pointer aliasing |
| `if`, `switch`, `while`, `for` | allocators, heap memory |
| local `var` whose address does not escape | `@ptrCast`, `packed` layout |
| read-only slices `[]const T` | inline asm, threads, atomics |
| structs passed by value | optionals (planned) |
| calls, recursion, mutual recursion, error unions (`E!T`) | |

Overflow, out-of-bounds access and `unreachable` become `throw`, not undefined behaviour. A proof that a function never throws in this model also shows that its `ReleaseFast` build has no illegal behaviour on those inputs. A Zig error (`error.Name`) is a return value, not a panic — it never goes through `Zig.Error`.

## What a proof covers

The trusted base is: Zig `Sema`, the AIR export patch, the translator, and the Lean kernel. The proof is about the generated Lean code. The differential tests check the translator against the compiler: `scripts/diff.sh` runs the compiled Zig and the generated Lean on the same inputs, including edge values, and compares results and panics.

## Zig versions

Supported: Zig **0.15.2**, and **0.14.1** (Linux only; no error unions yet). The design supports every Zig release: version-specific code is limited to the compiler patch and the normalizer table. See [PLAN.md § Zig version support](PLAN.md#zig-version-support).

## License

Apache-2.0. See [LICENSE](LICENSE).
