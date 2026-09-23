# air2lean

Translate a pure subset of Zig into Lean 4, then prove properties of the code in Lean.

**Status:** planning. No code yet. See [PLAN.md](PLAN.md).

## Idea

The Zig compiler does semantic analysis (`Sema`) and produces **AIR** (Analyzed Intermediate Representation). In AIR, `comptime` is already evaluated, generics are monomorphized, and every type is known. air2lean reads AIR for selected functions and writes one Lean definition per function. You then state and prove theorems about those definitions.

```
foo.zig ──zig (patched)──▶ foo.air.json ──air2lean──▶ Foo.lean ──lean──▶ proofs checked
```

## Example (target)

```zig
export fn cost(late_min: u32, weight: u8) u32 {
    return late_min * weight;
}
```

```lean
-- generated
def cost (late_min : U32) (weight : U8) : Result U32 := do
  let w ← U8.toU32 weight
  U32.checkedMul late_min w      -- overflow ⇒ Result.fail .overflow

-- written by you
theorem cost_no_overflow (l : U32) (w : U8) (h : l.val < 2^24) :
    ∃ r, cost l w = .ok r ∧ r.val = l.val * w.val := by
  ...
```

## Scope

| In (v0) | Out (v0) |
|---|---|
| integers of any width, `bool` | floats |
| checked, wrapping (`+%`), saturating (`+\|`) arithmetic | mutable pointers, pointer aliasing |
| `if`, `switch`, `while`, `for` | allocators, heap memory |
| local `var` whose address does not escape | `@ptrCast`, `@bitCast` on pointers, `packed` layout |
| read-only slices `[]const T` | inline asm, threads, atomics |
| structs passed by value | SIMD vectors |
| calls to other translated functions, recursion | `async`, error-return traces |

Overflow, out-of-bounds access, and `unreachable` become `Result.fail`, not undefined behaviour. A proof that a function never fails in this model also shows that its `ReleaseFast` build has no illegal behaviour on those inputs.

## What a proof covers

The trusted base is: Zig `Sema` + the AIR export patch + the translator + the Lean kernel. The proof is about the generated Lean code. Differential tests (run the Zig build and the Lean definition on the same random inputs, then compare) check the translator against the compiler.

## License

TBD.
