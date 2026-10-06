# Bounded byte-remap gate

`source.exercise` uses the existing recognized three-runtime-argument
`Allocator.remap(allocator, nonsentinel []u8, new_len)` boundary. It allocates a
one-byte caller frame before a four-byte buffer, initializes `[3,5,7,11]`, and
requests eight bytes. Only after success does it initialize the new suffix to
13. It checks the exact prefix and frame, then releases the actual live slice.
No undefined suffix byte is read before initialization.

`native.zig` supplies an explicit byte-only allocator with three fixed backing
slots of capacity 16 and logical live lengths. Slots are never reused. In-place
growth is allowed only for the latest allocated slot; moved success copies the
exact minimum prefix and invalidates the old logical allocation. Failure leaves
the original logical length, bytes and lifetime intact. Whole-block pointer and
length are validated before remap/free. As required by Zig's allocator contract,
the remapped slice retains its original allocation alignment. The probe requires these observations:

| Policy | Source result | Old live immediately after remap | Exact prefix/frame | Live after cleanup |
|---|---:|---|---|---:|
| in_place | 101 | true | preserved | 0 |
| moved | 201 | false | preserved | 0 |
| failed | 301 | true, length 4 unchanged | preserved | 0 |

The retained Linux 0.16.0 gate passed fresh export and translation, the three
native/model observations above, the ownership module's kernel check and the
representation, lifetime, cap and frame regressions. Its fresh AIR has exactly
one recognized remap call with three runtime arguments, and the generated client
calls `Zig.Allocator.remap`. These results cover this bounded byte-buffer client
and the explicitly stated ownership lemmas; they are not general source/model
correspondence or allocator qualification.

The model retains default failure and adds explicitly selected byte remap
policies. Whole-block ownership replaces each cell's size metadata, retains
`min(old,new)` byte representations, adds undefined grown bytes, and preserves
the exact caller heap frame. The moved branch allocates a fresh block and frees
the complete old block; the failure branch preserves memory. In-place growth
checks both the latest block index and that every other block, including dead
history, ends before its address. This check supplies an allocation-order
condition that is not implied by arbitrary sequential model memory. It advances
`nextAddr` monotonically. Race and whole-allocation premises remain explicit.

`Kernel.lean` checks representation facts and imports the ownership rules.
`Check.lean` executes separate assertions for prefix, suffix undefinedness,
length, old lifetime, request cap and caller-frame preservation, including an
adversarial dead-block address history. `Runner.lean` executes the fresh generated
source client under all three model policies. `check.sh` is a ROOT-only fresh
export/translation/native/model recipe. The Linux 0.16.0 gate passed;
`mutations.py` prepares five exact runtime mutations. All five passed the Linux
0.16.0 serial mutation gate: each fresh runtime build and plain `Check.lean`
elaboration succeeded before execution failed at the expected semantic assertion.
The mutations target wrong in-place length, corrupted prefix/defined suffix,
a live old moved block, mutation on failure and overlapping in-place growth. A meaningful mutant must compile the runtime-only
`Check.lean` and then fail an assertion; a build failure alone is not a semantic
mutation result.

Zero-size, empty, overflow and sentinel behavior retain existing API cases;
the source/native probe covers only nonempty nonsentinel byte growth from 4 to 8.

There is no allocator identity, native address reuse, general source/model
correspondence, `resize`, or `realloc` claim. `resize` is currently unrecognized;
`reallocAdvanced` lowers through raw vtable calls rather than this remap boundary.
