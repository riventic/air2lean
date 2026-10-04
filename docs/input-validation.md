# AIR input validation

The checked path parses each original input before anonymous-name normalization can rewrite
it. `StrictJson.parse` uses Lean's JSON string and number decoders and rejects repeated
**decoded** object keys at every level. Thus `"schema"` and `"sch\u0065ma"` collide, as do a
literal non-BMP character and its UTF-16 surrogate-pair escape. Lean decodes lone surrogates
as U+FFFD; keys that then collide are rejected too. Malformed escapes, trailing tokens and
commas produce parser diagnostics with byte offsets.

The CLI rejects oversized regular files from metadata and independently reads at most the
per-file limit plus one byte before UTF-8 decoding, covering short reads and file growth.
The 64 MiB policy applies to each file; it does not cap the sum of retained files.
Each file is limited to 64 MiB of UTF-8, 128 nested JSON containers, 1,024 characters in a
numeric token and exponent magnitude 4,096. Value-type and checked type traversal is limited
to 256 levels. Integer widths and packed backing integers cannot exceed Zig’s 65,535-bit
limit; decimal integer literal strings cannot exceed 32,768 characters. Integer constants and enum tags
must fit their declared integer widths. Float bit patterns, enum constants and named errors
must fit their own types too; duplicate field names/tags and a non-integer enum tag
or non-error-set error-union set type are rejected. These are supported-input limits, with explicit errors rather than substituted
values. They do not constitute an overall compiler time/memory guarantee.

Schema and target/build compatibility is specified in [profiles.md](profiles.md). Existing
local checks retain ownership of reference forms, aggregate constant shapes, type-graph
range/cycle checks, instruction IDs and lexical reference/branch scopes, modeled memory
layouts, pointer restrictions, supported instructions and standard-library model discovery.

`checkProgram` additionally validates signature IDs, parallel layout tables, duplicate
function/instruction names or IDs, operand/global references, argument-instruction types,
return values (including loaded-return pointer/pointee agreement), typed constant forms and global initializers, cross-file calls and definitions shared by emission. Calling it directly on
normalized `Func` values runs these checks too. Direct API callers still run `check` for the
subset and `normalize` for raw lexical scope validation; `checkProgram` is not a replacement
for those stages.

Ordinary calls require exact argument count and compatible argument/result types across the
caller's and callee's **local** type tables. Structural equality includes integer widths and
signedness, aggregate identity/field order, pointer qualifiers, all modeled layout facts and
recursive children. Type IDs can differ. Equality never supplies an implicit cast. Indirect
calls check every address-taken exported target of the function-pointer type. Spawn calls
compare their captured tuple's fields with the worker's parameters; the worker result remains
discarded by the established thread model.

Allocator create/alloc/alignedAlloc/dupe results must admit the model’s `OutOfMemory` error;
open error sets are accepted. Recognized allocator/thread calls keep their existing model exemptions, with runtime arity,
argument/result forms, named mutable Group/DarwinImpl/Timer receivers and required
pointee/item relationships checked before emission even
when an AIR file with that model name is present. A direct `Val.func` runtime argument lacks a
structured signature in the current normalized schema and receives a precise unsupported
diagnostic. Typed instruction values containing function pointers remain supported; checking
a printable function-type name does not establish a binary ABI correspondence theorem.

Named globals must have the same type/layout, mutability, thread-local/extern flags and initial
value everywhere. Comparison follows initializer pointers through the corresponding local
global tables, tracks recursive pairs, and retains named target identity; different local
indices are valid. Successful comparisons cache all visited global pairs only for the exact
ordered pair of local file tables; failed comparisons publish no provisional equality.
An unnamed target compares by definition, consistent with the emitter's
constant sharing. Conflicting used named aggregate definitions are rejected. Implementation
fields hidden behind recognized model types do not become additional emitted definitions.
A global that shares an exported function's name must be that function's address-taken
constant, rather than a conflicting data definition. Function initializers must be their named constant
function block; unnamed mutable globals are rejected because anonymous storage is shared by
constant value.

All checks run before the CLI writes the output path. A failure preserves any earlier output
file. The regression drivers are `tests/roadmap/input-validation/Validation.lean` (compiled
Lean evaluation of direct API/parser checks) and `test_cli.py` (positive/negative mutations
against a previously built translator). Neither is presented as a kernel proof of parser or
whole-program validation correctness. The direct API cases include stream-growth limits,
shared packed-width graphs, and enum integer boundaries; the CLI includes huge sparse-file
and unsupported-float rejection. The root's serialized compiler queue runs them after
building the modified translator.
