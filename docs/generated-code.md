# Generated Lean code

`lake exe air2lean <air-dir> -o <File.lean> --namespace <Ns> [--prefix <p>] [--float-semantics ieee|compiler-rt]` writes one Lean file for all JSON files in `<air-dir>`.

`--help` or `-h` prints usage and exits successfully. `--namespace` accepts dot-separated
Lean identifiers (for example `My.Program`); empty components, keywords, and names requiring
quoting are rejected before writing output. Filesystem errors identify the input directory,
input file, or output path. A spawned worker needs its own AIR file, just like a direct callee.

`--float-semantics` (default `ieee`) picks the model behind `@divExact`/`/`/`@divTrunc`/`@divFloor`/`@mulAdd` on a float operand: `ieee` (what a proof assumes) or `compiler-rt` (bit-exact port of the compiler_rt routines the reference target, `x86_64-linux -mcpu=baseline`, actually calls; `docs/floats.md` §Semantics). `scripts/check.sh` reads one example's opt-in from `examples/<ex>/translate.args` (one line of extra CLI args) if present, so most examples stay on the default with no translator invocation to update.

## Names

| Zig | Lean |
|---|---|
| function `basic.scale` (with `--prefix basic.`) | `Ns.scale` |
| any other `.` in a name | `_` |
| a generic instance `array_list.Aligned(u32,null).append` | `array_list_Aligned_u32_null_append` (each character other than a letter, a digit or `_` is `_`; `)` is dropped) |
| struct type `basic.Job` | `Ns.Job` (a `structure`, same field names) |
| enum or union type `variants.Shape` | `Ns.Shape` |
| tag enum of `union(enum)` `variants.Shape` | `Ns.ShapeTag` |
| a name that is a Lean keyword | `«name»` |

Declarations that collide with another emitted name receive a stable `_air2leanN` suffix.
Named types and functions also avoid the emitter's local binders, such as `v`, `g`, `p0` and
the instruction result names `iN`/`vN`, because type references and calls in generated helpers
and bodies are unqualified. For example, an enum named `v` becomes `v_air2lean1`, and a
function named `p0` becomes `p0_air2lean1`. Source fields and local fields likewise avoid allocated
type names so that one field cannot shadow the type of a later field.

## Types

| Zig | Lean |
|---|---|
| `uN`, `iN`, `usize`, `isize` | `BitVec N` (`usize`/`isize` = `BitVec 64`) |
| `f16`, `f32`, `f64`, `f80`, `f128` | `Zig.F16`, `Zig.F32`, `Zig.F64`, `Zig.F80`, `Zig.F128` (`Zig.Float .f16` … `.f128`; docs/floats.md) |
| `bool` | `Bool` |
| `void` | `Unit` |
| `[N]T` | `Vector T' N` |
| `[N:s]T` | `Vector T' (N+1)`: the sentinel is the last item, as in the AIR (a constant's `elems`, `docs/air-json.md`). A load or store copies all `N+1` items; a slice of it has length `N`. |
| `@Vector(N, T)` (`T` an integer, a float or `bool`) | `Zig.Vec T' N` (`ZigLean/Vec.lean`) |
| `[]const T` in a pure function (§Memory) | `Array T'` |
| `[]T`, `[:s]T`; `[]const T` in a function that uses memory | `Zig.Slice` (an item pointer and a `BitVec 64` length; §Memory) |
| `*T`, `*const T`, `[*]T`, `[*:s]T`, `*[N]T` | `Zig.Ptr` (a block and a byte offset; §Memory) |
| `?T` | `Option T'` (`?*T` is `Option Zig.Ptr`, `?[]T` is `Option Zig.Slice`) |
| `struct` (layout `auto` or `extern`) | `structure … deriving Repr, Inhabited, DecidableEq` |
| `E!T` (error union) | `Except Zig.ErrName T'` |
| exhaustive `enum` | `inductive` with one constructor per name |
| non-exhaustive `enum(T) { …, _ }` | `structure` with `bits : BitVec N` (every value of `T`) |
| `union(enum)` | `inductive` with one constructor per field (no argument for a `void` field) |
| error set (`error{A, B}`, `anyerror`) | `Zig.ErrName` (`abbrev ErrName := String`; an error's identity is its name) |
| `std.mem.Allocator` | `Zig.Allocator` (the allocator model, [std-models.md](std-models.md)) |

The file gets a named type (struct, enum, union) only if a function uses it: through a parameter, the result, an instruction, a constant or a global, directly or through the types that these name (`usedTys`). The AIR type table also has types that no code uses, for example the fields of `std.Thread`, which differ by host OS. They are not in the file, so the translation is the same on every host.

### Enums and unions

Each enum `E` also gets:

| Def | What |
|---|---|
| `E.toBits : E → BitVec N` | the tag value (`@intFromEnum`) |
| `E.ofInt? : Int → Option E` | the value with that tag, or `none` (`@enumFromInt` → `Zig.enumOf (E.ofInt? …)`, which throws `.panic` on `none`: `invalidEnumValue`) |
| `E.isNamed : E → Bool` | `is_named_enum_value` |
| `E.<name> : E` | a named value (non-exhaustive enum only; an exhaustive one has the constructor) |

Each tagged union `U` with tag enum `UTag` also gets, per field `f`:

| Def | What |
|---|---|
| `U.tag : U → UTag` | `get_union_tag` |
| `U.get_f : U → Zig.Result T` | the payload of `f` (`struct_field_val`); throws `.panic` if `f` is not active. Sema checks the tag first (`inactiveUnionField`), so the throw is not reached. |
| `U.modify_f : (T → T) → U → U` | a store into the payload of `f`: `f` becomes active with `g` applied to its payload, or to `default` if another field was active |
| `U.setTag_f : U → U` | `set_union_tag`: `f` becomes active; its payload stays if `f` was active, else it is `default` (Zig: undefined) |

Zig keeps the payload bytes when the tag changes, and the Zig versions write a union result in different orders: 0.15.2 and 0.16.0 set the tag first, then store the payload; 0.14.1 stores the payload first. `modify_f` and `setTag_f` give the same value for both orders.

A `switch` on an exhaustive enum that names every value becomes a `match` with one arm per case and no `else` arm (its `corruptSwitch` panic cannot happen). Any other `switch` is an `if` chain.

A bare union has a hidden tag in `ReleaseSafe` (the exporter's `safety_tag`): it is a tagged union, and a read of a field that is not active panics (`inactiveUnionField`). An `extern` or `packed` union is its bytes (§Casts, layout and function pointers).

### Vectors

The checked vector subset has integer, float, or bool lanes. Vectors of pointers and bitcasts
to, from, or between different vector types are rejected: no corresponding packing or
pointer-aware lane semantics is claimed. Identity casts keep the same vector value.

`Zig.Vec T' N` (`ZigLean/Vec.lean`) wraps a `Vector T' N`; `.lanes` is the only field. Lane 0 is
first. AIR op → generated code:

| AIR op | Generated code |
|---|---|
| `add`/`sub`/`mul`, checked/wrapping/saturating | `Zig.Vec.map2M`/`Zig.Vec.map2`, lane-wise, the same scalar function as the non-vector case |
| `splat` | `Zig.Vec.splat` |
| `select` (a vector of `bool` predicate) | `Zig.Vec.select` |
| `shuffle` | a `Zig.Vec` literal picked from the comptime-known mask, `#v[a.lanes[i]!, …]` — not a runtime shuffle function, since AIR gives the mask at translation time |
| every other lane-wise op: `div_*`, `rem`, `mod`, `div_float`, `min`/`max`, `add_with_overflow` family, `bit_and`/`bit_or`/`xor`, `not`, `abs`, shifts, `cmp_vector`, `bool_and`/`bool_or`, `intcast`, `trunc`, float rounding, `sqrt`, libm ops, `mul_add`, float/int conversions | the scalar op's expression on lane variables in `Zig.Vec.mapM`/`map2M`/`map3M` (`Emit.lean`'s `emitLaneWise`): each lane has the scalar semantics, and the first lane that throws gives the error. `@addWithOverflow` gives a vector of pairs, and `Zig.Vec.unzip` makes the tuple |
| `reduce` | `Zig.Vec.reduce` (int `.Add`/`.Mul` wrap: safe, since wraparound `+`/`*` stay associative; `.And`/`.Or`/`.Xor`/`.Min`/`.Max`; `bool` `.And`/`.Or`/`.Xor`, the safety checks of a vector op) or `Zig.Vec.reduceM` (float `.Min`/`.Max`: `Float.minChk`/`maxChk`, throws `.unspecified` on the `+0`/`-0` tie, docs/floats.md §+0 and −0 in `@min` / `@max`) |

A float `reduce`'s lane order is exactly Zig's (`Vec.reduce_four`-style, lane 0 first for a
4-lane vector) — float addition is not associative, so a proof about a float `reduce` states this
order rather than a lane-independent scalar sum (`Proofs/Vectors/Proofs.lean`'s `fDot_body`).

Sema writes the safety checks of a vector op (division by zero, overflow) as a `cmp_vector` and
a `reduce` of the `bool` vector, before the op.

In memory, a vector of integers or floats whose lane width is `8 * Enc.size T` (`u8`, `u32`,
`f64`, …) is its lanes, as an array, with the size rounded up to a power of 2 (`vecLayout`); every
backend lays these bytes out alike. A vector whose lanes have a non-byte width (`u9`) or scalar
ABI padding (`u24`, `u40`, `f80`) is bit-packed by the LLVM backend: lane `i` is bits
`[i * w, (i + 1) * w)` of one `n * w`-bit little-endian integer (`w = @bitSizeOf(T)`), with size and
alignment `⌈n * w / 8⌉` rounded up to a power of 2 (`packedVecLayout`, `Vec.packedEnc`; observed by
`tests/roadmap/vector-layouts/probe.zig`). The checker admits such a vector in memory only for an
AIR file whose schema-12 profile names `stage2_llvm` (other backends, and legacy profiles without
a backend, are rejected), and never a lane pointer into it. Value-only vectors of every lane type
still support the lane-wise operations above.

A `@Vector(n, bool)` is bit-packed: lane `i` is bit `i`, the
size is `⌈n / 8⌉` bytes rounded up to a power of 2 (`boolVecLayout`), and the bits above `n`
are padding (`Byte.part`, as a `uN`): a load that meets a set padding bit throws `.unspecified`.
A lane pointer (`&v[i]`, `ptr_elem_ptr` through a `*@Vector`) of a byte-strided integer or float
vector is an item pointer, as for an array. A lane pointer of a `bool` vector or of a bit-packed
vector is outside the subset: the lane is a bit field, and the AIR file has no lane index (the
pointer type's `vector_index`).

### Places

A pointer into a local is a **place**: an `alloc` (a `var`, or `ret_ptr`, the local the result is built in), a field pointer of a place (`struct_field_ptr*`; `ptr_slice_len_ptr`, `ptr_slice_ptr_ptr` of a slice), or a `bitcast` of a place. If every place of an `alloc` is used only as the pointer operand of `load`, `store`, a field pointer, `bitcast`, `set_union_tag` and `ret_load` (`Air2Lean/Memory.lean`), the local is a `Locals` field plus a path of struct fields and union payloads. Any other use (a call argument, a stored value, a returned pointer, `optional_payload_ptr`, an item pointer of a local array) makes the address escape: the local is then a stack block in memory (§Memory).

```lean
-- store to rect.w in the result local (a union): change the payload of `rect`
modify (fun s => { s with local2 := (Shape.modify_rect (fun x => { x with w := i19 }) s.local2) })
```

## Memory

`ZigLean/Mem/` models memory as blocks of bytes (CompCert style), using a little-endian ABI with 64-bit pointers. The optional AIR field `target_endian` records `"little"` or `"big"`; the parser rejects an explicit non-little-endian value or a malformed field. This additive schema-11 field is optional for older exports: if absent, little-endian is assumed, not verified. The memory layout checker compares exported sizes and alignments with the model, including its 8-byte pointers and 16-byte slices. A block has its bytes, an alignment, a kind (`stack`, `heap`, `global`), a live flag and an address. A byte is `undef`, `int b`, `ptrFrag p i` (byte `i` of the pointer `p`, so a pointer in memory keeps its block), `errFrag e i` (byte `i` of the code of the error `e`, §Casts, layout and function pointers), or `part m b` (only the low `m` bits of `b` are defined). A `Zig.Ptr` is a block and a byte offset.

A function **uses memory** if a parameter or the return type contains a pointer (a top-level `[]const T` with a pointer-free `T` does not count), an `alloc` escapes (§Places), it has a pointer constant (a global, a string literal) or a memory op (pointer arithmetic, an item pointer, `@memset`, `@memcpy`, `@tagName`, a call to the allocator model, …; `memoryOp`), or it calls a function that uses memory (`Air2Lean/Memory.lean`). Every other function is **pure**: its translation does not change.

| | Pure | Uses memory |
|---|---|---|
| result | `Zig.Result α` | `Zig.MemM α` (`StateT Zig.Mem Zig.Result α`) |
| body | `Zig.M Locals Exit` | `Zig.MM Locals Exit` (`StateT Locals Zig.MemM`) |
| call of a function that uses memory | — | `Zig.callM` |
| call of a pure function | `Zig.call` | `Zig.callR`; a `[]const T` argument is `Zig.readSlice T align s` |

Scalar nonoptional C/allowzero pointer values have an explicit [qualified fragment](null-pointers.md): address null tests, casts and direct accesses under the existing live-block rule. Nullable pointer temporaries classify a function as using memory even when its inputs/output are integers or bools, because address observations read the block-address state. A stored C/allowzero pointer (a `*[*c]T` target, struct field, array item or global) binds the storage dictionary `Zig.nullablePtrEnc` (null is eight zero bytes), and a projection from a C/allowzero base is `Zig.ptrProjectNullable` (illegal at address zero). Optionals of nullable pointers, nullable pointers in unions/tuples/error-union payloads, and nullable slicing/bulk memory/parent recovery remain rejected.

| AIR, through a pointer to memory | Lean |
|---|---|
| `load` | `Zig.load T align p` |
| `store` | `Zig.store (α := T) align p v`; a store of `undefined` is `Zig.storeUndef T align p`; a partly `undefined` array, struct or tuple constant is `Zig.storeBytes p align (Zig.writeBytes (Zig.Enc.encode (v : T)) off (Array.replicate len .undef))`, one `writeBytes` per `undefined` item or field (below) |
| `struct_field_ptr*` | `p.add <offset>` (the exporter's field offset) |
| `is_null_ptr`, `is_non_null_ptr` | `?*T`: a load of the pointer (`null` is address 0). `?T`: `Zig.optIsSome T p`, the flag byte after the payload |
| `optional_payload_ptr`, `optional_payload_ptr_set` | `p` (the payload is at offset 0); `_set` of a `?T` sets the flag: `Zig.optSetSome T p` |
| `cmp_eq`, `cmp_neq` on pointers | Ordinary pointers: `==`, `!=` on block/offset. Scalar C/allowzero pointers: address comparison through `Zig.ptrEqAddr`. |
| `cmp_lt`, `cmp_lte`, `cmp_gt`, `cmp_gte` on pointers | `Zig.ptrLt`, `Zig.ptrLe`: the order of the addresses (`Zig.ptrAddr`) |
| `ptr_add`, `ptr_sub` | `p.elem size n`, `p.elemSub size n` (`size`: the item's `abi_size`) |
| `ptr_elem_ptr`, `slice_elem_ptr` | `p.elem size i`; of a slice `s.ptr.elem size i` |
| `ptr_elem_val`, `slice_elem_val` | `Zig.load T align (p.elem size i)` (`align`: the pointer's `align(N)`, at most `T`'s alignment) |
| `slice`, `slice_ptr`, `slice_len`, `array_to_slice` | `⟨p, len⟩`, `s.ptr`, `s.len`, `⟨p, N⟩` |
| `memset`, `memset_safe` | `Zig.memset (α := T) align p n (some v)`; `none` for `undefined` |
| `memcpy`, `memmove` | `Zig.memmove size dstAlign srcAlign dst src n` (all bytes are read before the first write) |
| `tag_name` | `E.tagName e` (below) |
| `error_name` | `errorNameOf e` (below) |
| `call` of `mem.Allocator.create`, `alloc`, `free`, … | `Zig.Allocator.create a size align`, … ([std-models.md](std-models.md)) |

**`undefined` operands.** `undefined` is never read as a default (`0`, `false`) that a later read could observe. A store writes it as undefined bytes: a wholly `undefined` value with `Zig.storeUndef`, and a partly `undefined` constant (an `undefined` item of an array, or field of a non-`packed` struct or tuple, at any depth) as the bytes of the value with the bytes of each `undefined` part undefined (`Air2Lean/Memory.lean`'s `undefByteRanges`, from the exporter's sizes and offsets). A load that reads one of those bytes throws `.unspecified`. A local that receives such a store is a stack block, not a `Locals` field (`escapingAllocs`). `memset` of a wholly `undefined` item writes undefined bytes. Every other `undefined` operand is outside the subset (`unsupported_semantics`): a partly `undefined` value under an optional, error union, union, slice, vector or packed struct, a store of one to a packed struct field, a partly `undefined` `memset` item, an `undefined` `shuffle` lane, and `undefined` (wholly or partly) as a call argument, return or block result, `aggregate_init` element, arithmetic, `select` or atomic operand (`Thread.spawn`'s `SpawnConfig`, which the model does not read, is exempt). A local that receives a store of a wholly `undefined` value is one of three kinds (`Air2Lean/Memory.lean`): if the next access to the local in the same body overwrites all of it with a defined value (a `store`, an output-only asm output) and nothing before it can leave the body (a `br`, `repeat` or dispatch to an enclosing block or loop), the `undefined` store is dead (no read can observe it) and the local stays a typed `Locals` field; else, if its type has no pointer and its places are the local and fields of non-`packed` structs, used only by `load`, `store`, `struct_field_ptr` and `dbg`, it is a **byte local** (`byteLocals`): a `Locals` field of type `Zig.Bytes T` (`ZigLean/Mem/Basic.lean`), the bytes of its value, all undefined at entry; every other such local is a stack block. In a byte local, a store writes the stored value's bytes at the place's offset (`Zig.Bytes.set`, `Zig.Bytes.setUndef`) and a load of a place decodes only its bytes (`Zig.Bytes.get`, which throws `.unspecified` if one is undefined). A load of the whole local whose every use copies it keeps its bytes, undecoded (`FCtx.computeRawInsts`): a `struct_field_val` of a non-`packed` struct decodes only the field (`Zig.Bytes.get F v off`), a store to memory is `Zig.storeBytes p align v` and to a byte local `Zig.Bytes.copy`, and a `ret` makes the function return `Zig.Bytes T` (`rawFunctions`; its other returns are `Zig.Enc.encode v`). A call of such a function is the same kind of copy, or, if a use reads the value otherwise, `Zig.Bytes.get T (← call) 0`, which decodes all of it. A function whose address is taken or that a thread runs keeps its type. So `Thread.Futex.Deadline.init(null)` returns the bytes of `timeout = null` with `started` undefined, and `Condition.wait`'s store of it into its deadline block is `Zig.storeBytes`.

`align` is the pointer type's `align(N)` (`ptr_align`, `docs/air-json.md`). An access throws `.illegal` if the block is dead, a byte is outside the block, or the address is not a multiple of `align`.

`Zig.Enc T` gives the size, alignment and bytes of a value (little-endian, x86_64 ABI). `ZigLean/Mem/Enc.lean` has the instances for integers, `bool`, floats, `Zig.Ptr`, `Zig.Slice`, optionals and arrays (`Vector`); each struct and enum that a pointer can point to gets a generated instance from the exporter's offsets. `Check.lean` compares the model's size and alignment of each type in memory with the exporter's `abi_size`/`abi_align`, and rejects a difference. Padding bytes are `undef`. A `uN` with `N % 8 ≠ 0` has padding bits: its last byte is `part (N % 8) b`, because Zig stores it as its integer type and the bits above are undefined. A load that reads an `undef` byte or bit of the value throws `.unspecified` (a `uM` read of a `part m` byte needs its bits in that byte to be at most `m`). A set bit above a `uN` in its last byte also throws `.unspecified`: LLVM makes a load of `iN` undefined if no `iN` store wrote it (a union tag byte 2 of a 1-bit tag). A `packed` union field read is a bit-cast of the backing integer and truncates; a byte other than 0 or 1 as a `bool`, or a tag value without a name of an exhaustive enum, throws `.illegal`. Packed structs, tagged unions and error unions in memory: §Casts, layout and function pointers.

`@memset`, `@memcpy` and `@memmove` do nothing for 0 bytes, also through a pointer that is not valid; this includes a positive count of zero-size items. `Zig.readSlice` does nothing for 0 items. For a positive count of zero-size items it decodes the empty encoding once and returns that many decoded values, preserving decoder errors without accessing memory. For nonzero-size items, `Zig.readSlice` (a `[]const T` argument of a pure function) throws `.unspecified` if any item has an `undef` byte, also an item that the callee does not read.

`Zig.ptrFromAddr` recovers a block's provenance for addresses inside it or exactly one byte past its last byte, including dead blocks. The one-past pointer can be moved back into the block; it cannot be dereferenced, and recovering provenance does not revive a freed block. Addresses in allocation gaps retain no block.

Two pointers into different blocks have the order of the model's addresses, which can differ from the compiled code. The `@memcpy` overlap check of `ReleaseSafe` compares pointers: for two blocks, the model and the compiled code both find no overlap.

### Globals

A function file lists the globals that its pointer constants point into (`docs/air-json.md` §Global). The translator makes one program-wide table: a named global is one block, shared by name; an unnamed constant (a string literal) with the same type and value as another one shares its block. Then one block per name of each enum that a function reads with `@tagName`, and one per name of each error of the program's error sets if a function reads `@errorName`. `mem0` is the memory at program start: block `k` is global `k`, with its initial bytes. A pointer constant is `⟨some k, off⟩`. An array with a sentinel (`[12:0]u8`) is stored with its sentinel.

```lean
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: slices.counter
  (Zig.Enc.encode ((0 : BitVec 32) : BitVec 32), 4),
  ...]

def Color.tagName (e : Color) : Zig.Result Zig.Slice :=
  match e with
  | .red => pure ⟨⟨some 2, 0⟩, 3⟩
  ...
```

`errorNameOf e` throws `.unspecified` for an error whose name no error set of the program has. A `const` global, a string literal, a tag or error name and a function block are read-only (`Zig.BlockKind.constGlobal`): a store, an atomic read-modify-write or a `cmpxchg` to one throws `.illegal` (`Zig.Mem.accessW`), for example a write through `@constCast`. `threadlocal` globals are outside the subset.

**Initial values are never defaulted.** A wholly `undefined` global (`var x: T = undefined`) is
`Zig.Enc.size T` undefined bytes, so a load before the first store throws `.unspecified`. A
partly `undefined` initial value (an aggregate, optional, error-union or union payload with an
`undefined` part) is rejected: a value constant would read that part as `0`/`false`. A global
without an `init` that is not `extern` (Sema had not resolved it) is rejected with "the AIR
file has no initial value".

**External initial state.** An `extern` global (`extern var x: T;`, `extern const`) has no
initial value in the program. If the program has one, the translator emits a structure
`ExternInit` with one field per `extern` global, named after it without the prefix, in block
order, and `mem0` takes it explicitly:

```lean
structure ExternInit where
  /-- Block 0: `global_init.counter` (`var`, writable). -/
  counter : BitVec 32

def mem0 (ext : ExternInit) : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: global_init.counter (extern: initial value `ext.counter`)
  (Zig.Enc.encode (ext.counter : BitVec 32), 4, .global),
  ...]
```

The blocks of `mem0` are added in order (`Mem.ofGlobals`), which fixes their addresses and the
initialization order: block addresses do not depend on the external values. Every statement
about the program start is therefore about `mem0 ext` for an `ext` that the proof quantifies
over; assumptions about external storage are hypotheses on `ext`
(`tests/roadmap/global-init/GlobalInit/Proofs.lean`). The field type is the contract: the
external definition must hold a valid encoding of that type (padding bytes undefined) before the
program starts; external writes during the run are not modelled. Only a named, pointer-free,
union-free and error-free type qualifies (integers, floats, `bool`, enums, arrays, vectors,
structs, tuples and optionals of these); an `extern` function, pointer, union or error storage,
an `extern` with an `init`, and an unnamed `extern` are rejected (`GLOBAL_FAILURE`). A name
shared by several files must agree on `extern`. Without an `extern` global, `mem0 : Zig.Mem` is
unchanged.

### Casts, layout and function pointers

| Zig | AIR | Lean |
|---|---|---|
| `@intFromPtr(p)` | `bitcast` pointer → integer | `Zig.ptrAddr p` (the block's address plus the offset) |
| `@ptrFromInt(a)` | `bitcast` integer → pointer, after the `castToNull` and `incorrectAlignment` checks | `Zig.ptrFromAddr a`: the block whose bytes contain `a`, else `⟨none, a⟩` |
| `@ptrCast`, `@constCast`, `@volatileCast`, `@alignCast` | `bitcast` pointer → pointer (`@alignCast` after its `incorrectAlignment` check) | the same `Zig.Ptr`. A load through the new type reads the same bytes as the new type. |
| `@fieldParentPtr("f", p)` | `field_parent_ptr` | memory: `p.add (-offset)`; local place: remove the proven terminal struct field |
| `@bitCast` of a packed struct | `bitcast` packed struct ↔ backing integer | `Zig.Packed.toBits`, `Zig.Packed.ofBits?` |
| `@bitCast` of an array, `extern` struct or `extern` union (Zig ≤0.16) | `bitcast` with one on either side | `Zig.reprCast T x`: the memory bytes of `x`, padding undefined, decoded as `T` (`docs/aggregate-casts.md`) |
| `@ptrCast` `?*T` → `*U`; `@intFromPtr`/`@ptrFromInt` of `?*T` (Zig ≤0.16) | `bitcast` | `Zig.optPtrUnwrap` (null: `.panic`), `Zig.optPtrAddr` (null: 0), `Zig.optPtrFromAddr` (0: null) |
| `f(x)`, `f: *const fn` | `call` of an instruction or a constant address | `if f == ⟨some k, 0⟩ then g x else …` for each function `g` of the type of `f` whose address the program takes; any other pointer throws `.illegal` |

A local-place `@fieldParentPtr` recovers the original local allocation and its enclosing
path by removing exactly the matching terminal field of an ordinary (`auto` or `extern`)
struct. The field index, container and child types must match the recorded projection.
Same-pointee qualifier casts preserve the path, and a mutation through the recovered parent
updates the original local. A later escaping use still lowers that allocation to stack
memory. Packed/union parents, bit-pointers, slice-field recovery, nullable or nonsingle
pointers and pointee reinterpretation are outside this local fragment. Recovery preserves
const and volatile qualifiers. A local whose place escapes, for example through an array
element inside a struct (`&s.items[i].f`), is a stack block: its fields and parents use the
memory lowering, any depth, in the original block. `ZigLean/Mem/Parent.lean` proves that this
recovery gives the container pointer (`Ptr.parent_field`, `Ptr.parent_path`,
`Ptr.parent_elem_field`) and that a write through the recovered parent is visible through the
field pointer and conversely (`parent_store_visible`, `field_store_visible`). The source and
synthetic qualification recipe is in
[`tests/roadmap/local-parent/README.md`](../tests/roadmap/local-parent/README.md).

A **packed struct** is a Lean `structure` with a generated `Zig.Packed S n` instance (`ZigLean/Packed.lean`): `toBits` puts field 0 in the lowest bits, `ofBits` reads the fields back. A field is an integer, a `bool`, an enum (its tag integer; each enum has a `Zig.Packed` instance) or a packed struct; other fields are outside the subset. A packed struct constant is its backing integer (`Zig.Packed.ofBits`); the exporter writes some as `.{ .f = v, … }`, which `Json.lean`'s `parsePackedLit` reads. `valid` is `false` for bits with a tag value without a name of an exhaustive enum, in any field: where bits become a value (a load, `@bitCast`, a bit-pointer or a `packed` union read), `Zig.Packed.ofBits?` throws `.illegal` for them, as the `Enc` of an enum does. In memory, a packed struct is its backing integer. A **bit-pointer** (`&p.f` of a packed struct field, `*align(a:o:h) T`) points to the host integer: `Zig.loadBits T h align o p` and `Zig.storeBits` read and write the `n` bits at bit `o` of the `h` bytes at `p`, any `h` (the exporter's `host_size`: `(bits + 7) / 8` on LLVM, the ABI size on the self-hosted x86_64 backend). Both read the whole host (provenance, bounds, alignment, races) but use **defined-bit masks** (`ZigLean/Packed.lean` §Defined bits): each host byte is a defined-bit mask and a value (`Byte.int`, `.undef`, `.part m`, and `.mask d` for any other mask), a load needs only the field's bits to be defined (else `.unspecified`), and a store replaces only the field's bits: every other bit keeps its state, defined or undefined. A store of `undefined` to a packed field is `Zig.storeUndefBits n h align o p`: only the field's bits become undefined, never the whole byte and never a default; a local with such a store is a stack block (`escapingAllocs`). `ZigLean/PackedLemmas.lean` proves the frame (other bits unchanged, the field reads back, a disjoint field reads as before, `undefined` makes the field undefined). A byte-aligned field whose bit size fills its ABI size can have a byte pointer instead, at byte `(o_base + bit) / 8` of the host when its base is a bit-pointer. The checker compares every exporter pointer to a packed struct field (and `@fieldParentPtr` back) with the model's layout (`Check.lean`'s `packedFieldPtr?`: the field's bit offset is the sum of the earlier fields' bit sizes plus a bit-pointer base's offset, whose host it keeps) and rejects a mismatch with `PACKED_LAYOUT` (`docs/diagnostics.md`); a field past its host is a type error. A store of a partly `undefined` value to a packed field stays outside the subset (`tests/roadmap/packed-fields`).

An **`extern` struct** uses the exporter's field offsets, as every struct does.

A **tagged union** in memory has its tag and the active field's payload at the compiler's offsets: the part with the larger alignment first, the tag if the alignments are equal (`Check.lean`'s `unionLayout`). The translator compares the resulting size and alignment with the exporter's. A tag value without a name throws `.illegal`. A bare union is a tagged union (§Enums and unions).

An **error union** `E!T` in memory is `Zig.Enc (Except Zig.ErrName T)` (`ZigLean/Mem/Enc.lean`): a 2-byte error code and the payload, the payload first if its alignment is more than 2. The compiler numbers the errors per compilation, so the model does not know the code of an error. The code of error `e` is the 2 bytes `errFrag e 0`, `errFrag e 1`; 0 is no error; any other integer code throws `.unspecified`. The differential test compares an `errFrag` byte as a wildcard. `is_err_ptr`, `unwrap_errunion_payload_ptr`, `unwrap_errunion_err_ptr` and `errunion_payload_ptr_set` are `Zig.errIsErrAt`, `Zig.errPayloadPtr`, `Zig.errCodeAt` and `Zig.errSetOk`.

An **`extern` or `packed` union** is a Lean `structure` with the one field `bytes : Vector Zig.Byte n` (`n`: its size; `ZigLean/Union.lean`). Every field starts at byte 0. `U.get_f` reads field `f` from the first bytes; `U.modify_f` writes it and keeps the bytes after it. An `extern` field is its `Zig.Enc` encoding (`Zig.Raw`): a read that meets an `undef` byte throws `.unspecified`. This is the rule of every value load: a read of an array field decodes all items, so one `undef` item throws, also if the code then uses only another item (0.15.2 and 0.14.1 read `w.bytes[0]` of a union value this way; 0.16.0 reads it through memory). A `packed` field is its `Zig.Packed` bits at bit 0 (`Zig.PackedU`); in 0.16.0 all fields have the same bit width. A `packed` write, as a store of a `uN`, makes the bits above the field in its last byte undefined (`Byte.part`). `union_init` (a union built as a value, e.g. as a call argument) is `U.init`; 0.16.0 builds a `packed` union from its field with a `bitcast`, which is `Zig.PackedU.init` of the backing integer. A `packed` union as a field of a packed struct, and an `extern` or `packed` union constant without an active field, are outside the subset.

A **function pointer** points to a 1-byte global block of its function in `mem0`. Only the functions whose address the program takes (a global whose initial value is a function) have a block. These blocks and their function types form one callable-address table (`fnRefs`). Every function-pointer value resolves through it, whatever its origin: a constant (also a constant callee), a global initializer, a struct field, a parameter or memory. A call through a pointer of type `T` dispatches over exactly the table's functions of type `T`, and the program check validates each of their signatures against the call. A fixed callee address (`fixedGlobalOrigin?`) that is not the zero-offset block of a function of type `T` is rejected statically, as an unknown executable address or an incompatible signature. At runtime, a pointer to a function of another type, to data or to no block throws `.illegal`. A stored or cast function pointer carries no data storage; a data view of a function block stays outside the subset. The call graph and the memory analysis count each table function as a callee of every indirect call through a pointer of its type. `ZigLean.External.Callback` states the table rules (`resolve_complete`, `resolve_incompatible`, `resolve_unknown`); [`tests/roadmap/indirect-calls/README.md`](../tests/roadmap/indirect-calls/README.md) proves that an emitted call is that dispatch.

### Atomics and threads

A function that reaches a sync op (an atomic op, `Thread.spawn`, `Thread.join`, or a call to such a function; `Air2Lean/Memory.lean`'s `concFunctions`) is a **concurrent function**: it returns `Zig.ConcM Tgt α`, and its body runs in `Zig.CM Tgt σ` (`ZigLean/Conc/`). Calls from it: to a concurrent function `Zig.callC`, to a memory function `Zig.callMC` (no stop), to a pure function `Zig.callRC`. The scheduler runs it ([std-models.md](std-models.md) §Thread model).

| AIR | Lean |
|---|---|
| `atomic_load` | `Zig.atomicLoadC (n := N) ord align p` |
| `atomic_store_monotonic`/`release`/`seq_cst` | `Zig.atomicStoreC ord align p v` |
| `atomic_rmw` | `Zig.atomicRmwC op signed ord align p v` (`op`: `Zig.RmwOp`) |
| `cmpxchg_strong` | `Zig.cmpxchgC succ fail align p expected new` (typed Packed: `cmpxchgAsC`) |
| `cmpxchg_weak` | `Zig.cmpxchgWeakC succ fail align p expected new` (typed Packed: `cmpxchgWeakAsC`); matching-value failure is an additional read-only choice |
| an atomic op on an enum, a `bool` or a packed struct | the same with `Zig.atomicLoadAsC (T)`, `atomicStoreAsC`, `atomicRmwAsC`, `cmpxchgAsC`: the op on the value's `Zig.Packed` bits |
| an atomic op on a `*T`, `[*]T` or `?*T` | `Zig.atomicLoadPtrC (T)`, `atomicStorePtrC (α := T)`, `atomicXchgPtrC` (`.Xchg` only), `cmpxchgPtrC`, `cmpxchgWeakPtrC` (`T`: `Zig.Ptr` or `Option (Zig.Ptr)`): messages keep the pointer's block; `cmpxchg` compares identities ([pointer-atomics.md](pointer-atomics.md)) |

`ord` is a `Zig.AtomicOrder` (`monotonic` is `.relaxed`; `unordered` is rejected). Each `*C` op is a `Zig.pickC` (the oracle picks the message to read or the place of the write, RC11, std-models.md §Thread model), then the op in `MemM` (`Zig.atomicLoadAt c …`).
| `call` of `Thread.spawn(config, f, args)` | `Zig.spawnC (Tgt.f args)` |
| `call` of `Thread.join(handle)` | `Zig.joinC handle` |
| `call` of `Io.futexWaitUncancelable(T, ptr, expected)` / `Io.futexWait` / `Io.futexWake(T, ptr, n)` (0.16.0) | `Zig.futexWaitC io ptr expected` / `Zig.futexWaitCancelableC …` / `Zig.futexWakeC io ptr n` |

A program with a concurrent function gets the type `Tgt`, one constructor per spawned function with its complete captured argument tuple, and `dispatch : Tgt → Zig.ConcM Tgt Unit`, which runs a target (a memory function through `Zig.ConcM.liftMem`):

```lean
inductive Tgt where
  | bump (a : Zig.Ptr)
  | writeFlag (a : Zig.Ptr)

def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .bump a => discard (bump a)
  | .writeFlag a => discard (Zig.ConcM.liftMem (writeFlag a))
```

An empty capture has type `Unit`; a single field preserves the scalar constructor shown above. A four-field mixed capture has type `BitVec 32 × Zig.Ptr × BitVec 32 × Zig.Ptr`; the dispatcher calls `worker a.1 a.2.1 a.2.2.1 a.2.2.2` in source order. Pure workers receive a `Zig.readSlice` conversion for each captured slice. For programs containing an empty or multi-field capture, `Tgt.spawnInit P target ghost` is an alias of `P.init target ghost` for expressing the ownership or sharing obligation over the full capture. Such programs also get `Tgt.captures : Tgt → List Zig.Conc.Capture`, which classifies each field in source order from its AIR type. A pointer-free value is `.value`, a pointer is `.ptr p`, a slice is `.slice s`, and any other field is `.other`, for example an aggregate holding a pointer, an allocator, `Io`, or a thread handle. `Zig.Conc.Capture.grant` (`ZigLean/Conc/Transfer.lean`) turns this list into the per-argument ownership obligation; see [proofs.md](proofs.md#concurrent-separation-logic).

Every access, plain or atomic, is one `Zig.AccessKind`: `.read`, `.write`, `.atomicRead` or `.atomicWrite`. Each access is one `Zig.FootprintEntry` (block, byte range, kind, and the thread's vector clock at the time), kept in `Zig.Mem.footprint`. `Zig.recordAccess` checks a new access against every earlier entry that overlaps its bytes with a concurrent clock (`Zig.VClock.concurrent`: neither clock is `≤` the other) via `Zig.racePair`: at least one write and at least one plain access is a data race, `.illegal`; anything else is no race. The spawn and join edges, and the release and acquire edges of atomics, are in std-models.md §Thread model. `Thread.yield` emits `Zig.threadYieldC`, preserving both success and `error.SystemCannotYield`. Audited inline `std.atomic.spinLoopHint` instructions emit `Zig.spinLoopHintC`; both expose scheduling opportunities with no fairness guarantee ([progress-hints.md](progress-hints.md)). `Thread.detach` (0.16.0) emits `Zig.detachC`, which consumes the handle without a stop ([std-models.md](std-models.md#thread-model)). `Io.futexWaitTimeout` is rejected at translation time (`stdModels`, `Air2Lean/StdModels.lean`) with its reason. `Thread.Futex.wait`/`wake` are modelled; the supported `Thread.Mutex` and `Thread.Condition` methods are translated from std code, with the macOS mutex boundary modelled ([std-models.md](std-models.md#thread-model)).

An escaping `alloc` gets a stack block at function entry. Its `Locals` field holds the pointer, and the block is freed when the function returns:

```lean
def sumTo (p0 : BitVec 32) : Zig.MemM (BitVec 64) := do
  let s1 ← Zig.allocStack 8 8
  let e ← ((do ...) : Zig.MM sumToLocals sumToExit).run' { (default : sumToLocals) with acc := s1 }
  Zig.free s1
  match e with ...
```

`ZigLean/Sep/` (separation logic, [proofs.md](proofs.md)) and `ZigLean/Mem/Lemmas.lean` (generated code imports neither) have the lemmas for proofs: a load after a store at the same pointer, a load of bytes that a store does not touch, and `LawfulEnc` (`u32`). It adds `Zig.callM` and `Zig.callR` to the `zig_unfold` simp set.

## Signature

```lean
import ZigLean
namespace Ns
def scale (a : BitVec 32) (b : BitVec 8) : Zig.Result (BitVec 32) := ...
```

- Parameters keep the Zig order. Their names are `p0`, `p1`, … unless a `dbg_arg_inline` gives the source name.
- A function that panics (overflow, bounds, `unreachable`) returns `throw e`; for the error values see `Zig.Error`.
- A function that uses memory (§Memory) returns `Zig.MemM T`; `(f args).run m` is its result with the memory after the call.
- A function that does not terminate returns `none` (the `Option` layer of `Zig.Result`).
- Functions come in dependency order: a callee before its caller.
- A recursive group (a function that calls itself, or functions that call each other) becomes one `mutual` block. The group's `Locals`/`Exit` types and `again<k>` defs come before the block. In the block, every function def and every `loop<k>` def has `partial_fixpoint`: a loop body can call a group member. The monotonicity lemmas in `ZigLean/Basic.lean` (`Zig.call`, `run'`, `Zig.loop`) let Lean accept these defs.

## Loops

Each AIR `loop` body is its own top-level def, named `<fn>.loop<id>` (instruction ID of the `loop`: its position in the function, debug instructions not counted, so the same in every Zig version; `Air2Lean/Air/Canon.lean`), emitted just before `def <fn>` — so a proof can name the loop body directly (`Zig.loop_spec (body := <fn>.loop<id> …) …`), instead of only the anonymous term `Zig.loop` used to take inline.

```lean
def sum.again7 : sumExit → Bool
  | .rep7 => true
  | _ => false

def sum.loop7 (p0 : Array (BitVec 32)) (i5 : BitVec 64) : Zig.M sumLocals sumExit := do
  ...

def sum (p0 : Array (BitVec 32)) : Zig.Result (BitVec 64) := do
  ...
    Zig.loop (sum.loop7 p0 i5) sum.again7
  ...
```

- Parameters are the loop body's captures: every SSA value (`p<i>`/`i<id>`) it reads that is bound outside it; order is params first (param order), then by id. The call passes the caller's name of each value (the payload of a `try` is `v<id>` there).
- A `Locals` field (`total`, `local3`, …) is not a capture: it goes through `get`/`modify`, unaffected by which def the code sits in.
- A nested loop gets its own def too, emitted before its enclosing loop's def; the enclosing loop's body calls it the same way `<fn>` calls the outer one.
- The repeat test is a named def `<fn>.again<id>` too. An inline `fun e => match …` would get a new matcher each time it is elaborated, so a proof could not restate it.

## Panics

`Zig.Error` has 8 constructors: `overflow`, `outOfBounds`, `divByZero`, `unreachable`, `panic`, `unspecified`, `illegal`, `deadlock` (every thread that has not ended waits, std-models.md §Thread model). `unspecified` = Zig leaves the result open and the model does not choose one (the bits of a NaN, `@intFromFloat` without a safety check out of range, an `undef` byte in a loaded value). `illegal` = illegal behaviour that `ReleaseSafe` does not check (§Memory: an access to a dead block, out of bounds or misaligned; a double free; `@rem`/`@mod` of `minInt` by `-1`, where x86_64's `idiv` traps). Checked arithmetic (`add_safe`/`sub_safe`/`mul_safe`) and `unreach` map directly; a `call` to a noreturn function (AIR's `func` field, e.g. `debug.FullPanic((function 'defaultPanic')).outOfBounds`) is a Zig std lib panic-handler function named by its trailing `.`-segment — `Air2Lean/Air/Op.lean`'s `panicErrorFor?` maps that segment to a constructor, and `Check.lean` rejects a noreturn callee outside the table:

| segment | constructor |
|---|---|
| `integerOverflow`, `integerOutOfBounds`, `integerPartOutOfBounds`, `shlOverflow`, `shrOverflow` | `.overflow` |
| `divideByZero` | `.divByZero` |
| `reachedUnreachable` | `.unreachable` |
| `outOfBounds`, `startGreaterThanEnd` | `.outOfBounds` |
| `exactDivisionRemainder`, `unwrapNull`, `unwrapError`, `forLenMismatch`, `invalidEnumValue`, `inactiveUnionField`, `corruptSwitch`, `sentinelMismatch`, `copyLenMismatch`, `memcpyAlias`, `call` (`@panic`) | `.panic` |

The exact noreturn callee `debug.defaultPanic` maps to `.panic` as well. Pinned std sources for 0.14.1, 0.15.2 and 0.16.0 define this standard panic handler as noreturn; fresh 0.16.0 adapter-fixture AIR calls it directly. This is an exact-name compatibility rule: foreign names and suffix variants remain rejected, and a returning call with this name has no external-call model. The existing `FullPanic` table is unchanged.

A generic member (`inactiveUnionField`) is an instance named `<member>__anon_<n>`; the suffix is not part of the segment.

`tests/diff/common.zig` installs a matching `std.builtin.panic` override (same member names, one per Zig safety check), shared by every example's `tests/diff/<ex>/harness.zig`, so the Zig side reports which check tripped instead of aborting; `scripts/diff.sh` compares that name — via the same table (`expected_ctor_for_zig_kind`) — against the `Zig.Error` constructor the Lean side actually threw. A `fail`/`fail` line only counts as a match when the kinds agree; a Zig kind with no table entry, or `unknown` (the child died without reporting one, e.g. a signal), is always a mismatch. A Lean `unspecified` or `illegal` matches any Zig line; the number of such lines per function must equal `tests/diff/<ex>/unspecified.txt` (`<fn> <count>` lines, default 0), or lie in a range `<fn> <min>-<max>` for a function whose count depends on the timing of the compiled threads (`atomics`' `mpRelaxed`: the real run sees the flag on some inputs, and then the model has a data race).

## Inline asm

M21 (register operands only, x86_64): one `opaque` per distinct (source template, ordered constraint list, operand widths) tuple — a proof gets only what the caller states about an op, no built-in axiom for what it computes (`Air2Lean/Air/Op.lean`'s `.asm` doc comment). Two occurrences with the same source, constraints and widths share one opaque; the name is `airAsm_<hash>`, a hash of that tuple (`Air2Lean/Emit.lean`'s `asmDefName` — not Lean's own `hash`, just stable within one generation run). `Check.lean` rejects a memory or immediate constraint, so every operand is a register, hence a plain `BitVec`; the opaque is `BitVec` in, `BitVec` out (`Unit` for no output). An input may also carry a matching constraint (`0`) tying it to the sole output register — the standard idiom for a register-modify-in-place instruction (`bswap32`'s `bswap`, which both reads and writes one register); still a register operand, so the opaque's shape does not change:

```lean
opaque airAsm_3500345798 (i0 : BitVec 32) : BitVec 32   -- bswap32: one input, one output, both 32 bits

def bswap32 (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (airAsm_3500345798 p0)
    pure (.ret i1)) : Zig.M bswap32Locals bswap32Exit).run' (default : bswap32Locals)
  match e with
  | .ret v => pure v
```

**More than one output.** Each output is a register output (`=r`, `={reg}`) of an integer. At most one is the expression's result (`-> T`); every other one is an lvalue output: the asm writes it to its operand, a pointer. The opaque then returns a tuple of all outputs, in output order. The translation binds the result output, and writes each lvalue output with the code of a `store` (a local's field, or `Zig.store` through a pointer). A matching input constraint (`"1"`) can name any output. `examples/asm/asm.zig`'s `divmod` (`divl`: the quotient is the result, the remainder goes to the local `rem`):

```lean
opaque airAsm_2482283570 (i0 : BitVec 32) (i1 : BitVec 32) : BitVec 32 × BitVec 32

    let a4 := airAsm_2482283570 p0 p1
    let i4 ← pure a4.1
    modify (fun s => { s with rem := a4.2 })
```

The diff test calls the opaque directly (below), so it checks the op; `Proofs/Asm/Proofs.lean`'s `divmod_spec` checks the translation around it.

### Effect contract: read-write and memory operands, aliases, clobbers (A01)

A01 extends the accepted constraints only where the effect is explicit (`Air2Lean/AsmContract.lean`, `ZigLean/Asm.lean`, premise [ASM-03](premises.md#asm-03)). Register-only ops keep their exact translation and `airAsm_<hash>` name (`Proofs/Asm/Gen.lean` is byte-identical). An op with a read-write output, a memory output or a registry-approved `"memory"` clobber is named `airAsmFx_<hash>` (same hash):

| Constraint | Operand | Translation |
|---|---|---|
| `+r`, `+{reg}` | lvalue output | the old value is read before the call (a local's field, or `Zig.load` through a pointer), passed after the inputs, and the new value is stored after |
| `=m` | lvalue output | the opaque's output is stored to the pointee: the footprint is exactly `Enc.size` bytes at the pointer (a 1, 2, 4 or 8 byte integer) |
| `+m` | lvalue output | as `+r`, through the memory operand |

The opaque's type is the contract: it takes the register inputs and the old values of the read-write outputs and returns the outputs, so it cannot touch memory or the locals. Every memory effect is in the wrapper, in this order: `Zig.Asm.guard` (when two or more outputs are written through memory pointers), the read-write loads in output order, the call, the stores in output order:

```lean
opaque airAsmFx_3102165980 (i0 : BitVec 32) (i1 : BitVec 32) : BitVec 32 × BitVec 32

    Zig.Asm.guard [(p0, 4), (p1, 4)]
    let a2o0 ← Zig.load (BitVec 32) 4 p0
    let a2o1 ← Zig.load (BitVec 32) 4 p1
    let a2 := airAsmFx_3102165980 a2o0 a2o1
    Zig.store (α := BitVec 32) 4 p0 a2.1
    Zig.store (α := BitVec 32) 4 p1 a2.2
```

- **Frame.** A wrapper writes only its declared locations: `Proofs/Asm/Effects.lean`'s `Zig.Asm.Frame` (every block keeps its shape, every byte outside the locations its value) composes over loads and stores, and inverts any successful run. `tests/roadmap/asm-effects` proves it for the generated `+m`, `=m` and two-`+m` wrappers.
- **Aliases.** Two written locations that overlap would make the result depend on the instructions' store order, which the opaque does not fix: `Zig.Asm.guard` throws `.unspecified` (the model picks no order). Two outputs with the same pointer value or the same local are rejected statically. A successful run therefore had disjoint operands (`swapm_disjoint`).
- **Clobbers.** `cc`, flags and named registers have no Lean-visible state and are accepted, but a clobber may not name the register of a pinned operand (`{eax}` with a `rax` clobber: the x86_64 sub-register families are one register), two outputs or two inputs may not pin one register, and an input may not pin the register of an early-clobber or read-write output. A matching input may tie only to a write-only register output.
- **`"memory"` clobber.** Rejected (the block may write any memory) unless the whole block is an entry of the reviewed `asmPureRegistry`. The only entry is the compiler barrier `asm volatile ("" ::: "memory")`: no instruction, so no effect in a model that runs accesses in program order.
- **Still rejected.** `m` and immediate inputs, `rm`/`g` alternatives, `=&m`, `+&r`, a read-write or memory result (`-> T`), a memory operand of another width, an output through a `const` pointer.

Zig source names a variable as an output operand, so real `=m`/`+m` refs are local `alloc`s (a `Locals` field, or a stack block if the local escapes). The translator accepts any pointer ref the AIR names; `tests/roadmap/asm-effects` reaches the memory-pointer path with hand-written AIR. Zig 0.16.0's LLVM backend fails module verification for `+m` (`Elementtype attribute can only be applied for indirect constraints`); the self-hosted x86_64 backend compiles it.

Register-only support does not make arbitrary asm safe: ASM-03 is the premise that the instructions behave like the wrapper (read only the declared inputs and read-write locations, write every declared output and nothing else, including through an integer input that holds an address).

`volatile` and register/flag `clobbers` (`docs/air-json.md`) do not change the translation: an opaque's correctness comes only from what a proof states about it, so nothing represents "this may have effects a proof cannot see." In particular a volatile asm (port I/O, counters) is modelled as a repeatable function of its inputs; see [volatile-effects.md](volatile-effects.md) §Residuals. Volatile *memory* accesses are rejected there.

### Differential-test implementation

`Asm.airAsm_*` has no defining equation to run — that is M21's whole point — so `tests/diff/asm/asm.zig` gives the diff test one, the same role `tests/diff/libm/libm.zig` plays for `ZigLean/Float/Libm.lean`'s transcendental ops: one `export fn air2lean_asm_<op>` per op, reimplementing `examples/asm/asm.zig`'s behaviour with ordinary Zig builtins (`@byteSwap`, `@popCount`, `@clz`) instead of the inline asm itself — the diff test needs behavioural equivalence, not instruction equivalence, and a builtin-based archive builds on every host, not only x86_64. Built into `air2lean_asm.a` by `scripts/diff.sh` and linked into `difftest` (`tests/diff/lakefile.toml`'s `moreLinkArgs`).

Wiring an already-imported opaque to an `@[extern]` archive function needs `@[csimp]`, not `@[implemented_by]`: both attributes refuse to attach to a declaration from an already-imported module (`Asm.airAsm_*` lives in `Proofs/Asm/Gen.lean`, imported by `tests/diff/Diff.lean`), but `@[csimp]` tags a fresh theorem instead (`@Asm.airAsm_3500345798 = @airAsm_3500345798_impl`, one per op, in `Diff.lean`) and swaps `f` for `g` in compiled code only, never in the kernel. The theorem needs a real proof, and none exists (again, M21's point) — `Diff.lean` uses `sorry` for it, the one place in the repo that assumes rather than proves; confined to `tests/diff/`, outside `scripts/no-sorry.sh`'s scope (`ZigLean`, `Proofs`).

`@[csimp]` only redirects references *compiled after* the theorem — `Asm.bswap32` (and `lzcnt64`, `popcnt64`) are compiled once, inside `Proofs/Asm/Gen.lean`, long before `Diff.lean`'s theorems exist, so a call through the generated wrapper never sees the swap and stays on the opaque's `Inhabited`-default placeholder. `Diff.lean`'s `runBswap32`/`runLzcnt64`/`runPopcnt64` call `Asm.airAsm_*` directly instead, bypassing the wrapper: those calls compile after the theorems, so the swap applies.

The wrappers themselves (operand order, result placement, lvalue-output stores) are covered by [tests/roadmap/asm-wrappers](../tests/roadmap/asm-wrappers/README.md). It runs the unchanged generated wrapper text against a test-only x86_64 register-machine interpretation bound to each opaque by its translator hash, with wrapper mutants and an audit that keeps the harness out of theorem dependencies.

Mutation (i) (`scripts/mutate.sh`) mutates this archive (`air2lean_asm_bswap32` returns its input unchanged), not a Lean file: there is no Lean-side equation to mutate for an opaque, so this is the only way to confirm the comparison against `examples/asm/asm.zig`'s real inline asm is live, not vacuous.

## Differential test

The runner also emits [typed outcome accounting](outcome-accounting.md), separating source error returns, runtime errors, excluded cases and bounded searches while retaining legacy counters.

One example directory `examples/<ex>/` = one namespace `<Ex>` = one prefix `<ex>.`. `<ex>` must not be the name of a std namespace (`enums`, `heap`, `mem`, `math`, …): the dump filter `<ex>.` would also match those std functions (e.g. `enums.EnumArray(…).get`, which std's debug code uses on x86_64-linux). Per example:

| Path | What |
|---|---|
| `examples/<ex>/<ex>.zig` | The Zig source under test |
| `examples/<ex>/filter` | Optional: more name prefixes to translate, one per line (std code; [std-models.md](std-models.md)) |
| `tests/golden/<ex>/air/` | Golden AIR-JSON, checked by `scripts/check.sh`; per-version overrides in `tests/golden/<v>/<ex>/air/`, per-OS overrides in `tests/golden/<v>/<ex>/air-<os>/` (`uname -s` in lower case). The Linux files come from CI: the Mac cannot write them. A failed CI job uploads the AIR it dumped (artifact `air-<version>-<n>`, `AIR2LEAN_OUT_DIR`); copy the differing files to `air-linux/` |
| `Proofs/<Ex>/Gen.lean` | Committed translator output (`--namespace <Ex> --prefix <ex>.`), for Linux (the reference host). `tests/golden/<v>/<ex>/Gen.lean` replaces it for Zig `<v>`; `tests/golden/<v>/<ex>/Gen-<os>.lean` for Zig `<v>` on host OS `<os>` only (`scripts/check.sh` compares the translation with the first that exists) |
| `tests/diff/<ex>/inputs/<fn>.jsonl` | Generated inputs, one file per function (`tests/diff/gen_inputs.zig`) |
| `tests/diff/<ex>/harness.zig` | Per-function dispatch only: imports `<ex>` + `common`, forks, writes `tests/diff/out/zig/<ex>/<fn>.jsonl` |
| `tests/diff/out/lean/<ex>/<fn>.jsonl` | Lean-side output, written by `tests/diff/Diff.lean` (one exe, dispatches by example+function) |

`tests/diff/common.zig` holds everything shared across examples: the fork-per-input child, the panic override, `renderPayload` (the protocol below, generic over `@typeInfo(T)`, so one function serializes ints, `bool`, and nested `?T`/`E!T`), and the JSONL read/write loop. A harness only lists its example's functions.

`scripts/check.sh`, `scripts/diff.sh`, and `scripts/mutate.sh` loop over `AIR2LEAN_EXAMPLES` (default: every dir in `examples/`).

### Protocol

One JSONL line per input, `{"ok": v}` / `{"fail": "<kind>"}` / `{"diverge": true}` (`Zig.Result`'s `none` — non-termination), `v` per Zig type:

| Zig type | `v` |
|---|---|
| plain int | bare decimal, or quoted decimal for a wide (`u64`/`usize`) result |
| `bool` | `0` or `1` |
| `?T` | `null`, or `T`'s `v` |
| `E!T` | `{"err": "<Name>"}` (the bare error name, e.g. `@errorName` on the Zig side), or `T`'s `v` |
| enum | the tag value, a bare decimal |
| `union(enum)` | `{"<active field>": v}` (`null` for a field without payload) |
| struct | `{"<field>": v, …}` in field order |

A `?T`/`E!T` result nests: e.g. `?(E!T)` renders as `null`, `{"err":"Name"}`, or `T`'s `v`, all three at the same JSON depth as a plain `?T`.

A function that uses memory reads `{"bufs": [[<byte>, …], …], "args": [...]}`: the harness makes one 16-byte aligned buffer per list, and `tests/diff/Diff.lean` one block per buffer, after the globals of `mem0` (block `g + i` = buffer `i`). A buffer block has the kind `.stack`: the allocator did not make it, so a free of it throws `.illegal`. A pointer argument is `{"buf": i, "off": o}`, or `null` for a `?*T`; a slice argument also has `"len": n`. A pointer or slice result into the buffers is written the same way; a result into a global or a heap block is `{"bytes": "<hex>"}`, the bytes of the value or of the items. The result line also has the buffers after the call: `{"ok": v, "bufs": ["<hex>", …]}`, two lowercase hex digits per byte. The Lean side writes an `undef` byte as `??`, and `scripts/diff.sh` matches it with any Zig byte (for example a padding byte of a stored struct). A `part m` byte is `?` and its low hex digit if `m ≥ 4`, else `??`.

A function that takes a `std.mem.Allocator` gets `TestAllocator` ([std-models.md](std-models.md)). Its first argument in `args` is the allocation that fails: `null` or its number (`Zig.Mem.failAt`). The result line ends with the number of live allocations after the call, `,"live": n`, and `scripts/diff.sh` compares it. A free that `TestAllocator` does not accept is the kind `doubleFree` (the Lean side: `.illegal`).

## Error unions

A Zig error (`error.Name`) is a return value, not a panic — a distinct type from `Zig.Error` above. `error.Name` becomes the string literal `"Name"`; an `E!T` constant becomes `.ok v` or `.error "Name"`.

`try v` (sugar for "return the error if `v` holds one, otherwise use its payload") becomes a `match` on `v`: the error arm runs the AIR `try`'s error body (itself ending in an exit, e.g. `ret`), and the ok arm binds the payload under a fresh name and continues with the rest of the instruction sequence:

```lean
match {v} with
| .error _ => (do ...)   -- the `try`'s error body; ends in an exit
| .ok v16 => (do ...)    -- the rest of the sequence, payload bound as `v16`
```

`catch` does not use `try`: it lowers to `is_err`/`is_non_err` plus a `cond_br`, so it becomes a plain `if`/`else` on `Zig.isNonErr`/`Zig.isErr`, unwrapping with `Zig.unwrapPayload`/`Zig.unwrapErr` (`ZigLean/Basic.lean`) in each arm.


## Stable scalar proof interface (opt-in)

`--proof-api` adds a bounded P07 interface for named, checked, straight-line scalar
functions. This initial slice covers integer arguments/constants, checked/wrapping/
saturating add/subtract/multiply, bit and/or/xor, not/negation, integer casts,
truncation/bitcasts and return. Calls, control flow, memory, globals, floats and
anonymous functions receive no interface or partial semantic fingerprint. Their
ordinary definitions continue to emit normally. Default generation is unchanged.

Each selected full source name receives an injective UTF-8 byte encoding:
`air2lean_api_<byte>_<byte>..._model` and the corresponding `_unfold` theorem.
The model is an abbreviation of the actual emitted function. The theorem unfolds
that abbreviation to the function's actual emitted body, with explicit arguments,
and is proved by `rfl`; it introduces neither an axiom nor a replacement semantics.
These names are reserved before ordinary declaration allocation. A source function
that would collide is renamed by the existing declaration allocator. Unrelated
anonymous instantiations therefore do not rename the public scalar interface.

Use the `model` and `unfold` fields of the generated `air2lean-proof-api` JSON
record to find these names, rather than depending on temporary instruction/local
names. A client can use `rw [Namespace.<unfold>]` to enter the generated model.
The unfolded expression remains implementation detail: this slice stabilizes the
entry boundary, not every intermediate expression or a general step-rule calculus.

The existing `scripts/normalize-generated.py report Gen.lean AIR_DIR report.json`
indexes these records under `proof_api.interfaces`. `semantic_sha256` hashes
canonical JSON of normalized scalar IR facts plus checked profile/float assumptions.
It records structured operation/mode, typed constants, structural scalar types and
layouts, parameter order and canonical instruction references. It hashes neither
emitted stdout nor pretty-print whitespace. Raw AIR and generated artifact hashes
remain separate. Source-line/debug maps also remain separate; exporter line numbers
are retained as supplied and are not claimed to be absolute source-file locations.

The report checks record outer fields, identity names and format versions, and
rejects duplicate source identities and interface name collisions. It hashes the
translator-emitted nested facts without validating their meaning; imported reports
are not semantic certificates. Semantics, checked mode, scalar layouts or profile changes affect
the fingerprint. Harmless instruction renumbering and unrelated instantiations do
not. This fingerprint is a change detector for this bounded normalized model, not
a semantic-equivalence, compiler-correspondence or shipping-binary certificate.
A changed fingerprint requires reviewing and rebuilding affected client proofs.

Portable report tests do not invoke a translator or compiler:

```sh
python3 -B tests/roadmap/proof-api/test_report.py
```

ROOT validation uses the built translator and retains its actual generated output
and a downstream arithmetic proof candidate, then kernel checks that candidate:

```sh
python3 tests/roadmap/proof-api/test_cli.py .lake/build/bin/air2lean \
  --retain /tmp/Generated.lean
lake env lean /tmp/Generated.client.lean
lake env lean /tmp/Generated.renumbered.client.lean
lake env lean /tmp/Generated.unrelated.client.lean
# This identical client contract must fail after add is changed to subtract:
if lake env lean /tmp/Generated.changed.client.lean; then exit 1; fi
```

The CLI driver checks renumbered AIR and an unrelated generic instance, then a
semantic mutation. Neither this driver nor synthetic report tests are qualification
evidence until the actual translator and kernel checks have completed.

For every emitted function, including calls, memory and recursion,
`--source-map-json` writes source maps and call-graph semantic fingerprints to a
sidecar. Generated Lean is unchanged. See `docs/stable-generation.md`.

`--split-modules <Module>` writes the same declarations as one module per call group,
plus an umbrella module and invalidation keys. See `docs/modular-output.md`.
