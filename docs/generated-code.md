# Generated Lean code

`lake exe air2lean <air-dir> -o <File.lean> --namespace <Ns> [--prefix <p>] [--float-semantics ieee|compiler-rt]` writes one Lean file for all JSON files in `<air-dir>`.

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

## Types

| Zig | Lean |
|---|---|
| `uN`, `iN`, `usize`, `isize` | `BitVec N` (`usize`/`isize` = `BitVec 64`) |
| `f16`, `f32`, `f64`, `f80`, `f128` | `Zig.F16`, `Zig.F32`, `Zig.F64`, `Zig.F80`, `Zig.F128` (`Zig.Float .f16` … `.f128`; docs/floats.md) |
| `bool` | `Bool` |
| `void` | `Unit` |
| `[N]T` | `Vector T' N` |
| `[N:s]T` | `Vector T' (N+1)`: the sentinel is the last item, as in the AIR (a constant's `elems`, `docs/air-json.md`). A load or store copies all `N+1` items; a slice of it has length `N`. |
| `@Vector(N, T)` (`T` an integer or a float) | `Zig.Vec T' N` (`ZigLean/Vec.lean`) |
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

In memory, a vector of integers or floats is its lanes, as an array, with the size rounded up
to a power of 2 (`vecLayout`). A `@Vector(n, bool)` is bit-packed: lane `i` is bit `i`, the
size is `⌈n / 8⌉` bytes rounded up to a power of 2 (`boolVecLayout`), and the bits above `n`
are padding (`Byte.part`, as a `uN`): a load that meets a set padding bit throws `.unspecified`.
A lane pointer (`&v[i]`, `ptr_elem_ptr` through a `*@Vector`) of an integer or float vector is
an item pointer, as for an array. A lane pointer of a `bool` vector is outside the subset: the
lane is a bit, and the AIR file has no lane index (the pointer type's `vector_index`).

### Places

A pointer into a local is a **place**: an `alloc` (a `var`, or `ret_ptr`, the local the result is built in), a field pointer of a place (`struct_field_ptr*`; `ptr_slice_len_ptr`, `ptr_slice_ptr_ptr` of a slice), or a `bitcast` of a place. If every place of an `alloc` is used only as the pointer operand of `load`, `store`, a field pointer, `bitcast`, `set_union_tag` and `ret_load` (`Air2Lean/Memory.lean`), the local is a `Locals` field plus a path of struct fields and union payloads. Any other use (a call argument, a stored value, a returned pointer, `optional_payload_ptr`, an item pointer of a local array) makes the address escape: the local is then a stack block in memory (§Memory).

```lean
-- store to rect.w in the result local (a union): change the payload of `rect`
modify (fun s => { s with local2 := (Shape.modify_rect (fun x => { x with w := i19 }) s.local2) })
```

## Memory

`ZigLean/Mem/` models memory as blocks of bytes (CompCert style). A block has its bytes, an alignment, a kind (`stack`, `heap`, `global`), a live flag and an address. A byte is `undef`, `int b`, `ptrFrag p i` (byte `i` of the pointer `p`, so a pointer in memory keeps its block), `errFrag e i` (byte `i` of the code of the error `e`, §Casts, layout and function pointers), or `part m b` (only the low `m` bits of `b` are defined). A `Zig.Ptr` is a block and a byte offset.

A function **uses memory** if a parameter or the return type contains a pointer (a top-level `[]const T` with a pointer-free `T` does not count), an `alloc` escapes (§Places), it has a pointer constant (a global, a string literal) or a memory op (pointer arithmetic, an item pointer, `@memset`, `@memcpy`, `@tagName`, a call to the allocator model, …; `memoryOp`), or it calls a function that uses memory (`Air2Lean/Memory.lean`). Every other function is **pure**: its translation does not change.

| | Pure | Uses memory |
|---|---|---|
| result | `Zig.Result α` | `Zig.MemM α` (`StateT Zig.Mem Zig.Result α`) |
| body | `Zig.M Locals Exit` | `Zig.MM Locals Exit` (`StateT Locals Zig.MemM`) |
| call of a function that uses memory | — | `Zig.callM` |
| call of a pure function | `Zig.call` | `Zig.callR`; a `[]const T` argument is `Zig.readSlice T align s` |

| AIR, through a pointer to memory | Lean |
|---|---|
| `load` | `Zig.load T align p` |
| `store` | `Zig.store (α := T) align p v`; a store of `undefined` is `Zig.storeUndef T align p` |
| `struct_field_ptr*` | `p.add <offset>` (the exporter's field offset) |
| `is_null_ptr`, `is_non_null_ptr` | `?*T`: a load of the pointer (`null` is address 0). `?T`: `Zig.optIsSome T p`, the flag byte after the payload |
| `optional_payload_ptr`, `optional_payload_ptr_set` | `p` (the payload is at offset 0); `_set` of a `?T` sets the flag: `Zig.optSetSome T p` |
| `cmp_eq`, `cmp_neq` on pointers | `==`, `!=` on block and offset |
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

`align` is the pointer type's `align(N)` (`ptr_align`, `docs/air-json.md`). An access throws `.illegal` if the block is dead, a byte is outside the block, or the address is not a multiple of `align`.

`Zig.Enc T` gives the size, alignment and bytes of a value (little-endian, x86_64 ABI). `ZigLean/Mem/Enc.lean` has the instances for integers, `bool`, floats, `Zig.Ptr`, `Zig.Slice`, optionals and arrays (`Vector`); each struct and enum that a pointer can point to gets a generated instance from the exporter's offsets. `Check.lean` compares the model's size and alignment of each type in memory with the exporter's `abi_size`/`abi_align`, and rejects a difference. Padding bytes are `undef`. A `uN` with `N % 8 ≠ 0` has padding bits: its last byte is `part (N % 8) b`, because Zig stores it as its integer type and the bits above are undefined. A load that reads an `undef` byte or bit of the value throws `.unspecified` (a `uM` read of a `part m` byte needs its bits in that byte to be at most `m`). A set bit above a `uN` in its last byte also throws `.unspecified`: LLVM makes a load of `iN` undefined if no `iN` store wrote it (a union tag byte 2 of a 1-bit tag). A `packed` union field read is a bit-cast of the backing integer and truncates; a byte other than 0 or 1 as a `bool`, or a tag value without a name of an exhaustive enum, throws `.illegal`. Packed structs, tagged unions and error unions in memory: §Casts, layout and function pointers.

`@memset`, `@memcpy`, `@memmove` and `Zig.readSlice` do nothing for 0 items, also through a pointer that is not valid. `Zig.readSlice` (a `[]const T` argument of a pure function) throws `.unspecified` if any item has an `undef` byte, also an item that the callee does not read.

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

`errorNameOf e` throws `.unspecified` for an error whose name no error set of the program has. A `const` global, a string literal, a tag or error name and a function block are read-only (`Zig.BlockKind.constGlobal`): a store, an atomic read-modify-write or a `cmpxchg` to one throws `.illegal` (`Zig.Mem.accessW`), for example a write through `@constCast`. `threadlocal` and `extern` globals are outside the subset.

### Casts, layout and function pointers

| Zig | AIR | Lean |
|---|---|---|
| `@intFromPtr(p)` | `bitcast` pointer → integer | `Zig.ptrAddr p` (the block's address plus the offset) |
| `@ptrFromInt(a)` | `bitcast` integer → pointer, after the `castToNull` and `incorrectAlignment` checks | `Zig.ptrFromAddr a`: the block whose bytes contain `a`, else `⟨none, a⟩` |
| `@ptrCast`, `@constCast`, `@volatileCast`, `@alignCast` | `bitcast` pointer → pointer (`@alignCast` after its `incorrectAlignment` check) | the same `Zig.Ptr`. A load through the new type reads the same bytes as the new type. |
| `@fieldParentPtr("f", p)` | `field_parent_ptr` | `p.add (-offset)` |
| `@bitCast` of a packed struct | `bitcast` packed struct ↔ backing integer | `Zig.Packed.toBits`, `Zig.Packed.ofBits?` |
| `f(x)`, `f: *const fn` | `call` of an instruction | `if f == ⟨some k, 0⟩ then g x else …` for each function `g` of the type of `f` whose address the program takes; any other pointer throws `.illegal` |

A **packed struct** is a Lean `structure` with a generated `Zig.Packed S n` instance (`ZigLean/Packed.lean`): `toBits` puts field 0 in the lowest bits, `ofBits` reads the fields back. A field is an integer, a `bool`, an enum (its tag integer; each enum has a `Zig.Packed` instance) or a packed struct; other fields are outside the subset. `valid` is `false` for bits with a tag value without a name of an exhaustive enum, in any field: where bits become a value (a load, `@bitCast`, a bit-pointer or a `packed` union read), `Zig.Packed.ofBits?` throws `.illegal` for them, as the `Enc` of an enum does. In memory, a packed struct is its backing integer. A **bit-pointer** (`&p.f` of a packed struct field, `*align(a:o:h) T`) points to the host integer: `Zig.loadBits T h align o p` and `Zig.storeBits` read and write the `n` bits at bit `o` of the `h`-byte host integer. `storeBits` reads the host integer first, so it throws `.unspecified` if a byte of the host integer is `undef`. The undefined padding bits in the last byte of a packed struct whose backing integer is not `8h` bits (`Byte.part`) read as 0 (`Zig.loadHost`), and `storeBits` keeps them undefined. A field bit in the undefined part throws `.unspecified`. A store of `undefined` to a packed field is outside the subset. The host integer must be `h` bytes as a `u(8h)` in the model: 1, 2, 4, 8 or a multiple of 16 bytes.

An **`extern` struct** uses the exporter's field offsets, as every struct does.

A **tagged union** in memory has its tag and the active field's payload at the compiler's offsets: the part with the larger alignment first, the tag if the alignments are equal (`Check.lean`'s `unionLayout`). The translator compares the resulting size and alignment with the exporter's. A tag value without a name throws `.illegal`. A bare union is a tagged union (§Enums and unions).

An **error union** `E!T` in memory is `Zig.Enc (Except Zig.ErrName T)` (`ZigLean/Mem/Enc.lean`): a 2-byte error code and the payload, the payload first if its alignment is more than 2. The compiler numbers the errors per compilation, so the model does not know the code of an error. The code of error `e` is the 2 bytes `errFrag e 0`, `errFrag e 1`; 0 is no error; any other integer code throws `.unspecified`. The differential test compares an `errFrag` byte as a wildcard. `is_err_ptr`, `unwrap_errunion_payload_ptr`, `unwrap_errunion_err_ptr` and `errunion_payload_ptr_set` are `Zig.errIsErrAt`, `Zig.errPayloadPtr`, `Zig.errCodeAt` and `Zig.errSetOk`.

An **`extern` or `packed` union** is a Lean `structure` with the one field `bytes : Vector Zig.Byte n` (`n`: its size; `ZigLean/Union.lean`). Every field starts at byte 0. `U.get_f` reads field `f` from the first bytes; `U.modify_f` writes it and keeps the bytes after it. An `extern` field is its `Zig.Enc` encoding (`Zig.Raw`): a read that meets an `undef` byte throws `.unspecified`. This is the rule of every value load: a read of an array field decodes all items, so one `undef` item throws, also if the code then uses only another item (0.15.2 and 0.14.1 read `w.bytes[0]` of a union value this way; 0.16.0 reads it through memory). A `packed` field is its `Zig.Packed` bits at bit 0 (`Zig.PackedU`); in 0.16.0 all fields have the same bit width. A `packed` write, as a store of a `uN`, makes the bits above the field in its last byte undefined (`Byte.part`). `union_init` (a union built as a value, e.g. as a call argument) is `U.init`; 0.16.0 builds a `packed` union from its field with a `bitcast`, which is `Zig.PackedU.init` of the backing integer. A `packed` union as a field of a packed struct, and an `extern` or `packed` union constant without an active field, are outside the subset.

A **function pointer** points to a 1-byte global block of its function in `mem0`. Only the functions whose address the program takes (a global whose initial value is a function) have a block. The call graph and the memory analysis count each of them as a callee of every indirect call through a pointer of its type.

### Atomics and threads

A function that reaches a sync op (an atomic op, `Thread.spawn`, `Thread.join`, or a call to such a function; `Air2Lean/Memory.lean`'s `concFunctions`) is a **concurrent function**: it returns `Zig.ConcM Tgt α`, and its body runs in `Zig.CM Tgt σ` (`ZigLean/Conc/`). Calls from it: to a concurrent function `Zig.callC`, to a memory function `Zig.callMC` (no stop), to a pure function `Zig.callRC`. The scheduler runs it ([std-models.md](std-models.md) §Thread model).

| AIR | Lean |
|---|---|
| `atomic_load` | `Zig.atomicLoadC (n := N) ord align p` |
| `atomic_store_monotonic`/`release`/`seq_cst` | `Zig.atomicStoreC ord align p v` |
| `atomic_rmw` | `Zig.atomicRmwC op signed ord align p v` (`op`: `Zig.RmwOp`) |
| `cmpxchg_weak`, `cmpxchg_strong` | `Zig.cmpxchgC succ fail align p expected new` (both compile to the same call: the model never fails a `cmpxchg_weak` spuriously) |
| an atomic op on an enum or a `bool` | the same with `Zig.atomicLoadAsC (T)`, `atomicStoreAsC`, `atomicRmwAsC`, `cmpxchgAsC`: the op on the value's `Zig.Packed` bits |

`ord` is a `Zig.AtomicOrder` (`monotonic` is `.relaxed`; `unordered` is rejected). Each `*C` op is a `Zig.pickC` (the oracle picks the message to read or the place of the write, RC11, std-models.md §Thread model), then the op in `MemM` (`Zig.atomicLoadAt c …`).
| `call` of `Thread.spawn(config, f, args)` | `Zig.spawnC (Tgt.f args)` |
| `call` of `Thread.join(handle)` | `Zig.joinC handle` |
| `call` of `Io.futexWaitUncancelable(T, ptr, expected)` / `Io.futexWait` / `Io.futexWake(T, ptr, n)` (0.16.0) | `Zig.futexWaitC io ptr expected` / `Zig.futexWaitCancelableC …` / `Zig.futexWakeC io ptr n` |

A program with a concurrent function gets the type `Tgt`, one constructor per spawned function with its one argument, and `dispatch : Tgt → Zig.ConcM Tgt Unit`, which runs a target (a memory function through `Zig.ConcM.liftMem`):

```lean
inductive Tgt where
  | bump (a : Zig.Ptr)
  | writeFlag (a : Zig.Ptr)

def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .bump a => discard (bump a)
  | .writeFlag a => discard (Zig.ConcM.liftMem (writeFlag a))
```

Every access, plain or atomic, is one `Zig.AccessKind`: `.read`, `.write`, `.atomicRead` or `.atomicWrite`. Each access is one `Zig.FootprintEntry` (block, byte range, kind, and the thread's vector clock at the time), kept in `Zig.Mem.footprint`. `Zig.recordAccess` checks a new access against every earlier entry that overlaps its bytes with a concurrent clock (`Zig.VClock.concurrent`: neither clock is `≤` the other) via `Zig.racePair`: at least one write and at least one plain access is a data race, `.illegal`; anything else is no race. The spawn and join edges, and the release and acquire edges of atomics, are in std-models.md §Thread model. `Thread.detach`, `.yield`, `.spinLoopHint`, `std.Thread.Futex.*`, `std.Thread.Mutex.*`/`Mutex.*`, `std.Thread.Condition.*` are rejected at translation time (`rejectedThreadFn?`), each with its own reason.

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

A generic member (`inactiveUnionField`) is an instance named `<member>__anon_<n>`; the suffix is not part of the segment.

`tests/diff/common.zig` installs a matching `std.builtin.panic` override (same member names, one per Zig safety check), shared by every example's `tests/diff/<ex>/harness.zig`, so the Zig side reports which check tripped instead of aborting; `scripts/diff.sh` compares that name — via the same table (`expected_ctor_for_zig_kind`) — against the `Zig.Error` constructor the Lean side actually threw. A `fail`/`fail` line only counts as a match when the kinds agree; a Zig kind with no table entry, or `unknown` (the child died without reporting one, e.g. a signal), is always a mismatch. A Lean `unspecified` or `illegal` matches any Zig line; the number of such lines per function must equal `tests/diff/<ex>/unspecified.txt` (`<fn> <count>` lines, default 0).

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

A read-write output (`+r`) is outside the subset. The diff test calls the opaque directly (below), so it checks the op; `Proofs/Asm/Proofs.lean`'s `divmod_spec` checks the translation around it.

`volatile` and `clobbers` (`docs/air-json.md`) do not change the translation: an opaque's correctness comes only from what a proof states about it, so nothing represents "this may have effects a proof cannot see."

### Differential-test implementation

`Asm.airAsm_*` has no defining equation to run — that is M21's whole point — so `tests/diff/asm/asm.zig` gives the diff test one, the same role `tests/diff/libm/libm.zig` plays for `ZigLean/Float/Libm.lean`'s transcendental ops: one `export fn air2lean_asm_<op>` per op, reimplementing `examples/asm/asm.zig`'s behaviour with ordinary Zig builtins (`@byteSwap`, `@popCount`, `@clz`) instead of the inline asm itself — the diff test needs behavioural equivalence, not instruction equivalence, and a builtin-based archive builds on every host, not only x86_64. Built into `air2lean_asm.a` by `scripts/diff.sh` and linked into `difftest` (`tests/diff/lakefile.toml`'s `moreLinkArgs`).

Wiring an already-imported opaque to an `@[extern]` archive function needs `@[csimp]`, not `@[implemented_by]`: both attributes refuse to attach to a declaration from an already-imported module (`Asm.airAsm_*` lives in `Proofs/Asm/Gen.lean`, imported by `tests/diff/Diff.lean`), but `@[csimp]` tags a fresh theorem instead (`@Asm.airAsm_3500345798 = @airAsm_3500345798_impl`, one per op, in `Diff.lean`) and swaps `f` for `g` in compiled code only, never in the kernel. The theorem needs a real proof, and none exists (again, M21's point) — `Diff.lean` uses `sorry` for it, the one place in the repo that assumes rather than proves; confined to `tests/diff/`, outside `scripts/no-sorry.sh`'s scope (`ZigLean`, `Proofs`).

`@[csimp]` only redirects references *compiled after* the theorem — `Asm.bswap32` (and `lzcnt64`, `popcnt64`) are compiled once, inside `Proofs/Asm/Gen.lean`, long before `Diff.lean`'s theorems exist, so a call through the generated wrapper never sees the swap and stays on the opaque's `Inhabited`-default placeholder. `Diff.lean`'s `runBswap32`/`runLzcnt64`/`runPopcnt64` call `Asm.airAsm_*` directly instead, bypassing the wrapper: those calls compile after the theorems, so the swap applies.

Mutation (i) (`scripts/mutate.sh`) mutates this archive (`air2lean_asm_bswap32` returns its input unchanged), not a Lean file: there is no Lean-side equation to mutate for an opaque, so this is the only way to confirm the comparison against `examples/asm/asm.zig`'s real inline asm is live, not vacuous.

## Differential test

One example directory `examples/<ex>/` = one namespace `<Ex>` = one prefix `<ex>.`. `<ex>` must not be the name of a std namespace (`enums`, `heap`, `mem`, `math`, …): the dump filter `<ex>.` would also match those std functions (e.g. `enums.EnumArray(…).get`, which std's debug code uses on x86_64-linux). Per example:

| Path | What |
|---|---|
| `examples/<ex>/<ex>.zig` | The Zig source under test |
| `examples/<ex>/filter` | Optional: more name prefixes to translate, one per line (std code; [std-models.md](std-models.md)) |
| `tests/golden/<ex>/air/` | Golden AIR-JSON, checked by `scripts/check.sh`; per-version overrides in `tests/golden/<v>/<ex>/air/`, per-OS overrides in `tests/golden/<v>/<ex>/air-<os>/` (`uname -s` in lower case). The Linux files come from CI: the Mac cannot write them |
| `Proofs/<Ex>/Gen.lean` | Committed translator output (`--namespace <Ex> --prefix <ex>.`) |
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
