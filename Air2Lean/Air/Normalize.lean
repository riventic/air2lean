import Air2Lean.Air.Canon

/-!
# Per-version normalizer

`normalize : Raw.RawFunc → Except String Func` turns the raw, tag-agnostic JSON mirror
(`Air2Lean/Air/Json.lean`) into the version-independent IR (`Air2Lean/Air/Op.lean`). All
version-specific knowledge — the AIR tag table — lives here. `Check.lean` and `Emit.lean`
never see a `Raw.RawFunc` or a tag string.

One tag table serves every supported version: no subset tag differs between 0.14.1, 0.15.2 and
0.16.0 (`zig-patch/<version>/TAGS.md`). To add a Zig version: add it to `supportedVersions`;
if a subset tag differs, add a version case to `normalizeOp` (`PLAN.md` §Zig version support).
-/

namespace Air2Lean

def arg1 (fnName : String) (raw : Raw.RawInst) (strict : Bool := false) : Except String Val := do
  if strict && raw.args.size != 1 then
    throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs exactly 1 arg"
  match raw.args[0]? with
  | some v => pure v
  | none => throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs 1 arg"

def arg2 (fnName : String) (raw : Raw.RawInst) (strict : Bool := false) : Except String (Val × Val) := do
  if strict && raw.args.size != 2 then
    throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs exactly 2 args"
  match raw.args[0]?, raw.args[1]? with
  | some a, some b => pure (a, b)
  | _, _ => throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs 2 args"

def arg3 (fnName : String) (raw : Raw.RawInst) : Except String (Val × Val × Val) :=
  match raw.args[0]?, raw.args[1]?, raw.args[2]? with
  | some a, some b, some c => pure (a, b, c)
  | _, _, _ => throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs 3 args"

/-- `std.builtin.AtomicOrder` field name → `AtomicOrder`. -/
def parseOrder (fnName : String) (raw : Raw.RawInst) (field : String) (s : String) :
    Except String AtomicOrder :=
  match s with
  | "unordered" => pure .unordered
  | "monotonic" => pure .monotonic
  | "acquire" => pure .acquire
  | "release" => pure .release
  | "acq_rel" => pure .acqRel
  | "seq_cst" => pure .seqCst
  | _ => throw s!"{fnName}: inst {raw.id}: unknown '{field}' value '{s}'"

/-- `std.builtin.AtomicRmwOp` field name → `RmwOp`. -/
def parseRmwOp (fnName : String) (raw : Raw.RawInst) (s : String) : Except String RmwOp :=
  match s with
  | "Xchg" => pure .xchg
  | "Add" => pure .add
  | "Sub" => pure .sub
  | "And" => pure .and
  | "Nand" => pure .nand
  | "Or" => pure .or
  | "Xor" => pure .xor
  | "Max" => pure .max
  | "Min" => pure .min
  | _ => throw s!"{fnName}: inst {raw.id}: unknown 'op' value '{s}'"

/-- Known compiler-state/effect tags that remain rejected, with their reasons. This classifies
reasons, not support or compiler-version membership; the inventory selects actual enum members. -/
def runtimeTagReasons : Array (Array String × String) := #[
  (#["inferred_alloc", "inferred_alloc_comptime"],
    "unresolved inferred allocation is outside analyzed-AIR translation; inspect the compiler/export stage rather than treating it as alloc"),
  (#["legalize_vec_store_elem", "legalize_vec_elem_val", "legalize_compiler_rt_call"],
    "compiler legalization tags are outside the analyzed-AIR export contract; inspect the exporter hook and profile.export_stage"),
  (#["vector_store_elem"],
    "vector-element memory writes require checked lane bounds and vector-memory semantics outside the model; immutable array element reads are not a substitute"),
  (#["cmp_lt_errors_len", "cmp_lte_errors_len"],
    "error-count comparisons depend on the finalized compiler error universe beyond analyzed-AIR export; do not substitute a currently known error count"),
  (#["runtime_nav_ptr"],
    "runtime TLS/extern navigation pointers require identity and lifetime semantics outside the model; constant global pointers are not a substitute"),
  (#["err_return_trace", "set_err_return_trace", "save_err_return_trace_index"],
    "mutable error-return-trace state is outside the model; profile.error_tracing records configuration, not trace semantics")]

/-- The reason for a tag in `runtimeTagReasons`. -/
def runtimeTagReason? (tag : String) : Option String :=
  (runtimeTagReasons.find? (·.1.contains tag)).map (·.2)

/-- The suffix of every fast-math tag, rejected before decoding. -/
def fastMathSuffix : String := "_optimized"

/-- Reason and guidance for every fast-math (`*_optimized`) tag. -/
def optimizedFloatGuidance : String :=
  "fast-math permits reassociation and value changes the float model does not match; remove @setFloatMode(.optimized) from translated functions"

/-- Reason and guidance (`reason; guidance`) for tags the exporter marks `unsupported`.
`scripts/coverage.py` requires a reason for every such tag of every supported compiler. -/
def exporterTagReasons : Array (Array String × String) := #[
  (#["assembly"],
    "0.14.1 inline-assembly AIR uses a layout the exporter does not decode; translate assembly wrappers with Zig 0.15.2 or 0.16.0 (docs/generated-code.md, Inline asm)"),
  (#["breakpoint"],
    "@breakpoint debugger traps have no modelled effect; remove @breakpoint from translated functions or guard it behind a comptime flag"),
  (#["ret_addr"],
    "@returnAddress exposes machine return addresses outside the memory model; pass any needed identity as an explicit argument"),
  (#["frame_addr"],
    "@frameAddress exposes machine stack addresses outside the memory model; pass any needed identity as an explicit argument"),
  (#["int_from_float_optimized_safe"],
    "checked float-to-int conversion under @setFloatMode(.optimized) is fast-math outside the float model; use the default strict float mode in translated functions"),
  (#["error_set_has_value"],
    "the @errorCast safety check needs the finalized compiler error set beyond analyzed-AIR export; cast to a superset error set or switch on the error explicitly"),
  (#["prefetch"],
    "@prefetch cache hints have no modelled effect; remove @prefetch from translated functions"),
  (#["wasm_memory_size", "wasm_memory_grow"],
    "WebAssembly linear-memory builtins are outside the qualified targets; keep them out of translated functions"),
  (#["addrspace_cast"],
    "@addrSpaceCast between non-generic address spaces is outside the memory model; use generic address-space pointers in translated functions"),
  (#["c_va_arg", "c_va_copy", "c_va_end", "c_va_start"],
    "C variadic argument state is outside the calling-convention model; export fixed-arity functions instead"),
  (#["work_item_id", "work_group_size", "work_group_id"],
    "GPU work-item builtins are outside the qualified targets; keep them out of translated functions")]

/-- The reason for a tag in `exporterTagReasons`. -/
def exporterTagReason? (tag : String) : Option String :=
  (exporterTagReasons.find? (·.1.contains tag)).map (·.2)

/-- Message suffix for a marked tag: its reviewed reason and guidance, if any. -/
def markedTagGuidance (tag : String) : String :=
  if tag.endsWith fastMathSuffix then s!": {optimizedFloatGuidance}"
  else match exporterTagReason? tag with
    | some reason => s!": {reason}"
    | none => ""

/-- A `runtime_nav_ptr` that names its global (the current exporter): `Check.lean` admits it
for a `threadlocal` global only (`docs/generated-code.md` §Thread-local storage). Without the
global, or with the exporter's unsupported marker, it keeps its rejection. -/
def runtimeNavGlobal? (raw : Raw.RawInst) : Option Nat :=
  if raw.tag == "runtime_nav_ptr" && !raw.unsupported then raw.global else none

private def rejectRuntimeTag (fnName : String) (raw : Raw.RawInst) : Except String Unit := do
  if (runtimeNavGlobal? raw).isSome then return
  if let some reason := runtimeTagReason? raw.tag then
    throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}': {reason}"

mutual

/-- The AIR tag table, shared by every supported version. -/
partial def normalizeOp (fnName : String) (raw : Raw.RawInst) : Except String Op := do
  -- Fast-math tags (float ops, `reduce_optimized`, `cmp_vector_optimized`): a specific message.
  -- Most of these the exporter also marks `unsupported`; `reduce_optimized`/`cmp_vector_optimized`
  -- decode fully (same shape as `reduce`/`cmp_vector`) but are rejected here regardless, since
  -- fast-math permits reassociation the model does not claim to match.
  if raw.tag.endsWith fastMathSuffix then
    throw s!"{fnName}: inst {raw.id}: optimized float mode is outside the subset ({raw.tag}): {optimizedFloatGuidance}"
  rejectRuntimeTag fnName raw
  if raw.unsupported then
    throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' is unsupported by the exporter{markedTagGuidance raw.tag}"
  match raw.tag with
  | "arg" =>
    let some p := raw.param
      | throw s!"{fnName}: inst {raw.id}: 'arg' needs 'param'"
    return .arg p
  | "add" | "add_safe" => let (a, b) ← arg2 fnName raw; return .arith .add .checked a b
  | "add_wrap" => let (a, b) ← arg2 fnName raw; return .arith .add .wrap a b
  | "add_sat" => let (a, b) ← arg2 fnName raw; return .arith .add .sat a b
  | "sub" | "sub_safe" => let (a, b) ← arg2 fnName raw; return .arith .sub .checked a b
  | "sub_wrap" => let (a, b) ← arg2 fnName raw; return .arith .sub .wrap a b
  | "sub_sat" => let (a, b) ← arg2 fnName raw; return .arith .sub .sat a b
  | "mul" | "mul_safe" => let (a, b) ← arg2 fnName raw; return .arith .mul .checked a b
  | "mul_wrap" => let (a, b) ← arg2 fnName raw; return .arith .mul .wrap a b
  | "mul_sat" => let (a, b) ← arg2 fnName raw; return .arith .mul .sat a b
  | "div_trunc" => let (a, b) ← arg2 fnName raw; return .div .divTrunc a b
  | "div_floor" => let (a, b) ← arg2 fnName raw; return .div .divFloor a b
  | "div_exact" => let (a, b) ← arg2 fnName raw; return .div .divExact a b
  | "div_float" => let (a, b) ← arg2 fnName raw; return .divFloat a b
  | "rem" => let (a, b) ← arg2 fnName raw; return .div .rem a b
  | "mod" => let (a, b) ← arg2 fnName raw; return .div .mod a b
  | "min" => let (a, b) ← arg2 fnName raw; return .minMax false a b
  | "max" => let (a, b) ← arg2 fnName raw; return .minMax true a b
  | "add_with_overflow" => let (a, b) ← arg2 fnName raw; return .withOverflow .add a b
  | "sub_with_overflow" => let (a, b) ← arg2 fnName raw; return .withOverflow .sub a b
  | "mul_with_overflow" => let (a, b) ← arg2 fnName raw; return .withOverflow .mul a b
  | "shl_with_overflow" => let (a, b) ← arg2 fnName raw true; return .shlWithOverflow a b
  | "clz" => let a ← arg1 fnName raw true; return .countBits .clz a
  | "ctz" => let a ← arg1 fnName raw true; return .countBits .ctz a
  | "popcount" => let a ← arg1 fnName raw true; return .countBits .popcount a
  | "byte_swap" => let a ← arg1 fnName raw true; return .permuteBits .byteSwap a
  | "bit_reverse" => let a ← arg1 fnName raw true; return .permuteBits .bitReverse a
  | "bit_and" => let (a, b) ← arg2 fnName raw; return .bit .and a b
  | "bit_or" => let (a, b) ← arg2 fnName raw; return .bit .or a b
  | "xor" => let (a, b) ← arg2 fnName raw; return .bit .xor a b
  | "not" => let a ← arg1 fnName raw; return .not a
  | "neg" => let a ← arg1 fnName raw; return .neg a
  | "abs" => let a ← arg1 fnName raw; return .abs a
  | "sqrt" => let a ← arg1 fnName raw; return .sqrt a
  | "floor" => let a ← arg1 fnName raw; return .floatRound .floor a
  | "ceil" => let a ← arg1 fnName raw; return .floatRound .ceil a
  | "trunc_float" => let a ← arg1 fnName raw; return .floatRound .trunc a
  | "round" => let a ← arg1 fnName raw; return .floatRound .round a
  | "sin" => let a ← arg1 fnName raw; return .libm .sin a
  | "cos" => let a ← arg1 fnName raw; return .libm .cos a
  | "tan" => let a ← arg1 fnName raw; return .libm .tan a
  | "exp" => let a ← arg1 fnName raw; return .libm .exp a
  | "exp2" => let a ← arg1 fnName raw; return .libm .exp2 a
  | "log" => let a ← arg1 fnName raw; return .libm .log a
  | "log2" => let a ← arg1 fnName raw; return .libm .log2 a
  | "log10" => let a ← arg1 fnName raw; return .libm .log10 a
  | "mul_add" => let (a, b, c) ← arg3 fnName raw; return .mulAdd a b c
  | "fptrunc" | "fpext" => let a ← arg1 fnName raw; return .floatConv a
  | "float_from_int" => let a ← arg1 fnName raw; return .floatFromInt a
  | "int_from_float" => let a ← arg1 fnName raw; return .intFromFloat false a
  | "int_from_float_safe" => let a ← arg1 fnName raw; return .intFromFloat true a
  | "shl" => let (a, b) ← arg2 fnName raw; return .shift .shl a b
  | "shl_exact" => let (a, b) ← arg2 fnName raw; return .shift .shlExact a b
  | "shl_sat" => let (a, b) ← arg2 fnName raw; return .shift .shlSat a b
  | "shr" => let (a, b) ← arg2 fnName raw; return .shift .shr a b
  | "shr_exact" => let (a, b) ← arg2 fnName raw; return .shift .shrExact a b
  | "cmp_lt" => let (a, b) ← arg2 fnName raw; return .cmp .lt a b
  | "cmp_lte" => let (a, b) ← arg2 fnName raw; return .cmp .le a b
  | "cmp_eq" => let (a, b) ← arg2 fnName raw; return .cmp .eq a b
  | "cmp_neq" => let (a, b) ← arg2 fnName raw; return .cmp .ne a b
  | "cmp_gte" => let (a, b) ← arg2 fnName raw; return .cmp .ge a b
  | "cmp_gt" => let (a, b) ← arg2 fnName raw; return .cmp .gt a b
  | "cmp_vector" =>
    let (a, b) ← arg2 fnName raw
    let some opName := raw.op
      | throw s!"{fnName}: inst {raw.id}: 'cmp_vector' needs 'op'"
    let op ← match opName with
      | "lt" => pure .lt | "lte" => pure .le | "eq" => pure .eq
      | "gte" => pure .ge | "gt" => pure .gt | "neq" => pure .ne
      | other => throw s!"{fnName}: inst {raw.id}: unknown compare op '{other}'"
    return .cmp op a b
  | "splat" => let a ← arg1 fnName raw; return .splat a
  | "select" =>
    let (a, b, pred) ← arg3 fnName raw
    return .select pred a b
  | "reduce" =>
    let a ← arg1 fnName raw
    let some opName := raw.op
      | throw s!"{fnName}: inst {raw.id}: 'reduce' needs 'op'"
    let op ← match opName with
      | "And" => pure .and | "Or" => pure .or | "Xor" => pure .xor
      | "Min" => pure .min | "Max" => pure .max | "Add" => pure .add | "Mul" => pure .mul
      | other => throw s!"{fnName}: inst {raw.id}: unknown reduce op '{other}'"
    return .reduce op a
  | "shuffle_one" | "shuffle_two" | "shuffle" =>
    let some a := raw.args[0]?
      | throw s!"{fnName}: inst {raw.id}: '{raw.tag}' needs at least 1 arg"
    return .shuffle a raw.args[1]? raw.mask
  | "bool_and" => let (a, b) ← arg2 fnName raw; return .boolAnd a b
  | "bool_or" => let (a, b) ← arg2 fnName raw; return .boolOr a b
  | "intcast" | "intcast_safe" => let a ← arg1 fnName raw; return .intCast a
  | "trunc" => let a ← arg1 fnName raw; return .trunc a
  | "bitcast" => let a ← arg1 fnName raw; return .bitcast a
  | "is_null" => let a ← arg1 fnName raw; return .isNull a
  | "is_non_null" => let a ← arg1 fnName raw; return .isNonNull a
  | "optional_payload" => let a ← arg1 fnName raw; return .optPayload a
  | "wrap_optional" => let a ← arg1 fnName raw; return .wrapOptional a
  | "is_null_ptr" => let a ← arg1 fnName raw; return .isNullPtr true a
  | "is_non_null_ptr" => let a ← arg1 fnName raw; return .isNullPtr false a
  | "optional_payload_ptr" => let a ← arg1 fnName raw; return .optPayloadPtr false a
  | "optional_payload_ptr_set" => let a ← arg1 fnName raw; return .optPayloadPtr true a
  | "is_err_ptr" => let a ← arg1 fnName raw; return .isErrPtr true a
  | "is_non_err_ptr" => let a ← arg1 fnName raw; return .isErrPtr false a
  | "unwrap_errunion_payload_ptr" => let a ← arg1 fnName raw; return .errPayloadPtr false a
  | "errunion_payload_ptr_set" => let a ← arg1 fnName raw; return .errPayloadPtr true a
  | "unwrap_errunion_err_ptr" => let a ← arg1 fnName raw; return .errCodePtr a
  | "is_err" => let a ← arg1 fnName raw; return .isErr a
  | "is_non_err" => let a ← arg1 fnName raw; return .isNonErr a
  | "unwrap_errunion_payload" => let a ← arg1 fnName raw; return .errPayload a
  | "unwrap_errunion_err" => let a ← arg1 fnName raw; return .errCode a
  | "wrap_errunion_payload" => let a ← arg1 fnName raw; return .wrapErrPayload a
  | "wrap_errunion_err" => let a ← arg1 fnName raw; return .wrapErr a
  | "is_named_enum_value" => let a ← arg1 fnName raw; return .isNamedEnum a
  | "get_union_tag" => let a ← arg1 fnName raw; return .unionTag a
  | "union_init" =>
    let a ← arg1 fnName raw
    let some idx := raw.index
      | throw s!"{fnName}: inst {raw.id}: 'union_init' needs 'index'"
    return .unionInit idx a
  | "alloc" | "ret_ptr" => return .alloc
  | "runtime_nav_ptr" =>
    let some g := runtimeNavGlobal? raw
      | throw s!"{fnName}: inst {raw.id}: 'runtime_nav_ptr' needs 'global'"
    unless raw.args.isEmpty do
      throw s!"{fnName}: inst {raw.id}: 'runtime_nav_ptr' has no args"
    return .runtimeNavPtr g
  | "struct_field_ptr" =>
    let a ← arg1 fnName raw
    let some idx := raw.index
      | throw s!"{fnName}: inst {raw.id}: 'struct_field_ptr' needs 'index'"
    return .fieldPtr a idx
  | "struct_field_ptr_index_0" => let a ← arg1 fnName raw; return .fieldPtr a 0
  | "struct_field_ptr_index_1" => let a ← arg1 fnName raw; return .fieldPtr a 1
  | "struct_field_ptr_index_2" => let a ← arg1 fnName raw; return .fieldPtr a 2
  | "struct_field_ptr_index_3" => let a ← arg1 fnName raw; return .fieldPtr a 3
  | "field_parent_ptr" =>
    let a ← arg1 fnName raw
    let some idx := raw.index
      | throw s!"{fnName}: inst {raw.id}: 'field_parent_ptr' needs 'index'"
    return .fieldParentPtr a idx
  | "set_union_tag" => let (a, b) ← arg2 fnName raw; return .setUnionTag a b
  | "ret_load" => let a ← arg1 fnName raw; return .retLoad a
  | "load" => let a ← arg1 fnName raw; return .load a
  | "store" | "store_safe" => let (a, b) ← arg2 fnName raw; return .store a b
  | "atomic_load" =>
    let a ← arg1 fnName raw
    let some orderS := raw.order
      | throw s!"{fnName}: inst {raw.id}: 'atomic_load' needs 'order'"
    let order ← parseOrder fnName raw "order" orderS
    return .atomicLoad a order
  | "atomic_store_unordered" | "atomic_store_monotonic" | "atomic_store_release"
  | "atomic_store_seq_cst" =>
    let (a, b) ← arg2 fnName raw
    let order ← parseOrder fnName raw "order" ((raw.tag.splitOn "atomic_store_").getLastD "")
    return .atomicStore a b order
  | "atomic_rmw" =>
    let (a, b) ← arg2 fnName raw
    let some rmwOpS := raw.rmwOp
      | throw s!"{fnName}: inst {raw.id}: 'atomic_rmw' needs 'op'"
    let some orderS := raw.order
      | throw s!"{fnName}: inst {raw.id}: 'atomic_rmw' needs 'order'"
    let op ← parseRmwOp fnName raw rmwOpS
    let order ← parseOrder fnName raw "order" orderS
    return .atomicRmw op order a b
  | "cmpxchg_weak" | "cmpxchg_strong" =>
    let (ptr, expected, new) ← arg3 fnName raw
    let some succS := raw.successOrder
      | throw s!"{fnName}: inst {raw.id}: '{raw.tag}' needs 'success_order'"
    let some failS := raw.failureOrder
      | throw s!"{fnName}: inst {raw.id}: '{raw.tag}' needs 'failure_order'"
    let succ ← parseOrder fnName raw "success_order" succS
    let fail ← parseOrder fnName raw "failure_order" failS
    return .cmpxchg (raw.tag == "cmpxchg_weak") ptr expected new succ fail
  | "slice_len" => let a ← arg1 fnName raw; return .sliceLen a
  | "slice_elem_val" => let (a, b) ← arg2 fnName raw; return .sliceElemVal a b
  | "ptr_add" => let (a, b) ← arg2 fnName raw; return .ptrAdd false a b
  | "ptr_sub" => let (a, b) ← arg2 fnName raw; return .ptrAdd true a b
  | "ptr_elem_ptr" | "slice_elem_ptr" => let (a, b) ← arg2 fnName raw; return .elemPtr a b
  | "ptr_elem_val" => let (a, b) ← arg2 fnName raw; return .ptrElemVal a b
  | "array_elem_val" => let (a, b) ← arg2 fnName raw; return .arrayElemVal a b
  | "slice" => let (a, b) ← arg2 fnName raw; return .slice a b
  | "slice_ptr" => let a ← arg1 fnName raw; return .slicePtr a
  | "array_to_slice" => let a ← arg1 fnName raw; return .arrayToSlice a
  | "ptr_slice_len_ptr" => let a ← arg1 fnName raw; return .sliceFieldPtr true a
  | "ptr_slice_ptr_ptr" => let a ← arg1 fnName raw; return .sliceFieldPtr false a
  | "memset" | "memset_safe" => let (a, b) ← arg2 fnName raw; return .memset a b
  | "memcpy" => let (a, b) ← arg2 fnName raw; return .memcpy false a b
  | "memmove" => let (a, b) ← arg2 fnName raw; return .memcpy true a b
  | "tag_name" => let a ← arg1 fnName raw; return .tagName a
  | "error_name" => let a ← arg1 fnName raw; return .errorName a
  | "struct_field_val" =>
    let a ← arg1 fnName raw
    let some idx := raw.index
      | throw s!"{fnName}: inst {raw.id}: 'struct_field_val' needs 'index'"
    return .structFieldVal a idx
  | "aggregate_init" => return .aggregateInit raw.args
  | "block" | "dbg_inline_block" =>
    let body ← raw.body.mapM (normalizeInst fnName)
    return .block body
  | "loop" =>
    let body ← raw.body.mapM (normalizeInst fnName)
    return .loop body
  | "br" =>
    let some target := raw.target
      | throw s!"{fnName}: inst {raw.id}: 'br' needs 'target'"
    let v ← arg1 fnName raw
    return .br target v
  | "repeat" =>
    let some target := raw.target
      | throw s!"{fnName}: inst {raw.id}: 'repeat' needs 'target'"
    return .repeat target
  | "cond_br" =>
    let c ← arg1 fnName raw
    let thenBody ← raw.thenBody.mapM (normalizeInst fnName)
    let elseBody ← raw.elseBody.mapM (normalizeInst fnName)
    return .condBr c thenBody elseBody
  | "switch_br" | "loop_switch_br" =>
    if raw.tag == "loop_switch_br" && raw.args.size != 1 then
      throw s!"{fnName}: inst {raw.id}: loop_switch_br needs exactly 1 arg"
    let v ← arg1 fnName raw
    let cases ← raw.cases.mapM (normalizeCase fnName)
    let elseBody ← raw.elseBody.mapM (normalizeInst fnName)
    return if raw.tag == "loop_switch_br" then .loopSwitchBr v cases elseBody
      else .switchBr v cases elseBody
  | "switch_dispatch" =>
    unless raw.args.size == 1 do
      throw s!"{fnName}: inst {raw.id}: switch_dispatch needs exactly 1 arg"
    let some target := raw.target
      | throw s!"{fnName}: inst {raw.id}: 'switch_dispatch' needs 'target'"
    let v ← arg1 fnName raw
    return .switchDispatch target v
  | "try" | "try_cold" =>
    let v ← arg1 fnName raw
    let errBody ← raw.body.mapM (normalizeInst fnName)
    return .«try» v errBody
  | "try_ptr" | "try_ptr_cold" =>
    unless raw.args.size == 1 do
      throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs exactly 1 arg"
    let p ← arg1 fnName raw
    let errBody ← raw.body.mapM (normalizeInst fnName)
    return .tryPtr p errBody
  | "ret" | "ret_safe" => let v ← arg1 fnName raw; return .ret v
  | "unreach" => return .unreach
  | "trap" => return .trap
  | "dbg_stmt" =>
    let some line := raw.line
      | throw s!"{fnName}: inst {raw.id}: 'dbg_stmt' needs 'line'"
    return .line line
  | "dbg_var_ptr" | "dbg_var_val" | "dbg_arg_inline" | "dbg_empty_stmt" =>
    return .dbg raw.name raw.args[0]?
  | "assembly" =>
    let some a := raw.asm
      | throw s!"{fnName}: inst {raw.id}: 'assembly' needs asm data (schema ≥ 8)"
    let toOperand (o : Raw.RawAsmOperand) : AsmOperand :=
      { constraint := o.constraint, name := o.name, ref := o.ref }
    return .asm a.source a.isVolatile a.clobbers (a.outputs.map toOperand) (a.inputs.map toOperand)
  -- The four call tags differ only in tail-call and inlining hints. Any other `call*` tag
  -- is unknown: a future tag with other semantics fails closed.
  | "call" | "call_always_tail" | "call_never_tail" | "call_never_inline" =>
    let some callee := raw.callee
      | throw s!"{fnName}: inst {raw.id}: '{raw.tag}' needs 'callee'"
    return .call callee raw.args
  -- Fail closed: a tag is decoded only by an explicit arm above (and listed in `decodedTags`).
  | tag => throw s!"{fnName}: inst {raw.id}: unknown AIR tag '{tag}' (not in the tag table)"

partial def normalizeInst (fnName : String) (raw : Raw.RawInst) : Except String Inst := do
  -- The exporter deliberately omits ty for temporary inferred allocations. Preserve
  -- every other missing-ty error while giving these two tags their semantic reason.
  if raw.ty.isNone && (raw.tag == "inferred_alloc" || raw.tag == "inferred_alloc_comptime") then
    rejectRuntimeTag fnName raw
  let some ty := raw.ty
    | throw s!"{fnName}: inst {raw.id}: missing 'ty'"
  let op ← normalizeOp fnName raw
  return { id := raw.id, ty, op }

partial def normalizeCase (fnName : String) (raw : Raw.RawCase) :
    Except String SwitchCase := do
  let body ← raw.body.mapM (normalizeInst fnName)
  return { items := raw.items, ranges := raw.ranges, body }

end

/-- Every tag that `normalizeOp` decodes, in its arm order. `air2lean --print-op-table`
probes each; `tests/roadmap/op-effects` checks this list against `normalizeOp`'s arms. -/
def decodedTags : Array String := #[
  "arg", "add", "add_safe", "add_wrap", "add_sat", "sub", "sub_safe", "sub_wrap", "sub_sat",
  "mul", "mul_safe", "mul_wrap", "mul_sat", "div_trunc", "div_floor", "div_exact", "div_float",
  "rem", "mod", "min", "max", "add_with_overflow", "sub_with_overflow", "mul_with_overflow",
  "shl_with_overflow", "clz", "ctz", "popcount", "byte_swap", "bit_reverse", "bit_and", "bit_or",
  "xor", "not", "neg", "abs", "sqrt", "floor", "ceil", "trunc_float", "round", "sin", "cos",
  "tan", "exp", "exp2", "log", "log2", "log10", "mul_add", "fptrunc", "fpext", "float_from_int",
  "int_from_float", "int_from_float_safe", "shl", "shl_exact", "shl_sat", "shr", "shr_exact",
  "cmp_lt", "cmp_lte", "cmp_eq", "cmp_neq", "cmp_gte", "cmp_gt", "cmp_vector", "splat", "select",
  "reduce", "shuffle_one", "shuffle_two", "shuffle", "bool_and", "bool_or", "intcast",
  "intcast_safe", "trunc", "bitcast", "is_null", "is_non_null", "optional_payload",
  "wrap_optional", "is_null_ptr", "is_non_null_ptr", "optional_payload_ptr",
  "optional_payload_ptr_set", "is_err_ptr", "is_non_err_ptr", "unwrap_errunion_payload_ptr",
  "errunion_payload_ptr_set", "unwrap_errunion_err_ptr", "is_err", "is_non_err",
  "unwrap_errunion_payload", "unwrap_errunion_err", "wrap_errunion_payload", "wrap_errunion_err",
  "is_named_enum_value", "get_union_tag", "union_init", "alloc", "ret_ptr", "runtime_nav_ptr",
  "struct_field_ptr",
  "struct_field_ptr_index_0", "struct_field_ptr_index_1", "struct_field_ptr_index_2",
  "struct_field_ptr_index_3", "field_parent_ptr", "set_union_tag", "ret_load", "load", "store",
  "store_safe", "atomic_load", "atomic_store_unordered", "atomic_store_monotonic",
  "atomic_store_release", "atomic_store_seq_cst", "atomic_rmw", "cmpxchg_weak", "cmpxchg_strong",
  "slice_len", "slice_elem_val", "ptr_add", "ptr_sub", "ptr_elem_ptr", "slice_elem_ptr",
  "ptr_elem_val", "array_elem_val", "slice", "slice_ptr", "array_to_slice", "ptr_slice_len_ptr",
  "ptr_slice_ptr_ptr", "memset", "memset_safe", "memcpy", "memmove", "tag_name", "error_name",
  "struct_field_val", "aggregate_init", "block", "dbg_inline_block", "loop", "br", "repeat",
  "cond_br", "switch_br", "loop_switch_br", "switch_dispatch", "try", "try_cold", "try_ptr",
  "try_ptr_cold", "ret", "ret_safe", "unreach", "trap", "dbg_stmt", "dbg_var_ptr", "dbg_var_val",
  "dbg_arg_inline", "dbg_empty_stmt", "assembly", "call", "call_always_tail", "call_never_tail",
  "call_never_inline"]

def supportedVersions : List String := ["0.16.0", "0.15.2", "0.14.1"]

/-- The layout of a lane pointer `*align(a:0:n:i) T` (`&v[i]` of `@Vector(n, T)`, `T` an integer
or `bool` of `w` bits) as the bit-pointer that `Zig.loadLane`/`Zig.storeLane` take: the
vector's integer of `n * w` bits is its host (`⌈n * w / 8⌉` bytes, LLVM's store size), the lane
is at bit `i * w`. `packedLanes` marks it. Any other lane pointer keeps its layout, which the
checker rejects. -/
def lanePtrLayout (types : Array Ty) (child : TyId) (l : Layout) : Layout :=
  match l.vectorIndex, types[child]? with
  | some lane, some t =>
    let w := match t with | .int _ bits => bits | .bool => 1 | _ => 0
    if w == 0 || l.bitOffset != 0 || lane ≥ l.hostSize then l
    else { l with hostSize := (l.hostSize * w + 7) / 8, bitOffset := lane * w, packedLanes := true }
  | _, _ => l

/-- Tag interpretation after successful canonicalization. Shared by the ordinary
translator and diagnostic path so the rewrites are applied exactly once. -/
def normalizeCanonical (raw : Raw.RawFunc) : Except String Func := do
  unless supportedVersions.contains raw.zigVersion do
    throw s!"{raw.name}: unsupported zig_version '{raw.zigVersion}' (supported: \
      {String.intercalate ", " supportedVersions})"
  let body ← raw.body.mapM (normalizeInst raw.name)
  -- The bit-packed vector layout is the LLVM backend's (`tests/roadmap/vector-layouts`).
  let llvm := raw.profile.backend == "stage2_llvm"
  -- The pointer width is the profile's (`BuildProfile.parse` admits 32 and 64 bits).
  let ptrBytes := raw.profile.pointerBits / 8
  -- A lane pointer into a bit-packed vector (`tests/roadmap/vector-layouts/lanes.zig`) becomes
  -- a bit-pointer into the vector's integer, as LLVM lays it out; checked natively only on
  -- these targets.
  let laneTarget := llvm && ["x86_64", "aarch64"].contains
    ((raw.profile.targetTriple.splitOn "-").headD "")
  let layouts := raw.layouts.mapIdx fun i l =>
    let l := { l with ptrBytes }
    match raw.types[i]? with
    | some (.vector ..) => { l with packedLanes := llvm }
    | some (.ptr "one" _ c) => if laneTarget then lanePtrLayout raw.types c l else l
    | _ => l
  return { zigVersion := raw.zigVersion, name := raw.name, params := raw.params, ret := raw.ret,
           body, types := raw.types, layouts, globals := raw.globals,
           errorSetBits := raw.profile.errorSetBits, backend := raw.profile.backend,
           targetArch := if raw.profile.targetTriple == "unverified" then ""
             else (raw.profile.targetTriple.splitOn "-").headD "",
           bigEndian := raw.profile.endian == "big", identities := raw.identities }

/-- `RawFunc → Func`. Rejects a `zig_version` outside `supportedVersions`. -/
def normalize (raw : Raw.RawFunc) : Except String Func := do
  normalizeCanonical (← Raw.canonicalize raw)

end Air2Lean
