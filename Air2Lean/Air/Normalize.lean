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

def arg1 (fnName : String) (raw : Raw.RawInst) : Except String Val :=
  match raw.args[0]? with
  | some v => pure v
  | none => throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' needs 1 arg"

def arg2 (fnName : String) (raw : Raw.RawInst) : Except String (Val × Val) :=
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

mutual

/-- The AIR tag table, shared by every supported version. -/
partial def normalizeOp (fnName : String) (raw : Raw.RawInst) : Except String Op := do
  -- Fast-math tags (float ops, `reduce_optimized`, `cmp_vector_optimized`): a specific message.
  -- Most of these the exporter also marks `unsupported`; `reduce_optimized`/`cmp_vector_optimized`
  -- decode fully (same shape as `reduce`/`cmp_vector`) but are rejected here regardless, since
  -- fast-math permits reassociation the model does not claim to match.
  if raw.tag.endsWith "_optimized" then
    throw s!"{fnName}: inst {raw.id}: optimized float mode is outside the subset ({raw.tag})"
  if raw.unsupported then
    throw s!"{fnName}: inst {raw.id}: tag '{raw.tag}' is unsupported by the exporter"
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
  | "memcpy" | "memmove" => let (a, b) ← arg2 fnName raw; return .memcpy a b
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
  | "switch_br" =>
    let v ← arg1 fnName raw
    let cases ← raw.cases.mapM (normalizeCase fnName)
    let elseBody ← raw.elseBody.mapM (normalizeInst fnName)
    return .switchBr v cases elseBody
  | "try" | "try_cold" =>
    let v ← arg1 fnName raw
    let errBody ← raw.body.mapM (normalizeInst fnName)
    return .«try» v errBody
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
  | tag =>
    if tag.startsWith "call" then
      let some callee := raw.callee
        | throw s!"{fnName}: inst {raw.id}: '{tag}' needs 'callee'"
      return .call callee raw.args
    else
      throw s!"{fnName}: inst {raw.id}: unknown AIR tag '{tag}' (not in the tag table)"

partial def normalizeInst (fnName : String) (raw : Raw.RawInst) : Except String Inst := do
  let some ty := raw.ty
    | throw s!"{fnName}: inst {raw.id}: missing 'ty'"
  let op ← normalizeOp fnName raw
  return { id := raw.id, ty, op }

partial def normalizeCase (fnName : String) (raw : Raw.RawCase) :
    Except String SwitchCase := do
  let body ← raw.body.mapM (normalizeInst fnName)
  return { items := raw.items, ranges := raw.ranges, body }

end

def supportedVersions : List String := ["0.16.0", "0.15.2", "0.14.1"]

/-- `RawFunc → Func`. Rejects a `zig_version` outside `supportedVersions`. -/
def normalize (raw : Raw.RawFunc) : Except String Func := do
  let raw := Raw.canonicalize raw
  unless supportedVersions.contains raw.zigVersion do
    throw s!"{raw.name}: unsupported zig_version '{raw.zigVersion}' (supported: \
      {String.intercalate ", " supportedVersions})"
  let body ← raw.body.mapM (normalizeInst raw.name)
  return { zigVersion := raw.zigVersion, name := raw.name, params := raw.params, ret := raw.ret,
           body, types := raw.types, layouts := raw.layouts, globals := raw.globals }

end Air2Lean
