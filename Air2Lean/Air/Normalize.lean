import Air2Lean.Air.Json

/-!
# Per-version normalizer

`normalize : Raw.RawFunc → Except String Func` turns the raw, tag-agnostic JSON mirror
(`Air2Lean/Air/Json.lean`) into the version-independent IR (`Air2Lean/Air/Op.lean`). All
version-specific knowledge — the AIR tag table — lives here. `Check.lean` and `Emit.lean`
never see a `Raw.RawFunc` or a tag string.

To add a Zig version: add a case to `normalize`'s outer `match`, and a tag table that calls
`normalizeOp_0_15_2` for tags that did not change (`PLAN.md` §Zig version support).
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

mutual

/-- The 0.15.2 AIR tag table. -/
partial def normalizeOp_0_15_2 (fnName : String) (raw : Raw.RawInst) : Except String Op := do
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
  | "bool_and" => let (a, b) ← arg2 fnName raw; return .boolAnd a b
  | "bool_or" => let (a, b) ← arg2 fnName raw; return .boolOr a b
  | "intcast" | "intcast_safe" => let a ← arg1 fnName raw; return .intCast a
  | "trunc" => let a ← arg1 fnName raw; return .trunc a
  | "bitcast" => let a ← arg1 fnName raw; return .bitcast a
  | "is_null" => let a ← arg1 fnName raw; return .isNull a
  | "is_non_null" => let a ← arg1 fnName raw; return .isNonNull a
  | "optional_payload" => let a ← arg1 fnName raw; return .optPayload a
  | "wrap_optional" => let a ← arg1 fnName raw; return .wrapOptional a
  | "is_err" => let a ← arg1 fnName raw; return .isErr a
  | "is_non_err" => let a ← arg1 fnName raw; return .isNonErr a
  | "unwrap_errunion_payload" => let a ← arg1 fnName raw; return .errPayload a
  | "unwrap_errunion_err" => let a ← arg1 fnName raw; return .errCode a
  | "wrap_errunion_payload" => let a ← arg1 fnName raw; return .wrapErrPayload a
  | "wrap_errunion_err" => let a ← arg1 fnName raw; return .wrapErr a
  | "alloc" => return .alloc
  | "load" => let a ← arg1 fnName raw; return .load a
  | "store" | "store_safe" => let (a, b) ← arg2 fnName raw; return .store a b
  | "slice_len" => let a ← arg1 fnName raw; return .sliceLen a
  | "slice_elem_val" => let (a, b) ← arg2 fnName raw; return .sliceElemVal a b
  | "struct_field_val" =>
    let a ← arg1 fnName raw
    let some idx := raw.index
      | throw s!"{fnName}: inst {raw.id}: 'struct_field_val' needs 'index'"
    return .structFieldVal a idx
  | "aggregate_init" => return .aggregateInit raw.args
  | "block" | "dbg_inline_block" =>
    let body ← raw.body.mapM (normalizeInst_0_15_2 fnName)
    return .block body
  | "loop" =>
    let body ← raw.body.mapM (normalizeInst_0_15_2 fnName)
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
    let thenBody ← raw.thenBody.mapM (normalizeInst_0_15_2 fnName)
    let elseBody ← raw.elseBody.mapM (normalizeInst_0_15_2 fnName)
    return .condBr c thenBody elseBody
  | "switch_br" =>
    let v ← arg1 fnName raw
    let cases ← raw.cases.mapM (normalizeCase_0_15_2 fnName)
    let elseBody ← raw.elseBody.mapM (normalizeInst_0_15_2 fnName)
    return .switchBr v cases elseBody
  | "try" | "try_cold" =>
    let v ← arg1 fnName raw
    let errBody ← raw.body.mapM (normalizeInst_0_15_2 fnName)
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
  | tag =>
    if tag.startsWith "call" then
      let some callee := raw.callee
        | throw s!"{fnName}: inst {raw.id}: '{tag}' needs 'callee'"
      return .call callee raw.args
    else
      throw s!"{fnName}: inst {raw.id}: unknown AIR tag '{tag}' (0.15.2 tag table)"

partial def normalizeInst_0_15_2 (fnName : String) (raw : Raw.RawInst) : Except String Inst := do
  let some ty := raw.ty
    | throw s!"{fnName}: inst {raw.id}: missing 'ty'"
  let op ← normalizeOp_0_15_2 fnName raw
  return { id := raw.id, ty, op }

partial def normalizeCase_0_15_2 (fnName : String) (raw : Raw.RawCase) :
    Except String SwitchCase := do
  let body ← raw.body.mapM (normalizeInst_0_15_2 fnName)
  return { items := raw.items, ranges := raw.ranges, body }

end

def supportedVersions : List String := ["0.15.2", "0.14.1"]

/-- `RawFunc → Func`, dispatching on `zig_version`. -/
def normalize (raw : Raw.RawFunc) : Except String Func := do
  match raw.zigVersion with
  -- 0.14.1 has no subset tag that differs from 0.15.2 (`zig-patch/0.14.1/TAGS.md`), so it
  -- uses the same table.
  | "0.15.2" | "0.14.1" =>
    let body ← raw.body.mapM (normalizeInst_0_15_2 raw.name)
    return { zigVersion := raw.zigVersion, name := raw.name, params := raw.params, ret := raw.ret,
             body, types := raw.types }
  | v =>
    throw s!"{raw.name}: unsupported zig_version '{v}' (supported: \
      {String.intercalate ", " supportedVersions})"

end Air2Lean
