import Air2Lean.Air.Op

/-!
# Subset checker

`check : Func → Except String Unit` rejects anything `Emit.lean` cannot translate:
floats/`other` types, pointer types that are not an `alloc` local or a read-only slice, and
an `alloc` result whose address escapes past `load`/`store`/`dbg`. Errors name the function
and the nearest `dbg_stmt` line.
-/

namespace Air2Lean

/-- Checker state threaded through a function body in program order: `line` is the most
recent `dbg_stmt`'s source line (for error messages), `allocs` is every `alloc` id seen so
far. -/
structure CheckState where
  line : Nat
  allocs : Array InstId

/-- The only pointer shapes in the subset: an `alloc` local (`one`, mutable) or a read-only
slice (`slice`, const). -/
def ptrInSubset (size : String) (isConst : Bool) : Bool :=
  (size == "one" && !isConst) || (size == "slice" && isConst)

/-- Reject floats/`other` and non-alloc/non-const-slice pointers, recursively through struct
fields, array/optional children, and tuple fields. -/
partial def checkTy (fnName : String) (types : Array Ty) (line : Nat) (id : TyId) :
    Except String Unit := do
  let some ty := types[id]?
    | throw s!"{fnName}: near line {line}: unknown type id {id}"
  match ty with
  | .other name =>
    throw s!"{fnName}: near line {line}: type '{name}' is outside the subset (float or \
      otherwise unsupported)"
  | .ptr size isConst child =>
    if ptrInSubset size isConst then checkTy fnName types line child
    else
      throw s!"{fnName}: near line {line}: pointer type (size={size}, const={isConst}) is \
        outside the subset (only an `alloc` local or a read-only slice `[]const T`)"
  | .array _ child => checkTy fnName types line child
  | .optional child =>
    if let some (.ptr ..) := types[child]? then
      throw s!"{fnName}: near line {line}: optional pointer type is outside the subset (only \
        `?T` for a non-pointer T)"
    else checkTy fnName types line child
  | .struct _ _ fields => fields.forM fun (_, fty) => checkTy fnName types line fty
  | .tuple fields => fields.forM (checkTy fnName types line)
  | .int .. | .bool | .void | .noreturn => pure ()

/-- `v` is not the address of an `alloc` seen so far — the escape check. Any other use of an
`alloc`'s id besides the `ptr` operand of `load`/`store` or inside `dbg` goes through here. -/
def checkNotEscaping (fnName : String) (st : CheckState) (ctxId : InstId) (v : Val) :
    Except String Unit :=
  match v with
  | .inst vid =>
    if st.allocs.contains vid then
      throw s!"{fnName}: near line {st.line}: inst {ctxId} uses local {vid}'s address outside \
        load/store/dbg"
    else pure ()
  | _ => pure ()

mutual

partial def checkInst (fnName : String) (types : Array Ty) (st : CheckState) (inst : Inst) :
    Except String CheckState := do
  checkTy fnName types st.line inst.ty
  checkOp fnName types st inst.id inst.op

partial def checkOp (fnName : String) (types : Array Ty) (st : CheckState) (id : InstId)
    (op : Op) : Except String CheckState := do
  let chk1 (v : Val) : Except String Unit := checkNotEscaping fnName st id v
  let chk (vs : Array Val) : Except String Unit := vs.forM chk1
  match op with
  | .arg _ => pure st
  | .arith _ _ a b => chk #[a, b]; pure st
  | .div _ a b => chk #[a, b]; pure st
  | .minMax _ a b => chk #[a, b]; pure st
  | .withOverflow _ a b => chk #[a, b]; pure st
  | .bit _ a b => chk #[a, b]; pure st
  | .not a => chk1 a; pure st
  | .neg a => chk1 a; pure st
  | .shift _ a b => chk #[a, b]; pure st
  | .cmp _ a b => chk #[a, b]; pure st
  | .boolAnd a b => chk #[a, b]; pure st
  | .boolOr a b => chk #[a, b]; pure st
  | .intCast a => chk1 a; pure st
  | .trunc a => chk1 a; pure st
  | .bitcast a => chk1 a; pure st
  | .isNull a => chk1 a; pure st
  | .isNonNull a => chk1 a; pure st
  | .optPayload a => chk1 a; pure st
  | .wrapOptional a => chk1 a; pure st
  | .alloc => pure { st with allocs := st.allocs.push id }
  | .load _ptr => pure st
  | .store _ptr v => chk1 v; pure st
  | .sliceLen s => chk1 s; pure st
  | .sliceElemVal s i => chk #[s, i]; pure st
  | .structFieldVal s _ => chk1 s; pure st
  | .aggregateInit elems => chk elems; pure st
  | .call callee args => chk1 callee; chk args; pure st
  | .block body => checkInsts fnName types st body
  | .loop body => checkInsts fnName types st body
  | .br _target v => chk1 v; pure st
  | .«repeat» _ => pure st
  | .condBr c thenBody elseBody => do
    chk1 c
    let _ ← checkInsts fnName types st thenBody
    let _ ← checkInsts fnName types st elseBody
    pure st
  | .switchBr v cases elseBody => do
    chk1 v
    for c in cases do
      let _ ← checkInsts fnName types st c.body
    let _ ← checkInsts fnName types st elseBody
    pure st
  | .ret v => chk1 v; pure st
  | .unreach => pure st
  | .trap => pure st
  | .line n => pure { st with line := n }
  | .dbg _ _ => pure st

partial def checkInsts (fnName : String) (types : Array Ty) (st : CheckState)
    (insts : Array Inst) : Except String CheckState :=
  insts.foldlM (checkInst fnName types) st

end

/-- Reject anything `Emit.lean` cannot translate: see the module doc. -/
def check (f : Func) : Except String Unit := do
  for p in f.params do
    checkTy f.name f.types 0 p
  checkTy f.name f.types 0 f.ret
  let _ ← checkInsts f.name f.types { line := 0, allocs := #[] } f.body
  pure ()

end Air2Lean
