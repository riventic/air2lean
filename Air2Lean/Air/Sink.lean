import Std.Data.HashMap
import Air2Lean.Air.Op

/-!
# Certified canonical rewrites over the decoded IR

The rewrites of canonical AIR that are proved to preserve the formal AIR semantics
(`Air2Lean/Sem.lean`) for every input, once (`Air2Lean/CanonProof.lean`), rather than reviewed
(`Air2Lean/Air/Canon.lean`'s raw rewrites, `docs/air-semantics.md` §Canonicalization). They run
on the decoded `Func`, the datatype of the semantics, after `Raw.canonicalize` and decoding
(`normalizeCanonical`).

* `sinkFunc` (`sinkPastChecks`). Sema forms a pointer before the safety checks that guard it:
  `p[a..b]` is `ptr_add(p, a)`, then the bounds checks (`startGreaterThanEnd`, `outOfBounds`) and,
  for a C pointer, the null check (`unwrapNull`), then `slice`. LLVM's `getelementptr inbounds`
  out of its allocation is poison, illegal behaviour only when used, so the native program panics
  at the check; the model's checked formation (`Zig.ptrProject`) is `.illegal` at once. The pass
  moves a pointer formation (`ptr_add`, `ptr_sub`, `ptr_elem_ptr`, a struct field pointer, a
  pointer-to-pointer `bitcast`) past the safety checks before its first use in its body, to just
  before that use, when only `sinkable` instructions come between: safety checks whose failure
  path cannot fall through, debug instructions, and instructions that neither touch memory nor
  have a nested body (so no call, store, allocation, early exit or loop is skipped, and nothing
  can resize the base's block, which `Mem.inBounds` judges at formation). Chains (`ptr_add` then
  `bitcast`) move together. `Sem.Sink.execFunc_sinkFunc`: the semantics of the result equals
  the semantics of the input, for every function, oracle, argument list and memory.
* `renumberFunc` (`renumber`). Instruction IDs name generated definitions (`<fn>.loop<id>`,
  `.br<id>`), and the debug instructions that a version adds shift them. The pass gives the
  non-debug instructions the IDs `0, 1, …` in body order, then the debug instructions the IDs
  after them. Not yet certified (a renaming; `docs/air-semantics.md` §Canonicalization).
-/

namespace Air2Lean.Sink

theorem sizeOf_toList' {α : Type} [SizeOf α] (a : Array α) : sizeOf a.toList = sizeOf a - 1 := by
  cases a; simp

/-- The instruction IDs a value operand names. -/
def valIds : Val → List InstId
  | .inst id => [id]
  | _ => []

/-- Every value operand of an instruction, nested bodies excluded. -/
def Op.vals : Op → List Val
  | .arg _ | .alloc | .runtimeNavPtr _ | .block _ | .loop _ | .«repeat» _ | .unreach | .trap
  | .line _ => []
  | .arith _ _ a b | .div _ a b | .divFloat a b | .minMax _ a b | .withOverflow _ a b
  | .shlWithOverflow a b | .bit _ a b | .shift _ a b | .cmp _ a b | .boolAnd a b | .boolOr a b
  | .store a b | .atomicStore a b _ | .atomicRmw _ _ a b | .sliceElemVal a b | .ptrAdd _ a b
  | .elemPtr a b | .ptrElemVal a b | .arrayElemVal a b | .slice a b | .memset a b
  | .memcpy _ a b | .setUnionTag a b => [a, b]
  | .countBits _ a | .permuteBits _ a | .splat a | .reduce _ a | .not a | .neg a | .abs a
  | .intCast a | .trunc a | .bitcast a | .floatRound _ a | .sqrt a | .libm _ a | .floatConv a
  | .floatFromInt a | .intFromFloat _ a | .isNull a | .isNonNull a | .optPayload a
  | .wrapOptional a | .isNullPtr _ a | .optPayloadPtr _ a | .isErrPtr _ a | .errPayloadPtr _ a
  | .errCodePtr a | .isErr a | .isNonErr a | .errPayload a | .errCode a | .wrapErrPayload a
  | .wrapErr a | .isNamedEnum a | .unionTag a | .unionInit _ a | .fieldPtr a _
  | .fieldParentPtr a _ | .retLoad a | .load a | .atomicLoad a _ | .sliceLen a | .slicePtr a
  | .arrayToSlice a | .sliceFieldPtr _ a | .tagName a | .errorName a | .structFieldVal a _
  | .br _ a | .condBr a _ _ | .switchDispatch _ a | .«try» a _ | .tryPtr a _ | .ret a => [a]
  | .select a b c | .mulAdd a b c | .cmpxchg _ a b c _ _ => [a, b, c]
  | .shuffle a b mask =>
    a :: b.toList ++ mask.toList.filterMap fun | .value v => some v | _ => none
  | .aggregateInit vs => vs.toList
  | .call callee args => callee :: args.toList
  | .switchBr v cases _ | .loopSwitchBr v cases _ =>
    v :: cases.toList.flatMap fun c => c.items.toList ++ c.ranges.toList.flatMap fun (a, b) => [a, b]
  | .dbg _ v => v.toList
  | .asm _ _ _ outs ins => (outs ++ ins).toList.filterMap (·.ref)

/-- The instruction IDs an instruction reads as operands, nested bodies excluded. -/
def uses (i : Inst) : List InstId := (Op.vals i.op).flatMap valIds

/-- The nested bodies of an instruction, in body order. -/
def Op.bodies : Op → List (Array Inst)
  | .block b | .loop b | .«try» _ b | .tryPtr _ b => [b]
  | .condBr _ t e => [t, e]
  | .switchBr _ cs e | .loopSwitchBr _ cs e => e :: cs.toList.map (·.body)
  | _ => []

mutual

/-- The instruction IDs an instruction reads, nested bodies included. -/
def deepUses : Inst → List InstId
  | ⟨id, ty, op⟩ => uses ⟨id, ty, op⟩ ++ match op with
    | .block b | .loop b | .«try» _ b | .tryPtr _ b => bodyUses b.toList
    | .condBr _ t e => bodyUses t.toList ++ bodyUses e.toList
    | .switchBr _ cs e | .loopSwitchBr _ cs e => bodyUses e.toList ++ casesUses cs.toList
    | _ => []
termination_by i => sizeOf i
decreasing_by all_goals (simp_wf; simp only [sizeOf_toList']; omega)

def bodyUses : List Inst → List InstId
  | [] => []
  | i :: r => deepUses i ++ bodyUses r
termination_by l => sizeOf l

def casesUses : List SwitchCase → List InstId
  | [] => []
  | c :: cs => bodyUses c.body.toList ++ casesUses cs
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals (obtain ⟨items, ranges, body⟩ := c; simp_wf; have := sizeOf_toList' body; omega)

end

/-- A debug instruction (`dbg_stmt`, `dbg_var_*`, `dbg_arg_inline`, `dbg_empty_stmt`). -/
def isDbg (i : Inst) : Bool :=
  match i.op with
  | .line _ | .dbg _ _ => true
  | _ => false

/-- An instruction that leaves its body only by falling through to the next one or by
failing: no nested body, no `br`/`repeat`/`ret`/`switch_dispatch`. -/
def straight (i : Inst) : Bool :=
  match i.op with
  | .block _ | .loop _ | .condBr .. | .switchBr .. | .loopSwitchBr .. | .«try» .. | .tryPtr ..
  | .br .. | .«repeat» _ | .ret _ | .switchDispatch .. => false
  | _ => true

/-- A safety check: `block { cond_br c then { br } else { … } }`, whose `then` body only leaves
the block with `{}` and whose `else` body is straight-line code (`straight`): it fails or panics,
it never reaches the block's end. After it, `c` is true. -/
def isCheck (b : Inst) : Bool :=
  match b.op with
  | .block body =>
    match body.toList with
    | [cb] =>
      match cb.op with
      | .condBr (.inst _) th el =>
        (match th.toList with
          | [br] => match br.op with | .br t .void => t == b.id | _ => false
          | _ => false) &&
        el.toList.all straight
      | _ => false
    | _ => false
  | _ => false

/-- Straight-line code that can neither resize a block nor let another thread do so: no call,
inline assembly, atomic operation, allocation or store. (An allocation and a store do not resize
an existing block either; they stay out until the proof covers them.) -/
def noResize (j : Inst) : Bool :=
  straight j && match j.op with
    | .call .. | .asm .. | .atomicLoad .. | .atomicStore .. | .atomicRmw .. | .cmpxchg ..
    | .alloc | .store .. | .memset .. | .memcpy .. | .setUnionTag .. | .optPayloadPtr true _
    | .errPayloadPtr true _ => false
    | _ => true

/-- `sinkPastChecks` (module doc): an instruction a pointer formation may move past. -/
def sinkable (j : Inst) : Bool := isDbg j || isCheck j || noResize j

/-- The pointer formations of the semantics (`Sem.formVal`): `ptr_add`/`ptr_sub`,
`ptr_elem_ptr`/`slice_elem_ptr`, `struct_field_ptr*`, and a `bitcast` to a pointer. -/
def isFormation (types : Array Ty) (i : Inst) : Bool :=
  match i.op with
  | .ptrAdd .. | .elemPtr .. | .fieldPtr .. => true
  | .bitcast _ => match types[i.ty]? with | some (.ptr ..) => true | _ => false
  | _ => false

/-- The split of `rest` at the first non-debug instruction that reads `x` (nested bodies
included): the instructions before it, and the rest from it on. -/
def splitUse (x : InstId) : List Inst → Option (List Inst × List Inst)
  | [] => none
  | j :: r =>
    if !isDbg j && (deepUses j).contains x then some ([], j :: r)
    else (splitUse x r).map fun (a, b) => (j :: a, b)

/-- A debug instruction of `x` (`dbg_var_val` of the formation): it moves with `x`. -/
def dbgOf (x : InstId) (j : Inst) : Bool := isDbg j && (uses j).contains x

/-- Move the formation `x` past the instructions before its first use in `rest`, if they are
`sinkable`, at least one is a check, and none defines an ID `x` reads or `x`'s own ID (always so
in valid SSA). -/
def insertSink (x : Inst) (rest : List Inst) : List Inst :=
  match splitUse x.id rest with
  | some (mid, post) =>
    if mid.any isCheck && mid.all (fun j => sinkable j && j.id != x.id && !((uses x).contains j.id))
    then mid.filter (!dbgOf x.id ·) ++ x :: mid.filter (dbgOf x.id) ++ post
    else x :: rest
  | none => x :: rest

mutual

/-- `sinkPastChecks` over a body and its nested bodies, last formation first, so that a chain
moves together. `mv`: the formations to move. -/
def sinkList (mv : Inst → Bool) : List Inst → List Inst
  | [] => []
  | i :: rest =>
    let i := sinkInst mv i
    let rest := sinkList mv rest
    if mv i then insertSink i rest else i :: rest
termination_by l => sizeOf l

/-- `sinkList` in the nested bodies of `i`. -/
def sinkInst (mv : Inst → Bool) (i : Inst) : Inst :=
  match i with
  | ⟨id, ty, op⟩ => ⟨id, ty, match op with
    | .block b => .block (sinkList mv b.toList).toArray
    | .loop b => .loop (sinkList mv b.toList).toArray
    | .condBr c t e => .condBr c (sinkList mv t.toList).toArray (sinkList mv e.toList).toArray
    | .switchBr v cs e => .switchBr v (sinkCases mv cs.toList).toArray (sinkList mv e.toList).toArray
    | .loopSwitchBr v cs e =>
      .loopSwitchBr v (sinkCases mv cs.toList).toArray (sinkList mv e.toList).toArray
    | .«try» v b => .«try» v (sinkList mv b.toList).toArray
    | .tryPtr p b => .tryPtr p (sinkList mv b.toList).toArray
    | op => op⟩
termination_by sizeOf i
decreasing_by all_goals (simp_wf; simp only [sizeOf_toList']; omega)

def sinkCases (mv : Inst → Bool) : List SwitchCase → List SwitchCase
  | [] => []
  | c :: cs => { c with body := (sinkList mv c.body.toList).toArray } :: sinkCases mv cs
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals (obtain ⟨items, ranges, body⟩ := c; simp_wf; have := sizeOf_toList' body; omega)

end

/-- The type of every instruction of `f`, nested bodies included. -/
partial def instTypes (f : Func) : Std.HashMap InstId TyId :=
  let rec go (m : Std.HashMap InstId TyId) (b : Array Inst) : Std.HashMap InstId TyId :=
    b.foldl (init := m) fun m i => (Op.bodies i.op).foldl go (m.insert i.id i.ty)
  go {} f.body

/-- `sinkPastChecks` (module doc): the formations it moves are those from a pointer base;
`ptr_elem_ptr` of a slice (`slice_elem_ptr`) stays. -/
def movable (f : Func) (tys : Std.HashMap InstId TyId) (i : Inst) : Bool :=
  let ptrTy (v : Val) : Option Ty :=
    (match v with | .inst id => tys[id]? | _ => none).bind (f.types[·]?)
  isFormation f.types i && match i.op with
    | .elemPtr p _ => match ptrTy p with | some (.ptr size ..) => size != "slice" | _ => false
    | .ptrAdd _ p _ | .fieldPtr p _ | .bitcast p =>
      match ptrTy p with | some (.ptr ..) => true | _ => false
    | _ => false

/-- `sinkPastChecks` (module doc) on a function. -/
def sinkFunc (f : Func) : Func :=
  { f with body := (sinkList (movable f (instTypes f)) f.body.toList).toArray }

/-! ## Renumbering -/

/-- Every instruction of `body`, nested bodies included, in body order (`Raw.flatten`'s order:
an instruction, then its `body`, `then`, `else`, and the cases). -/
partial def flatten (body : Array Inst) : Array Inst :=
  body.foldl (init := #[]) fun acc i =>
    let nested : List (Array Inst) := match i.op with
      | .switchBr _ cs e | .loopSwitchBr _ cs e => e :: cs.toList.map (·.body)
      | op => Op.bodies op
    nested.foldl (fun acc b => acc ++ flatten b) (acc.push i)

/-- `op` with `rv` applied to each value operand and `rt` to each branch target, nested bodies
by `rb`. -/
def Op.mapIds (rv : Val → Val) (rt : InstId → InstId) (rb : Array Inst → Array Inst) : Op → Op
  | .arg k => .arg k
  | .arith o m a b => .arith o m (rv a) (rv b)
  | .div o a b => .div o (rv a) (rv b)
  | .divFloat a b => .divFloat (rv a) (rv b)
  | .minMax x a b => .minMax x (rv a) (rv b)
  | .withOverflow o a b => .withOverflow o (rv a) (rv b)
  | .shlWithOverflow a b => .shlWithOverflow (rv a) (rv b)
  | .countBits o a => .countBits o (rv a)
  | .permuteBits o a => .permuteBits o (rv a)
  | .splat a => .splat (rv a)
  | .select p a b => .select (rv p) (rv a) (rv b)
  | .reduce o a => .reduce o (rv a)
  | .shuffle a b mask => .shuffle (rv a) (b.map rv) mask
  | .bit o a b => .bit o (rv a) (rv b)
  | .not a => .not (rv a)
  | .neg a => .neg (rv a)
  | .abs a => .abs (rv a)
  | .shift o a b => .shift o (rv a) (rv b)
  | .cmp o a b => .cmp o (rv a) (rv b)
  | .boolAnd a b => .boolAnd (rv a) (rv b)
  | .boolOr a b => .boolOr (rv a) (rv b)
  | .intCast a => .intCast (rv a)
  | .trunc a => .trunc (rv a)
  | .bitcast a => .bitcast (rv a)
  | .floatRound o a => .floatRound o (rv a)
  | .sqrt a => .sqrt (rv a)
  | .libm o a => .libm o (rv a)
  | .mulAdd a b c => .mulAdd (rv a) (rv b) (rv c)
  | .floatConv a => .floatConv (rv a)
  | .floatFromInt a => .floatFromInt (rv a)
  | .intFromFloat s a => .intFromFloat s (rv a)
  | .isNull a => .isNull (rv a)
  | .isNonNull a => .isNonNull (rv a)
  | .optPayload a => .optPayload (rv a)
  | .wrapOptional a => .wrapOptional (rv a)
  | .isNullPtr n p => .isNullPtr n (rv p)
  | .optPayloadPtr s p => .optPayloadPtr s (rv p)
  | .isErrPtr e p => .isErrPtr e (rv p)
  | .errPayloadPtr s p => .errPayloadPtr s (rv p)
  | .errCodePtr p => .errCodePtr (rv p)
  | .isErr a => .isErr (rv a)
  | .isNonErr a => .isNonErr (rv a)
  | .errPayload a => .errPayload (rv a)
  | .errCode a => .errCode (rv a)
  | .wrapErrPayload a => .wrapErrPayload (rv a)
  | .wrapErr a => .wrapErr (rv a)
  | .isNamedEnum a => .isNamedEnum (rv a)
  | .unionTag a => .unionTag (rv a)
  | .unionInit k a => .unionInit k (rv a)
  | .alloc => .alloc
  | .runtimeNavPtr g => .runtimeNavPtr g
  | .fieldPtr p k => .fieldPtr (rv p) k
  | .fieldParentPtr p k => .fieldParentPtr (rv p) k
  | .setUnionTag p t => .setUnionTag (rv p) (rv t)
  | .retLoad p => .retLoad (rv p)
  | .load p => .load (rv p)
  | .store p v => .store (rv p) (rv v)
  | .atomicLoad p o => .atomicLoad (rv p) o
  | .atomicStore p v o => .atomicStore (rv p) (rv v) o
  | .atomicRmw o ord p v => .atomicRmw o ord (rv p) (rv v)
  | .cmpxchg w p e n s fl => .cmpxchg w (rv p) (rv e) (rv n) s fl
  | .sliceLen s => .sliceLen (rv s)
  | .sliceElemVal s i => .sliceElemVal (rv s) (rv i)
  | .ptrAdd s p n => .ptrAdd s (rv p) (rv n)
  | .elemPtr p i => .elemPtr (rv p) (rv i)
  | .ptrElemVal p i => .ptrElemVal (rv p) (rv i)
  | .arrayElemVal a i => .arrayElemVal (rv a) (rv i)
  | .slice p n => .slice (rv p) (rv n)
  | .slicePtr s => .slicePtr (rv s)
  | .arrayToSlice p => .arrayToSlice (rv p)
  | .sliceFieldPtr l p => .sliceFieldPtr l (rv p)
  | .memset d v => .memset (rv d) (rv v)
  | .memcpy m d s => .memcpy m (rv d) (rv s)
  | .tagName a => .tagName (rv a)
  | .errorName a => .errorName (rv a)
  | .structFieldVal s k => .structFieldVal (rv s) k
  | .aggregateInit vs => .aggregateInit (vs.map rv)
  | .call c args => .call (rv c) (args.map rv)
  | .block b => .block (rb b)
  | .loop b => .loop (rb b)
  | .br t v => .br (rt t) (rv v)
  | .«repeat» t => .«repeat» (rt t)
  | .condBr c t e => .condBr (rv c) (rb t) (rb e)
  | .switchBr v cs e => .switchBr (rv v) (cs.map (case rv rb)) (rb e)
  | .loopSwitchBr v cs e => .loopSwitchBr (rv v) (cs.map (case rv rb)) (rb e)
  | .switchDispatch t v => .switchDispatch (rt t) (rv v)
  | .«try» v b => .«try» (rv v) (rb b)
  | .tryPtr p b => .tryPtr (rv p) (rb b)
  | .ret v => .ret (rv v)
  | .unreach => .unreach
  | .trap => .trap
  | .line n => .line n
  | .dbg n v => .dbg n (v.map rv)
  | .asm s v cl outs ins =>
    let op (o : AsmOperand) : AsmOperand := { o with ref := o.ref.map rv }
    .asm s v cl (outs.map op) (ins.map op)
where
  case (rv : Val → Val) (rb : Array Inst → Array Inst) (c : SwitchCase) : SwitchCase :=
    { items := c.items.map rv, ranges := c.ranges.map fun (a, b) => (rv a, rv b), body := rb c.body }

/-- `body` with `r` applied to every instruction ID, operand and branch target. -/
partial def renameBody (r : InstId → InstId) (body : Array Inst) : Array Inst :=
  let rv (v : Val) : Val := match v with | .inst id => .inst (r id) | _ => v
  body.map fun i => { id := r i.id, ty := i.ty, op := Op.mapIds rv r (renameBody r) i.op }

/-- `renumber` (module doc). -/
def renumberFunc (f : Func) : Func :=
  let all := flatten f.body
  let order := all.filter (!isDbg ·) ++ all.filter isDbg
  let ids : Std.HashMap InstId InstId :=
    (order.mapIdx fun k i => (i.id, k)).foldl (fun m (a, b) => m.insert a b) {}
  { f with body := renameBody (fun id => ids.getD id id) f.body }

/-- The certified and the reviewed rewrites of the decoded IR, in order. -/
def canonFunc (f : Func) : Func := renumberFunc (sinkFunc f)

end Air2Lean.Sink
