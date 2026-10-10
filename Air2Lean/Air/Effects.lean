import Air2Lean.Air.Op
import Air2Lean.StdModels

/-!
# Op effects

`Op.effects` is the one classifier of every `Op` constructor: its operands, the memory it
accesses through pointer operands, the pointer its result is derived from, whether it needs the
memory model, and its control flow. It has no wildcard arm, so a new `Op` constructor does not
compile until it is classified here.

The safety analyses read these facts instead of matching on `Op` with a default arm: the
volatile check (`CheckCtx.checkVolatile`), the try-error and block summaries
(`summarizeTryErrors`), place and escape analysis (`placeOperands`, `ptrOperands`), memory and
sync detection (`memoryOp`, `Func.syncLocally`, `Func.usesMemoryLocally`), nested bodies
(`flattenOp`, `bodyLists`) and the emitter's terminator split (`isTerminating`). An analysis
that still matches on `Op` lists the ops it treats specially; its default must be harmless for
every op (documented at the arm), or fail closed.

`air2lean --print-op-table` prints the tag → constructor → effect class → emitter route table
(`Air2Lean/OpTable.lean`) that `scripts/coverage.py` reads.
-/

namespace Air2Lean

/-- The op table's effect class of an op (`air2lean --print-op-table`). Descriptive: the
analyses read the `Effects` fields, not the class. -/
inductive EffectClass where
  /-- A value computed from value operands only. -/
  | value
  /-- A local (`alloc`, `ret_ptr`): a place. -/
  | «local»
  /-- A pointer derived from a pointer operand, without an access. -/
  | address
  /-- Reads memory through a pointer operand. -/
  | read
  /-- Writes memory through a pointer operand. -/
  | write
  /-- Reads one pointer operand and writes another (`memcpy`). -/
  | readWrite
  /-- An atomic access: a sync op. -/
  | atomic
  /-- Inline assembly: opaque, volatile-capable, may store through its output operands. -/
  | asm
  | call
  /-- Structured control flow, a branch or a return. -/
  | control
  /-- Ends the program (`unreach`, `trap`). -/
  | noreturn
  /-- No effect; source information only. -/
  | debug
  deriving Repr, BEq, Inhabited

def EffectClass.name : EffectClass → String
  | .value => "value"
  | .local => "local"
  | .address => "address"
  | .read => "read"
  | .write => "write"
  | .readWrite => "read-write"
  | .atomic => "atomic"
  | .asm => "asm"
  | .call => "call"
  | .control => "control"
  | .noreturn => "noreturn"
  | .debug => "debug"

/-- A memory access through a pointer operand. Every kind is volatile-capable: a volatile
pointer makes it a device effect (`CheckCtx.checkVolatile`). -/
inductive Access where
  | load
  | store
  | atomic
  /-- A store through an asm output operand. -/
  | asmStore
  deriving Repr, BEq, Inhabited

/-- The word in a volatile-access diagnostic. -/
def Access.describe : Access → String
  | .load => "load"
  | .store => "store"
  | .atomic => "atomic access"
  | .asmStore => "asm output store"

/-- Where control goes after an op. -/
inductive Control where
  /-- The next instruction. -/
  | next
  /-- Leaves the function: `ret`, `ret_load`, `unreach`, `trap`, a noreturn call. -/
  | exit
  /-- Leaves the enclosing block `target`. -/
  | br (target : InstId)
  /-- Back to the loop `target`. -/
  | «repeat» (target : InstId)
  /-- Back to the loop-switch `target` with a new selector. -/
  | dispatch (target : InstId)
  /-- Runs `body`; the next instruction runs after a `br` to the block. -/
  | block (body : Array Inst)
  /-- Repeats until a body leaves it: `loop`, `loop_switch_br` (its case bodies, then `else`). -/
  | loop (bodies : Array (Array Inst))
  /-- Runs one of `bodies`, each ending the instruction sequence: `cond_br` (then, else),
  `switch_br` (case bodies, then `else`). -/
  | branch (bodies : Array (Array Inst))
  /-- `try`, `try_ptr`: runs `errBody` on an error; otherwise the next instruction. -/
  | «try» (errBody : Array Inst)

/-- The nested instruction bodies, in body order. -/
def Control.bodies : Control → Array (Array Inst)
  | .next | .exit | .br _ | .repeat _ | .dispatch _ => #[]
  | .block body | .try body => #[body]
  | .loop bodies | .branch bodies => bodies

/-- The enclosing block, loop or loop-switch that a jump leaves to. -/
def Control.jumpTarget? : Control → Option InstId
  | .br t | .repeat t | .dispatch t => some t
  | .next | .exit | .block _ | .loop _ | .branch _ | .try _ => none

/-- The effects of one op. Every field is explicit in every `Op.effects` arm's helper: there
are no defaults to inherit silently. -/
structure Effects where
  cls : EffectClass
  /-- The operands read as values (`valueOperands`). -/
  values : Array Val
  /-- The pointer operands used as places, not as values: the pointer of `load`, `store`,
  `struct_field_ptr`, `field_parent_ptr`, `ret_load`, `ptr_slice_*_ptr`, `bitcast`,
  `set_union_tag`, an atomic op, and the asm output operands. -/
  places : Array Val
  /-- Operands that only debug information names (`dbg_var_*`). -/
  debug : Array Val
  /-- Memory accessed through pointer operands. -/
  access : Array (Val × Access)
  /-- The pointer operand whose provenance (and `volatile` qualifier) the result carries. -/
  derives : Option Val
  /-- Only a function that uses memory has this op (`memoryOp`). -/
  memoryOnly : Bool
  /-- A sync op: a concurrent function has it (`Func.syncLocally`). -/
  sync : Bool
  control : Control

/-- A value computation that reads only `values`. -/
def Effects.pure (values : Array Val) : Effects :=
  { cls := .value, values, places := #[], debug := #[], access := #[], derives := none,
    memoryOnly := false, sync := false, control := .next }

/-- A pointer derived from `ptr` (a value operand) without an access. -/
def Effects.address (ptr : Val) (values : Array Val) (memoryOnly : Bool) : Effects :=
  { Effects.pure values with cls := .address, derives := some ptr, memoryOnly }

/-- A place projection: the pointer `ptr` is a place operand, not a value. -/
def Effects.projection (cls : EffectClass) (ptr : Val) (memoryOnly : Bool) : Effects :=
  { Effects.pure #[] with cls, places := #[ptr], derives := some ptr, memoryOnly }

/-- An access of kind `kind` through the place operand `ptr`, reading `values`. -/
def Effects.placeAccess (cls : EffectClass) (ptr : Val) (kind : Access) (values : Array Val) :
    Effects :=
  { Effects.pure values with cls, places := #[ptr], access := #[(ptr, kind)] }

/-- An access through `ptr`, a value operand (an item pointer, a slice, an optional or error
union pointer). -/
def Effects.valueAccess (cls : EffectClass) (access : Array (Val × Access)) (values : Array Val)
    (memoryOnly : Bool) : Effects :=
  { Effects.pure values with cls, access, memoryOnly }

/-- An atomic access through the place operand `ptr`. -/
def Effects.atomicAccess (ptr : Val) (values : Array Val) : Effects :=
  { Effects.pure values with
    cls := .atomic, places := #[ptr], access := #[(ptr, .atomic)], memoryOnly := true
    sync := true }

/-- Control flow reading `values`. -/
def Effects.flow (cls : EffectClass) (control : Control) (values : Array Val) : Effects :=
  { Effects.pure values with cls, control }

/-- Audited operand-free spin instructions emitted by `std.atomic.spinLoopHint` on
x86/x86_64 (and RISC-V with Zihintpause) and aarch64. Exact volatile instructions only:
other assembly keeps its opaque semantics. This is an extra scheduling opportunity, not a
memory fence or progress premise (`docs/progress-hints.md`). -/
def Op.isSpinHint : Op → Bool
  | .asm source true clobbers outputs inputs =>
    (source == "pause" || source == "isb") && clobbers.isEmpty && outputs.isEmpty && inputs.isEmpty
  | _ => false  -- keep: only `asm` can be a spin hint

/-- The switch selector and every case item and range bound, in order. -/
private def switchValues (v : Val) (cases : Array SwitchCase) : Array Val :=
  #[v] ++ cases.foldl (fun acc c =>
    let acc := c.items.foldl Array.push acc
    c.ranges.foldl (fun acc (lo, hi) => (acc.push lo).push hi) acc) #[]

/-- The case bodies, then the `else` body. -/
private def switchBodies (cases : Array SwitchCase) (elseBody : Array Inst) : Array (Array Inst) :=
  cases.map (·.body) ++ #[elseBody]

/-- The classifier (module doc). No wildcard arm: classify every new constructor here. -/
def Op.effects (op : Op) : Effects :=
  match op with
  | .arg _ => .pure #[]
  | .arith _ _ a b | .div _ a b | .divFloat a b | .minMax _ a b | .withOverflow _ a b
  | .shlWithOverflow a b | .bit _ a b | .shift _ a b | .cmp _ a b | .boolAnd a b | .boolOr a b
  | .arrayElemVal a b => .pure #[a, b]
  | .countBits _ a | .permuteBits _ a | .not a | .neg a | .abs a | .intCast a | .trunc a
  | .floatRound _ a | .sqrt a | .libm _ a | .floatConv a | .floatFromInt a | .intFromFloat _ a
  | .isNull a | .isNonNull a | .optPayload a | .isErr a | .isNonErr a | .errPayload a
  | .errCode a | .wrapErrPayload a | .wrapErr a | .isNamedEnum a | .unionTag a | .unionInit _ a
  | .splat a | .reduce _ a | .sliceLen a | .structFieldVal a _ => .pure #[a]
  | .mulAdd a b c => .pure #[a, b, c]
  | .select pred a b => .pure #[pred, a, b]
  | .shuffle a b mask =>
    .pure (#[a] ++ b.toArray ++ mask.filterMap fun l => match l with | .value v => some v | _ => none)
  | .aggregateInit elems => .pure elems
  -- `?*T` from `*T`: the optional carries the pointer and its qualifiers.
  | .wrapOptional p => { Effects.pure #[p] with derives := some p }
  -- The name tables are in memory.
  | .tagName a | .errorName a => { Effects.pure #[a] with memoryOnly := true }
  -- A place has no optional-payload or error-union path: the local becomes a stack block.
  | .isNullPtr _ p | .isErrPtr _ p | .errCodePtr p => .valueAccess .read #[(p, .load)] #[p] false
  | .optPayloadPtr set p | .errPayloadPtr set p =>
    { Effects.address p #[p] false with
      cls := if set then .write else .address
      access := if set then #[(p, .store)] else #[] }
  | .alloc => { Effects.pure #[] with cls := .local }
  -- The current thread's instance of a `threadlocal` global: an address in memory.
  | .runtimeNavPtr _ => { Effects.pure #[] with cls := .address, memoryOnly := true }
  | .bitcast p => .projection .value p false
  | .fieldPtr p _ | .fieldParentPtr p _ => .projection .address p false
  | .sliceFieldPtr _ p => .projection .address p true
  | .ptrAdd _ p n | .elemPtr p n | .slice p n => .address p #[p, n] true
  | .slicePtr p | .arrayToSlice p => .address p #[p] true
  | .load p => .placeAccess .read p .load #[]
  | .retLoad p => { Effects.placeAccess .control p .load #[] with control := .exit }
  | .store p v => .placeAccess .write p .store #[v]
  | .setUnionTag p tag => .placeAccess .write p .store #[tag]
  | .atomicLoad p _ => .atomicAccess p #[]
  | .atomicStore p v _ | .atomicRmw _ _ p v => .atomicAccess p #[v]
  | .cmpxchg _ p expected new _ _ => .atomicAccess p #[expected, new]
  | .ptrElemVal p i => .valueAccess .read #[(p, .load)] #[p, i] true
  | .sliceElemVal s i => .valueAccess .read #[(s, .load)] #[s, i] false
  | .memset dst v => .valueAccess .write #[(dst, .store)] #[dst, v] true
  | .memcpy _ dst src => .valueAccess .readWrite #[(dst, .store), (src, .load)] #[dst, src] true
  | .call callee args =>
    let (memoryOnly, sync, control) := match callee with
      | .func name noreturn .. =>
        (modelledStdFn name, (threadFn? name).isSome, if noreturn then Control.exit else .next)
      | _ => (false, false, .next)
    { Effects.pure (#[callee] ++ args) with cls := .call, memoryOnly, sync, control }
  | .block body => .flow .control (.block body) #[]
  | .loop body => .flow .control (.loop #[body]) #[]
  | .br target v => .flow .control (.br target) #[v]
  | .«repeat» target => .flow .control (.repeat target) #[]
  | .condBr c t e => .flow .control (.branch #[t, e]) #[c]
  | .switchBr v cases e => .flow .control (.branch (switchBodies cases e)) (switchValues v cases)
  | .loopSwitchBr v cases e => .flow .control (.loop (switchBodies cases e)) (switchValues v cases)
  | .switchDispatch target v => .flow .control (.dispatch target) #[v]
  | .«try» v errBody => .flow .control (.try errBody) #[v]
  | .tryPtr p errBody =>
    { Effects.flow .control (.try errBody) #[p] with access := #[(p, .load)], memoryOnly := true }
  | .ret v => .flow .control .exit #[v]
  | .unreach | .trap => .flow .noreturn .exit #[]
  -- `@returnAddress` reads the oracle in `Zig.Mem` (`Zig.returnAddress`).
  | .retAddr => { Effects.pure #[] with memoryOnly := true }
  | .line _ => { Effects.pure #[] with cls := .debug }
  | .dbg _ v => { Effects.pure #[] with cls := .debug, debug := v.toArray }
  -- Only the inputs are read as values (like `call`'s args); an output's `ref` (if present) is
  -- a place the result stores to, like `store`'s pointer operand.
  | .asm _ _ _ outputs inputs =>
    let refs := outputs.filterMap (·.ref)
    { Effects.pure (inputs.filterMap (·.ref)) with
      cls := .asm, places := refs, access := refs.map (·, .asmStore)
      memoryOnly := op.isSpinHint, sync := op.isSpinHint }

/-- How `Emit.lean`'s `emitStmts` emits an op: the op table's emitter column. -/
inductive EmitRoute where
  /-- Ends its body (`emitTerminator`): a jump, a branch or an exit. -/
  | terminator
  /-- A nested body that `emitStmts` emits: `block`, `loop`, `loop_switch_br`, `try`. -/
  | structured
  /-- One binding or statement (`emitSimple`). -/
  | straightLine
  /-- No output: debug information. -/
  | erased
  deriving Repr, BEq, Inhabited

def EmitRoute.name : EmitRoute → String
  | .terminator => "terminator"
  | .structured => "structured"
  | .straightLine => "straight-line"
  | .erased => "erased"

def Op.emitRoute (op : Op) : EmitRoute :=
  let e := op.effects
  match e.control with
  | .exit | .br _ | .repeat _ | .dispatch _ | .branch _ => .terminator
  | .block _ | .loop _ | .try _ => .structured
  | .next => if e.cls == .debug then .erased else .straightLine

/-- The op table's name of a constructor (`air2lean --print-op-table`): the Lean constructor
name, which `scripts/coverage.py` looks up in `ZigLean` and `Proofs`. No wildcard arm. -/
def Op.ctorName : Op → String
  | .arg .. => "arg" | .arith .. => "arith" | .div .. => "div" | .divFloat .. => "divFloat"
  | .minMax .. => "minMax" | .withOverflow .. => "withOverflow"
  | .shlWithOverflow .. => "shlWithOverflow" | .countBits .. => "countBits"
  | .permuteBits .. => "permuteBits" | .splat .. => "splat" | .select .. => "select"
  | .reduce .. => "reduce" | .shuffle .. => "shuffle" | .bit .. => "bit" | .not .. => "not"
  | .neg .. => "neg" | .abs .. => "abs" | .shift .. => "shift" | .cmp .. => "cmp"
  | .boolAnd .. => "boolAnd" | .boolOr .. => "boolOr" | .intCast .. => "intCast"
  | .trunc .. => "trunc" | .bitcast .. => "bitcast" | .floatRound .. => "floatRound"
  | .sqrt .. => "sqrt" | .libm .. => "libm" | .mulAdd .. => "mulAdd" | .floatConv .. => "floatConv"
  | .floatFromInt .. => "floatFromInt" | .intFromFloat .. => "intFromFloat" | .isNull .. => "isNull"
  | .isNonNull .. => "isNonNull" | .optPayload .. => "optPayload"
  | .wrapOptional .. => "wrapOptional" | .isNullPtr .. => "isNullPtr"
  | .optPayloadPtr .. => "optPayloadPtr" | .isErrPtr .. => "isErrPtr"
  | .errPayloadPtr .. => "errPayloadPtr" | .errCodePtr .. => "errCodePtr" | .isErr .. => "isErr"
  | .isNonErr .. => "isNonErr" | .errPayload .. => "errPayload" | .errCode .. => "errCode"
  | .wrapErrPayload .. => "wrapErrPayload" | .wrapErr .. => "wrapErr"
  | .isNamedEnum .. => "isNamedEnum" | .unionTag .. => "unionTag" | .unionInit .. => "unionInit"
  | .alloc => "alloc" | .runtimeNavPtr .. => "runtimeNavPtr" | .fieldPtr .. => "fieldPtr"
  | .fieldParentPtr .. => "fieldParentPtr"
  | .setUnionTag .. => "setUnionTag" | .retLoad .. => "retLoad" | .load .. => "load"
  | .store .. => "store" | .atomicLoad .. => "atomicLoad" | .atomicStore .. => "atomicStore"
  | .atomicRmw .. => "atomicRmw" | .cmpxchg .. => "cmpxchg" | .sliceLen .. => "sliceLen"
  | .sliceElemVal .. => "sliceElemVal" | .ptrAdd .. => "ptrAdd" | .elemPtr .. => "elemPtr"
  | .ptrElemVal .. => "ptrElemVal" | .arrayElemVal .. => "arrayElemVal" | .slice .. => "slice"
  | .slicePtr .. => "slicePtr" | .arrayToSlice .. => "arrayToSlice"
  | .sliceFieldPtr .. => "sliceFieldPtr" | .memset .. => "memset" | .memcpy .. => "memcpy"
  | .tagName .. => "tagName" | .errorName .. => "errorName"
  | .structFieldVal .. => "structFieldVal" | .aggregateInit .. => "aggregateInit"
  | .call .. => "call" | .block .. => "block" | .loop .. => "loop" | .br .. => "br"
  | .«repeat» .. => "repeat" | .condBr .. => "condBr" | .switchBr .. => "switchBr"
  | .loopSwitchBr .. => "loopSwitchBr" | .switchDispatch .. => "switchDispatch"
  | .«try» .. => "try" | .tryPtr .. => "tryPtr" | .ret .. => "ret" | .unreach => "unreach"
  | .trap => "trap" | .line .. => "line" | .dbg .. => "dbg" | .asm .. => "asm"
  | .retAddr => "retAddr"

end Air2Lean
