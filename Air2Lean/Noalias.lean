import Std.Data.HashMap
import Air2Lean.Memory

/-!
# `noalias` parameters: the root of every access

Zig lowers a `noalias` parameter to LLVM's `noalias` argument attribute: during the call, memory
accessed through a pointer *based on* the parameter must not also be accessed through a pointer
not based on it, if either access writes (`docs/illegal-behavior.md`). The generated function
checks this at run time (`ZigLean/Mem/Noalias.lean`). This module gives it, for each
instruction, the *root* of its reads and of its writes: the `noalias` parameter that the pointer
of the access is based on, or `none`.

"Based on" follows LLVM: a pointer derived from another (`getelementptr`: field, item, slice
and offset pointers, casts) is based on its base pointer, `@ptrFromInt` on every pointer that
contributes to the integer. So a value is *tainted* by the parameters that its value depends
on through operands, and `other` if it may be based on any other pointer: another parameter, a
global, a local, a call result, a pointer read from memory. A pointer read from memory is never
based on a `noalias` parameter, because the analysis rejects every function in which a tainted
value reaches memory or another function: a store, an atomic or `memset` operand, a call or
asm argument, a copy out of a local that holds one. The return value may be tainted: the scope
ends with the call. Locals that the translation keeps as values (not in memory) carry the
taint of the values stored to them.

An access through a pointer tainted by exactly one parameter has that root; one with no
parameter has `none`; anything else (two parameters, a parameter and another pointer, as in
`if (c) p else q`) is rejected: its root depends on the run. A call has the roots
`(none, none)`: no argument is tainted, so the callee's accesses are based on none of the
parameters. Every function that such a function may call (directly or not) marks its own
accesses with `none` (`calleeMarks`), so a conflict in a callee is found before the callee can
fail in another way. A function with `noalias` parameters that runs concurrently (`Zig.ConcM`)
is rejected by the checker.
-/

namespace Air2Lean.Noalias

/-- The `noalias` parameters that a value may depend on (sorted), and whether it may be based
on another pointer. -/
structure Taint where
  params : Array Nat := #[]
  other : Bool := false
  deriving BEq, Inhabited

def Taint.union (a b : Taint) : Taint :=
  { params := (b.params.foldl (fun acc p => if acc.contains p then acc else acc.push p) a.params).qsort (· < ·)
    other := a.other || b.other }

def Taint.tainted (t : Taint) : Bool := !t.params.isEmpty

def Taint.otherPtr : Taint := { other := true }

/-- The root of an access through a pointer of taint `t`, or an error if it is not one
parameter or none. -/
def Taint.root (t : Taint) : Except String (Option Nat) :=
  match t.params.toList, t.other with
  | [], _ => pure none
  | [p], false => pure (some p)
  | _, _ => throw "the pointer of an access may be based on more than one of a noalias \
      parameter and another pointer"

/-- The roots of the reads and of the writes of each instruction that can touch memory. -/
abbrev Marks := Std.HashMap InstId (Option Nat × Option Nat)

/-- The analysis state: the taint of each instruction's value, and of each local (by `alloc`). -/
structure State where
  vals : Std.HashMap InstId Taint := {}
  slots : Std.HashMap InstId Taint := {}

private def tyOfVal (insts : Std.HashMap InstId Inst) (v : Val) : Option TyId :=
  match v with
  | .inst id => insts[id]?.map (·.ty)
  | v => v.constTy?

/-- A value of type `ty` keeps the `other` flag only if it can hold a pointer, and its
parameters unless it cannot hold an address at all (`bool`, `void`, `noreturn`): an address
can also travel in an optional, error union, aggregate, vector or float (`@bitCast`). -/
private def normalize (types : Array Ty) (ty : TyId) (t : Taint) : Taint :=
  if hasPtr types ty then t
  else match types[ty]? with
    | some .bool | some .void | some .noreturn => {}
    | _ => { t with other := false }

/-- The two states have the same taints. -/
private def State.same (a b : State) : Bool :=
  a.vals.size == b.vals.size && a.slots.size == b.slots.size &&
    a.vals.fold (fun ok k v => ok && b.vals[k]? == some v) true &&
    a.slots.fold (fun ok k v => ok && b.slots[k]? == some v) true

/-- The local (`alloc`) of each place of `f` that the translation keeps as a value. -/
private def locals (f : Func) (insts : Array Inst) : Std.HashMap InstId InstId :=
  let escaping := escapingAllocs f
  (placeRoots insts).foldl (init := {}) fun m (p, r) => if escaping.contains r then m else m.insert p r

/-- `i` can touch memory: a call, an op that only a function using memory has, or an access
outside the locals kept as values. -/
private def touchesMemory (locals : Std.HashMap InstId InstId) (i : Inst) : Bool :=
  i.op.effects.cls == .call || i.op.effects.memoryOnly ||
    i.op.effects.access.any fun (p, _) => match p with
      | .inst id => !locals.contains id
      | _ => true

/-- The marks of a function that a function with `noalias` parameters may call: each
instruction that can touch memory, with the roots `none` (no argument is based on a `noalias`
parameter). Its marks check its accesses against the caller's scope at once. -/
def calleeMarks (f : Func) : Marks :=
  let insts := f.allInsts
  let locals := locals f insts
  insts.foldl (init := {}) fun m i => if touchesMemory locals i then m.insert i.id (none, none) else m

/-- The roots and rejections of `f`, a function with `noalias` parameters. -/
def analyze (f : Func) : Except String Marks := do
  let insts := f.allInsts
  let byId : Std.HashMap InstId Inst := insts.foldl (fun m i => m.insert i.id i) {}
  let locals := locals f insts
  let localOf (v : Val) : Option InstId := match v with
    | .inst id => locals[id]?
    | _ => none
  let isInt (v : Val) : Bool := match (tyOfVal byId v).bind (f.types[·]?) with
    | some (.int ..) => true
    | _ => false
  let taintOf (s : State) (v : Val) : Taint := match v with
    | .inst id => s.vals.getD id {}
    | v => if (v.constTy?.map (hasPtr f.types)).getD false then .otherPtr else {}
  let step (s : State) (i : Inst) : State := Id.run do
    let t := taintOf s
    let union (vs : Array Val) : Taint := vs.foldl (fun acc v => acc.union (t v)) {}
    let mut s := s
    let e := i.op.effects
    let result : Taint := match i.op with
      | .arg idx => if f.noalias.contains idx then { params := #[idx] } else .otherPtr
      | .alloc | .runtimeNavPtr _ | .call .. | .asm .. | .tagName _ | .errorName _
      | .ptrElemVal .. | .sliceElemVal .. | .atomicLoad .. | .atomicRmw .. | .cmpxchg ..
      | .errCodePtr _ => .otherPtr
      | .load p => match localOf p with
        | some a => s.slots.getD a {}
        | none => .otherPtr
      -- A length is not an address.
      | .sliceLen _ => {}
      | .tryPtr p _ | .try p _ => t p
      -- `@ptrFromInt`: based on the pointers of the integer, or on any other.
      | .bitcast p => if isInt p && hasPtr f.types i.ty then (t p).union .otherPtr else t p
      | _ => match e.derives with
        | some p => t p
        | none => union e.values
    s := { s with vals := s.vals.insert i.id ((s.vals.getD i.id {}).union (normalize f.types i.ty result)) }
    -- A block's value is the union of the values that `br` passes to it.
    if let .br target v := i.op then
      if let some b := byId[target]? then
        s := { s with vals := s.vals.insert target ((s.vals.getD target {}).union (normalize f.types b.ty (t v))) }
    -- What a local holds.
    let addSlot (s : State) (p : Val) (v : Taint) : State := match localOf p with
      | some a => { s with slots := s.slots.insert a ((s.slots.getD a {}).union v) }
      | none => s
    match i.op with
    | .store p v | .memset p v => s := addSlot s p (t v)
    | .memcpy _ dst src =>
      s := addSlot s dst (match localOf src with | some a => s.slots.getD a {} | none => .otherPtr)
    | _ => pure ()
    return s
  -- Taints only grow: each round that changes something adds a parameter or `other` to a value
  -- or a local, so the fixpoint comes within that many rounds.
  let mut s : State := {}
  let mut stable := false
  for _ in [0:2 * (insts.size + 1) * (f.noalias.size + 1) + 1] do
    let s' := insts.foldl step s
    if s'.same s then
      stable := true
      break
    s := s'
  unless stable do throw s!"{f.name}: the noalias analysis did not converge"
  let t := taintOf s
  let fail {α : Type} (i : Inst) (what : String) : Except String α :=
    throw s!"{f.name}: inst {i.id}: {what} in a function with noalias parameters is outside the \
      subset (the call's accesses through it would not be checked against its noalias parameters)"
  let mut marks : Marks := {}
  for i in insts do
    -- A tainted value may not reach memory or another function.
    let escapes : Array Val := match i.op with
      | .store p v | .memset p v => if (localOf p).isSome then #[] else #[v]
      | .atomicStore _ v _ | .atomicRmw _ _ _ v => #[v]
      | .cmpxchg _ _ expected new _ _ => #[expected, new]
      | .call callee args => #[callee] ++ args
      | .asm .. => i.op.effects.values
      | _ => #[]
    if escapes.any (t · |>.tainted) then
      fail i "a value based on a noalias parameter that is stored, passed to a call or used by asm"
    if let .memcpy _ dst src := i.op then
      if (localOf dst).isNone && ((localOf src).map (s.slots.getD · {}) |>.getD {}).tainted then
        fail i "a copy of a local that holds a pointer based on a noalias parameter"
    -- `some r`: the root of the instruction's reads (writes); every one must have the same.
    let mut read : Option (Option Nat) := none
    let mut write : Option (Option Nat) := none
    -- A sentinel slicing reads the item at its end through `p` (`Zig.checkSentinelByte`).
    let sentinelRead : Array (Val × Access) := match i.op with
      | .slice p _ => if ((f.layouts[i.ty]?).bind (·.sentinelByte)).isSome then #[(p, .load)] else #[]
      | _ => #[]
    for (p, kind) in i.op.effects.access ++ sentinelRead do
      if (localOf p).isSome then continue
      let r ← match (t p).root with
        | .ok r => pure r
        | .error what => fail i what
      let join (cur : Option (Option Nat)) : Except String (Option (Option Nat)) :=
        if cur.any (· != r) then fail i "accesses with two different noalias roots" else pure (some r)
      if kind matches .load | .atomic then read ← join read
      unless kind matches .load do write ← join write
    -- A store may first read the bytes it writes through the same pointer (a bit-pointer or
    -- vector-lane store reads its host, `Zig.storeBits`): those reads have the write's root. Only
    -- an instruction that can touch memory needs a mark.
    if touchesMemory locals i then marks := marks.insert i.id ((read <|> write).getD none, write.getD none)
  return marks

/-- The rejection of a concurrent function with noalias parameters (`Check.programIssues`; the
emitter fails closed with the same message). -/
def concurrentMsg (name : String) : String :=
  s!"{name}: a concurrent function with noalias parameters is outside the subset"

end Air2Lean.Noalias
