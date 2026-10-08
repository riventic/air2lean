import ZigLean.Basic
import Air2Lean.Air.Op
import Air2Lean.SemAttr

/-!
# Formal semantics of canonical AIR (fragment)

A definitional interpreter for the decoded, canonical AIR that the translator reads
(`Air2Lean.Func`, the output of `Air2Lean.normalize`). It is stated over the translator's own
input datatypes, not over the generated Lean, so a theorem relating the two is a statement
about the translation (`docs/air-semantics.md`).

The fragment:

* values: integers of any width with their signedness, `bool`, `void`, and a pointer to a
  function-local cell (`alloc`);
* integer arithmetic (`add`/`sub`/`mul` checked, wrapping and saturating; division and
  remainder; `min`/`max`; bitwise `and`/`or`/`xor`/`not`), comparisons, `bool_and`/`bool_or`,
  `intcast` and `trunc`;
* control flow: `block`/`br`, `cond_br`, `switch_br` on an integer, `loop`/`repeat`, `ret`,
  `unreach`, `trap`, and a call to a safety-panic handler;
* locals: `alloc`, then whole-value `load`/`store` through the cell pointer;
* direct calls through an oracle (`Ctx.call`); `runFn` ties the oracle to the program;
* debug instructions have no effect.

Every other instruction, value or shape is *stuck*: it denotes `⊥` (no behaviour, `Option`'s
`none`). The arithmetic primitives are ZigLean's (`Zig.add`, `Zig.intCast`, …): this file fixes
the meaning of the AIR *program structure* (SSA dataflow, operand typing, control flow, locals,
calls) over those primitives. The primitives' own fidelity to Zig is a separate premise
(`docs/air-semantics.md` §Trusted base).

Locals are value cells, not `Zig.Mem` bytes: a fragment local is only allocated, stored and
loaded as a whole value through its own pointer, never escaping. `docs/air-semantics.md`
§Gap states what a byte-level (`Zig.Mem`) refinement would add.
-/

namespace Air2Lean.Sem

open Zig

/-- A runtime value of the fragment. An integer carries its AIR signedness and width. -/
inductive Value where
  | int (signed : Bool) (w : Nat) (v : BitVec w)
  | bool (b : Bool)
  | void
  /-- The pointer to the cell of the local that `alloc` instruction `id` created. -/
  | cell (id : InstId)
  deriving DecidableEq, Inhabited

/-- No behaviour: an ill-typed or out-of-fragment step. Distinct from every panic
(`Zig.Error`): it is `Option`'s `none`, the bottom of `Zig.Result`'s order. -/
def stuck {α : Type} : Result α := ExceptT.mk none

/-- SSA environment: the value of each instruction that has run. -/
abbrev Env := InstId → Option Value

/-- Local cells, keyed by their `alloc` instruction. `none`: not allocated or not yet written. -/
abbrev Store := InstId → Option Value

def Env.set (env : Env) (id : InstId) (v : Value) : Env :=
  fun j => if j = id then some v else env j

/-- How a body ends: `br` to a block (with its value), `repeat` of a loop, or `ret`. -/
inductive Exit where
  | br (target : InstId) (v : Value)
  | rep (target : InstId)
  | ret (v : Value)
  deriving DecidableEq, Inhabited

/-- Everything a body needs besides its environment: the function (its type table) and a
call oracle for direct calls by fully qualified name. -/
structure Ctx where
  func : Func
  /-- The runtime arguments, in parameter order. -/
  args : List Value
  call : String → List Value → Result Value

def tyOf (f : Func) (t : TyId) : Ty := f.types[t]?.getD .void

/-- A constant of an integer type as the bit vector the generated code writes:
`n` for `n ≥ 0`, `-(|n|)` otherwise (both equal `BitVec.ofInt w n`, `litBV_eq_ofInt`). -/
def litBV (w : Nat) (n : Int) : BitVec w :=
  if n < 0 then -(BitVec.ofNat w (-n).toNat) else BitVec.ofNat w n.toNat

theorem litBV_eq_ofInt (w : Nat) (n : Int) : litBV w n = BitVec.ofInt w n := by
  unfold litBV
  split
  · rename_i h
    have : n = -((-n).toNat : Int) := by omega
    conv => rhs; rw [this]
    rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
  · rename_i h
    have : n = (n.toNat : Int) := by omega
    conv => rhs; rw [this]
    rw [BitVec.ofInt_natCast]

/-- An operand's value. -/
def operand (f : Func) (env : Env) : Val → Result Value
  | .inst id => match env id with
    | some v => pure v
    | none => stuck
  | .int t n => match tyOf f t with
    | .int s w => pure (.int s w (litBV w n))
    | _ => stuck
  | .bool b => pure (.bool b)
  | .void => pure .void
  | _ => stuck

/-- An integer operand of width `w`. -/
def Value.asInt (w : Nat) : Value → Result (BitVec w)
  | .int _ w' v => if h : w' = w then pure (v.cast h) else stuck
  | _ => stuck

def Value.asBool : Value → Result Bool
  | .bool b => pure b
  | _ => stuck

/-- The integer type of an instruction's result, or `none`. -/
def intTy? (f : Func) (t : TyId) : Option (Bool × Nat) :=
  match tyOf f t with
  | .int s w => some (s, w)
  | _ => none

def arithFn (op : ArithOp) (mode : Mode) (s : Bool) {w : Nat} (a b : BitVec w) : Result (BitVec w) :=
  match op, mode with
  | .add, .checked => Zig.add s a b
  | .add, .wrap => pure (Zig.addWrap a b)
  | .add, .sat => pure (Zig.addSat s a b)
  | .sub, .checked => Zig.sub s a b
  | .sub, .wrap => pure (Zig.subWrap a b)
  | .sub, .sat => pure (Zig.subSat s a b)
  | .mul, .checked => Zig.mul s a b
  | .mul, .wrap => pure (Zig.mulWrap a b)
  | .mul, .sat => pure (Zig.mulSat s a b)

def divFn (op : DivOp) (s : Bool) {w : Nat} (a b : BitVec w) : Result (BitVec w) :=
  match op with
  | .divTrunc => Zig.divTrunc s a b
  | .divFloor => Zig.divFloor s a b
  | .divExact => Zig.divExact s a b
  | .rem => Zig.rem s a b
  | .mod => Zig.mod s a b

def bitFn (op : BitOp) {w : Nat} (a b : BitVec w) : BitVec w :=
  match op with
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b

def cmpFn (op : CmpOp) (s : Bool) {w : Nat} (a b : BitVec w) : Bool :=
  match op with
  | .lt => Zig.lt s a b
  | .le => Zig.le s a b
  | .gt => Zig.gt s a b
  | .ge => Zig.ge s a b
  | .eq => a == b
  | .ne => a != b

/-- A binary integer operation whose operands and result have the instruction's type. -/
def intBin (f : Func) (env : Env) (ty : TyId) (a b : Val)
    (k : Bool → (w : Nat) → BitVec w → BitVec w → Result (BitVec w)) : Result Value :=
  match intTy? f ty with
  | some (s, w) => do
    let x ← (← operand f env a).asInt w
    let y ← (← operand f env b).asInt w
    let r ← k s w x y
    pure (.int s w r)
  | none => stuck

/-- The panic of a call to a safety-panic handler: Zig's default panic handler and the
non-generic members of `debug.FullPanic(defaultPanic)`, by exact name. The same classification
as the translator's `panicErrorFor?` (`docs/generated-code.md` §Panics) for these names; a
generic member (`inactiveUnionField__anon_<n>`) is outside the fragment. Stated as a literal
table so that a proof can evaluate it. -/
def panicOf? : String → Option Zig.Error
  | "debug.defaultPanic" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).integerOverflow" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).integerOutOfBounds" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).integerPartOutOfBounds" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).shlOverflow" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).shrOverflow" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).outOfBounds" => some .outOfBounds
  | "debug.FullPanic((function 'defaultPanic')).startGreaterThanEnd" => some .outOfBounds
  | "debug.FullPanic((function 'defaultPanic')).divideByZero" => some .divByZero
  | "debug.FullPanic((function 'defaultPanic')).reachedUnreachable" => some .unreachable
  | "debug.FullPanic((function 'defaultPanic')).exactDivisionRemainder" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).unwrapNull" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).unwrapError" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).forLenMismatch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).invalidEnumValue" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).corruptSwitch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).call" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).sentinelMismatch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).copyLenMismatch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).memcpyAlias" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).castToNull" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).incorrectAlignment" => some .panic
  | _ => none

/-- The value of one straight-line instruction (no control flow, no locals). -/
def evalPure (c : Ctx) (env : Env) (i : Inst) : Result Value :=
  let f := c.func
  match i.op with
  | .arith op mode a b => intBin f env i.ty a b fun s _ x y => arithFn op mode s x y
  | .div op a b => intBin f env i.ty a b fun s _ x y => divFn op s x y
  | .minMax isMax a b => intBin f env i.ty a b fun s _ x y =>
      pure (if isMax then Zig.max s x y else Zig.min s x y)
  | .bit op a b => match tyOf f i.ty with
    | .bool => do
      let x ← (← operand f env a).asBool
      let y ← (← operand f env b).asBool
      pure (.bool (match op with | .and => x && y | .or => x || y | .xor => x ^^ y))
    | _ => intBin f env i.ty a b fun _ _ x y => pure (bitFn op x y)
  | .not a => match tyOf f i.ty with
    | .bool => do pure (.bool (!(← (← operand f env a).asBool)))
    | .int s w => do pure (.int s w (~~~(← (← operand f env a).asInt w)))
    | _ => stuck
  | .cmp op a b => do
    match ← operand f env a with
    | .int s w x => do
      let y ← (← operand f env b).asInt w
      pure (.bool (cmpFn op s x y))
    | .bool x => match op with
      | .eq => do pure (.bool (x == (← (← operand f env b).asBool)))
      | .ne => do pure (.bool (x != (← (← operand f env b).asBool)))
      | _ => stuck
    | _ => stuck
  | .boolAnd a b => do
    let x ← (← operand f env a).asBool
    let y ← (← operand f env b).asBool
    pure (.bool (x && y))
  | .boolOr a b => do
    let x ← (← operand f env a).asBool
    let y ← (← operand f env b).asBool
    pure (.bool (x || y))
  | .intCast a => match intTy? f i.ty with
    | some (s₂, m) => do
      match ← operand f env a with
      | .int s₁ _ x => pure (.int s₂ m (← Zig.intCast s₁ s₂ m x))
      | _ => stuck
    | none => stuck
  | .trunc a => match intTy? f i.ty with
    | some (s₂, m) => do
      match ← operand f env a with
      | .int _ _ x => pure (.int s₂ m (Zig.trunc m x))
      | _ => stuck
    | none => stuck
  | .call (.func name _ _) args => do
    match panicOf? name with
    | some e => throw e
    | none => c.call name (← args.toList.mapM (operand f env))
  | _ => stuck

/-- Does the integer `x` select this `switch_br` case (an item equal, or inside a range)? -/
def caseHit (f : Func) (env : Env) (s : Bool) {w : Nat} (x : BitVec w) (sc : SwitchCase) :
    Result Bool := do
  let items ← sc.items.toList.mapM fun it => do pure (x == (← (← operand f env it).asInt w))
  let ranges ← sc.ranges.toList.mapM fun (lo, hi) => do
    let l ← (← operand f env lo).asInt w
    let h ← (← operand f env hi).asInt w
    pure (Zig.le s l x && Zig.le s x h)
  pure ((items ++ ranges).foldr (· || ·) false)

/-- Does `e` repeat the loop `id`? -/
def Exit.again (id : InstId) : Exit → Bool
  | .rep t => t == id
  | _ => false

abbrev SM := Zig.M Store

theorem sizeOf_toList {α : Type} [SizeOf α] (a : Array α) : sizeOf a.toList = sizeOf a - 1 := by
  cases a; simp

theorem sizeOf_case_body (sc : SwitchCase) : sizeOf sc.body < sizeOf sc := by
  cases sc; simp; omega

def liftR {α : Type} (x : Result α) : SM α := StateT.lift x

mutual

/-- Run an instruction sequence until it exits. Falling off the end is stuck (a well-formed
body ends in a terminator). -/
def execBody (c : Ctx) : List Inst → Env → SM Exit
  | [], _ => liftR stuck
  | i :: rest, env => execInst c i rest env
termination_by l => (sizeOf l, 0)

/-- Run `i`, then (unless it exits) `rest`. -/
def execInst (c : Ctx) (i : Inst) (rest : List Inst) (env : Env) : SM Exit :=
  match _h : i.op with
  | .arg index =>
    match c.args[index]? with
    | some v => execBody c rest (env.set i.id v)
    | none => liftR stuck
  | .block body => do
    let e ← execBody c body.toList env
    match e with
    | .br t v => if t = i.id then execBody c rest (env.set i.id v) else pure e
    | _ => pure e
  | .loop body =>
    -- A loop never falls through: it repeats on its own `repeat` and otherwise propagates.
    Zig.loop (execBody c body.toList env) (Exit.again i.id)
  | .br t v => do pure (.br t (← liftR (operand c.func env v)))
  | .«repeat» t => pure (.rep t)
  | .ret v => do pure (.ret (← liftR (operand c.func env v)))
  | .unreach => liftR (throw .unreachable)
  | .trap => liftR (throw .panic)
  | .condBr cv th el => do
    if ← liftR ((← liftR (operand c.func env cv)).asBool) then execBody c th.toList env
    else execBody c el.toList env
  | .switchBr v cases el => do
    match ← liftR (operand c.func env v) with
    | .int s _ x => execSwitch c s x cases.toList el env
    | _ => liftR stuck
  | .alloc => execBody c rest (env.set i.id (.cell i.id))
  | .load p => do
    match ← liftR (operand c.func env p) with
    | .cell a => match (← get) a with
      | some v => execBody c rest (env.set i.id v)
      | none => liftR stuck
    | _ => liftR stuck
  | .store p v => do
    match ← liftR (operand c.func env p) with
    | .cell a => do
      let x ← liftR (operand c.func env v)
      modify fun s j => if j = a then some x else s j
      execBody c rest env
    | _ => liftR stuck
  | .line _ => execBody c rest env
  | .dbg _ _ => execBody c rest env
  | _ => do
    let v ← liftR (evalPure c env i)
    execBody c rest (env.set i.id v)
termination_by (sizeOf i + sizeOf rest, 1)
decreasing_by
  all_goals
    obtain ⟨id, ty, op⟩ := i
    simp only at _h
    subst _h
    simp_wf
    try simp only [sizeOf_toList]
    omega

/-- `switch_br`'s case chain: the first case that `x` selects, else the `else` body. -/
def execSwitch (c : Ctx) (s : Bool) {w : Nat} (x : BitVec w) :
    List SwitchCase → Array Inst → Env → SM Exit
  | [], el, env => execBody c el.toList env
  | sc :: more, el, env => do
    if ← liftR (caseHit c.func env s x sc) then execBody c sc.body.toList env
    else execSwitch c s x more el env
termination_by l el => (sizeOf l + sizeOf el, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

/-- Does `v` have the AIR type `t`? Only the fragment's parameter types (integers, `bool`,
`void`) have values here. -/
def valOk (t : Ty) (v : Value) : Bool :=
  match t, v with
  | .int s w, .int s' w' _ => s == s' && w == w'
  | .bool, .bool _ => true
  | .void, .void => true
  | _, _ => false

/-- Do the arguments match the parameter types, one for one? -/
def argsOk (f : Func) : List TyId → List Value → Bool
  | [], [] => true
  | t :: ts, v :: vs => valOk (tyOf f t) v && argsOk f ts vs
  | _, _ => false

/-- Run a function on its argument values: an empty SSA environment (each `arg` instruction
binds its parameter) and no local cells. A call whose arguments do not match the parameter
types, and a function that ends other than by `ret`, are stuck. -/
def execFunc (call : String → List Value → Result Value) (f : Func) (args : List Value) :
    Result Value :=
  if argsOk f f.params.toList args then do
    let e ← (execBody ⟨f, args, call⟩ f.body.toList (fun _ => none)).run' (fun _ => none)
    match e with
    | .ret v => pure v
    | _ => stuck
  else stuck

/-- The integer an `int` value holds, at width `w` (`0` for any other value). -/
def Value.toBV (w : Nat) : Value → BitVec w
  | .int _ w' v => if h : w' = w then v.cast h else 0
  | _ => 0

def Value.toBool : Value → Bool
  | .bool b => b
  | _ => false

theorem argsOk_nil {f : Func} {args : List Value} (h : argsOk f [] args = true) : args = [] := by
  cases args <;> simp_all [argsOk]

theorem argsOk_cons {f : Func} {t : TyId} {ts : List TyId} {args : List Value}
    (h : argsOk f (t :: ts) args = true) :
    ∃ v vs, args = v :: vs ∧ valOk (tyOf f t) v = true ∧ argsOk f ts vs = true := by
  cases args with
  | nil => simp [argsOk] at h
  | cons v vs => simp only [argsOk, Bool.and_eq_true] at h; exact ⟨v, vs, rfl, h⟩

theorem valOk_int {s : Bool} {w : Nat} {v : Value} (h : valOk (.int s w) v = true) :
    v = .int s w (v.toBV w) := by
  cases v <;> simp_all [valOk, Value.toBV]
  obtain ⟨rfl, rfl⟩ := h; simp

theorem valOk_bool {v : Value} (h : valOk .bool v = true) : v = .bool v.toBool := by
  cases v <;> simp_all [valOk, Value.toBool]

theorem valOk_void {v : Value} (h : valOk .void v = true) : v = .void := by
  cases v <;> simp_all [valOk]

/-! ## Programs -/

/-- A call oracle: the meaning of a direct call by fully qualified name. -/
abbrev Oracle := String → List Value → Result Value

section Monotone
open Lean.Order

theorem evalPure_mono (f : Func) (args : List Value) (env : Env) (i : Inst) :
    monotone (fun o : Oracle => evalPure ⟨f, args, o⟩ env i) := by
  unfold evalPure
  split <;> (try exact monotone_const _) <;> (try (dsimp only; exact monotone_const _))
  split
  · exact monotone_const _
  · apply monotone_bind
    · dsimp only; exact monotone_const _
    · apply monotone_of_monotone_apply; intro a
      dsimp only
      exact monotone_apply a _ (monotone_apply _ _ monotone_id)

local macro "mono_step" : tactic => `(tactic| first
  | exact monotone_const _
  | (dsimp only; exact monotone_const _)
  | assumption
  | (apply_assumption <;> rfl)
  | (apply monotone_apply; first | assumption | apply_assumption)
  | exact evalPure_mono _ _ _ _
  | (apply Zig.monotone_loop)
  | (apply monotone_bind)
  | (apply monotone_ite)
  | split
  | (apply monotone_of_monotone_apply; intro))

/-- A body is monotone in its call oracle: a more defined callee gives a more defined
caller. -/
theorem execBody_mono (f : Func) (args : List Value) :
    ∀ l env, monotone (fun o : Oracle => execBody ⟨f, args, o⟩ l env) := by
  apply execBody.induct ⟨f, args, fun _ _ => stuck⟩
    (motive2 := fun i rest env => monotone (fun o : Oracle => execInst ⟨f, args, o⟩ i rest env))
    (motive3 := fun s w x cs el env => monotone (fun o : Oracle => execSwitch ⟨f, args, o⟩ s x cs el env))
  case case1 => intros; simp only [execBody]; exact monotone_const _
  case case2 => intros; simp only [execBody]; assumption
  case case20 => intros; simp only [execSwitch]; assumption
  case case21 => intros; unfold execSwitch; repeat' mono_step
  case case19 =>
    intro i rest env n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 ih
    unfold execInst
    split <;> (try (exfalso; simp_all; done))
    rename_i m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
    clear n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
    repeat' mono_step
  all_goals
    intro i; obtain ⟨id, ty, op⟩ := i; intro rest env; intros
    simp only at *
    subst_vars
    simp only [execInst]
    try simp only [*]
    repeat' mono_step

@[partial_fixpoint_monotone]
theorem execFunc_mono {γ : Type} [PartialOrder γ] (g : γ → Oracle) (hg : monotone g)
    (f : Func) (args : List Value) : monotone (fun x => execFunc (g x) f args) := by
  unfold execFunc
  apply monotone_ite _ _ _ _ (monotone_const _)
  apply monotone_bind
  · exact monotone_compose (g := fun o : Oracle =>
      (execBody ⟨f, args, o⟩ f.body.toList (fun _ => none)).run' (fun _ => none)) hg
      (Zig.monotone_run' _ (execBody_mono f args _ _) _)
  · exact monotone_const _

end Monotone

/-- A program: its functions by fully qualified name. -/
abbrev Prog := String → Option Func

/-- The semantics of a program: the least oracle that each function's body satisfies (the
least fixpoint of `execFunc`, in `Zig.Result`'s order where non-termination and stuck states
are the bottom). A call to a name outside the program is stuck. -/
def run (p : Prog) (name : String) (args : List Value) : Result Value :=
  match p name with
  | some f => execFunc (run p) f args
  | none => stuck
partial_fixpoint

open Lean.Order in
/-- Soundness of any fixpoint: if an oracle `G` satisfies every function's equation
(`execFunc G f = G f.name`), the program semantics is below it. So every terminating
AIR behaviour (a value or a panic) is `G`'s behaviour too. -/
theorem run_le_of_fixpoint (p : Prog) (G : Oracle)
    (hG : ∀ name f args, p name = some f → execFunc G f args = G name args) :
    run p ⊑ G := by
  apply run.fixpoint_induct p (motive := fun r => r ⊑ G)
  · exact fun c hc h => csup_le hc h
  · intro r hr name args
    show (match p name with | some f => execFunc r f args | none => stuck) ⊑ G name args
    split
    · rename_i f hf
      rw [← hG name f args hf]
      exact execFunc_mono (fun o : Oracle => o) monotone_id f args _ _ hr
    · exact FlatOrder.rel.bot

/-! ## Normalization lemmas for certificates -/

namespace Cert

theorem throw_bind {α β : Type} (e : Zig.Error) (f : α → Result β) :
    (throw e : Result α) >>= f = throw e := rfl

theorem run_throw {σ α : Type} (e : Zig.Error) (s : σ) :
    (throw e : Zig.M σ α).run s = throw e := rfl

theorem map_throw {α β : Type} (e : Zig.Error) (f : α → β) :
    f <$> (throw e : Result α) = throw e := rfl

theorem bind_ite {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) : (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem map_ite {m : Type → Type} [Functor m] {α β : Type} (c : Prop) [Decidable c]
    (a b : m α) (f : α → β) : f <$> (if c then a else b) = if c then f <$> a else f <$> b := by
  split <;> rfl

theorem run_ite' {σ α : Type} (c : Prop) [Decidable c] (a b : Zig.M σ α) (s : σ) :
    (if c then a else b).run s = if c then a.run s else b.run s := by
  split <;> rfl

attribute [air_sem] execFunc argsOk valOk execBody execInst execSwitch caseHit evalPure intBin intTy? tyOf
  operand Env.set Value.asInt Value.asBool arithFn divFn cmpFn bitFn liftR litBV Exit.again
  bind_ite map_ite run_ite' throw_bind map_throw run_throw Zig.call
  Array.toList List.mapM_cons List.mapM_nil List.getElem?_toArray Option.getD_some
  List.getElem_cons_zero StateT.run'_eq StateT.run_bind StateT.run_pure StateT.run_map
  StateT.run_lift StateT.run_monadLift StateT.run_get StateT.run_modify liftM monadLift
  MonadLift.monadLift bind_assoc pure_bind map_pure map_bind bind_map_left Functor.map_map
  BitVec.cast_eq dite_true ite_true ite_false decide_eq_true_eq List.getElem?_cons_zero
  List.getElem?_cons_succ Nat.reduceEqDiff reduceIte reduceDIte Bool.or_false Bool.false_or
  Int.reduceLT Int.reduceNeg Int.reduceToNat BitVec.ofNat_eq_ofNat List.cons_append
  List.nil_append List.foldr_cons List.foldr_nil true_and and_true Bool.and_true
  Bool.true_and beq_self_eq_true List.toList_toArray

end Cert

end Air2Lean.Sem
