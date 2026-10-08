import Lean
import ZigLean.Witness
-- Every claim head of assurance/claim-heads.json is imported here, so an audited module that
-- defines a declaration with the same name fails with a name clash instead of spoofing it.
import ZigLean.Sep.Triple
import ZigLean.Sep.Total
import ZigLean.Conc.Own
import ZigLean.Conc.Total

/-!
Environment-based assurance data extraction. The generated driver imports every selected
module and invokes `#assurance_audit`. Policy is deliberately applied outside this command:
the raw declaration graph and Lean's own transitive axiom inventory remain inspectable.
-/

open Lean Elab Command Meta

namespace Air2Lean.Assurance

private def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.allImportedModuleNames[i.toNat]!.toString
  | none => ""

private def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .defnInfo _ => "definition"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def namesJson (ns : Array Name) : Json :=
  toJson (ns.map Name.toString)

private def externEntryJson : ExternEntry → Json
  | .standard backend target => Json.mkObj [
      ("kind", toJson "standard"), ("backend", toJson backend.toString), ("target", toJson target)]
  | .inline backend pattern => Json.mkObj [
      ("kind", toJson "inline"), ("backend", toJson backend.toString), ("target", toJson pattern)]
  | .adhoc backend => Json.mkObj [
      ("kind", toJson "adhoc"), ("backend", toJson backend.toString), ("target", Json.null)]
  | .opaque => Json.mkObj [
      ("kind", toJson "opaque"), ("backend", toJson "all"), ("target", Json.null)]

private def externJson (env : Environment) (n : Name) : Json :=
  Json.arr <| ((getExternAttrData? env n).map fun data =>
    data.entries.toArray.map externEntryJson).getD #[]

/-- Include inductive/recursor relations as well as constants in types and bodies. -/
private def dependencies (c : ConstantInfo) : Array Name := Id.run do
  let mut ns := c.getUsedConstantsAsSet
  if let .recInfo v := c then
    for rule in v.rules do
      ns := ns ++ rule.rhs.getUsedConstantsAsSet
  if let .ctorInfo v := c then
    ns := ns.insert v.induct
  return ns.toArray.qsort Name.lt

/-- Build one shared graph, retaining edges through imported theorem and opaque bodies. -/
private partial def graph (env : Environment) (pending : List Name)
    (seen : NameSet := {}) (nodes : Array Json := #[]) : Array Json :=
  match pending with
  | [] => nodes
  | n :: rest =>
    if seen.contains n then graph env rest seen nodes else
    let seen := seen.insert n
    match env.checked.get.find? n with
    | none => graph env rest seen (nodes.push <| Json.mkObj [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("kind", toJson "unresolved"), ("dependencies", toJson (#[] : Array String))])
    | some c =>
      let ds := dependencies c
      let node := Json.mkObj [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("user_name", toJson ((privateToUserName? n).getD n).toString),
        ("kind", toJson (kind c)), ("unsafe", toJson c.isUnsafe),
        ("partial", toJson c.isPartial), ("dependencies", namesJson ds),
        ("implemented_by", toJson ((Compiler.getImplementedBy? env n).map Name.toString)),
        ("extern", externJson env n)]
      graph env (ds.toList ++ rest) seen (nodes.push node)

/-- Binders and hypotheses are premises; the conclusion is what remains. No definition is
unfolded, so a wrapper definition keeps its own head constant. -/
private partial def stripBinders : Expr → Expr
  | .forallE _ _ b _ => stripBinders b
  | .mdata _ b => stripBinders b
  | e => e

private def headJson (e : Expr) : Json :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => toJson n.toString
  | _ => Json.null

/-- Value shape on an equation's right-hand side. `Option.some` is peeled to its value;
`Pure.pure` to its monad and value, since `pure` in `Option` can wrap an error. -/
private partial def valueShape (depth : Nat) (e : Expr) : Json :=
  let e := e.consumeMData
  let head := ("head", headJson e)
  if depth == 0 then Json.mkObj [head]
  else if e.isAppOfArity ``Option.some 2 then
    Json.mkObj [head, ("args", Json.arr #[valueShape (depth - 1) e.appArg!])]
  else if e.isAppOfArity ``Pure.pure 4 then
    Json.mkObj [head, ("args", Json.arr #[Json.mkObj [("head", headJson (e.getArg! 0))],
      valueShape (depth - 1) e.appArg!])]
  else Json.mkObj [head]

/-- Raw conclusion shape for claim classification; policy is applied in `scripts/claims.py`.
Only an equation's right-hand side is expanded: the left side is the computation it states. -/
private def conclusionShape (depth : Nat) (e : Expr) : Json :=
  let e := (stripBinders e).consumeMData
  let head := ("head", headJson e)
  if depth == 0 then Json.mkObj [head]
  else if e.isAppOfArity ``Eq 3 then
    Json.mkObj [head, ("args", Json.arr #[valueShape (depth - 1) e.appArg!])]
  else Json.mkObj [head]

/-- Statement-only constants, read from the kernel type without the proof term or any
unfolding: a proof that merely mentions a definition does not make the theorem about it.
`conclusion_dependencies` drops binders and hypotheses as well. -/
private def statementDependencies (type : Expr) : List (String × Json) :=
  let names (e : Expr) := namesJson (e.getUsedConstants.qsort Name.lt)
  [("statement_dependencies", names type), ("conclusion_dependencies", names (stripBinders type))]

/-! ## Statement structure (claim binding, `scripts/claims.py`)

Everything below reads the kernel type only. Binders are the theorem's own telescope; the
conclusion head is identified by its declaration (module and expression hashes), and each of
its arguments is described as a computation: wrappers that run a computation on a state are
peeled, and the remaining application's arguments are bound variables of the telescope,
closed terms or open terms. -/

private def binderJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "inst_implicit"

/-- Computational constants of a hypothesis: definitions and opaques that are not projections,
instances, matchers or structural auxiliaries. -/
private def definitionsIn (env : Environment) (e : Expr) : Array Name :=
  (e.getUsedConstants.filter fun n =>
    match env.checked.get.find? n with
    | some (.defnInfo _) | some (.opaqueInfo _) =>
      !(env.isProjectionFn n || Meta.isInstanceCore env n || Meta.isMatcherCore env n ||
        isAuxRecursor env n || isNoConfusion env n)
    | _ => false).qsort Name.lt

/-- Telescope indices of the free variables occurring in `e`. -/
private def bvarUses (xs : Array Expr) (e : Expr) : Array Nat := Id.run do
  let mut out := #[]
  for i in [:xs.size] do
    if e.containsFVar xs[i]!.fvarId! then out := out.push i
  return out

private def atomJson (xs : Array Expr) (e : Expr) : Json :=
  let e := e.consumeMData
  match xs.idxOf? e with
  | some i => Json.mkObj [("bvar", toJson i)]
  | none =>
    let head := headJson e
    if e.hasFVar then Json.mkObj [("open", head), ("bvars", toJson (bvarUses xs e))]
    else Json.mkObj [("closed", head)]

/-- Wrappers that run a computation: (constant, arity, computation index, extra-argument
indices). The extra arguments (initial state, environment) belong to the claim's domain. -/
private def runners : List (Name × Nat × Nat × List Nat) :=
  [(``StateT.run, 5, 3, [4]), (``StateT.run', 6, 4, [5]), (``ExceptT.run, 4, 3, []),
   (``OptionT.run, 3, 2, []), (``ReaderT.run, 5, 3, [4]), (``Zig.call, 3, 2, [])]

/-- The leading binder kinds of a constant's type (its own parameters). -/
private def paramBinders (env : Environment) (n : Name) : Array Json := Id.run do
  let some c := env.checked.get.find? n | return #[]
  let mut out := #[]
  let mut t := c.type
  while true do
    match t.consumeMData with
    | .forallE _ _ b bi => out := out.push (binderJson bi); t := b
    | _ => break
  return out

/-- A conclusion argument as a computation: peeled runners, the applied constant, its
parameter kinds, its arguments and the runners' extra arguments, as atoms; `atom` describes the
argument itself. -/
private partial def subjectJson (env : Environment) (xs : Array Expr) (e : Expr) : Json :=
  (go e.consumeMData #[] #[]).setObjVal! "atom" (atomJson xs e)
where
  go (e : Expr) (peeled : Array Json) (extra : Array Json) : Json :=
    let args := e.getAppArgs
    let runner : Option (Name × Nat × Nat × List Nat) := match e.getAppFn.consumeMData with
      | .const n _ => runners.find? fun r => r.1 == n && args.size == r.2.1
      | _ => none
    match runner with
    | some (n, _, program, extras) =>
      go args[program]!.consumeMData (peeled.push (toJson n.toString))
        (extras.foldl (fun acc i => acc.push (atomJson xs args[i]!)) extra)
    | none =>
      let fn := match e.getAppFn.consumeMData with
        | .const n _ => some n
        | _ => none
      Json.mkObj [("peeled", Json.arr peeled), ("fn", toJson (fn.map Name.toString)),
        ("fn_module", toJson (fn.map (moduleOf env))),
        ("params", Json.arr ((fn.map (paramBinders env)).getD #[])),
        ("args", Json.arr (args.map (atomJson xs))), ("extra", Json.arr extra)]

private def hashHex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- A deterministic serialization of a closed kernel expression (binder names and metadata
dropped; constants, universe levels, binder kinds and literals kept). -/
private partial def serialize : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar _ => "?f"
  | .mvar _ => "?m"
  | .sort l => s!"(S {l})"
  | .const n ls => s!"(C {n} {ls})"
  | .app f a => s!"(A {serialize f} {serialize a})"
  | .lam _ t b bi => s!"(L {binderJson bi} {serialize t} {serialize b})"
  | .forallE _ t b bi => s!"(F {binderJson bi} {serialize t} {serialize b})"
  | .letE _ t v b _ => s!"(Z {serialize t} {serialize v} {serialize b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal v) => s!"(T {v.quote})"
  | .mdata _ e => serialize e
  | .proj n i e => s!"(P {n} {i} {serialize e})"

/-- 64-bit FNV-1a over the UTF-8 bytes, independent of Lean's `String.hash`. -/
private def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

/-- 128-bit fingerprint of a declaration's kernel type and value. -/
private def fingerprint (c : ConstantInfo) : String :=
  let text := serialize c.type ++ "|" ++ ((c.value? (allowOpaque := true)).map serialize).getD "-"
  hashHex text.hash ++ hashHex (fnv1a text)

/-- The declaration behind a conclusion head: its module and a fingerprint of its kernel type
and value, so that a same-named declaration elsewhere is distinguishable. -/
private def headIdentity (env : Environment) (e : Expr) : Json :=
  match e.getAppFn.consumeMData with
  | .const n _ =>
    match env.checked.get.find? n with
    | some c => Json.mkObj [("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("kind", toJson (kind c)), ("fingerprint", toJson (fingerprint c))]
    | none => Json.mkObj [("name", toJson n.toString), ("module", toJson ""),
        ("kind", toJson "unresolved"), ("fingerprint", Json.null)]
  | _ => Json.null

/-- A companion witness theorem: verified when its kernel type is exactly the statement
recomputed from the claim's type. -/
private def witnessJson (env : Environment) (thm : Name) (suffix : Name)
    (expected : Option Expr) : Json :=
  let companion := thm ++ suffix
  match expected, env.checked.get.find? companion with
  | none, _ => Json.mkObj [("status", toJson "not_required"), ("theorem", Json.null)]
  | some _, none => Json.mkObj [("status", toJson "absent"), ("theorem", Json.null)]
  | some ty, some c =>
    let ok := c.isTheorem && c.type == ty
    Json.mkObj [("status", toJson (if ok then "verified" else "mismatch")),
      ("theorem", toJson companion.toString)]

private def statementJson (n : Name) (type : Expr) : MetaM Json := do
  let env ← getEnv
  let nonvacuity ← Zig.Witness.nonvacuityType type
  let liveness ← Zig.Witness.livenessType? type
  let trivial ← Zig.Witness.triviallyInhabited type
  let nonvacuityJson :=
    if trivial then Json.mkObj [("status", toJson "trivial"), ("theorem", Json.null)]
    else witnessJson env n Zig.Witness.nonvacuousSuffix (some nonvacuity)
  forallTelescope type fun xs body => do
    let mut binders := #[]
    for i in [:xs.size] do
      let decl ← xs[i]!.fvarId!.getDecl
      binders := binders.push <| Json.mkObj [
        ("name", toJson decl.userName.toString), ("binder", binderJson decl.binderInfo),
        ("prop", toJson (← isProp decl.type)), ("defs", namesJson (definitionsIn env decl.type)),
        ("uses", toJson (bvarUses (xs.extract 0 i) decl.type))]
    let body := body.consumeMData
    return Json.mkObj [
      ("binders", Json.arr binders), ("head", headIdentity env body),
      ("args", Json.arr (body.getAppArgs.map (subjectJson env xs))),
      ("witnesses", Json.mkObj [("nonvacuity", nonvacuityJson),
        ("liveness", witnessJson env n Zig.Witness.livenessSuffix liveness)])]

syntax (name := assuranceAudit) "#assurance_audit" "[" str,* "]" : command

elab_rules : command
  | `(#assurance_audit [$modules:str,*]) => do
    let selected := modules.getElems.map (·.getString)
    if selected.isEmpty then throwError "assurance audit requires modules"
    -- The checked environment excludes erroneous elaborator placeholders. Private olean
    -- data is loaded by ordinary (non-`module`) imports, so proof bodies are available.
    let env := (← getEnv).setExporting false
    let selectedSet := Std.HashSet.ofArray selected
    let (roots, declarations) := env.checked.get.constants.fold
      (init := ((#[] : Array Name), (#[] : Array Name))) fun (roots, declarations) n c =>
        if !selectedSet.contains (moduleOf env n) then (roots, declarations) else
        let roots := if c.isTheorem then roots.push n else roots
        let declarations := if c.isAxiom || (kind c == "opaque") ||
            (Compiler.getImplementedBy? env n).isSome ||
            (getExternAttrData? env n).isSome then declarations.push n else declarations
        (roots, declarations)
    let roots := roots.qsort Name.lt
    let declarations := declarations.qsort Name.lt
    let mut theorems : Array Json := #[]
    for n in roots do
      let axs ← collectAxioms n
      let (conclusion, statement, shape) ← match env.checked.get.find? n with
        | some c => do
          let shape ← liftTermElabM <| withoutExporting <| statementJson n c.type
          pure (conclusionShape 8 c.type, statementDependencies c.type, shape)
        | none => pure (Json.null, [], Json.null)
      theorems := theorems.push <| Json.mkObj <| [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("axioms", namesJson axs), ("conclusion", conclusion)] ++ statement ++
        [("statement", shape)]
    let result := Json.mkObj [
      ("schema_version", toJson (1 : Nat)), ("modules", toJson selected),
      ("theorems", Json.arr theorems), ("project_declarations", namesJson declarations),
      ("nodes", Json.arr (graph env (roots.toList ++ declarations.toList)))]
    liftIO <| IO.println ("AIR2LEAN_ASSURANCE_JSON:" ++ result.compress)

end Air2Lean.Assurance
