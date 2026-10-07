import Lean

/-!
Environment-based assurance data extraction. The generated driver imports every selected
module and invokes `#assurance_audit`. Policy is deliberately applied outside this command:
the raw declaration graph and Lean's own transitive axiom inventory remain inspectable.
-/

open Lean Elab Command

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
      let conclusion := match env.checked.get.find? n with
        | some c => conclusionShape 8 c.type
        | none => Json.null
      theorems := theorems.push <| Json.mkObj [
        ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
        ("axioms", namesJson axs), ("conclusion", conclusion)]
    let result := Json.mkObj [
      ("schema_version", toJson (1 : Nat)), ("modules", toJson selected),
      ("theorems", Json.arr theorems), ("project_declarations", namesJson declarations),
      ("nodes", Json.arr (graph env (roots.toList ++ declarations.toList)))]
    liftIO <| IO.println ("AIR2LEAN_ASSURANCE_JSON:" ++ result.compress)

end Air2Lean.Assurance
