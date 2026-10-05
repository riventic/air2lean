import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def fixture (version : String) (weak packed : Bool) : Json :=
  let scalar := if packed then obj [("k", .str "bool"), ("abi_size", num 1), ("abi_align", num 1)]
    else obj [("k", .str "int"), ("signed", .bool false), ("bits", num 8),
      ("abi_size", num 1), ("abi_align", num 1)]
  let types := #[scalar,
    obj [("k", .str "ptr"), ("size", .str "one"), ("const", .bool false),
      ("child", num 0), ("ptr_align", num 1), ("abi_size", num 8), ("abi_align", num 8)],
    obj [("k", .str "optional"), ("child", num 0), ("abi_size", num 2), ("abi_align", num 1)],
    obj [("k", .str "noreturn")]]
  let arg := fun id ty param => obj [("id", num id), ("tag", .str "arg"), ("ty", num ty), ("param", num param)]
  obj [("schema", num 11), ("zig_version", .str version), ("target_endian", .str "little"),
    ("name", .str (if weak then (if packed then "weakBool" else "weak") else "strong")),
    ("types", .arr types), ("params", toJson (#[1, 0, 0] : Array Nat)), ("ret", num 2),
    ("body", .arr #[arg 0 1 0, arg 1 0 1, arg 2 0 2,
      obj [("id", num 3), ("tag", .str (if weak then "cmpxchg_weak" else "cmpxchg_strong")),
        ("ty", num 2), ("args", .arr #[ref 0, ref 1, ref 2]),
        ("success_order", .str "acq_rel"), ("failure_order", .str "acquire")],
      obj [("id", num 4), ("tag", .str "ret"), ("ty", num 3), ("args", .arr #[ref 3])]])]

private def checked (j : Json) : IO Func :=
  match (do let f ← normalize (← Raw.parseFunc j); check f; pure f : Except String Func) with
  | .ok f => pure f
  | .error e => throw (IO.userError e)

private def require (b : Bool) (s : String) : IO Unit :=
  unless b do throw (IO.userError s)

def main (args : List String) : IO Unit := do
  let directory := System.FilePath.mk (args.headD "/tmp")
  for version in supportedVersions do
    let weak ← checked (fixture version true false)
    let strong ← checked (fixture version false false)
    let packed ← checked (fixture version true true)
    match checkProgram #[weak, strong, packed] with
    | .error e => throw (IO.userError e)
    | .ok () => pure ()
    require (weak.body.any fun i => match i.op with | .cmpxchg true _ _ _ _ _ => true | _ => false)
      "normalization lost the weak tag"
    require (strong.body.any fun i => match i.op with | .cmpxchg false _ _ _ _ _ => true | _ => false)
      "normalization lost the strong tag"
    let source := emit #[weak, strong, packed] "WeakCasPipeline" "" .ieee
    require ((source.splitOn "Zig.cmpxchgWeakC").length > 1) "weak integer dispatch lost"
    require ((source.splitOn "Zig.cmpxchgWeakAsC").length > 1) "weak Packed dispatch lost"
    require ((source.splitOn "Zig.cmpxchgC ").length > 1) "strong dispatch changed"
    IO.FS.writeFile (directory / s!"WeakCasPipeline-{version}.lean") source
  IO.println "Weak CAS pipeline regressions passed"
