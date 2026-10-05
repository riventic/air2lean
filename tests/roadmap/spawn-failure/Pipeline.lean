import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def lit (ty : Nat) (s : String) : Json := obj [("ty", num ty), ("val", .str s)]
private def node (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def integer (bits size align : Nat) : Json :=
  obj [("k", .str "int"), ("signed", .bool false), ("bits", num bits),
    ("abi_size", num size), ("abi_align", num align)]
private def named (name : String) (fields : Array Json := #[]) (size : Nat := 0) : Json :=
  obj [("k", .str "struct"), ("name", .str name), ("layout", .str "auto"),
    ("fields", .arr fields), ("abi_size", num size), ("abi_align", num 8)]
private def field (name : String) (ty off : Nat) : Json :=
  obj [("name", .str name), ("ty", num ty), ("offset", num off)]
private def errors : Json := obj [("k", .str "error_set"), ("abi_size", num 2), ("abi_align", num 2),
  ("errors", .arr #[.str "ThreadQuotaExceeded", .str "SystemResources", .str "OutOfMemory",
    .str "LockedMemoryLimitExceeded", .str "Unexpected"])]
private def types : Array Json := #[integer 32 4 4,
  obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)],
  obj [("k", .str "noreturn")],
  obj [("k", .str "tuple"), ("fields", .arr #[obj [("ty", num 0)], obj [("ty", num 0)]])],
  named "Thread", errors,
  obj [("k", .str "error_union"), ("error", num 5), ("payload", num 4)],
  integer 64 8 8, named "mem.Allocator" #[] 16,
  obj [("k", .str "optional"), ("child", num 8), ("abi_size", num 24), ("abi_align", num 8)],
  named "Thread.SpawnConfig" #[field "stack_size" 7 0, field "allocator" 9 8] 32,
  named "Io.Group" #[] 16,
  obj [("k", .str "ptr"), ("size", .str "one"), ("const", .bool false), ("child", num 11),
    ("ptr_align", num 8), ("abi_size", num 8), ("abi_align", num 8)],
  named "Io" #[] 16,
  obj [("k", .str "error_set"), ("abi_size", num 2), ("abi_align", num 2),
    ("errors", .arr #[.str "ConcurrencyUnavailable"])],
  obj [("k", .str "error_union"), ("error", num 14), ("payload", num 1)]]

private def file (version name : String) (params : Array Nat) (ret : Nat) (body : Array Json) : Json :=
  obj [("schema", num 11), ("zig_version", .str version), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr types), ("params", toJson params), ("ret", num ret),
    ("body", .arr body)]
private def worker (version : String) : Json := file version "worker" #[0, 0] 1
  #[node 0 "arg" 0 #[] [("param", num 0)], node 1 "arg" 0 #[] [("param", num 1)],
    node 2 "ret" 2 #[lit 1 "{}"]]
private def config (stack : String := "16777216") (nullAllocator : Bool := true) : Json :=
  obj [("ty", num 10), ("elems", .arr #[lit 7 stack,
    if nullAllocator then obj [("ty", num 9), ("null", .bool true)] else
      obj [("ty", num 9), ("undef", .bool true)]])]
private def spawner (version callee : String) (cfg : Json := config) : Json :=
  let group := callee != "Thread.spawn"
  let ret := if !group then 6 else if callee == "Io.Group.async" then 1 else 15
  let argSetup := if group then #[node 0 "arg" 12 #[] [("param", num 0)],
    node 1 "arg" 13 #[] [("param", num 1)]] else #[]
  file version "launch" (if group then #[12, 13] else #[]) ret
    (argSetup ++ #[node 2 "aggregate_init" 3 #[lit 0 "7", lit 0 "19"],
      node 3 "call" ret (if group then #[ref 0, ref 1, ref 2] else #[cfg, ref 2])
        [("callee", obj [("func", .str callee), ("comptime_fn", .str "worker")])],
      node 4 "ret" 2 #[ref 3]])
private def parse (j : Json) : IO Func := do
  match (do let f ← normalize (← Raw.parseFunc j); check f; pure f : Except String Func) with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def hasText (text needle : String) : Bool := (text.splitOn needle).length > 1
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def checked (files : Array Json) : IO (Array Func) := do
  let fs ← files.mapM parse
  match checkProgram fs with | .ok _ => pure fs | .error e => throw (IO.userError e)
private def reject (label version : String) (cfg : Json) : IO Unit := do
  let fs ← checked #[spawner version "Thread.spawn" cfg, worker version]
  match checkFallibleSpawnCalls fs with
  | .ok _ => throw (IO.userError s!"accepted {label}")
  | .error message =>
    if label == "custom allocator" then
      require (hasText message "custom allocators are outside the model")
        "custom allocator fixture failed for an unrelated reason"

-- The generated code is elaborated separately. The equality fixes capture order in
-- both the child dispatcher and the independently selected caller fallback.
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Pipeline.lean OUTPUT_DIRECTORY")
  for (version, label) in #[("0.14.1", "14"), ("0.15.2", "15"), ("0.16.0", "16")] do
    let fs ← checked #[spawner version "Thread.spawn", worker version]
    require (checkFallibleSpawnCalls fs |>.toOption.isSome) s!"rejected supported {version}"
    require (emit fs "Synthetic" "" == emit fs "Synthetic" "" .ieee .available)
      "default emission changed from explicit available policy"
    let output := emit fs "Synthetic" "" .ieee .fallible
    require (hasText output "Thread assignment policy: fallible") "fallible header lost"
    require (hasText output "Zig.spawnWithPolicyC .fallible") "fallible spawn wrapper lost"
    IO.FS.writeFile (System.FilePath.mk directory / s!"spawn-{label}.lean")
      (output ++ "\nexample (a b : BitVec 32) : Synthetic.dispatch (.worker (a, b)) =\n  discard (Zig.ConcM.liftMem (StateT.lift (Synthetic.worker a b))) := by rfl\n")
    reject "nonpositive stack" version (config "0")
    reject "custom allocator" version (config "16777216" false)
  reject "unaudited version" "0.17.0" config
  for (callee, label, op) in #[("Io.Group.async", "async", "groupAsyncWithPolicyC"),
      ("Io.Group.concurrent", "concurrent", "groupConcurrentWithPolicyC")] do
    let fs ← checked #[spawner "0.16.0" callee, worker "0.16.0"]
    require (checkFallibleSpawnCalls fs |>.toOption.isSome) "supported group boundary rejected"
    let output := emit fs "Synthetic" "" .ieee .fallible
    require (hasText output s!"Zig.{op} .fallible") "wrong group wrapper name"
    if label == "async" then
      require (hasText output "worker capture0 capture1") "caller fallback lost complete captures"
    IO.FS.writeFile (System.FilePath.mk directory / s!"group-{label}.lean") output
    let old ← checked #[spawner "0.15.2" callee, worker "0.15.2"]
    require (checkFallibleSpawnCalls old |>.toOption.isNone) "pre-16 group was accepted"
  IO.println "all-version spawn policy and caller fallback pipeline fixtures passed"
