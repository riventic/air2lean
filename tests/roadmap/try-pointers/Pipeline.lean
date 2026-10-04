import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

open Lean Air2Lean
private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def node (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def pointer (child align : Nat) (isConst : Bool := false) (size : String := "one") :=
  obj [("k", .str "ptr"), ("size", .str size), ("const", .bool isConst), ("child", num child),
    ("ptr_align", num align), ("abi_size", num 8), ("abi_align", num 8)]
private def int8 := obj [("k", .str "int"), ("signed", .bool false), ("bits", num 8),
  ("abi_size", num 1), ("abi_align", num 1)]
private def union (payload size align : Nat) := obj [("k", .str "error_union"),
  ("error", num 1), ("payload", num payload), ("abi_size", num size), ("abi_align", num align)]
private def types (isConst : Bool := false) : Array Json :=
  #[int8, obj [("k", .str "error_set"), ("errors", .arr #[.str "Bad", .str "Other"]),
      ("abi_size", num 2), ("abi_align", num 2)], union 0 4 2,
    pointer 2 2 isConst, pointer 0 1 isConst, union 4 16 8,
    obj [("k", .str "noreturn")], obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)]]
private def errBody : Array Json :=
  #[node 2 "unwrap_errunion_err_ptr" 1 #[ref 0], node 3 "wrap_errunion_err" 5 #[ref 2],
    node 4 "ret" 6 #[ref 3]]
private def file (name tag : String) (ts : Array Json := types) (body : Array Json := errBody)
    (args : Array Json := #[ref 0]) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr ts), ("params", toJson (#[3] : Array Nat)),
    ("ret", num 5), ("body", .arr #[node 0 "arg" 3 #[] [("param", num 0)],
      node 1 tag 4 args [("body", .arr body)], node 5 "wrap_errunion_payload" 5 #[ref 1],
      node 6 "ret" 6 #[ref 5]])]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  let _ ← checkProgram #[f]
  pure f
private def accept (j : Json) : IO Func := do
  match process j with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def require (test : Bool) (message : String) : IO Unit := do
  unless test do throw (IO.userError message)
private def reject (j : Json) (name expected : String) : IO Unit := do
  match process j with
  | .ok _ => throw (IO.userError s!"accepted malformed pointer try: {name}")
  | .error e => require ((e.splitOn expected).length > 1) s!"wrong {name} diagnostic: {e}"

-- mode 0: unused load; 1: used only by nested returns; 2: stored value;
-- mode 3: used by a block's branch value. A bit-pointer still reads the entire host.
private def loadFile (name : String) (mode : Nat) (bitPointer : Bool := false) : Json :=
  let ptr := if bitPointer then
      ((pointer 0 2).setObjVal! "host_size" (num 2)).setObjVal! "bit_offset" (num 0)
    else pointer 0 1
  let ts := #[int8, ptr, obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)],
    obj [("k", .str "noreturn")], obj [("k", .str "bool"), ("abi_size", num 1), ("abi_align", num 1)]]
  let lit (ty : Nat) (v : String) := obj [("ty", num ty), ("val", .str v)]
  let finish := match mode with
    | 0 => #[node 3 "ret" 3 #[lit 2 "{}"]]
    | 1 => #[node 3 "cond_br" 3 #[ref 1] [("then", .arr #[node 4 "ret" 3 #[ref 2]]),
      ("else", .arr #[node 5 "ret" 3 #[lit 0 "7"]])]]
    | 2 => #[node 3 "store" 2 #[ref 1, ref 2], node 4 "ret" 3 #[lit 2 "{}"]]
    | _ => #[node 3 "block" 0 #[] [("body", .arr #[node 4 "br" 3 #[ref 2] [("target", num 3)]])],
      node 5 "ret" 3 #[ref 3]]
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr ts),
    ("params", toJson (#[1, if mode == 2 then 1 else 4] : Array Nat)),
    ("ret", num (if mode == 0 || mode == 2 then 2 else 0)),
    ("body", .arr (#[node 0 "arg" 1 #[] [("param", num 0)],
      node 1 "arg" (if mode == 2 then 1 else 4) #[] [("param", num 1)],
      node 2 "load" 0 #[ref 0]] ++ finish))]

private def placeFile : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str "place"), ("types", .arr #[int8, pointer 0 1,
      obj [("k", .str "void"), ("abi_size", num 0), ("abi_align", num 1)],
      obj [("k", .str "noreturn")]]), ("params", toJson (#[0] : Array Nat)), ("ret", num 0),
    ("body", .arr #[node 0 "arg" 0 #[] [("param", num 0)], node 1 "alloc" 1,
      node 2 "store" 2 #[ref 1, ref 0], node 3 "load" 0 #[ref 1], node 4 "ret" 3 #[ref 0]])]

private def writeLoadCases (output : String) : IO Unit := do
  let unused ← accept (loadFile "unused" 0)
  let nested ← accept (loadFile "nested" 1)
  let stored ← accept (loadFile "stored" 2)
  let blockUsed ← accept (loadFile "blockUsed" 3)
  let bitUnused ← accept (loadFile "bitUnused" 0 true)
  let place ← accept placeFile
  for f in #[unused, nested, stored, blockUsed, bitUnused] do
    let fc := mkFCtx f #[] #[] .ieee #[f.name] #[]
    let some load := f.allInsts.find? (fun i => match i.op with | .load _ => true | _ => false)
      | throw (IO.userError "load fixture lost its load")
    let expected := f.name == "nested" || f.name == "stored" || f.name == "blockUsed"
    require (fc.isReferenced load.id == expected) s!"wrong cached load use for {f.name}"
  let placeGen := emit #[place] "PurePlace" "" .ieee
  require ((placeGen.splitOn "loadDiscardBytes").length == 1) "changed pure-place unused-load behavior"
  let generated := emit #[unused, nested, stored, blockUsed, bitUnused, place] "LoadCases" "" .ieee
  require ((generated.splitOn "Zig.loadDiscardBytes").length == 3) "wrong unused-load emitter count"
  require ((generated.splitOn "Zig.loadDiscardBytes 2 2").length == 2) "bit-pointer did not retain full host read"
  IO.FS.writeFile (output ++ ".loads.lean") (generated ++ "\n" ++
"open Zig\nderiving instance DecidableEq for Except\nprivate def value (c : MemM α) := (c.run {}).run.map (·.map Prod.fst)\nprivate def discardFootprints (bit : Bool) : MemM (Array Nat) := do\n  let p ← alloc .heap (if bit then 2 else 1) (if bit then 2 else 1)\n  if bit then LoadCases.bitUnused p true else LoadCases.unused p true\n  pure ((← get).footprint.map (·.len))\nprivate def used (f : Ptr → Bool → MemM (BitVec 8)) (initialized : Bool) : MemM (BitVec 8) := do\n  let p ← alloc .heap 1 1\n  if initialized then store 1 p (17#8)\n  f p true\nprivate def stored : MemM (BitVec 8) := do\n  let p ← alloc .heap 1 1\n  let q ← alloc .heap 1 1\n  store 1 p (13#8)\n  LoadCases.stored p q\n  load (BitVec 8) 1 q\nprivate def badBounds : MemM Unit := do\n  let p ← alloc .heap 0 1\n  LoadCases.unused p false\nprivate def badAlignment : MemM Unit := do\n  let p ← alloc .heap 3 2\n  LoadCases.bitUnused (p.add 1) false\ndef main : IO Unit := do\n  unless value (discardFootprints false) = some (.ok #[1]) do throw (IO.userError \"unused raw read lost access/footprint\")\n  unless value (discardFootprints true) = some (.ok #[2]) do throw (IO.userError \"unused bit-pointer lost host access/footprint\")\n  for f in [LoadCases.nested, LoadCases.blockUsed] do\n    unless value (used f true) = some (.ok 17) do throw (IO.userError \"nested/block read value lost\")\n    unless value (used f false) = some (.error .unspecified) do throw (IO.userError \"used value decoder removed\")\n  unless value stored = some (.ok 13) do throw (IO.userError \"stored read value lost\")\n  unless value badBounds = some (.error .illegal) do throw (IO.userError \"unused read bounds removed\")\n  unless value badAlignment = some (.error .illegal) do throw (IO.userError \"unused bit-pointer alignment removed\")\n  unless (LoadCases.place 17 : Result (BitVec 8)).run = some (.ok (17#8)) do throw (IO.userError \"pure-place behavior changed\")\n  IO.println \"unused/used/nested/block/stored/bit-pointer load regressions passed\"\n")

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Pipeline.lean OUTPUT_FILE")
  let hot ← accept (file "hot" "try_ptr")
  let cold ← accept (file "cold" "try_ptr_cold")
  let constPointer ← accept (file "constPointer" "try_ptr" (types true))
  for version in ["0.14.1", "0.15.2", "0.16.0"] do
    let _ ← accept ((file "version" "try_ptr_cold").setObjVal! "zig_version" (.str version))
  reject (file "bad" "try_ptr" ((types false).set! 3 (pointer 0 1))) "nonunion operand" "pointer to an error union"
  reject (file "bad" "try_ptr" ((types false).set! 3 (pointer 2 2 false "many"))) "many operand" "single pointer"
  reject (file "bad" "try_ptr" ((types false).set! 4 (pointer 1 2))) "wrong payload" "same payload"
  reject (file "bad" "try_ptr" ((types true).set! 4 (pointer 0 1))) "lost constness" "matching constness"
  reject (file "bad" "try_ptr" types errBody #[]) "missing operand" "exactly 1 arg"
  reject (file "bad" "try_ptr" types errBody #[ref 0, ref 0]) "extra operand" "exactly 1 arg"
  reject (file "bad" "try_ptr" types #[]) "fallthrough error body" "must exit"
  reject (file "bad" "try_ptr" ((types false).set! 3 ((pointer 2 2).setObjVal! "volatile" (.bool true))))
    "volatile operand" "volatile pointer"
  reject (file "bad" "try_ptr" ((types false).set! 4 ((pointer 0 1).setObjVal! "volatile" (.bool true))))
    "volatile result" "volatile pointer"
  reject (file "bad" "try_ptr" ((types false).set! 3 (((pointer 2 2).setObjVal! "host_size" (num 4)).setObjVal! "bit_offset" (num 0))))
    "bit-pointer operand" "bit-pointer"
  reject (file "bad" "try_ptr" ((types false).set! 4 (obj [("k", .str "ptr"), ("size", .str "one"),
    ("const", .bool false), ("child", num 0), ("abi_size", num 8), ("abi_align", num 8)])))
    "missing result alignment" "no ptr_align"
  reject (file "bad" "try_ptr" types #[node 2 "unwrap_errunion_err_ptr" 1 #[ref 1],
    node 3 "wrap_errunion_err" 5 #[ref 2], node 4 "ret" 6 #[ref 3]])
    "payload value captured in error branch" "not available in this scope"
  let generated := emit #[hot, cold, constPointer] "SyntheticTry" "" .ieee
  require ((generated.splitOn "Zig.tryPayloadPtr").length == 4) "pointer try did not use the tag-only runtime helper"
  IO.FS.writeFile output (generated ++ "\n" ++
"open Zig\nderiving instance DecidableEq for Except\nprivate def observe (f : Ptr → MemM (Except ErrName Ptr)) (err : Option ErrName) : MemM (Bool × Except ErrName (BitVec 8)) := do\n  let p ← alloc .heap 4 2\n  match err with\n  | some e => store 2 p (Except.error e : Except ErrName (BitVec 8))\n  | none => let _ ← errSetOk (BitVec 8) 2 p; pure ()\n  match ← f p with\n  | .error e => pure (err == some e, ← load (Except ErrName (BitVec 8)) 2 p)\n  | .ok q =>\n    store 1 q (99#8)\n    pure (q == errPayloadPtr (BitVec 8) p, ← load (Except ErrName (BitVec 8)) 2 p)\nprivate def value (c : MemM α) := (c.run {}).run.map (·.map Prod.fst)\ndef main : IO Unit := do\n  for f in [SyntheticTry.hot, SyntheticTry.cold] do\n    unless value (observe f none) = some (.ok (true, .ok 99)) do throw (IO.userError \"alias/undefined-payload regression\")\n    for e in [\"Bad\", \"Other\"] do\n      unless value (observe f (some e)) = some (.ok (true, .error e)) do throw (IO.userError \"error preservation regression\")\n  IO.println \"synthetic pointer-try semantic regressions passed\"\n")
  writeLoadCases output
  IO.println "pointer-try parser/checker/emitter regressions passed"
