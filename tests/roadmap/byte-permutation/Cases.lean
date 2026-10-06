import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Synthetic accepted/rejected AIR and generated semantic assertions for byte permutations.
The caller runs this driver and executes each generated file separately.
Generated edge checks use ordinary compiled evaluation; Runtime.lean checks pure
semantic assertions with kernel reduction. -/
open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", .str tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def intTy (n : Nat) (s : Bool := false) : Json :=
  obj [("k", .str "int"), ("signed", .bool s), ("bits", num n)]
private def vecTy (len child : Nat) : Json :=
  obj [("k", .str "vector"), ("len", num len), ("child", num child)]
private def nrTy : Json := obj [("k", .str "noreturn")]
private def file (name : String) (types : Array Json) (params : Array Nat) (ret : Nat)
    (body : Array Json) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("name", .str name),
    ("types", .arr types), ("params", toJson params), ("ret", num ret), ("body", .arr body)]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def accept (j : Json) : IO Func :=
  match process j with
  | .ok f => pure f
  | .error e => throw (IO.userError e)
private def reject (j : Json) (label : String) : IO Unit :=
  match process j with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"accepted malformed permutation case: {label}")
private def writeGenerated (dir : System.FilePath) (name : String) (files : Array Json)
    (assertions : Array String) : IO Unit := do
  let fs ← files.mapM accept
  let checks := String.join (assertions.toList.map fun proposition =>
    s!"  unless decide ({proposition}) do throw (IO.userError \"generated permutation check failed: {name}\")\n")
  IO.FS.writeFile (dir / (name ++ ".lean")) (emit fs "Permutations" "" ++
    "\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption\ndef main : IO Unit := do\n" ++ checks)

private def permutationFile (name tag : String) (types : Array Json) (aty rty : Nat)
    (args : Array Json := #[ref 0]) : Json :=
  file name (types.push nrTy) #[aty] rty
    #[inst 0 "arg" aty #[] [("param", num 0)], inst 1 tag rty args,
      inst 2 "ret" types.size #[ref 1]]

private def loopFile (tag : String) : Json :=
  file "captured" #[intTy 16, nrTy, obj [("k", .str "bool")]] #[0] 0
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "loop" 1 #[]
      [("body", .arr #[inst 2 tag 0 #[ref 0], inst 3 "cond_br" 1
        #[obj [("ty", num 2), ("val", .str "true")]]
        [("then", .arr #[inst 4 "ret" 1 #[ref 2]]),
         ("else", .arr #[inst 5 "repeat" 1 #[] [("target", num 1)]])]])]]

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Cases.lean OUTPUT_DIR")
  let dir : System.FilePath := output
  IO.FS.createDirAll dir
  for tag in #["byte_swap", "bit_reverse"] do
    for width in #[0, 8, 16, 24, 64, 128, 65528] do
      for signed in #[false, true] do
        let _ ← accept (permutationFile "valid" tag #[intTy width signed] 0 0)
    if tag == "bit_reverse" then
      for width in #[1, 3, 9, 65, 65535] do
        for signed in #[false, true] do
          let _ ← accept (permutationFile "valid" tag #[intTy width signed] 0 0)
    for signed in #[false, true] do
      let _ ← accept (permutationFile "validVector" tag #[intTy 16 signed, vecTy 3 0] 1 1)
    reject (permutationFile "bad" tag #[intTy 16, intTy 16 true] 0 1) "changed sign"
    reject (permutationFile "bad" tag #[intTy 16, intTy 8] 0 1) "changed width"
    reject (permutationFile "bad" tag #[intTy 16, vecTy 3 0] 0 1) "scalar to vector"
    reject (permutationFile "bad" tag #[intTy 16, vecTy 3 0] 1 0) "vector to scalar"
    reject (permutationFile "bad" tag #[intTy 16, vecTy 3 0, vecTy 4 0] 1 2) "changed lane count"
    reject (permutationFile "bad" tag #[intTy 16, intTy 16 true, vecTy 3 0, vecTy 3 1] 2 3) "changed lane sign"
    for bad in #[obj [("k", .str "bool")], obj [("k", .str "float"), ("bits", num 32)]] do
      reject (permutationFile "bad" tag #[bad] 0 0) "noninteger scalar"
      reject (permutationFile "bad" tag #[bad, vecTy 3 0] 1 1) "noninteger vector"
    reject (permutationFile "bad" tag #[intTy 16] 0 0 #[]) "missing operand"
    reject (permutationFile "bad" tag #[intTy 16] 0 0 #[ref 0, ref 0]) "extra operand"
    reject (permutationFile "bad" tag #[intTy 16] 0 0 #[ref 99]) "unknown operand"
    let name := if tag == "byte_swap" then "swap" else "reverse"
    let value := if tag == "byte_swap" then "13330" else "11336"
    writeGenerated dir name
      #[permutationFile name tag #[intTy 16] 0 0,
        permutationFile (name ++ "Signed") tag #[intTy 16 true] 0 0,
        permutationFile (name ++ "Vector") tag #[intTy 16, vecTy 3 0] 1 1]
      #[s!"successful (Permutations.{name} 4660) = some {value}",
        s!"successful (Permutations.{name}Signed 4660) = some {value}",
        s!"(successful (Permutations.{name}Vector ⟨#v[4660, 4660, 4660]⟩)).map (fun v => v.lanes.toArray.map BitVec.toNat) = some #[{value}, {value}, {value}]"]
    writeGenerated dir (name ++ "Loop") #[loopFile tag]
      #[s!"successful (((Permutations.captured.loop1 4660).run' default).map fun e => match e with | .ret v => v | _ => 0) = some {value}"]
  for width in #[1, 3, 9, 65, 65535] do
    reject (permutationFile "unaligned" "byte_swap" #[intTy width] 0 0) "unaligned byte width"
    reject (permutationFile "unaligned" "byte_swap" #[intTy width, vecTy 3 0] 1 1) "unaligned lane width"
  writeGenerated dir "narrow"
    #[permutationFile "narrow" "bit_reverse" #[intTy 3 true] 0 0,
      permutationFile "narrowVector" "bit_reverse" #[intTy 3 true, vecTy 3 0] 1 1]
    #["successful (Permutations.narrow (-4)) = some 1",
      "(successful (Permutations.narrowVector ⟨#v[1, 2, 3]⟩)).map (fun v => v.lanes.toArray.map BitVec.toNat) = some #[4, 2, 6]"]
  IO.println "permutation parser, normalizer and checker regressions passed"
