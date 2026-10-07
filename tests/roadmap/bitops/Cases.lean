import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Synthetic accepted/rejected AIR and generated semantic assertions for L02.
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
private def tupleTy (fields : Array Nat) : Json :=
  obj [("k", .str "tuple"), ("fields", .arr (fields.map fun t => obj [("ty", num t)]))]
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
  | .ok _ => throw (IO.userError s!"accepted malformed bitops case: {label}")
private def writeGenerated (dir : System.FilePath) (name : String) (files : Array Json)
    (assertions : Array String) : IO Unit := do
  let fs ← files.mapM accept
  let checks := String.join (assertions.toList.map fun proposition =>
    s!"  unless decide ({proposition}) do throw (IO.userError \"generated bitops check failed: {name}\")\n")
  IO.FS.writeFile (dir / (name ++ ".lean")) (emit fs "Bitops" "" ++
    "\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption\nprivate def isIllegal {α : Type} (r : Zig.Result α) : Bool :=\n  match r.run with\n  | some (.error .illegal) => true\n  | _ => false\ndef main : IO Unit := do\n" ++ checks)

private def countFile (name tag : String) (types : Array Json) (aty rty : Nat) : Json :=
  file name (types.push nrTy) #[aty] rty
    #[inst 0 "arg" aty #[] [("param", num 0)], inst 1 tag rty #[ref 0],
      inst 2 "ret" types.size #[ref 1]]
private def shiftFile (types : Array Json) (aty bty rty : Nat) (name := "shift") : Json :=
  file name (types.push nrTy) #[aty, bty] rty
    #[inst 0 "arg" aty #[] [("param", num 0)], inst 1 "arg" bty #[] [("param", num 1)],
      inst 2 "shl_with_overflow" rty #[ref 0, ref 1], inst 3 "ret" types.size #[ref 2]]

/-- Wider and non-power-of-two widths: (width, signed, checker count width = log2 width + 1). -/
private def wideCounts : Array (Nat × Bool × Nat) :=
  #[(16, false, 5), (32, false, 6), (64, false, 7), (128, false, 8), (128, true, 8),
    (24, false, 5), (40, false, 6), (7, true, 3)]
/-- (width, signed, Log2Int count width, top valid count, illegal counts). -/
private def wideShifts : Array (Nat × Bool × Nat × Nat × Array Nat) :=
  #[(64, false, 6, 63, #[]), (64, true, 6, 63, #[]), (128, false, 7, 127, #[]),
    (128, true, 7, 127, #[]), (24, false, 5, 23, #[24, 31]), (40, false, 6, 39, #[40, 63]),
    (7, true, 3, 6, #[7])]
private def wideName (w : Nat) (signed : Bool) : String := s!"{if signed then "i" else "u"}{w}"

private def countLoop : Json :=
  file "countLoop" #[intTy 8, intTy 4, nrTy, obj [("k", .str "bool")]] #[0] 1
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "loop" 2 #[]
      [("body", .arr #[inst 2 "ctz" 1 #[ref 0], inst 3 "cond_br" 2
        #[obj [("ty", num 3), ("val", .str "true")]]
        [("then", .arr #[inst 4 "ret" 2 #[ref 2]]),
         ("else", .arr #[inst 5 "repeat" 2 #[] [("target", num 1)]])]])]]
private def shiftLoop : Json :=
  file "shiftLoop" #[intTy 8, intTy 3, intTy 1, tupleTy #[0, 2], nrTy, obj [("k", .str "bool")]] #[0, 1] 3
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "arg" 1 #[] [("param", num 1)],
      inst 2 "loop" 4 #[] [("body", .arr #[inst 3 "shl_with_overflow" 3 #[ref 0, ref 1],
        inst 4 "cond_br" 4 #[obj [("ty", num 5), ("val", .str "true")]]
          [("then", .arr #[inst 5 "ret" 4 #[ref 3]]),
           ("else", .arr #[inst 6 "repeat" 4 #[] [("target", num 2)]])]])]]

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Cases.lean OUTPUT_DIR")
  let dir : System.FilePath := output
  IO.FS.createDirAll dir
  for tag in #["clz", "ctz", "popcount"] do
    let unsigned := countFile tag tag #[intTy 8, intTy 4] 0 1
    let signed := countFile (tag ++ "Signed") tag #[intTy 8 true, intTy 4] 0 1
    let narrow := countFile (tag ++ "Narrow") tag #[intTy 3, intTy 2] 0 1
    let one := countFile (tag ++ "One") tag #[intTy 1, intTy 1] 0 1
    let zero := file (tag ++ "Zero") #[intTy 0, nrTy] #[] 0
      #[inst 0 tag 0 #[obj [("ty", num 0), ("val", .str "0")]], inst 1 "ret" 1 #[ref 0]]
    let z : Nat := if tag == "popcount" then 0 else 8
    let mx : Nat := if tag == "popcount" then 8 else 0
    let nz : Nat := if tag == "popcount" then 0 else 3
    let nm : Nat := if tag == "popcount" then 3 else 0
    let oz : Nat := if tag == "popcount" then 0 else 1
    let om : Nat := if tag == "popcount" then 1 else 0
    writeGenerated dir tag #[unsigned, signed, narrow, one, zero]
      #[s!"successful (Bitops.{tag} 0) = some {z}",
        s!"successful (Bitops.{tag} 255) = some {mx}",
        s!"successful (Bitops.{tag}Signed (-1)) = some {mx}",
        s!"successful (Bitops.{tag}Narrow 0) = some {nz}",
        s!"successful (Bitops.{tag}Narrow 7) = some {nm}",
        s!"successful (Bitops.{tag}One 0) = some {oz}",
        s!"successful (Bitops.{tag}One 1) = some {om}",
        s!"successful Bitops.{tag}Zero = some 0"]
    reject (countFile "bad" tag #[intTy 8, intTy 3] 0 1) "count result too narrow"
    reject (countFile "bad" tag #[intTy 8, intTy 5] 0 1) "count result too wide"
    reject (countFile "bad" tag #[intTy 8, intTy 4 true] 0 1) "signed count result"
    reject (countFile "bad" tag #[obj [("k", .str "bool")], intTy 1] 0 1) "bool operand"
    reject (countFile "bad" tag #[intTy 8, intTy 4, vecTy 4 0, vecTy 3 1] 2 3) "count vector length"
    reject (countFile "bad" tag #[intTy 8, intTy 4, vecTy 4 1] 0 2) "scalar-vector count"
    reject (countFile "bad" tag #[intTy 8, intTy 4, vecTy 4 0] 2 1) "vector-scalar count"
    let _ ← accept (countFile "validVector" tag #[intTy 8, intTy 4, vecTy 4 0, vecTy 4 1] 2 3)
    writeGenerated dir (tag ++ "Vector")
      #[countFile (tag ++ "Vector") tag #[intTy 8, intTy 4, vecTy 4 0, vecTy 4 1] 2 3]
      #[s!"(successful (Bitops.{tag}Vector ⟨#v[0, 255, 0, 255]⟩)).map (fun v => v.lanes.toArray.map BitVec.toNat) = some #[{z}, {mx}, {z}, {mx}]"]
  writeGenerated dir "shiftUnsigned"
    #[shiftFile #[intTy 8, intTy 3, intTy 1, tupleTy #[0, 2]] 0 1 3]
    #["successful (Bitops.shift 0 7) = some (0, 0)",
        "successful (Bitops.shift 1 7) = some (128, 0)",
        "successful (Bitops.shift 2 7) = some (0, 1)",
        "successful (Bitops.shift 255 0) = some (255, 0)"]
  writeGenerated dir "shiftSigned"
    #[shiftFile #[intTy 8 true, intTy 3, intTy 1, tupleTy #[0, 2]] 0 1 3]
    #["successful (Bitops.shift (-1) 7) = some (128, 0)",
        "successful (Bitops.shift 1 7) = some (128, 1)",
        "successful (Bitops.shift (-128) 1) = some (0, 1)",
        "successful (Bitops.shift 127 0) = some (127, 0)"]
  writeGenerated dir "shiftNarrow"
    #[shiftFile #[intTy 3, intTy 2, intTy 1, tupleTy #[0, 2]] 0 1 3]
    #["isIllegal (Bitops.shift 0 3) = true",
        "isIllegal (Bitops.shift 1 3) = true",
        "successful (Bitops.shift 1 2) = some (4, 0)"]
  writeGenerated dir "shiftVector"
    #[shiftFile #[intTy 8, intTy 3, intTy 1, vecTy 4 0, vecTy 4 1, vecTy 4 2, tupleTy #[3, 5]] 3 4 6]
    #["(successful (Bitops.shift ⟨#v[0, 1, 2, 255]⟩ ⟨#v[7, 7, 7, 0]⟩)).map (fun (r, f) => (r.lanes.toArray.map BitVec.toNat, f.lanes.toArray.map BitVec.toNat)) = some (#[0, 128, 0, 255], #[0, 0, 1, 0])"]
  writeGenerated dir "shiftSignedVector"
    #[shiftFile #[intTy 8 true, intTy 3, intTy 1, vecTy 4 0, vecTy 4 1, vecTy 4 2, tupleTy #[3, 5]] 3 4 6]
    #["(successful (Bitops.shift ⟨#v[-1, 1, -128, 127]⟩ ⟨#v[7, 7, 1, 0]⟩)).map (fun (r, f) => (r.lanes.toArray.map BitVec.toNat, f.lanes.toArray.map BitVec.toNat)) = some (#[128, 128, 0, 127], #[0, 1, 1, 0])"]
  writeGenerated dir "invalidShiftVector"
    #[shiftFile #[intTy 3, intTy 2, intTy 1, vecTy 4 0, vecTy 4 1, vecTy 4 2, tupleTy #[3, 5]] 3 4 6]
    #["isIllegal (Bitops.shift ⟨#v[0, 0, 1, 0]⟩ ⟨#v[0, 1, 3, 2]⟩) = true"]
  writeGenerated dir "loopCapture" #[countLoop, shiftLoop]
    #["successful (((Bitops.countLoop.loop1 32).run' default).map fun e => match e with | .ret v => v | _ => 0) = some 5",
        "successful (((Bitops.shiftLoop.loop2 2 7).run' default).map fun e => match e with | .ret v => v | _ => (0, 0)) = some (0, 1)"]
  -- Each count's zero, all-ones, lowest-bit and top-bit (sign boundary) operands.
  for tag in #["clz", "ctz", "popcount"] do
    let mut files := #[]
    let mut checks := #[]
    for (w, signed, cw) in wideCounts do
      let name := tag ++ wideName w signed
      files := files.push (countFile name tag #[intTy w signed, intTy cw] 0 1)
      let (ofZero, ofOnes, ofLow, ofTop) : Nat × Nat × Nat × Nat :=
        if tag == "clz" then (w, 0, w - 1, 0)
        else if tag == "ctz" then (w, 0, 0, w - 1)
        else (0, w, 1, 1)
      let allOnes := if signed then "(-1)" else toString (2 ^ w - 1)
      checks := checks ++ #[s!"successful (Bitops.{name} 0) = some {ofZero}",
        s!"successful (Bitops.{name} {allOnes}) = some {ofOnes}",
        s!"successful (Bitops.{name} 1) = some {ofLow}",
        s!"successful (Bitops.{name} {2 ^ (w - 1)}) = some {ofTop}"]
      reject (countFile "bad" tag #[intTy w signed, intTy (cw - 1)] 0 1) s!"{name} count result too narrow"
      reject (countFile "bad" tag #[intTy w signed, intTy (cw + 1)] 0 1) s!"{name} count result too wide"
    writeGenerated dir (tag ++ "Wide") files checks
  -- Shift boundaries: count zero, the top valid count, and illegal counts the Log2Int type can hold.
  let mut shiftFiles := #[]
  let mut shiftChecks := #[]
  for (w, signed, cw, top, illegal) in wideShifts do
    let name := "shift" ++ wideName w signed
    shiftFiles := shiftFiles.push (shiftFile #[intTy w signed, intTy cw, intTy 1, tupleTy #[0, 2]] 0 1 3 name)
    let minusOne := if signed then "(-1)" else toString (2 ^ w - 1)
    shiftChecks := shiftChecks ++ #[s!"successful (Bitops.{name} 0 {top}) = some (0, 0)",
      s!"successful (Bitops.{name} {minusOne} 0) = some ({minusOne}, 0)",
      s!"successful (Bitops.{name} 1 {top}) = some ({2 ^ top}, {if signed then 1 else 0})",
      s!"successful (Bitops.{name} 3 {top}) = some ({2 ^ top}, 1)",
      s!"successful (Bitops.{name} {minusOne} {top}) = some ({2 ^ top}, {if signed then 0 else 1})"]
    for count in illegal do
      shiftChecks := shiftChecks ++ #[s!"isIllegal (Bitops.{name} 0 {count}) = true",
        s!"isIllegal (Bitops.{name} 1 {count}) = true"]
    reject (shiftFile #[intTy w signed, intTy (cw - 1), intTy 1, tupleTy #[0, 2]] 0 1 3) s!"{name} narrow Log2Int"
    reject (shiftFile #[intTy w signed, intTy (cw + 1), intTy 1, tupleTy #[0, 2]] 0 1 3) s!"{name} wide Log2Int"
  writeGenerated dir "shiftWide" shiftFiles shiftChecks
  -- Narrow (u3) and wide (u64) lanes.
  writeGenerated dir "wideVector"
    #[countFile "clzNarrowLanes" "clz" #[intTy 3, intTy 2, vecTy 4 0, vecTy 4 1] 2 3,
      shiftFile #[intTy 64, intTy 6, intTy 1, vecTy 4 0, vecTy 4 1, vecTy 4 2, tupleTy #[3, 5]] 3 4 6 "shiftWideLanes",
      shiftFile #[intTy 24, intTy 5, intTy 1, vecTy 2 0, vecTy 2 1, vecTy 2 2, tupleTy #[3, 5]] 3 4 6 "shiftOddLanes"]
    #["(successful (Bitops.clzNarrowLanes ⟨#v[0, 7, 1, 4]⟩)).map (fun v => v.lanes.toArray.map BitVec.toNat) = some #[3, 0, 2, 0]",
      s!"(successful (Bitops.shiftWideLanes ⟨#v[0, 1, 3, {2 ^ 64 - 1}]⟩ ⟨#v[63, 63, 63, 0]⟩)).map (fun (r, f) => (r.lanes.toArray.map BitVec.toNat, f.lanes.toArray.map BitVec.toNat)) = some (#[0, {2 ^ 63}, {2 ^ 63}, {2 ^ 64 - 1}], #[0, 0, 1, 0])",
      "isIllegal (Bitops.shiftOddLanes ⟨#v[1, 1]⟩ ⟨#v[23, 24]⟩) = true"]
  reject (shiftFile #[intTy 8, intTy 3 true, intTy 1, tupleTy #[0, 2]] 0 1 3) "signed shift count"
  reject (shiftFile #[intTy 8, intTy 4, intTy 1, tupleTy #[0, 2]] 0 1 3) "wrong Log2Int width"
  reject (shiftFile #[intTy 8, intTy 3, intTy 2, tupleTy #[0, 2]] 0 1 3) "overflow flag width"
  reject (shiftFile #[intTy 8, intTy 3, intTy 1 true, tupleTy #[0, 2]] 0 1 3) "signed overflow flag"
  reject (shiftFile #[intTy 8, intTy 3, intTy 1, tupleTy #[1, 2]] 0 1 3) "wrong wrapped result"
  reject (shiftFile #[intTy 8, intTy 3, intTy 1, tupleTy #[0]] 0 1 3) "missing overflow flag"
  reject (shiftFile #[intTy 8, intTy 3, intTy 1, vecTy 4 0, vecTy 3 1, vecTy 4 2, tupleTy #[3, 5]] 3 4 6) "shift vector length"
  reject (shiftFile #[intTy 8, intTy 3, intTy 1, vecTy 4 0, vecTy 4 1, vecTy 3 2, tupleTy #[3, 5]] 3 4 6) "overflow vector length"
  for tag in #["clz", "ctz", "popcount"] do
    reject (file "arity" #[intTy 8, intTy 4, nrTy] #[0] 1
      #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 tag 1 #[ref 0, ref 0], inst 2 "ret" 2 #[ref 1]]) "extra count operand"
  reject (file "arity" #[intTy 8, intTy 3, intTy 1, tupleTy #[0, 2], nrTy] #[0, 1] 3
    #[inst 0 "arg" 0 #[] [("param", num 0)], inst 1 "arg" 1 #[] [("param", num 1)],
      inst 2 "shl_with_overflow" 3 #[ref 0, ref 1, ref 1], inst 3 "ret" 4 #[ref 2]]) "extra shift operand"
  IO.println "bitops parser, normalizer and checker regressions passed"
