import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Actual parser/normalizer/checker/emitter regressions. The driver only writes source;
check.sh elaborates every emitted case serially under the root compiler guard. -/
open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def lit (n : Nat) (ty : Nat := 0) : Json := obj [("ty", num ty), ("val", toJson (toString n))]
private def intTy (bits : Nat) : Json := obj [("k", toJson "int"), ("signed", toJson false), ("bits", num bits)]
private def baseTypes : Array Json :=
  #[intTy 8, obj [("k", toJson "bool")], obj [("k", toJson "void")],
    obj [("k", toJson "noreturn")], intTy 16]
private def inst (id : Nat) (tag : String) (ty : Nat) (args : Array Json := #[])
    (extra : List (String × Json) := []) : Json :=
  obj ([("id", num id), ("tag", toJson tag), ("ty", num ty), ("args", .arr args)] ++ extra)
private def case_ (items body : Array Json) (ranges : Array Json := #[]) : Json :=
  obj [("items", .arr items), ("ranges", .arr ranges), ("body", .arr body)]
private def switch_ (id : Nat) (v : Json) (cases elseBody : Array Json) : Json :=
  inst id "loop_switch_br" 3 #[v] [("cases", .arr cases), ("else", .arr elseBody)]
private def dispatch (id target : Nat) (v : Json) : Json :=
  inst id "switch_dispatch" 3 #[v] [("target", num target)]
private def ret (id : Nat) (v : Json) : Json := inst id "ret" 3 #[v]
private def arg (id param : Nat) : Json := inst id "arg" 0 #[] [("param", num param)]
private def file (name : String) (params : Array Nat) (body : Array Json) : Json :=
  obj [("schema", num 11), ("zig_version", toJson "0.16.0"), ("target_endian", toJson "little"),
    ("name", toJson name), ("params", toJson params), ("ret", num 0),
    ("types", .arr baseTypes), ("body", .arr body)]
private def process (j : Json) : Except String Func := do
  let f ← normalize (← Raw.parseFunc j)
  check f
  pure f
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def accept (j : Json) : IO Func :=
  match process j with | .ok f => pure f | .error e => throw (IO.userError e)
private def reject (j : Json) (diagnostic : String) : IO Unit :=
  match process j with
  | .ok _ => throw (IO.userError s!"accepted malformed fixture: {diagnostic}")
  | .error e => require ((e.splitOn diagnostic).length > 1) s!"wrong diagnostic: {e} (expected {diagnostic})"
private def writeCase (dir : System.FilePath) (name : String) (j : Json) (checks : String) : IO Unit := do
  let f ← accept j
  IO.FS.writeFile (dir / (name ++ ".lean")) (emit #[f] "Dispatch" "" .ieee ++
    "\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption\n" ++ checks ++ "\n")

private def stepFile : Json := file "step" #[0]
  #[arg 10 0, switch_ 20 (ref 10)
    #[case_ #[lit 0] #[dispatch 30 20 (lit 1)], case_ #[lit 1] #[ret 40 (lit 7)]]
    #[ret 50 (lit 9)]]

/-- Reads the original SSA operand after selector replacement, not the replacement itself. -/
private def fixedCapture : Json := file "fixedCapture" #[0]
  #[arg 10 0, switch_ 20 (ref 10)
    #[case_ #[lit 0] #[dispatch 30 20 (lit 1)], case_ #[lit 1] #[ret 40 (ref 10)]]
    #[ret 50 (lit 9)]]

/-- A block-result value is captured under its caller spelling, not a nonexistent i<id>. -/
private def blockCapture : Json := file "blockCapture" #[0]
  #[arg 10 0, inst 20 "block" 0 #[] [("body", .arr #[inst 21 "br" 3 #[ref 10] [("target", num 20)]])],
    switch_ 30 (lit 0) #[case_ #[lit 0] #[dispatch 40 30 (lit 1)],
      case_ #[lit 1] #[ret 50 (ref 20)]] #[ret 60 (lit 9)]]

/-- A nested loop may dispatch to its own or an outer loop, with different selector values. -/
private def nested : Json := file "nested" #[0, 0]
  #[arg 10 0, arg 11 1, switch_ 20 (ref 10)
    #[case_ #[lit 0] #[switch_ 30 (ref 11)
      #[case_ #[lit 0] #[dispatch 40 20 (lit 1)], case_ #[lit 1] #[dispatch 50 20 (lit 2)]]
      #[dispatch 60 30 (lit 0)]],
      case_ #[lit 1] #[ret 70 (lit 77)], case_ #[lit 2] #[ret 80 (lit 88)]] #[ret 90 (lit 99)]]

/-- A dispatch crosses an ordinary loop, then an enclosing block consumes the eventual exit. -/
private def crossed : Json := file "crossed" #[0]
  #[arg 10 0, inst 20 "block" 0 #[] [("body", .arr #[switch_ 30 (ref 10)
    #[case_ #[lit 0] #[inst 40 "loop" 3 #[] [("body", .arr #[dispatch 50 30 (lit 1)])]],
      case_ #[lit 1] #[inst 60 "br" 3 #[lit 42] [("target", num 20)]]]
    #[inst 70 "br" 3 #[lit 9] [("target", num 20)]]])], ret 80 (ref 20)]

private def ranges : Json := file "ranges" #[0]
  #[arg 10 0, switch_ 20 (ref 10)
    #[case_ #[] #[dispatch 30 20 (lit 10)] #[.arr #[lit 2, lit 5]],
      case_ #[lit 10] #[ret 40 (lit 17)]] #[ret 50 (lit 23)]]

private def boolLoop : Json := (file "boolLoop" #[]
  #[switch_ 20 (obj [("ty", num 1), ("val", toJson "false")])
    #[case_ #[obj [("ty", num 1), ("val", toJson "false")]]
      #[dispatch 30 20 (obj [("ty", num 1), ("val", toJson "true")])]] #[ret 40 (lit 31)]])

/-- Selector-field spelling must not collide with a dbg-named source local. -/
private def fieldCollision : Json := (file "fieldCollision" #[0]
  #[arg 10 0, inst 11 "alloc" 5, inst 12 "dbg_var_ptr" 2 #[ref 11] [("name", toJson "dispatchValue3")],
    inst 13 "store" 2 #[ref 11, ref 10],
    switch_ 20 (lit 0) #[case_ #[lit 0] #[dispatch 30 20 (lit 1)],
      case_ #[lit 1] #[inst 40 "load" 0 #[ref 11], ret 50 (ref 40)]] #[ret 60 (lit 9)]])
  |>.setObjVal! "types" (.arr (baseTypes.push
    (obj [("k", toJson "ptr"), ("size", toJson "one"), ("const", toJson false), ("child", num 0)])))

/-- An ordinary loop can leave an enclosing block without owning any repeat exit. -/
private def plainExit : Json := file "plainExit" #[]
  #[inst 10 "block" 0 #[] [("body", .arr #[inst 20 "loop" 3 #[]
    [("body", .arr #[inst 30 "br" 3 #[lit 38] [("target", num 10)]])]])], ret 40 (ref 10)]

/-- A noreturn block with no own-target branch propagates an outer dispatch directly. -/
private def blockDispatch : Json := file "blockDispatch" #[0]
  #[arg 10 0, switch_ 20 (ref 10)
    #[case_ #[lit 0] #[inst 30 "block" 3 #[] [("body", .arr #[dispatch 40 20 (lit 1)])],
      ret 50 (lit 7)], case_ #[lit 1] #[ret 60 (lit 44)]] #[ret 70 (lit 9)]]

private def malformed (target : Nat) : Json := file "badTarget" #[0]
  #[arg 10 0, inst 11 "block" 2 #[] [("body", .arr #[switch_ 20 (ref 10)
    #[case_ #[lit 0] #[dispatch 30 target (lit 1)]] #[ret 40 (lit 7)]])]]

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Emitter.lean OUTPUT_DIR")
  let dir : System.FilePath := output
  IO.FS.createDirAll dir
  writeCase dir "step" stepFile
    "example : successful ((Dispatch.step 0).map BitVec.toNat) = some 7 := by native_decide\nexample : successful ((Dispatch.step 2).map BitVec.toNat) = some 9 := by native_decide"
  writeCase dir "fixedCapture" fixedCapture
    "example : successful ((Dispatch.fixedCapture 0).map BitVec.toNat) = some 0 := by native_decide"
  writeCase dir "blockCapture" blockCapture
    "example : successful ((Dispatch.blockCapture 19).map BitVec.toNat) = some 19 := by native_decide"
  writeCase dir "nested" nested
    "example : successful ((Dispatch.nested 0 2).map BitVec.toNat) = some 77 := by native_decide\nexample : successful ((Dispatch.nested 0 1).map BitVec.toNat) = some 88 := by native_decide\nexample : successful ((Dispatch.nested 2 0).map BitVec.toNat) = some 88 := by native_decide"
  writeCase dir "crossed" crossed
    "example : successful ((Dispatch.crossed 0).map BitVec.toNat) = some 42 := by native_decide"
  writeCase dir "ranges" ranges
    "example : successful ((Dispatch.ranges 2).map BitVec.toNat) = some 17 := by native_decide\nexample : successful ((Dispatch.ranges 5).map BitVec.toNat) = some 17 := by native_decide\nexample : successful ((Dispatch.ranges 6).map BitVec.toNat) = some 23 := by native_decide"
  writeCase dir "boolLoop" boolLoop
    "example : successful (Dispatch.boolLoop.map BitVec.toNat) = some 31 := by native_decide"
  writeCase dir "fieldCollision" fieldCollision
    "example : successful ((Dispatch.fieldCollision 13).map BitVec.toNat) = some 13 := by native_decide"
  writeCase dir "plainExit" plainExit
    "example : successful (Dispatch.plainExit.map BitVec.toNat) = some 38 := by native_decide"
  writeCase dir "blockDispatch" blockDispatch
    "example : successful ((Dispatch.blockDispatch 0).map BitVec.toNat) = some 44 := by native_decide"
  reject (malformed 11) "not an enclosing loop-switch"
  reject (malformed 10) "not an enclosing loop-switch"
  reject (malformed 999) "not an enclosing loop-switch"
  reject (file "outside" #[] #[dispatch 10 20 (lit 0), switch_ 20 (lit 0) #[] #[ret 30 (lit 0)]]) "not an enclosing loop-switch"
  reject (file "sibling" #[] #[switch_ 20 (lit 0) #[] #[ret 30 (lit 0)],
    switch_ 40 (lit 0) #[] #[dispatch 50 20 (lit 1)]]) "not an enclosing loop-switch"
  reject (file "wrongType" #[] #[switch_ 20 (lit 0) #[] #[dispatch 30 20 (lit 1 4)]]) "dispatch operand type differs"
  reject (file "missingOperand" #[] #[switch_ 20 (lit 0) #[]
    #[inst 30 "switch_dispatch" 3 #[] [("target", num 20)]]]) "exactly 1 arg"
  reject (file "extraOperand" #[] #[switch_ 20 (lit 0) #[]
    #[inst 30 "switch_dispatch" 3 #[lit 0, lit 1] [("target", num 20)]]]) "exactly 1 arg"
  reject (file "hiddenSiblingValue" #[0] #[arg 10 0, switch_ 20 (ref 10)
    #[case_ #[lit 0] #[inst 30 "intcast" 0 #[ref 10], dispatch 40 20 (lit 1)],
      case_ #[lit 1] #[ret 50 (ref 30)]] #[ret 60 (lit 0)]]) "not available in this scope"
  let direct ← accept stepFile
  let forged := { direct with body := #[{ id := 200, ty := 3, op := .switchDispatch 999 (.int 0 0) }] }
  match check forged with
  | .ok _ => throw (IO.userError "direct Core bypassed dispatch scope checking")
  | .error _ => pure ()
  IO.println "dispatch parser and emitter generation passed"
