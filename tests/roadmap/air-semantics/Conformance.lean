import Air2Lean.Air.Anon
import Air2Lean.Air.Effects
import Air2Lean.Air.Normalize
import Air2Lean.Certificate
import Air2Lean.Check
import Air2Lean.Sem
import Lean.Data.Json

/-!
Conformance of the AIR interpreter on the differential corpus (V01 stage 7,
docs/air-semantics.md §Conformance): the interpreter's side.

For each example of the manifest this decodes the example's AIR files as the translator does
(`Anon.renumberAllWithNames`, `decode`), and for each corpus function
(`tests/diff/<ex>/inputs/<fn>.jsonl`) either runs `Sem.run` on every input line or records why
the function is outside the interpreter's coverage:

* an instruction whose constructor has no arm (`Sem.outside?`, with its reason and stage);
* an instruction, parameter, result or constant of a value kind that has no `Sem.Value`
  (`kindReason`, `constReason`);
* a call that is not a direct call to a function of the program or to a panic handler.

The reasons cover the function and every function it can reach by direct calls. Nothing is
dropped: a function without a reason runs on every input, and a run that is stuck all the same
is written as `{"stuck":true}`, which `conformance.py` reports as a gap of this classifier.

An input is the harness's (`tests/diff/Diff.lean`): a JSON array of arguments, or
`{"bufs":[…],"args":[…]}` for a function that uses memory, where a pointer is
`{"buf":i,"off":o}` and a slice has a `"len"` too. A slice argument of the array form (the
generated model takes the items) becomes a buffer here. The memory starts empty (`{}`): a
function inside the coverage reads no global, so only the block numbers differ from the model's
`mem0`, and a result is written relative to the first buffer, as `Diff.lean` writes it.

The output lines have `Diff.lean`'s wire format (`{"ok":…}`, `{"fail":"Zig.Error.…"}`), with
`Outcome.lean`'s kind next to each.

This is the executable `air-semantics-conformance` of the fixture package
(tests/roadmap/lakefile.toml), compiled: Lean's interpreter runs the corpus about fifty times
slower. `conformance.py` builds it, writes its manifest and compares its output.
-/

open Lean (Json)
open Air2Lean Air2Lean.Sem

namespace Conformance

/-! ## Coverage -/

/-- Why a value of the type `t` has no `Sem.Value`, or `none`. A pointer is a value whatever it
points to. -/
def kindReason (f : Func) : Nat → TyId → Option String
  | 0, _ => some "a type nested deeper than optionals and error unions go"
  | n + 1, t =>
    match f.types[t]? with
    | none => some "a type id outside the type table"
    | some (.int ..) | some .bool | some .void | some .noreturn | some (.errorSet _) => none
    | some (.ptr size ..) =>
      if f.plainPtr t || f.plainSlice t then none
      else if size == "c" then some "C pointers (not staged)"
      else some "volatile, allowzero, bit-packed or sentinel-terminated pointers (not staged)"
    | some (.optional c) =>
      if f.types[c]? matches some (.ptr ..) then some "pointer optionals (stage 4)"
      else kindReason f n c
    | some (.errorUnion _ p) => kindReason f n p
    | some (.float _) => some "float values (stage 5)"
    | some (.vector ..) => some "vector values (stage 5)"
    | some (.array ..) => some "array values (stage 4)"
    | some (.struct ..) | some (.tuple _) => some "struct values (stage 4)"
    | some (.enum ..) => some "enum values (stage 4)"
    | some (.union ..) => some "union values (stage 4)"
    | some .allocator | some .thread | some .io | some (.future _) =>
      some "std handles: allocator, thread, io, future (stage 6)"
    | some (.opaque ..) | some (.other _) => some "opaque and other types (not staged)"

/-- Why `Sem.operand` has no value for the constant `v`, or `none` (`undefined` is the value of
a `store` only: `storeOk`). -/
def constReason (storeOk : Bool) : Val → Option String
  | .inst _ | .int .. | .bool _ | .void | .optNull _ | .optSome .. | .err .. | .errUnionErr ..
  | .errUnionOk .. => none
  | .undef _ => if storeOk then none else some "`undefined` operands (not staged)"
  | .float .. => some "float values (stage 5)"
  | .func .. => some "function values: indirect calls (stage 6)"
  | .enumTag .. => some "enum values (stage 4)"
  | .unionVal .. => some "union values (stage 4)"
  | .agg .. => some "aggregate constants (stage 4)"
  | .ptrConst .. => some "pointers to globals (stage 4)"
  | .ptrNull _ => some "null pointer constants (stage 4)"
  | .ptrOther .. => some "comptime pointers (not staged)"
  | .ptrInt .. => some "pointers from integers (not staged)"
  | .sliceConst .. => some "slice constants (stage 4)"

/-- The operands that an arm evaluates (debug instructions evaluate none; a constructor
without an arm has its `Sem.outside?` reason instead). -/
def opVals : Op → List Val
  | .arith _ _ a b | .div _ a b | .minMax _ a b | .bit _ a b | .cmp _ a b | .boolAnd a b
  | .boolOr a b | .sliceElemVal a b | .ptrAdd _ a b | .elemPtr a b | .ptrElemVal a b
  | .store a b => [a, b]
  | .not a | .intCast _ a | .trunc a | .bitcast _ a | .isNull a | .isNonNull a | .optPayload a
  | .wrapOptional a | .isErr a | .isNonErr a | .errPayload a | .errCode a | .wrapErrPayload a
  | .wrapErr a | .fieldPtr a _ | .load a | .sliceLen a | .slicePtr a | .br _ a | .condBr a ..
  | .«try» a _ | .ret a => [a]
  | .switchBr v cases _ =>
    v :: cases.toList.flatMap fun c => c.items.toList ++ c.ranges.toList.flatMap fun (l, h) => [l, h]
  | .call _ args => args.toList
  | _ => []

/-- Why a value of the type `t`, which has a `Sem.Value`, has no load or store: `loadAs` and
`storeAs` read and write integers, `bool` and plain pointers. -/
def memReason (f : Func) (t : TyId) : Option String :=
  match f.types[t]? with
  | some (.int ..) | some .bool => none
  | some (.ptr ..) => if f.plainPtr t then none else some "slices in memory (stage 4)"
  | some (.optional _) => some "optionals in memory (stage 4)"
  | some (.errorUnion ..) | some (.errorSet _) => some "error unions and errors in memory (stage 4)"
  | _ => some "`void` in memory (not staged)"

/-- The reasons of an arm that takes only some of the value kinds: a memory access of a value
that is not an integer, `bool` or pointer (a register local holds any value), a comparison, a
switch selector, a cast, a field pointer. A type with a `kindReason` is reported by that. `all`:
every instruction of `f`. -/
def shapeReasons (f : Func) (all : Array Inst) (tyOf : InstId → Option TyId) (i : Inst) :
    List String :=
  let tyOfVal : Val → Option TyId
    | .inst x => tyOf x
    | v => v.constTy?
  let valued (t : TyId) : Bool := (kindReason f 4 t).isNone
  let isInt (t : TyId) : Bool := (intTy? f t).isSome
  let cell : Val → Bool
    | .inst a => all.any (fun j => j.id == a && j.op matches .alloc) && regAlloc f a
    | _ => false
  let mem (t : Option TyId) : List String :=
    (t.bind fun t => if valued t then memReason f t else none).toList
  -- `ok t` of the operand's type, when it has a value kind.
  let operand (v : Val) (ok : TyId → Bool) (reason : String) : List String :=
    match tyOfVal v with
    | some t => if !valued t || ok t then [] else [reason]
    | none => []
  match i.op with
  | .load p => if cell p then [] else mem (some i.ty)
  | .store p v => if cell p then [] else mem (tyOfVal v)
  | .ptrElemVal .. | .sliceElemVal .. => mem (some i.ty)
  | .cmp _ a _ => operand a (fun t => isInt t || f.types[t]? matches some .bool || f.plainPtr t)
      "comparisons of slices, optionals and errors (stage 4)"
  | .switchBr v .. => operand v isInt "a switch on a `bool` or an error (stage 4)"
  | .bitcast _ a => if !valued i.ty then [] else
      operand a (fun t => (isInt t && isInt i.ty) || (f.plainPtr t && f.plainPtr i.ty))
        "casts other than integer to integer and pointer to pointer (stage 4)"
  | .intCast _ a | .trunc a => if !valued i.ty then [] else
      operand a (fun t => isInt t && isInt i.ty) "integer casts of values that are not integers (stage 4)"
  | .fieldPtr base idx => operand base (fun t => (f.fieldOffset? t idx).isSome)
      "fields of packed structs and unions (stage 4)"
  | _ => []

/-- The reasons that keep one instruction of `f` outside the coverage, each as
`<constructor>: <reason>`. `all`: every instruction of `f`, `tyOf`: the type of each. `callOk`: a
direct call to this name runs (a function of the program). -/
def instReasons (f : Func) (all : Array Inst) (tyOf : InstId → Option TyId)
    (callOk : String → Bool) (i : Inst) : List String :=
  let name := i.op.ctorName
  match outside? i.op with
  | some reason => [s!"{name}: {reason}"]
  | none =>
    let callee : List String := match i.op with
      | .call (.func callee ..) _ =>
        if (panicOf? callee).isSome || callOk callee then []
        else ["call: a function outside the program (an external or std model, stage 6)"]
      | .call .. => ["call: indirect calls (stage 6)"]
      | _ => []
    -- A call to a panic handler evaluates no argument.
    let vals := match i.op with
      | .call (.func callee ..) _ => if (panicOf? callee).isSome then [] else opVals i.op
      | _ => opVals i.op
    let storeVal := match i.op with | .store _ v => some v | _ => none
    let ofVal (v : Val) : List String :=
      match constReason (storeVal == some v) v with
      | some r => [r]
      | none =>
        match v with
        | .inst x => ((tyOf x).bind (kindReason f 4)).toList
        | _ => (v.constTy?.bind (kindReason f 4)).toList
    callee ++ (((kindReason f 4 i.ty).toList ++ vals.flatMap ofVal ++ shapeReasons f all tyOf i).eraseDups.map
      fun r => s!"{name}: {r}")

/-- Every instruction of `f`, nested bodies included. -/
def insts (f : Func) : Array Inst := Certificate.allInsts f.body

/-- The reasons of `f` alone: its parameter and result types, then its instructions. -/
def funcReasons (p : Program) (f : Func) : List String :=
  let all := insts f
  let tyOf (x : InstId) : Option TyId := (all.find? (·.id == x)).map (·.ty)
  let params := f.params.toList.filterMap fun t => (kindReason f 3 t).map (s!"parameter: {·}")
  let ret := match f.types[f.ret]? with
    | some (.errorSet _) => ["result: harness: a bare error has no rendering"]
    | _ => ((kindReason f 3 f.ret).map (s!"result: {·}")).toList
  params ++ ret ++ all.toList.flatMap (instReasons f all tyOf fun n => (p.lookup n).isSome)

/-- The functions of `p` that `f` reaches by direct calls, `f` first. -/
def reach (p : Program) (f : Func) : Array Func := Id.run do
  let mut seen : Array Func := #[f]
  let mut k := 0
  -- Each pass handles one reached function; a function is added once.
  for _ in [:p.funcs.size + 1] do
    let some g := seen[k]? | break
    k := k + 1
    for i in insts g do
      if let .call (.func callee ..) _ := i.op then
        if let some h := p.lookup callee then
          unless seen.any (·.name == h.name) do seen := seen.push h
  return seen

/-- The coverage reasons of the corpus function `f`: `(function holding the instructions,
reason, instruction count)`. -/
def reasons (p : Program) (f : Func) : Array (String × String × Nat) :=
  (reach p f).flatMap fun g =>
    let rs := funcReasons p g
    rs.eraseDups.toArray.map fun r => (g.name, r, rs.count r)

/-! ## Inputs -/

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def intOf (j : Json) : Except String Int :=
  match j with
  | .str s => match s.toInt? with
    | some n => pure n
    | none => throw s!"not an integer: {s}"
  | j => j.getInt?

/-- A pointer `{"buf":i,"off":o}` into the input buffers (block `i`: the memory starts empty). -/
def ptrOf (j : Json) : Except String Zig.Ptr := do
  pure ⟨some (← intOf (← field j "buf")).toNat, ← intOf (← field j "off")⟩

/-- The argument `j` of the AIR type `t`. -/
def argOf (f : Func) : Nat → TyId → Json → Except String Value
  | 0, _, _ => throw "an argument type nested too deep"
  | n + 1, t, j =>
    match f.types[t]? with
    | some (.int s w) => do pure (.int s w (BitVec.ofInt w (← intOf j)))
    | some .bool =>
      match j with
      | .bool b => pure (.bool b)
      | j => do pure (.bool ((← intOf j) != 0))
    | some .void => pure .void
    | some (.ptr ..) =>
      if f.plainSlice t then do
        pure (.slice ⟨← ptrOf j, BitVec.ofInt 64 (← intOf (← field j "len"))⟩)
      else if (field j "len").isOk then throw "a slice argument for a pointer parameter"
      else do pure (.ptr (← ptrOf j))
    | some (.optional c) => if j.isNull then pure .optNone else do pure (.optSome (← argOf f n c j))
    | _ => throw "an argument of a type outside the coverage"

/-- One input line: the buffers to make, the arguments, and whether the outcome lists the
buffers (the `bufs` form). A buffer is its bytes, or the items of a slice argument given by
value: `(item type, items)`. -/
structure Input where
  bufs : Array (Sum (Array (BitVec 8)) (TyId × Array Json))
  args : Array Json
  showBufs : Bool

def parseInput (f : Func) (j : Json) : Except String Input := do
  match j with
  | .arr items =>
    -- Arguments by value: a slice is its items, which go to a buffer of their own.
    let mut bufs := #[]
    let mut args := #[]
    for (t, a) in f.params.zip items do
      match f.plainSlice t, pointee? f t, a with
      | true, some c, .arr xs =>
        args := args.push (Json.mkObj [("buf", bufs.size), ("off", (0 : Nat)), ("len", xs.size)])
        bufs := bufs.push (.inr (c, xs))
      | _, _, a => args := args.push a
    unless items.size == f.params.size do throw "the argument count is not the parameter count"
    pure ⟨bufs, args, false⟩
  | j =>
    let bufs ← (← (← field j "bufs").getArr?).mapM fun b => do
      pure (.inl (← (← b.getArr?).mapM fun x => do pure (BitVec.ofInt 8 (← intOf x))))
    let args ← (← field j "args").getArr?
    let .obj kvs := j | throw "an input that is neither an array nor an object"
    unless kvs.toList.all (fun (k, _) => k == "bufs" || k == "args") do
      throw "an input field other than bufs and args"
    unless args.size == f.params.size do throw "the argument count is not the parameter count"
    pure ⟨bufs, args, true⟩

/-- Make the input buffers, 16-byte aligned stack blocks as `Diff.lean`'s `memOf` makes them. -/
def makeBufs (f : Func) (bufs : Array (Sum (Array (BitVec 8)) (TyId × Array Json))) :
    Except String (Zig.MemM Unit) := do
  let acts ← bufs.mapM fun
    | .inl bytes => pure (do
        let p ← Zig.alloc .stack bytes.size 16
        Zig.storeBytes p 1 (bytes.map .int))
    | .inr (c, xs) => do
      let some (size, _) := layoutOf f c | throw "a slice item without a layout"
      let some (.int _ w) := f.types[c]? | throw "a slice argument by value of items that are not integers"
      let items ← xs.mapM intOf
      pure (do
        let p ← Zig.alloc .stack (size * items.size) 16
        for k in [:items.size] do
          Zig.store 1 (p.elem size (BitVec.ofNat 64 k)) (BitVec.ofInt w items[k]!))
  pure (acts.forM id)

/-! ## Outcomes (the wire format of `tests/diff/Diff.lean`) -/

def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (d + '0'.toNat) else Char.ofNat (d - 10 + 'a'.toNat)

def hex2 (n : Nat) : String := String.ofList [hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- `Diff.lean`'s `byteStr`. -/
def byteStr (b : Zig.Byte) : String :=
  match b with
  | .ptrFrag .. => "pp"
  | _ =>
    let (d, x) := b.defBits.getD (0, 0)
    let nib (v : BitVec 8) (k : Nat) := (v.toNat >>> k) % 16
    let digit (k : Nat) := if nib d k = 15 then String.singleton (hexDigit (nib x k)) else "?"
    if [0, 15].contains (nib d 4) && [0, 15].contains (nib d 0) then digit 4 ++ digit 0
    else "(" ++ hex2 d.toNat ++ ":" ++ hex2 x.toNat ++ ")"

/-- `Diff.lean`'s `ptrStr` with no globals. -/
def ptrStr (m : Zig.Mem) (p : Zig.Ptr) (size : Nat) (len : Option Nat := none) : String :=
  let lenStr := match len with | some n => s!",\"len\":{n}" | none => ""
  match p.block with
  | some b =>
    if (m.blocks[b]?.map (·.kind != .heap)).getD true then
      s!"\{\"buf\":{b},\"off\":{p.off}{lenStr}}"
    else
      let bytes := (m.blocks[b]?.map (·.bytes)).getD #[]
      let o := p.off.toNat
      "{\"bytes\":\"" ++ String.join ((bytes.extract o (o + size)).toList.map byteStr) ++ "\"}"
  | none => if size = 0 then "{\"bytes\":\"\"}" else "\"outside the buffers\""

/-- A returned value of the AIR type `t` (`none`: a value without a rendering), and whether it
holds a returned error. -/
def valueStr (f : Func) (m : Zig.Mem) : TyId → Value → Option (String × Bool)
  | _, .int s w v =>
    let n := if s then toString v.toInt else toString v.toNat
    some (if w ≥ 64 then "\"" ++ n ++ "\"" else n, false)
  | _, .bool b => some (if b then "1" else "0", false)
  | _, .void => some ("null", false)
  | t, .ptr p => ((pointee? f t).bind (layoutOf f)).map fun (size, _) => (ptrStr m p size, false)
  | t, .slice s => ((pointee? f t).bind (layoutOf f)).map fun (size, _) =>
      (ptrStr m s.ptr (size * s.len.toNat) (some s.len.toNat), false)
  | _, .optNone => some ("null", false)
  | t, .optSome v => match f.types[t]? with
    | some (.optional c) => valueStr f m c v
    | _ => none
  | t, .errOk v => match f.types[t]? with
    | some (.errorUnion _ c) => valueStr f m c v
    | _ => none
  | _, .errErr name => some ("{\"err\":\"" ++ name ++ "\"}", true)
  | _, .errName _ | _, .cell _ => none

/-- `Outcome.lean`'s kind of a model error. -/
def errorKind : Zig.Error → String
  | .illegal => "illegal"
  | .unspecified => "unspecified"
  | .unsupportedTimer => "unspecified_timer"
  | .deadlock => "deadlock"
  | .trap => "trap"
  | .stackOverflow => "stack_overflow"
  | .overflow | .outOfBounds | .divByZero | .unreachable | .panic => "model_panic"

/-- One input line as the interpreter takes it: the arguments and the memory holding the
buffers. An error is a reason of the function (the harness cannot hand the input over). -/
def prepare (f : Func) (line : String) : Except String (Input × List Value × Zig.Mem) := do
  let input ← parseInput f (← Json.parse line)
  let args ← (f.params.zip input.args).toList.mapM fun (t, a) => argOf f 4 t a
  let setup ← makeBufs f input.bufs
  let some (.ok ((), m0)) := (setup.run {}).run | throw "the input buffers cannot be made"
  pure (input, args, m0)

/-- Run `f` on a prepared input: the outcome line and its kind (`none`: a returned value without
a rendering, which the result's reason should have excluded). -/
def runLine (p : Program) (f : Func) (input : Input) (args : List Value) (m0 : Zig.Mem) :
    Option (String × String) :=
  match ((run p f.name args).run m0).run with
  | none => some ("{\"stuck\":true}", "stuck")
  | some (.error e) => some ("{\"fail\":\"" ++ reprStr e ++ "\"}", errorKind e)
  | some (.ok (v, m)) => do
    let (s, isErr) ← valueStr f m f.ret v
    let bufs := if input.showBufs then
        let bs := (m.blocks.extract 0 input.bufs.size).toList.map fun blk =>
          "\"" ++ String.join (blk.bytes.toList.map byteStr) ++ "\""
        ",\"bufs\":[" ++ ",".intercalate bs ++ "]"
      else ""
    pure ("{\"ok\":" ++ s ++ bufs ++ "}", if isErr then "error_return" else "value")

/-! ## Driver -/

def str (s : String) : Json := .str s

/-- One AIR file as the translator reads it: parsed, normalized, checked (`Air2Lean.processOne`,
whose module declares the translator's `main`). -/
def decode (contents : String) : Except String Func := do
  let f ← normalize (← Raw.parseFile contents)
  check f
  pure f

def skipRecord (ex fn : String) (rs : Array (String × String × Nat)) : Json :=
  Json.mkObj [("example", str ex), ("fn", str fn), ("status", str "skip"),
    ("reasons", Json.arr (rs.map fun (w, r, n) =>
      Json.mkObj [("where", str w), ("reason", str r), ("insts", n)]))]

/-- One corpus function: its record for `conformance.py`. `execute`: run it on its inputs (else
only its coverage is recorded). An input that the harness cannot hand to the interpreter is a
reason of its own, never a dropped line. -/
def runFunction (p : Program) (ex fn : String) (inputs : System.FilePath) (execute : Bool) :
    IO Json := do
  let some f := p.lookup s!"{ex}.{fn}"
    | return skipRecord ex fn
        #[(s!"{ex}.{fn}", "harness: the corpus function is not an AIR function of the example", 0)]
  let rs := reasons p f
  unless rs.isEmpty do return skipRecord ex fn rs
  let mut prepared := #[]
  for line in ← IO.FS.lines inputs do
    if line.trimAscii.isEmpty then continue
    match prepare f line with
    | .ok x => prepared := prepared.push x
    | .error e => return skipRecord ex fn #[(f.name, s!"harness: {e}", 0)]
  let mut out := #[]
  if execute then
    for (input, args, m0) in prepared do
      let some (l, kind) := runLine p f input args m0
        | throw (IO.userError s!"{f.name}: a returned value without a rendering")
      out := out.push (Json.mkObj [("line", str l), ("kind", str kind)])
  return Json.mkObj [("example", str ex), ("fn", str fn), ("status", str "run"),
    ("outcomes", Json.arr out)]

def runExample (ex : Json) (execute : Bool) (out : IO.FS.Handle) : IO Unit := do
  let name ← IO.ofExcept (ex.getObjValAs? String "name")
  let air ← IO.ofExcept (ex.getObjValAs? (Array String) "air")
  let fns ← IO.ofExcept (ex.getObjValAs? (Array String) "functions")
  let inputs ← IO.ofExcept (ex.getObjValAs? String "inputs")
  let texts ← air.mapM fun path => IO.FS.readFile (System.FilePath.mk path)
  let (_, texts) := Anon.renumberAllWithNames texts
  let records ← match texts.mapM decode with
    | .ok funcs =>
      let p : Program := ⟨funcs, #[]⟩
      fns.mapM fun fn => runFunction p name fn (System.FilePath.mk inputs / s!"{fn}.jsonl") execute
    | .error e => pure (fns.map fun fn =>
        skipRecord name fn #[(name, s!"harness: the example's AIR does not decode: {e}", 0)])
  for record in records do out.putStrLn record.compress
  out.flush

end Conformance

def main (args : List String) : IO UInt32 := do
  let [manifest] := args
    | IO.eprintln "usage: air-semantics-conformance <manifest.json>"; return 2
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile manifest))
  let examples ← IO.ofExcept (j.getObjValAs? (Array Json) "examples")
  let outPath ← IO.ofExcept (j.getObjValAs? String "out")
  let execute ← IO.ofExcept (j.getObjValAs? Bool "execute")
  IO.FS.withFile outPath .write fun out => do
    for ex in examples do Conformance.runExample ex execute out
  return 0
