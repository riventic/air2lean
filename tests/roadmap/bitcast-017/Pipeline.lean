import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit

/-! Zig 0.17 `@bitCast` (logical bit order) through the parser, checker and emitter.

Each fixture is one function `fn (x: Src) Dst { return @bitCast(x); }`, written in the
canonical (0.16.0) tag vocabulary. The normalized `Func` is relabelled with each `zig_version`
under test, which isolates the version gate of `Check.lean`/`Emit.lean` from the tag decoding.
Canon renames 0.17's `bit_cast`/`bit_cast_safe` to the same canonical `bitcast`; real 0.17.0 AIR
is covered by `BitCastReal/` (docs/bitcast-semantics.md §What the translator does).

Usage: `lean --run Pipeline.lean OUT.lean` checks every accept/reject verdict and diagnostic,
then writes the emitted 0.17 module plus a `main` that compares each function's result with the
Zig 0.17.0 behaviour tests and native probes (`docs/bitcast-semantics.md` §Evidence). -/

open Lean Air2Lean

private def obj := Json.mkObj
private def num (n : Nat) : Json := toJson n
private def ref (n : Nat) : Json := obj [("inst", num n)]
private def lay (j : List (String × Json)) (size align : Nat) : Json :=
  obj (j ++ [("abi_size", num size), ("abi_align", num align)])
private def int (signed : Bool) (bits size align : Nat) : Json :=
  lay [("k", .str "int"), ("signed", .bool signed), ("bits", num bits)] size align
private def arr (len child size align : Nat) (sentinel := false) : Json :=
  lay [("k", .str "array"), ("len", num len), ("child", num child), ("sentinel", .bool sentinel)] size align
private def vec (len child size : Nat) : Json :=
  lay [("k", .str "vector"), ("len", num len), ("child", num child)] size size
private def enumTy (name : String) (tag : Nat) (exhaustive : Bool) (fields : List (String × Int))
    (size : Nat) : Json :=
  lay [("k", .str "enum"), ("name", .str name), ("tag", num tag), ("exhaustive", .bool exhaustive),
    ("fields", .arr (fields.toArray.map fun (n, v) => obj [("name", .str n), ("value", .str (toString v))]))]
    size size

/-- The shared type table (index = type ID). -/
private def types : Array Json := #[
  int false 20 4 4,                                   -- 0 u20
  int false 5 1 1,                                    -- 1 u5
  vec 4 1 4,                                          -- 2 @Vector(4, u5)
  int false 4 1 1,                                    -- 3 u4
  arr 5 3 5 1,                                        -- 4 [5]u4
  int false 16 2 2,                                   -- 5 u16
  lay [("k", .str "bool")] 1 1,                       -- 6 bool
  vec 16 6 2,                                         -- 7 @Vector(16, bool)
  int false 1 1 1,                                    -- 8 u1
  arr 16 8 16 1,                                      -- 9 [16]u1
  lay [("k", .str "struct"), ("name", .str "P"), ("layout", .str "packed"),
    ("fields", .arr #[obj [("name", .str "foo"), ("ty", num 1)], obj [("name", .str "bar"), ("ty", num 11)],
      obj [("name", .str "baz"), ("ty", num 12)], obj [("name", .str "qux"), ("ty", num 6)]])] 2 2,  -- 10 P
  int true 7 1 1,                                     -- 11 i7
  int false 3 1 1,                                    -- 12 u3
  int false 24 4 4,                                   -- 13 u24
  arr 2 13 8 4,                                       -- 14 [2]u24
  int false 48 8 8,                                   -- 15 u48
  enumTy "E" 17 true [("a", 0), ("b", 1), ("c", 2)] 1, -- 16 enum(u8) { a, b, c }
  int false 8 1 1,                                    -- 17 u8
  int true 8 1 1,                                     -- 18 i8
  obj [("k", .str "noreturn")],                       -- 19
  arr 4 17 4 1,                                       -- 20 [4]u8
  int false 32 4 4,                                   -- 21 u32
  arr 8 6 8 1,                                        -- 22 [8]bool
  arr 4 6 4 1,                                        -- 23 [4]bool
  arr 4 23 16 1,                                      -- 24 [4][4]bool
  lay [("k", .str "float"), ("bits", num 32)] 4 4,    -- 25 f32
  arr 2 25 8 4,                                       -- 26 [2]f32
  int false 64 8 8,                                   -- 27 u64
  arr 2 17 3 1 (sentinel := true),                    -- 28 [2:0]u8
  vec 4 17 4,                                         -- 29 @Vector(4, u8)
  enumTy "N" 17 false [("a", 0)] 1,                   -- 30 enum(u8) { a, _ }
  enumTy "S" 18 true [("m", -1), ("z", 0)] 1,         -- 31 enum(i8) { m = -1, z = 0 }
  int false 9 2 2,                                    -- 32 u9
  arr 3 32 6 2,                                       -- 33 [3]u9
  int false 27 4 4,                                   -- 34 u27
  vec 3 32 8,                                         -- 35 @Vector(3, u9)
  lay [("k", .str "void")] 0 1,                       -- 36 void
  int false 0 0 1]                                    -- 37 u0

private def file (name : String) (src dst : Nat) : Json :=
  obj [("schema", num 11), ("zig_version", .str "0.16.0"), ("target_endian", .str "little"),
    ("name", .str name), ("types", .arr types), ("params", toJson (#[src] : Array Nat)),
    ("ret", num dst), ("body", .arr #[
      obj [("id", num 0), ("tag", .str "arg"), ("ty", num src), ("param", num 0)],
      obj [("id", num 1), ("tag", .str "bitcast"), ("ty", num dst), ("args", .arr #[ref 0])],
      obj [("id", num 2), ("tag", .str "ret"), ("ty", num 19), ("args", .arr #[ref 1])]])]

private def require (test : Bool) (message : String) : IO Unit := do
  unless test do throw (IO.userError message)

private def load (name : String) (src dst : Nat) (version : String) : IO Func := do
  match (do pure (← normalize (← Raw.parseFunc (file name src dst))) : Except String Func) with
  | .ok f => pure { f with zigVersion := version }
  | .error e => throw (IO.userError s!"{name}: {e}")

private def verdict (f : Func) : Except String Unit := do
  check f
  let _ ← checkProgram #[f]

/-- The 0.17 casts the model translates: name, source and destination type. -/
private def accepted : List (String × Nat × Nat) := [
  ("vec4u5ToU20", 2, 0), ("u20ToVec4u5", 0, 2), ("vec4u5ToArr5u4", 2, 4),
  ("vec16boolToU16", 7, 5), ("u16ToVec16bool", 5, 7), ("packedToArr16u1", 10, 9),
  ("arr16u1ToPacked", 9, 10), ("arr2u24ToU48", 14, 15), ("u48ToArr2u24", 15, 14),
  ("arr3u9ToU27", 33, 34), ("vec3u9ToU27", 35, 34), ("u8ToEnum", 17, 16), ("i8ToEnum", 18, 16),
  ("enumToI8", 16, 18), ("u8ToSignedEnum", 17, 31), ("signedEnumToU8", 31, 17),
  ("u8ToOpenEnum", 17, 30), ("arr4u8ToU32", 20, 21), ("arr8boolToU8", 22, 17),
  ("vec4u8ToU32", 29, 21), ("arr4u8ToVec4u8", 20, 29)]

/-- The 0.17 casts the model rejects, with the diagnostic fragment. -/
private def rejected : List (String × Nat × Nat × String) := [
  ("nestedBoolArray", 24, 5, "element is not an integer or `bool`"),
  ("floatLanes", 26, 27, "element is not an integer or `bool`"),
  ("sentinelArray", 28, 13, "sentinel-terminated array"),
  ("sizeMismatch", 14, 27, "between types of 48 and 64 logical bits")]

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Pipeline.lean OUT.lean")
  let mut funcs : Array Func := #[]
  for (name, src, dst) in accepted do
    let f ← load name src dst "0.17.0"
    match verdict f with
    | .ok _ => funcs := funcs.push f
    | .error e => throw (IO.userError s!"0.17 cast rejected: {name}: {e}")
  for (name, src, dst, expected) in rejected do
    match verdict (← load name src dst "0.17.0") with
    | .ok _ => throw (IO.userError s!"0.17 cast accepted: {name}")
    | .error e =>
      require ((e.splitOn "a Zig 0.17 `@bitCast`").length > 1 && (e.splitOn expected).length > 1)
        s!"wrong 0.17 diagnostic for {name}: {e}"
  -- ≤0.16 keeps its rules: the aggregate and vector casts stay rejected there.
  for version in ["0.14.1", "0.15.2", "0.16.0"] do
    for (name, src, dst) in [("vec4u5ToU20", 2, 0), ("arr4u8ToU32", 20, 21), ("packedToArr16u1", 10, 9)] do
      match verdict (← load name src dst version) with
      | .ok _ => throw (IO.userError s!"{version} accepted the aggregate cast {name}")
      | .error e => require ((e.splitOn "0.17").length == 1) s!"{version} got a 0.17 diagnostic: {e}"
  -- A scalar cast emits the same text under every version.
  let scalar (v : String) : IO String := do
    let f ← load "i8ToU8" 18 17 v
    pure (emit #[f] "Scalar" "")
  require ((← scalar "0.16.0") == (← scalar "0.17.0")) "scalar bitcast emission depends on the version"
  let generated := emit funcs "BitCast017" ""
  require ((generated.splitOn "Zig.BitCast.ofLanes").length > 1) "lane cast did not use ofLanes"
  IO.FS.writeFile output (generated ++ "\n" ++ runtime)
  IO.println "0.17 bitcast checker/emitter regressions passed"
where
  runtime : String := "
open Zig BitCast017

private def ok {α : Type} [DecidableEq α] (name : String) (r : Zig.Result α) (v : α) : IO Unit :=
  unless r.run = some (Except.ok v) do throw (IO.userError s!\"{name}: wrong result\")
private def panics {α : Type} (name : String) (r : Zig.Result α) : IO Unit :=
  match r.run with
  | some (.error .panic) => pure ()
  | _ => throw (IO.userError s!\"{name}: no invalidEnumValue panic\")
private def v5 : Zig.Vec (BitVec 5) 4 := ⟨#v[0b00010, 0b01111, 0b11001, 0b00000]⟩
private def bools16 : Zig.Vec Bool 16 :=
  ⟨Vector.ofFn fun i => i.val != 1⟩
private def p : P := Zig.Packed.ofBits 0xafc9#16

def main : IO Unit := do
  -- test/behavior/bitcast.zig \"@bitCast vector to array with different element size\"
  ok \"vec4u5ToU20\" (vec4u5ToU20 v5) 0x65e2#20
  ok \"u20ToVec4u5\" ((u20ToVec4u5 0x0cbe2#20).map (·.lanes.toList)) [2, 31, 18, 1]
  ok \"vec4u5ToArr5u4\" ((vec4u5ToArr5u4 v5).map (·.toList)) [0b0010, 0b1110, 0b0101, 0b0110, 0b0000]
  -- \"bitcast vector to integer and back\"
  ok \"vec16boolToU16\" (vec16boolToU16 bools16) 0b1111_1111_1111_1101#16
  ok \"u16ToVec16bool\" ((u16ToVec16bool 0xfffd#16).map (·.lanes.toList)) bools16.lanes.toList
  -- \"@bitCast packed struct to array of bits\"
  ok \"packedToArr16u1\" ((packedToArr16u1 p).map (·.toList))
    [1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]
  ok \"arr16u1ToPacked\" ((arr16u1ToPacked #v[1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]).map
    Zig.Packed.toBits) 0xafc9#16
  -- padded elements: no padding in 0.17 (native probe: 0x445566112233, 0x6a9ff01)
  ok \"arr2u24ToU48\" (arr2u24ToU48 #v[0x112233, 0x445566]) 0x445566112233#48
  ok \"u48ToArr2u24\" ((u48ToArr2u24 0x445566112233#48).map (·.toList)) [0x112233, 0x445566]
  ok \"arr3u9ToU27\" (arr3u9ToU27 #v[0x101, 0x0ff, 0x1aa]) 0x6a9ff01#27
  ok \"vec3u9ToU27\" (vec3u9ToU27 ⟨#v[0x101, 0x0ff, 0x1aa]⟩) 0x6a9ff01#27
  -- enums: test/cases/safety/bitcast_to_enum_no_matching_tag_value.zig
  ok \"u8ToEnum\" ((u8ToEnum 1#8).map (· == E.b)) true
  panics \"u8ToEnum invalid\" (u8ToEnum 3#8)
  ok \"i8ToEnum\" ((i8ToEnum 2#8).map (· == E.c)) true
  ok \"enumToI8\" (enumToI8 E.c) 2#8
  ok \"u8ToSignedEnum\" ((u8ToSignedEnum 0xff#8).map (· == S.m)) true
  panics \"u8ToSignedEnum invalid\" (u8ToSignedEnum 0x80#8)
  ok \"signedEnumToU8\" (signedEnumToU8 S.m) 0xff#8
  ok \"u8ToOpenEnum\" ((u8ToOpenEnum 3#8).map (fun e => N.toBits e)) 3#8
  -- byte-multiple elements: same as 0.16 on little-endian (native probe: 0x44332211)
  ok \"arr4u8ToU32\" (arr4u8ToU32 #v[0x11, 0x22, 0x33, 0x44]) 0x44332211#32
  ok \"vec4u8ToU32\" (vec4u8ToU32 ⟨#v[0x11, 0x22, 0x33, 0x44]⟩) 0x44332211#32
  ok \"arr4u8ToVec4u8\" ((arr4u8ToVec4u8 #v[0x11, 0x22, 0x33, 0x44]).map (·.lanes.toList)) [0x11, 0x22, 0x33, 0x44]
  ok \"arr8boolToU8\" (arr8boolToU8 #v[true, false, false, true, false, false, false, true]) 0x89#8
  IO.println \"0.17 bitcast emitted runtime values passed\"
"
