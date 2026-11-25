import ToVec.Gen

/-! Runs the translation of the compiler-exported `array_to_vector` AIR (`air/0.17.1`) on each line
`fn x0 … x(n-1)` of the inputs file (an integer in decimal, a `bool` as 0/1, a float as its bit
pattern) and prints the vector as `fn y0 … y(n-1)` in the same encoding, or `fn error` when the
generated code throws (`check.sh` compares this with the native run). -/

open Zig ToVec

/-- One lane kind: how an input item becomes a value and a lane is printed. -/
private structure Kind (α : Type) where
  ofInt : Int → α
  render : α → String

private def unsigned (w : Nat) : Kind (BitVec w) := ⟨BitVec.ofInt w, fun x => toString x.toNat⟩
private def signed (w : Nat) : Kind (BitVec w) := ⟨BitVec.ofInt w, fun x => toString x.toInt⟩
private def boolean : Kind Bool := ⟨(· != 0), fun b => if b then "1" else "0"⟩
private def float (fmt : FloatFmt) : Kind (Zig.Float fmt) :=
  ⟨fun x => ⟨BitVec.ofInt fmt.width x⟩, fun x => toString x.bits.toNat⟩

/-- The array of the items `xs` followed by the sentinel, if any, the function's vector. -/
private def call {α : Type} {m n : Nat} (k : Kind α)
    (f : Vector α m → Zig.Result (Zig.Vec α n)) (xs : List Int) (sentinel : Option α := none) :
    Except String String := do
  let items := (xs.map k.ofInt ++ sentinel.toList).toArray
  if h : items.size = m then
    match (f ⟨items, h⟩).run with
    | some (.ok v) => pure (" ".intercalate (v.lanes.toList.map k.render))
    | _ => pure "error"
  else throw s!"{xs.length} items for an array of {m} (sentinel included)"

private def run1 (name : String) (xs : List Int) : Except String String :=
  match name with
  | "toVecU8" => call (unsigned 8) toVecU8 xs
  | "toVecI16" => call (signed 16) toVecI16 xs
  | "toVecU24" => call (unsigned 24) toVecU24 xs
  | "toVecI32" => call (signed 32) toVecI32 xs
  | "toVecU64" => call (unsigned 64) toVecU64 xs
  | "toVecI128" => call (signed 128) toVecI128 xs
  | "toVecU1" => call (unsigned 1) toVecU1 xs
  | "toVecI7" => call (signed 7) toVecI7 xs
  | "toVecBool" => call boolean toVecBool xs
  | "toVecF16" => call (float .f16) toVecF16 xs
  | "toVecF32" => call (float .f32) toVecF32 xs
  | "toVecF64" => call (float .f64) toVecF64 xs
  | "toVecF80" => call (float .f80) toVecF80 xs
  | "toVecF128" => call (float .f128) toVecF128 xs
  -- `tovec.zig`'s sentinels: `[5:0]u8` and `[3:7]i16`.
  | "toVecZ8" => call (unsigned 8) toVecZ8 xs (some 0#8)
  | "toVecZ16" => call (signed 16) toVecZ16 xs (some 7#16)
  | _ => throw s!"unknown function: {name}"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: Runtime INPUTS")
  for line in (← IO.FS.lines path) do
    match line.splitOn " " with
    | name :: items@(_ :: _) =>
      let some xs := items.mapM String.toInt? | throw (IO.userError s!"bad input: {line}")
      match run1 name xs with
      | .ok r => IO.println s!"{name} {r}"
      | .error e => throw (IO.userError s!"{line}: {e}")
    | _ => unless line.isEmpty do throw (IO.userError s!"bad input: {line}")
