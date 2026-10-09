import DivCeil.Gen

/-! Runs the translation of the compiler-exported `@divCeil` AIR (`air/0.17.0`) on each line
`fn a b` of the inputs file and prints `fn a b result`, or `fn a b panic:<error>` when the
generated code throws (`check.sh` compares this with the native run). -/

open Zig DivCeil

private def show1 {n : Nat} (signed : Bool) (r : Zig.Result (BitVec n)) : String :=
  match r.run with
  | some (.ok v) => if signed then toString v.toInt else toString v.toNat
  | some (.error .divByZero) => "panic:divByZero"
  | some (.error .overflow) => "panic:overflow"
  | some (.error e) => s!"panic:other({repr e})"
  | none => "panic:none"

private def run1 (name : String) (a b : Int) : Option String :=
  let f {n : Nat} (s : Bool) (g : BitVec n → BitVec n → Zig.Result (BitVec n)) : String :=
    show1 s (g (BitVec.ofInt n a) (BitVec.ofInt n b))
  match name with
  | "divCeilI8" => some (f true divCeilI8)
  | "divCeilU8" => some (f false divCeilU8)
  | "divCeilI32" => some (f true divCeilI32)
  | "divCeilU32" => some (f false divCeilU32)
  | "divCeilI64" => some (f true divCeilI64)
  | "divCeilU64" => some (f false divCeilU64)
  | "divCeilI13" => some (f true divCeilI13)
  | _ => none

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: Runtime INPUTS")
  for line in (← IO.FS.lines path) do
    match line.splitOn " " with
    | [name, a, b] =>
      let (some a, some b) := (a.toInt?, b.toInt?) | throw (IO.userError s!"bad input: {line}")
      let some r := run1 name a b | throw (IO.userError s!"unknown function: {name}")
      IO.println s!"{name} {a} {b} {r}"
    | _ => unless line.isEmpty do throw (IO.userError s!"bad input: {line}")
