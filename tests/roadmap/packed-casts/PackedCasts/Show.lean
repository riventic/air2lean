import ZigLean

/-! Formatting of model results as `native.zig` prints them (`name: value`, hex). A value with an
undetermined bit (a NaN, an undefined bit; `Zig.Packed.toBits?`) prints as `unspecified`, which
`check.sh` matches with any native value. -/

namespace PackedCastsShow

def hexN (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A value as `native.zig` prints it. -/
class Show (α : Type) where
  format : α → String

instance (priority := low) {α : Type} {n : Nat} [Zig.Packed α n] : Show α where
  format v := match (Zig.Packed.toBits? v).run with
    | some (.ok b) => hexN b.toNat
    | _ => "unspecified"

/-- `void` has no bits to print. -/
instance : Show Unit where
  format _ := "void"

instance {α : Type} {n : Nat} [Show α] : Show (Vector α n) where
  format v := "[" ++ " ".intercalate (v.toList.map Show.format) ++ "]"

instance {α : Type} {n : Nat} [Show α] : Show (Zig.Vec α n) where
  format v := Show.format v.lanes

def fmt {α : Type} [Show α] : Option (Except Zig.Error α) → String
  | some (.ok v) => Show.format v
  | some (.error .unspecified) => "unspecified"
  | some (.error e) => s!"error {repr e}"
  | none => "none"

def line {α : Type} [Show α] (name : String) (r : Zig.Result α) : IO Unit :=
  IO.println s!"{name}: {fmt r.run}"

/-- A memory function run from the translation's initial memory. -/
def lineM {α : Type} [Show α] (name : String) (m : Zig.Mem) (f : Zig.MemM α) : IO Unit :=
  IO.println s!"{name}: {fmt (((f.run m).run).map (·.map Prod.fst))}"

/-- The result of a translated function in whichever monad its version's translation has: one
compiler keeps a local as a value (`Zig.Result`), another puts it on the stack (`Zig.MemM`, run
from a memory without globals). A model written once for every version states its results
through this. -/
class Runs (m : Type → Type) where
  result {α : Type} : m α → Option (Except Zig.Error α)

instance : Runs Zig.Result where
  result r := r.run

instance : Runs Zig.MemM where
  result f := ((f.run (Zig.Mem.ofGlobals .fresh [])).run).map (·.map Prod.fst)

/-- `line` for either monad. -/
def lineR {m : Type → Type} {α : Type} [Runs m] [Show α] (name : String) (f : m α) : IO Unit :=
  IO.println s!"{name}: {fmt (Runs.result f)}"

end PackedCastsShow
