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

end PackedCastsShow
