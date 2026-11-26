import Air2Lean
import Air2Lean.Check
open Air2Lean

/-! Checker controls for container layouts (`Air2Lean/Check.lean`, `modelLayout`): a field's
model layout must be the exporter's layout of its type, also for a field that no instruction
loads; an `extern` struct or union must have a C layout (`externLayoutError?`): fields in
declaration order, each at its predecessor's end rounded up to a power-of-two alignment of at
most the struct's (the field's own or an explicit `align(N)`), the size rounded up.

    lake env lean --run tests/roadmap/pointer-width/LayoutChecker.lean -/

private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)

private def has (r : Except String α) (marker : String) : Bool :=
  match r with
  | .error e => (e.splitOn marker).length > 1
  | .ok _ => false

private def describe (r : Except String α) : String :=
  match r with
  | .error e => e
  | .ok _ => "accepted"

/-- `u8`, `u16`, `u32`, `u64`, then the containers under test from index 4. -/
private def scalars : Array Ty := #[.int false 8, .int false 16, .int false 32, .int false 64]

private def scalarLayouts : Array Layout := #[
  {size := some 1, align := some 1}, {size := some 2, align := some 2},
  {size := some 4, align := some 4}, {size := some 8, align := some 8}]

/-- The model layout of one container (type 4) over the scalars. -/
private def container (ty : Ty) (layout : Layout) (scalarsAs : Array Layout := scalarLayouts) :
    Except String (Nat × Nat) :=
  modelLayout (scalars.push ty) (scalarsAs.push layout) 4

private def fields (tys : List TyId) : Array (String × TyId) :=
  (tys.zipIdx.map fun (t, i) => (s!"f{i}", t)).toArray

private def struct (layout : String) (tys : List TyId) : Ty := .struct "m.S" layout (fields tys)

def main : IO Unit := do
  -- `externLayoutError?` on (offset, size) lists.
  let ok (fs : Array (Nat × Nat)) (size align : Nat) : Bool := (externLayoutError? fs size align).isNone
  -- { u8, u32, u16 }: natural, with `b align(1)`, with `b align(16)`.
  require (ok #[(0, 1), (4, 4), (8, 2)] 12 4) "natural layout rejected"
  require (ok #[(0, 1), (1, 4), (6, 2)] 8 2) "under-aligned field rejected"
  require (ok #[(0, 1), (16, 4), (20, 2)] 32 16) "over-aligned field rejected"
  require (ok #[] 0 1 && ok #[(0, 0)] 0 1 && ok #[(0, 1), (4, 0), (4, 1)] 8 4) "empty or zero-sized rejected"
  for (what, fs, size, align) in [
      ("fields out of order", #[(0, 1), (8, 4), (4, 2)], 12, 4),
      ("overlapping fields", #[(0, 4), (2, 4)], 8, 4),
      ("a gap that no alignment explains", #[(0, 1), (3, 4)], 8, 4),
      ("padding above the struct's alignment", #[(0, 1), (8, 4)], 12, 4),
      ("a first field not at 0", #[(4, 4)], 8, 4),
      ("a size above the rounded end", #[(0, 1), (4, 4)], 12, 4),
      ("a size below the rounded end", #[(0, 1), (4, 4)], 6, 4),
      ("an alignment that is no power of two", #[(0, 4)], 6, 6),
      ("alignment 0", #[(0, 4)], 4, 0)] do
    require (!ok fs size align) s!"{what} accepted"
  -- Through `modelLayout`: an `extern` struct, the same fields as an `auto` struct (the
  -- compiler's choice: any order), an `extern` union.
  let externOk := container (struct "extern" [0, 2, 1]) {size := some 12, align := some 4, offsets := #[0, 4, 8]}
  require (externOk == .ok (12, 4)) s!"extern struct: {describe externOk}"
  let reordered : Layout := {size := some 12, align := some 4, offsets := #[8, 0, 4]}
  require (has (container (struct "extern" [0, 2, 1]) reordered) "is not a C layout: a field at offset")
    s!"reordered extern struct: {describe (container (struct "extern" [0, 2, 1]) reordered)}"
  require (container (struct "auto" [0, 2, 1]) reordered == .ok (12, 4)) "reordered auto struct rejected"
  let union (size align : Nat) := container (.union "m.U" "extern" none (fields [0, 3, 1]))
    {size := some size, align := some align}
  require (union 8 8 == .ok (8, 8)) s!"extern union: {describe (union 8 8)}"
  require (has (union 16 8) "`extern` union 'm.U' is not a C layout: its size") s!"large extern union: {describe (union 16 8)}"
  require (has (union 4 4) "is not a C layout") s!"small extern union: {describe (union 4 4)}"
  -- A field type whose exported layout is not the model's (`u32` with size 2, or alignment
  -- 2), in an `auto` struct, an `extern` struct and an `extern` union; no load names the field.
  for bad in [{size := some 2, align := some 2}, ({size := some 4, align := some 2} : Layout)] do
    let table := scalarLayouts.set! 2 bad
    for (what, r) in [
        ("auto struct", container (struct "auto" [0, 2]) {size := some 8, align := some 4, offsets := #[0, 4]} table),
        ("extern struct", container (struct "extern" [0, 2]) {size := some 8, align := some 4, offsets := #[0, 4]} table),
        ("extern union", container (.union "m.U" "extern" none (fields [0, 2])) {size := some 4, align := some 4} table)] do
      require (has r "the memory model gives type 2, a field of") s!"{what} with a diverging field type: {describe r}"
  -- A field type without a layout in the AIR file.
  let noLayout := container (struct "auto" [0, 2]) {size := some 8, align := some 4, offsets := #[0, 4]}
    (scalarLayouts.set! 2 {})
  require (has noLayout "has no layout in the AIR file") s!"field without a layout: {describe noLayout}"
  IO.println "container layout checker controls passed"
