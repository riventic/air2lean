import Air2Lean.Check
import ZigLean

/-! MM-12 regression: accesses of zero bytes.

Zig touches no memory for a zero-bit value: `p.*` of a `*const u0` is no access, through any
pointer, and Sema emits no `load` for it (`fn f(p: *const u0) u0 { return p.*; }` called with
`@ptrFromInt(0x1000)` runs natively). The model's access of zero bytes still needs a live
block, in bounds and aligned, so it is `.illegal` through a pointer without a block. Before
the fix the checker accepted such a load in AIR and the emitter wrote `Zig.load (BitVec 0)`;
the checker now rejects every memory access, item access (also a slice read in a function
that uses memory) and `@fieldParentPtr` of a zero-size type. The runtime rule stays
conservative. -/

open Air2Lean

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- `fn f(p: *const u0) u0 { return p.*; }` with the `load` that Sema does not emit. -/
private def loadU0 : Func := {
  zigVersion := "0.16.0"
  name := "zero.loadU0"
  params := #[1]
  ret := 0
  types := #[.int false 0, .ptr "one" true 0, .noreturn]
  layouts := #[{ size := some 0, align := some 1 },
    { size := some 8, align := some 8, ptrAlign := some 1 }, {}]
  globals := #[]
  body := #[
    { id := 0, ty := 1, op := .arg 0 },
    { id := 1, ty := 0, op := .load (.inst 0) },
    { id := 2, ty := 2, op := .ret (.inst 1) }] }

/-- The same function on a `*const u8`. -/
private def loadU8 : Func := { loadU0 with
  name := "zero.loadU8"
  types := #[.int false 8, .ptr "one" true 0, .noreturn]
  layouts := loadU0.layouts.set! 0 { size := some 1, align := some 1 } }

/-- `p[i]` of a `[*]const u0`. -/
private def elemU0 : Func := { loadU0 with
  name := "zero.elemU0"
  params := #[1, 3]
  types := #[.int false 0, .ptr "many" true 0, .noreturn, .int false 64]
  layouts := loadU0.layouts.push { size := some 8, align := some 8 }
  body := #[
    { id := 0, ty := 1, op := .arg 0 },
    { id := 1, ty := 3, op := .arg 1 },
    { id := 2, ty := 0, op := .ptrElemVal (.inst 0) (.inst 1) },
    { id := 3, ty := 2, op := .ret (.inst 2) }] }

/-- `fn f(s: []const u0, i: usize, q: *const u8) u0 { _ = q.*; return s[i]; }`: a function
that uses memory reads the slice item with `loadItem` (`checkProgram`). -/
private def sliceU0 : Func := { loadU0 with
  name := "zero.sliceU0"
  params := #[1, 3, 4]
  types := #[.int false 0, .ptr "slice" true 0, .noreturn, .int false 64, .ptr "one" true 5,
    .int false 8]
  layouts := #[{ size := some 0, align := some 1 },
    { size := some 16, align := some 8, ptrAlign := some 1 }, {},
    { size := some 8, align := some 8 }, { size := some 8, align := some 8, ptrAlign := some 1 },
    { size := some 1, align := some 1 }]
  body := #[
    { id := 0, ty := 1, op := .arg 0 },
    { id := 1, ty := 3, op := .arg 1 },
    { id := 2, ty := 4, op := .arg 2 },
    { id := 3, ty := 5, op := .load (.inst 2) },
    { id := 4, ty := 0, op := .sliceElemVal (.inst 0) (.inst 1) },
    { id := 5, ty := 2, op := .ret (.inst 4) }] }

-- The runtime rule (unchanged, conservative): zero bytes through a pointer without a block.
open Zig in
#guard ((load (BitVec 0) 1 ⟨none, 4096⟩).run' ({} : Mem)).run = some (.error .illegal)

def main : IO Unit := do
  for f in [loadU0, elemU0] do
    match check f with
    | .ok _ => throw (IO.userError s!"check accepts {f.name}")
    | .error e =>
      require ((e.splitOn "zero-size type is outside the subset").length == 2)
        s!"unexpected rejection of {f.name}: {e}"
  match checkProgram #[sliceU0] with
  | .ok _ => throw (IO.userError "checkProgram accepts zero.sliceU0")
  | .error e =>
    require ((e.splitOn "zero-size type is outside the subset").length == 2)
      s!"unexpected rejection of zero.sliceU0: {e}"
  require (check loadU8).isOk "check rejects a load of a u8"
  IO.println "zero-length accesses: rejected by the checker"

#eval main
