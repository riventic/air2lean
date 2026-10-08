import Air2Lean
import Air2Lean.Check
import Air2Lean.Emit
open Air2Lean

private def types : Array Ty := #[.errorSet (some #["Alpha", "Beta", "Gamma"]),
  .optional 0, .optional 1, .array 3 1 false, .struct "Status" "auto" #[("guard", 8), ("pending", 1), ("last", 0)],
  .ptr "one" false 1, .bool, .noreturn, .int false 16, .void, .ptr "one" false 0]
private def layouts : Array Layout := #[
  {size := some 2, align := some 2}, {size := some 2, align := some 2},
  {size := some 4, align := some 2}, {size := some 6, align := some 2},
  {size := some 6, align := some 2, offsets := #[0,2,4]},
  {size := some 8, align := some 8, ptrAlign := some 2},
  {size := some 1, align := some 1}, {}, {size := some 2, align := some 2},
  {size := some 0, align := some 1}, {size := some 8, align := some 8, ptrAlign := some 2}]
private def f : Func := {zigVersion := "0.16.0", name := "error_storage.optional", params := #[5], ret := 1, types, layouts, globals := #[], body := #[{id := 0, ty := 5, op := .arg 0}, {id := 1, ty := 9, op := .store (.inst 0) (.optSome 1 (.err 0 "Alpha"))}, {id := 2, ty := 1, op := .load (.inst 0)}, {id := 3, ty := 7, op := .ret (.inst 2)}]}
private def require (p : Bool) (why : String) : IO Unit := unless p do throw (IO.userError why)
private def accept (out : Except String α) : IO α := match out with
  | .ok v => pure v | .error e => throw (IO.userError e)
private def reject (out : Except String α) (why : String) : IO Unit := match out with
  | .error _ => pure () | .ok _ => throw (IO.userError s!"accepted {why}")
def main (args : List String) : IO Unit := do
  for id in #[0,1,2,3,4] do discard (accept (checkMemTy "test" types layouts 0 id))
  discard (accept (check f))
  discard (accept (checkProgram #[f]))
  reject (checkMemTy "test" (types.set! 0 (.errorSet none)) layouts 0 0) "unresolved anyerror"
  reject (checkMemTy "test" (types.set! 0 (.errorSet (some #[]))) layouts 0 0) "empty errors"
  reject (checkMemTy "test" (types.set! 0 (.errorSet (some #["Alpha", "Alpha"]))) layouts 0 0) "duplicate domain"
  reject (checkMemTy "test" (types.set! 0 (.errorSet (some #[""]))) layouts 0 0) "empty name"
  let capacityNames := (Array.range 65536).map (fun i => s!"Error{i}")
  require (validErrorDomainNames (capacityNames.extract 0 65535)) "valid capacity boundary"
  reject (checkMemTy "test" (types.set! 0 (.errorSet (some capacityNames))) layouts 0 0) "domain capacity"
  reject (checkMemTy "test" types (layouts.set! 0 {size := some 4, align := some 4}) 0 0) "error width"
  reject (checkMemTy "test" types (layouts.set! 1 {size := some 4, align := some 2}) 0 1) "optional flag ABI"
  let foreign := {f with body := f.body.set! 1 {id := 1, ty := 9, op := .store (.inst 0) (.optSome 1 (.err 0 "Other"))}}
  reject (check foreign >>= fun _ => checkProgram #[foreign]) "foreign constant"
  let cast : Func := {f with params := #[0], ret := 8, body := #[ {id := 0, ty := 0, op := .arg 0}, {id := 1, ty := 8, op := .bitcast (.inst 0)}, {id := 2, ty := 7, op := .ret (.inst 1)}]}
  reject (check cast) "raw error/int bitcast"
  let intcast := {cast with body := cast.body.set! 1 {id := 1, ty := 8, op := .intCast (.inst 0)}}
  reject (check intcast) "error ordinal integer cast"
  let optionalCast := {cast with params := #[1], body := #[ {id := 0, ty := 1, op := .arg 0}, {id := 1, ty := 8, op := .bitcast (.inst 0)}, {id := 2, ty := 7, op := .ret (.inst 1)}]}
  reject (check optionalCast) "opaque optional error bitcast"
  let rawTypes := types.push (.ptr "one" false 8)
  let rawLayouts := layouts.push {size := some 8, align := some 8, ptrAlign := some 2}
  let rawPtr : Func := {cast with types := rawTypes, layouts := rawLayouts, params := #[10], body := #[ {id := 0, ty := 10, op := .arg 0}, {id := 1, ty := 11, op := .bitcast (.inst 0)}, {id := 2, ty := 8, op := .load (.inst 1)}, {id := 3, ty := 7, op := .ret (.inst 2)}]}
  reject (check rawPtr) "raw error pointer observation"
  let optionalPtrTypes := rawTypes.push (.optional 10) |>.push (.optional 11)
  let optionalPtrLayouts := rawLayouts.push {size := some 8, align := some 8} |>.push {size := some 8, align := some 8}
  let optionalRawPtr : Func := {cast with types := optionalPtrTypes, layouts := optionalPtrLayouts, params := #[12], ret := 13, body := #[{id := 0, ty := 12, op := .arg 0}, {id := 1, ty := 13, op := .bitcast (.inst 0)}, {id := 2, ty := 7, op := .ret (.inst 1)}]}
  reject (check optionalRawPtr) "optional pointer raw error exposure"
  let directToOptional := {optionalRawPtr with params := #[10], body := optionalRawPtr.body.set! 0 {id := 0, ty := 10, op := .arg 0}}
  reject (check directToOptional) "direct to optional raw error exposure"
  let emptyUnionTypes := types.push (.errorUnion 0 8) |>.set! 0 (.errorSet (some #[]))
  let emptyUnionLayouts := layouts.push {size := some 4, align := some 2}
  discard (accept (checkMemTy "emptyUnion" emptyUnionTypes emptyUnionLayouts 0 11))
  let gen := emit #[f] "ErrorStorage" "error_storage." .ieee
  require ((gen.splitOn "Zig.optionalErrorEnc").length > 1) "optional dictionary missing"
  require ((gen.splitOn "Option (Zig.ErrName)").length > 1) "public optional API changed"
  require ((gen.splitOn "instance : Zig.Enc Zig.ErrName").length == 1) "global String encoder"
  require (emitTy #[] types types[0]! == "Zig.ErrName") "pure error API changed"
  let array := emitStorageEnc #[] types 16 3
  require (array.isSome && ((array.getD "").splitOn "Zig.Enc.vectorWith").length > 1) "array dictionary missing"
  let status : NamedType := {zigName := "Status", leanName := "Status", ty := types[4]!, srcTypes := types, srcLayouts := layouts, layout := layouts[4]!}
  let structGen := emitEnc #[] status
  require ((structGen.splitOn "Zig.optionalErrorEnc").length > 1 && (structGen.splitOn "Zig.errorEnc").length > 1) "field dictionaries missing"
  match args with
  | [output] => IO.FS.writeFile output gen
  | _ => pure ()
