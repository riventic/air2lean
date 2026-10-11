import ZigLean.Sep.Block
import ZigLean.Mem.Alloc
open Zig

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def initial (mode : ByteRemapMode) : Mem := {
  blocks := #[
    { bytes := #[.int 41], align := 1, kind := .heap, live := true, addr := 4096 },
    { bytes := #[.int 3, .int 5, .int 7, .int 11], align := 1, kind := .heap, live := true, addr := 4098 }]
  allocPolicy := { maxBytes := 16, byteRemap := mode }
}
private def old : Slice := ⟨⟨some 1, 0⟩, 4⟩

private def block (m : Mem) (i : Nat) : Block :=
  (m.blocks[i]?).getD { bytes := #[], align := 1, kind := .heap, live := false, addr := 0 }

private def checkMode (mode : ByteRemapMode) : IO Unit := do
  let m := initial mode
  match ((Allocator.remap {} 1 old 8).run m).run with
  | some (.ok (result, final)) =>
    require ((block final 0).bytes == #[.int 41] && (block final 0).live)
      "caller frame was changed"
    match mode, result with
    | .fail, none =>
      require ((block final 1).bytes == (block m 1).bytes && (block final 1).live &&
        final.top == m.top && final.blocks.size == m.blocks.size)
        "failed remap changed bytes, capacity or lifetime"
    | .inPlace, some s =>
      require (s.ptr == old.ptr && s.len == 8 && (block final 1).live &&
        (block final 1).bytes == #[.int 3, .int 5, .int 7, .int 11, .undef, .undef, .undef, .undef] &&
        final.top > 4098 + 8 && final.blocks.size == 2)
        "in-place remap lost prefix, new undefinedness, size or address boundary"
    | .move, some s =>
      require (s.ptr.block == some 2 && s.ptr.off == 0 && s.len == 8 &&
        !(block final 1).live && (block final 2).live && final.blocks.size == 3 &&
        (block final 2).bytes == #[.int 3, .int 5, .int 7, .int 11, .undef, .undef, .undef, .undef])
        "moved remap lost prefix, undefined suffix or old-block invalidation"
      match (final.access old.ptr 1 1).run with
      | some (.ok _) => throw (IO.userError "old pointer stayed usable after relocation")
      | some (.error .illegal) => pure ()
      | _ => throw (IO.userError "old-pointer check had an unexpected outcome")
    | _, _ => throw (IO.userError "selected byte policy returned the wrong outcome")
  | _ => throw (IO.userError "remap produced an error or no result")

private def checkRefusal : IO Unit := do
  let m := initial .inPlace
  let withLater := m.afterAlloc .heap 1 1
  match ((Allocator.remap {} 1 old 8).run withLater).run with
  | some (.ok (none, final)) =>
    require ((block final 1).bytes == (block m 1).bytes && (block final 2).live &&
      final.top == withLater.top) "live-block refusal changed the frame"
  | _ => throw (IO.userError "in-place growth overlapped a later allocation")
  -- Growth needs only that the grown range is clear of every other live block
  -- (`Mem.growFree`): a dead block's address range may be reused, as natively.
  let dead : Block := { bytes := Array.replicate 16 .undef, align := 1, kind := .heap, live := false, addr := 4100 }
  let history := { m with blocks := m.blocks.set! 0 dead }
  match ((Allocator.remap {} 1 old 8).run history).run with
  | some (.ok (some s, final)) =>
    require (s.len == 8 && (block final 1).live && !(block final 0).live)
      "growth over a dead block's range changed lifetimes"
  | _ => throw (IO.userError "in-place growth refused a dead block's address range")
  -- A live block below the growing block does not stop growth (no allocation order).
  let below : Block := { bytes := #[.int 1], align := 1, kind := .heap, live := true, addr := 64 }
  let lower := { m with blocks := m.blocks.push below }
  match ((Allocator.remap {} 1 old 8).run lower).run with
  | some (.ok (some _, final)) =>
    require ((block final 2).live && (block final 2).bytes == #[.int 1]) "growth changed a lower block"
  | _ => throw (IO.userError "in-place growth refused because a later block id lies below")
  let capped := { m with allocPolicy := { maxBytes := 7, byteRemap := .inPlace } }
  match ((Allocator.remap {} 1 old 8).run capped).run with
  | some (.ok (none, final)) =>
    require ((block final 1).bytes == (block m 1).bytes && (block final 1).live)
      "cap refusal mutated old allocation"
  | _ => throw (IO.userError "request cap was ignored")

private def checkInvalid : IO Unit := do
  for invalid in [({ old with ptr := old.ptr.add 1 } : Slice), { old with len := 3 }] do
    match ((Allocator.remap {} 1 invalid 8).run (initial .move)).run with
    | some (.error .illegal) => pure ()
    | _ => throw (IO.userError "success policy accepted an interior pointer or wrong old length")

def main : IO Unit := do
  checkMode .fail
  checkMode .inPlace
  checkMode .move
  checkRefusal
  checkInvalid
  IO.println "byte remap representation, lifetime, capacity and frame checks passed"
