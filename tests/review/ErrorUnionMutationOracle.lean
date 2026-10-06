import ZigLean.Mem.Enc

open Zig

def main (args : List String) : IO Unit := do
  let name := args.head!
  let ok := match name with
    | "equal_alignment" => decide (errUnionOffsets 2 2 = (2, 0))
    | "zero_offset" => decide (errUnionOffsets 0 8 = (0, 0))
    | "zero_size" => decide (errUnionSize 0 8 = 8)
    | _ => false
  unless ok do throw (IO.userError s!"ABI_MUTANT_DETECTED:{name}")
  IO.println s!"ABI mutation oracle passed: {name}"
