import Gen
/-! `std.mem.Allocator.create` modified (via `--zig-lib-dir`) to always return
`error.OutOfMemory`: the export still names it module `std`, so the translator binds the reviewed
allocator model. Natively `made` returns 0; the model returns 5. Fixed: `air/` is re-exported with
the binding exporter, which names that std `std@modified`; the translator rejects it, so this
witness is never reached. -/
open H

#guard (match ((made ⟨⟩).run (mem0 .fresh)).run with
  | some (.ok (v, _)) => v.toNat
  | _ => 999) = 5
