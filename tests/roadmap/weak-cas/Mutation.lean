import ZigLean
open Zig
private def matching (p : Ptr) : MemM (Option (BitVec 8)) :=
  cmpxchgWeakAt 1 .acqRel .acquire 1 p (42#8) (7#8)

def main : IO Unit := do
  let test : MemM Bool := do
    let p ← alloc .heap 1 1
    store 1 p (42#8)
    let r ← matching p
    let m ← get
    let v ← load (BitVec 8) 1 p
    pure (r == some 42#8 && v == 42#8 && m.atomics[0]!.msgs.size == 1 &&
      !(m.footprint.any fun a => a.kind == .atomicWrite))
  match (test.run {}).run with
  | some (.ok (true, _)) => pure ()
  | _ =>
    IO.eprintln "C11_ASSERTION: spurious failure branch removed"
    IO.Process.exit 85
  IO.println "Weak CAS mutation baseline passed"
