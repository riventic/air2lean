-- Appended to the fresh source translation; never run against a stale generated module.
private def attempt (zero : Bool) (n : BitVec 64) : Zig.MemM Bool := do
  let result ← if zero then ByteSentinel.makeZero {} n else ByteSentinel.makeByte {} n
  match result with
  | .error e =>
    if e != "OutOfMemory" then throw .illegal
    pure false
  | .ok s =>
    let m ← get
    let some b := s.ptr.block | throw .illegal
    let some block := m.blocks[b]? | throw .illegal
    if s.len != n || block.bytes.size != n.toNat + 1 then throw .illegal
    let sentinel ← Zig.load (BitVec 8) 1 (s.ptr.add n.toNat)
    if sentinel != (if zero then 0 else 42) then throw .illegal
    for j in [:n.toNat] do Zig.store 1 (s.ptr.add j) (BitVec.ofNat 8 (j + 7))
    for j in [:n.toNat] do
      let got ← Zig.load (BitVec 8) 1 (s.ptr.add j)
      if got != BitVec.ofNat 8 (j + 7) then throw .illegal
    let again ← Zig.load (BitVec 8) 1 (s.ptr.add n.toNat)
    if again != sentinel then throw .illegal
    if zero then ByteSentinel.releaseZero {} s else ByteSentinel.releaseByte {} s
    pure true

private def runCases (zero : Bool) (name : String) (cap : Nat) (failures : List Nat)
    (sizes : List Nat) (expected : List Bool) : IO Unit := do
  let mut m : Zig.Mem := { allocPolicy := { maxBytes := cap, failures } }
  for ((n, want), i) in (sizes.zip expected).zipIdx do
    match ((attempt zero (BitVec.ofNat 64 n)).run m).run with
    | some (.ok (ok, next)) =>
      unless ok == want && next.allocs == i + 1 && next.blocks.all (fun b => !b.live) do
        throw (IO.userError s!"sentinel outcome/ownership mismatch: {name}")
      m := next
      IO.println s!"{name} {i} {if ok then 1 else 0} {m.allocs} 0"
    | _ => throw (IO.userError s!"sentinel runtime assertion failed: {name}")

def main : IO Unit := do
  runCases true "zero-sentinel" 64 [] [0, 1, 8] [true, true, true]
  runCases false "nonzero-sentinel" 64 [] [0, 1, 8] [true, true, true]
  runCases false "repeated-failure" 64 [0, 2] [0, 8, 0, 8] [false, true, false, true]
  runCases false "extra-byte-cap" 8 [] [7, 8] [true, false]
  runCases true "empty-can-fail" 0 [] [0] [false]
  match ((ByteSentinel.makeByte {} (BitVec.ofNat 64 (2^64-1))).run {}).run with
  | some (.error .panic) => pure ()
  | _ => throw (IO.userError "maximum usize must panic before allocation")
