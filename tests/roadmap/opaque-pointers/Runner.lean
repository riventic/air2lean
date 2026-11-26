-- Appended to the freshly emitted OpaquePtrs translation of `air/<version>` by check.sh: the
-- model's transcript of `main` in opaque_ptrs.zig, up to the `viaApply` line.
private def observed (x : Zig.MemM α) : IO α :=
  match (x.run (OpaquePtrs.mem0 .fresh)).run with
  | some (.ok (v, _)) => pure v
  | some (.error e) => throw (IO.userError s!"unexpected modeled error: {reprStr e}")
  | none => throw (IO.userError "unexpected modeled divergence")

private def bit (b : Bool) : Nat := if b then 1 else 0
/-- A `u32` variable holding `v` (the native `x` and `y`). -/
private def word (v : BitVec 32) : Zig.MemM Zig.Ptr := do
  let p ← Zig.alloc .heap 4 4
  Zig.store 4 p v
  pure p
/-- The native `hx` and `hy`: the handles of `x = 41` and `y = 7`. -/
private def handles : Zig.MemM (Zig.Ptr × Zig.Ptr × Zig.Ptr × Zig.Ptr) := do
  let x ← word 41
  let y ← word 7
  pure (x, y, ← OpaquePtrs.erase x, ← OpaquePtrs.erase y)

def main : IO Unit := do
  let (a, b, c, d) ← observed (do
    let (_, _, hx, hy) ← handles
    pure (bit ((← OpaquePtrs.copy hx) = hx), bit (← OpaquePtrs.same hx hx),
      bit (← OpaquePtrs.same hx hy), bit (← OpaquePtrs.constSame hx hx)))
  IO.println s!"copy {a} same {b} {c} constSame {d}"
  let (a, b, c, d) ← observed (do
    let (_, _, hx, hy) ← handles
    pure (bit (← OpaquePtrs.isNull none), bit (← OpaquePtrs.isNull (some hx)),
      bit ((← OpaquePtrs.wrap hx) = some hx), bit ((← OpaquePtrs.unwrap (some hy)) = hy)))
  IO.println s!"isNull {a} {b} wrap {c} unwrap {d}"
  let (a, b, c, d, e) ← observed (do
    let (_, _, hx, hy) ← handles
    pure (bit ((← OpaquePtrs.orElse none hy) = hy), bit ((← OpaquePtrs.orElse (some hx) hy) = hx),
      bit (← OpaquePtrs.optSame none none), bit (← OpaquePtrs.optSame (some hx) none),
      bit (← OpaquePtrs.optSame (some hx) (some hx))))
  IO.println s!"orElse {a} {b} optSame {c} {d} {e}"
  let (a, b) ← observed (do
    let (_, _, hx, hy) ← handles
    let slot ← Zig.alloc .heap 8 8
    Zig.store 8 slot hx
    let old ← OpaquePtrs.slotSwap slot hy
    pure (bit (old = hx), bit ((← Zig.load Zig.Ptr 8 slot) = hy)))
  IO.println s!"slotSwap {a} {b}"
  let (a, b, n, c, d) ← observed (do
    let (_, _, hx, hy) ← handles
    let cell ← Zig.alloc .heap 24 8
    Zig.store 8 cell ({ h := hx, o := none, n := 3 } : OpaquePtrs.Cell)
    OpaquePtrs.cellPut cell hy (some hx)
    let a := bit ((← OpaquePtrs.cellGet cell) = hy)
    let b := bit ((← OpaquePtrs.cellOpt cell) = some hx)
    let n := (← Zig.load OpaquePtrs.Cell 8 cell).n.toNat
    OpaquePtrs.cellPut cell hx none
    pure (a, b, n, bit ((← OpaquePtrs.cellGet cell) = hx), bit ((← OpaquePtrs.cellOpt cell) = none)))
  IO.println s!"cell {a} {b} {n} {c} {d}"
  let (a, b, c, d) ← observed (do
    let (_, _, hx, hy) ← handles
    let hs ← OpaquePtrs.pair hx hy
    let block ← Zig.alloc .heap 16 8
    Zig.store 8 block hs
    let slice : Zig.Slice := { ptr := block, len := 2 }
    pure (bit (hs[0] = hx), bit (hs[1] = hy), bit ((← OpaquePtrs.item slice 0) = hx),
      bit ((← OpaquePtrs.item slice 1) = hy)))
  IO.println s!"pair {a} {b} item {c} {d}"
  let (a, b, c, d, e, f) ← observed (do
    let (x, y, hx, hy) ← handles
    pure (bit ((← OpaquePtrs.fromAny (← OpaquePtrs.toAny hx)) = hx),
      bit ((← Zig.ptrAddr (← OpaquePtrs.toOther hx)) = (← Zig.ptrAddr hx)),
      bit ((← OpaquePtrs.toConst hx) = hx), bit ((← OpaquePtrs.optErase none) = none),
      bit ((← OpaquePtrs.optErase (some y)) = some hy),
      bit ((← OpaquePtrs.address hx).toNat = (← Zig.ptrAddr x).toNat)))
  IO.println s!"casts {a} {b} {c} {d} {e} {f}"
  let a ← observed (do
    let (_, _, hx, _) ← handles
    pure (bit ((← OpaquePtrs.alignDown (← OpaquePtrs.alignUp hx)) = hx)))
  IO.println s!"align {a}"
  let (a, b, c) ← observed (do
    let (x, y, hx, _) ← handles
    let tx ← OpaquePtrs.typedOf x
    pure (bit (← OpaquePtrs.typedSame tx (← OpaquePtrs.typedOf x)),
      bit (← OpaquePtrs.typedSame tx (← OpaquePtrs.typedOf y)),
      bit ((← OpaquePtrs.typedToHandle tx) = hx)))
  IO.println s!"typed {a} {b} {c}"
  let a ← observed (do
    let (_, _, hx, _) ← handles
    pure (bit (← OpaquePtrs.viaApply hx)))
  IO.println s!"viaApply {a}"
  let (a, b, c) ← observed (do
    let (_, _, hx, _) ← handles
    pure (bit ((← OpaquePtrs.viaExtern hx) = hx), bit (← OpaquePtrs.viaExternOpt (some hx)),
      bit (← OpaquePtrs.viaExternOpt none)))
  IO.println s!"extern {a} {b} {c}"
  -- Model only (the native `main` would end here): the `@alignCast` check of a handle at an
  -- odd address panics.
  let misaligned := ((do
    let block ← Zig.alloc .heap 8 4
    discard <| OpaquePtrs.alignUp (← OpaquePtrs.erase (block.add 1))) : Zig.MemM Unit)
  match (misaligned.run (OpaquePtrs.mem0 .fresh)).run with
  | some (.error .panic) => IO.println "model alignUp misaligned panic"
  | _ => throw (IO.userError "a misaligned alignUp did not panic")
