import Air2Lean
import Air2Lean.Check
open Air2Lean

/-! L09 checker controls: a vector with non-byte (`u9`) or ABI-padded (`u24`, `f80`) lanes is a
memory type only for an AIR file whose schema-12 profile names the LLVM backend, with the
bit-packed size and alignment; lane pointers into such a vector stay rejected; byte-strided
lanes keep their backend-independent layout.

    lake env lean --run tests/roadmap/vector-layouts/Checker.lean -/

private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)

private def types : Array Ty := #[
  .int false 9, .vector 4 0, .ptr "one" false 1,       -- 0..2: u9, @Vector(4, u9), *@Vector(4, u9)
  .int false 32, .vector 4 3, .ptr "one" false 4,      -- 3..5: u32, @Vector(4, u32), *@Vector(4, u32)
  .float 80, .vector 2 6,                              -- 6..7: f80, @Vector(2, f80)
  .int false 24, .vector 3 8,                          -- 8..9: u24, @Vector(3, u24)
  .int false 0, .vector 4 10]                          -- 10..11: u0, @Vector(4, u0)

/-- The compiler's (LLVM backend) sizes and alignments, as the exporter writes them. -/
private def exported : Array Layout := #[
  {size := some 2, align := some 2}, {size := some 8, align := some 8},
  {size := some 8, align := some 8, ptrAlign := some 8},
  {size := some 4, align := some 4}, {size := some 16, align := some 16},
  {size := some 8, align := some 8, ptrAlign := some 16},
  {size := some 16, align := some 16}, {size := some 32, align := some 32},
  {size := some 4, align := some 4}, {size := some 16, align := some 16},
  {size := some 0, align := some 1}, {size := some 0, align := some 1}]

private def raw (backend : String) (schema : Nat := 12) : Raw.RawFunc :=
  { schema, zigVersion := "0.16.0", name := "probe.f", params := #[], ret := 3, body := #[],
    types, layouts := exported, globals := #[],
    profile := { name := "abi64-le-v1", schema, zigVersion := "0.16.0", backend } }

private def layoutsOf (backend : String) (schema : Nat := 12) : IO (Array Layout) := do
  match normalizeCanonical (raw backend schema) with
  | .ok f => pure f.layouts
  | .error e => throw (IO.userError e)

private def accepts (layouts : Array Layout) (id : TyId) : Bool :=
  (checkMemTy "probe.f" types layouts 0 id).toOption.isSome

private def laneCx (layouts : Array Layout) (pty : TyId) : CheckCtx :=
  { fnName := "probe.f", types, layouts, instTys := #[(0, pty)], places := #[] }

def main : IO Unit := do
  let llvm ← layoutsOf "stage2_llvm"
  require ([1, 4, 7, 9, 11].all fun i => llvm[i]!.packedLanes) "LLVM vector layouts are not marked bit-packed"
  require ([0, 2, 3, 5, 6, 8, 10].all fun i => !llvm[i]!.packedLanes) "a non-vector layout is marked"
  require (modelLayout types llvm 1 == .ok (8, 8)) "u9x4: bit-packed 36 bits, 8 bytes"
  require (modelLayout types llvm 9 == .ok (16, 16)) "u24x3: bit-packed 72 bits, 16 bytes"
  require (modelLayout types llvm 7 == .ok (32, 32)) "f80x2: bit-packed 160 bits, 32 bytes"
  require (modelLayout types llvm 4 == .ok (16, 16)) "u32x4: byte lanes, 16 bytes"
  require ([1, 4, 7, 9].all (accepts llvm)) "an LLVM vector layout is rejected"
  require (!accepts llvm 11) "a vector of u0 lanes in memory is accepted"
  -- A size the model does not produce (another backend's byte-strided u9 lanes) fails closed.
  require (!accepts (llvm.set! 1 {llvm[1]! with size := some 16, align := some 16}) 1)
    "a u9x4 with a 16-byte exported layout is accepted"
  IO.println "LLVM-profile bit-packed vector layouts accepted"
  for (backend, schema) in [("stage2_x86_64", 12), ("stage2_c", 12), ("unverified", 11)] do
    let other ← layoutsOf backend schema
    require ([1, 7, 9].all fun i => !accepts other i) s!"{backend}: a non-byte-lane vector is accepted"
    require (accepts other 4) s!"{backend}: the byte-lane u32x4 vector is rejected"
  IO.println "non-LLVM and legacy profiles reject non-byte lanes, keep byte lanes"
  -- A pointer to a lane: an item pointer for byte lanes only.
  require ((laneCx llvm 5).itemAccess 0 (.inst 0) |>.toOption.isSome) "u32 lane pointer rejected"
  require ((laneCx llvm 2).itemAccess 0 (.inst 0) |>.toOption.isNone) "u9 lane pointer accepted"
  IO.println "lane pointers: byte lanes accepted, bit-packed lanes rejected"
