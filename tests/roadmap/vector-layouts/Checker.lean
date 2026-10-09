import Air2Lean
import Air2Lean.Check
open Air2Lean

/-! L09 checker controls: a vector with non-byte (`u9`) or ABI-padded (`u24`, `f80`) lanes is a
memory type only for an AIR file whose schema-12 profile names the LLVM backend, with the
bit-packed size and alignment; byte-strided lanes keep their backend-independent layout. A lane
pointer (`vector_index`) into an integer or `bool` vector becomes a bit-pointer into the vector's
integer only for an LLVM profile on x86_64 or aarch64; float lanes, runtime lanes, other
backends and other targets stay rejected.

    lake env lean --run tests/roadmap/vector-layouts/Checker.lean -/

private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)

private def types : Array Ty := #[
  .int false 9, .vector 4 0, .ptr "one" false 1,       -- 0..2: u9, @Vector(4, u9), *@Vector(4, u9)
  .int false 32, .vector 4 3, .ptr "one" false 4,      -- 3..5: u32, @Vector(4, u32), *@Vector(4, u32)
  .float 80, .vector 2 6,                              -- 6..7: f80, @Vector(2, f80)
  .int false 24, .vector 3 8,                          -- 8..9: u24, @Vector(3, u24)
  .int false 0, .vector 4 10,                          -- 10..11: u0, @Vector(4, u0)
  .ptr "one" false 0, .bool, .vector 5 13,             -- 12: &v[2] of u9x4; 13..14: bool, @Vector(5, bool)
  .ptr "one" false 14, .ptr "one" false 13,            -- 15: *@Vector(5, bool); 16: &v[3] of bool5
  .ptr "one" false 6, .ptr "one" false 0]              -- 17: &v[1] of f80x2; 18: runtime lane of u9x4

/-- The compiler's (LLVM backend) sizes and alignments, as the exporter writes them. -/
private def exported : Array Layout := #[
  {size := some 2, align := some 2}, {size := some 8, align := some 8},
  {size := some 8, align := some 8, ptrAlign := some 8},
  {size := some 4, align := some 4}, {size := some 16, align := some 16},
  {size := some 8, align := some 8, ptrAlign := some 16},
  {size := some 16, align := some 16}, {size := some 32, align := some 32},
  {size := some 4, align := some 4}, {size := some 16, align := some 16},
  {size := some 0, align := some 1}, {size := some 0, align := some 1},
  {size := some 8, align := some 8, ptrAlign := some 2, hostSize := 4, vectorIndex := some 2,
    vectorIndexExported := true},
  {size := some 1, align := some 1}, {size := some 1, align := some 1},
  {size := some 8, align := some 8, ptrAlign := some 1},
  {size := some 8, align := some 8, ptrAlign := some 1, hostSize := 5, vectorIndex := some 3,
    vectorIndexExported := true},
  {size := some 8, align := some 8, ptrAlign := some 16, hostSize := 2, vectorIndex := some 1,
    vectorIndexExported := true},
  {size := some 8, align := some 8, ptrAlign := some 2, hostSize := 4, runtimeLane := true,
    vectorIndexExported := true}]

private def raw (backend : String) (schema : Nat := 12)
    (targetTriple : String := "x86_64-linux.5.10...6.19-musl") : Raw.RawFunc :=
  { schema, zigVersion := "0.16.0", name := "probe.f", params := #[], ret := 3, body := #[],
    types, layouts := exported, globals := #[],
    profile := { name := "abi64-le-v1", schema, zigVersion := "0.16.0", backend, targetTriple } }

private def layoutsOf (backend : String) (schema : Nat := 12)
    (targetTriple : String := "x86_64-linux.5.10...6.19-musl") : IO (Array Layout) := do
  match normalizeCanonical (raw backend schema targetTriple) with
  | .ok f => pure f.layouts
  | .error e => throw (IO.userError e)

private def accepts (layouts : Array Layout) (id : TyId) : Bool :=
  (checkMemTy "probe.f" types layouts 0 id).toOption.isSome

private def laneCx (layouts : Array Layout) (pty : TyId) : CheckCtx :=
  { fnName := "probe.f", types, layouts, instTys := #[(0, pty)], places := #[] }

private def tyOk (layouts : Array Layout) (id : TyId) : Bool :=
  (checkTy "probe.f" types layouts 0 id).toOption.isSome

def main : IO Unit := do
  let llvm ← layoutsOf "stage2_llvm"
  require ([1, 4, 7, 9, 11, 14].all fun i => llvm[i]!.packedLanes) "LLVM vector layouts are not marked bit-packed"
  require ([0, 2, 3, 5, 6, 8, 10, 13, 15, 17, 18].all fun i => !llvm[i]!.packedLanes)
    "a non-vector layout is marked"
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
  IO.println "item pointers: byte lanes accepted, bit-packed lanes rejected"
  -- Lane pointers (`vector_index`): bit-pointers into the vector's integer.
  let u9 := llvm[12]!
  require (u9.laneBitPtr && u9.hostSize == 5 && u9.bitOffset == 18) "u9x4 lane 2: 5 host bytes, bit 18"
  let b5 := llvm[16]!
  require (b5.laneBitPtr && b5.hostSize == 1 && b5.bitOffset == 3) "bool5 lane 3: 1 host byte, bit 3"
  require (tyOk llvm 12 && tyOk llvm 16) "an integer or bool lane pointer is rejected"
  require (!tyOk llvm 17 && !llvm[17]!.laneBitPtr) "an f80 lane pointer is accepted"
  require (!tyOk llvm 18 && !llvm[18]!.laneBitPtr) "a runtime lane pointer is accepted"
  let lane (cx : CheckCtx) (ty : TyId) (k : Int) := (cx.lanePtr 0 ty (.inst 0) (.int 3 k)).toOption.isSome
  require (lane (laneCx llvm 2) 12 2 && lane (laneCx llvm 15) 16 3) "&v[i] with its own lane is rejected"
  require (!lane (laneCx llvm 2) 12 1) "&v[1] typed as lane 2 is accepted"
  require (!lane (laneCx llvm 15) 12 2) "a u9 lane pointer into a bool vector is accepted"
  require (!lane (laneCx llvm 5) 12 2) "a u9 lane pointer into a u32 vector is accepted"
  require ((laneCx llvm 16).atomicChild 0 (.inst 0) |>.toOption.isNone)
    "an atomic op through a bool lane pointer is accepted"
  IO.println "lane pointers: integer and bool lanes are bit-pointers on LLVM x86_64/aarch64"
  for (backend, schema, triple) in [("stage2_x86_64", 12, "x86_64-linux.5.10...6.19-musl"),
      ("stage2_c", 12, "x86_64-linux.5.10...6.19-musl"), ("unverified", 11, "unverified"),
      ("stage2_llvm", 12, "riscv64-linux.5.10...6.19-musl"),
      ("stage2_llvm", 12, "arm-linux.5.10...6.19-musleabihf")] do
    let other ← layoutsOf backend schema triple
    require ([12, 16].all fun i => !tyOk other i && !other[i]!.laneBitPtr)
      s!"{backend} {triple}: a lane pointer is accepted"
  IO.println "lane pointers: other backends and targets rejected"
