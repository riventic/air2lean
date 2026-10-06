import Gen

/-! Clients of the retained generated definitions; no generated body is replaced.
The source types are Outer(before:u64, inner:Inner, after:u64) and
Inner(optional:?Payload, small:E!u8, wide:E!u64, equal:E!u16),
with Payload(guard:u32, value:u8). The qualified stage2_x86_64 ABI puts
Outer.inner after its 8-byte prefix. Inside Inner, alignment orders wide
first (16 bytes, alignment 8), optional next (12 bytes, alignment 4),
small next (4 bytes, alignment 2), then equal (4 bytes, alignment 2).
Payload.value follows its 4-byte guard. The small payload follows the
2-byte error discriminator; wide/equal payloads precede their discriminator.
These arithmetic expectations are independent of exported pointer constants. -/

namespace GlobalGeneratedClients

private def optionalOffset : Nat := 8 + 16 + 4
private def smallOffset : Nat := 8 + 28 + (Zig.errUnionOffsets 1 1).2
private def wideOffset : Nat := 8 + 0 + (Zig.errUnionOffsets 8 8).2
-- Equal-alignment payload-first ordering is the qualified stage2 source ABI.
private def equalOffset : Nat := 8 + 32

theorem optionalPtr_run (m : Zig.Mem) :
    (GlobalPayload.optionalPtr.run m).run =
      some (.ok ((⟨some 0, optionalOffset⟩ : Zig.Ptr), m)) := by rfl

theorem smallPtr_run (m : Zig.Mem) :
    (GlobalPayload.smallPtr.run m).run =
      some (.ok ((⟨some 0, smallOffset⟩ : Zig.Ptr), m)) := by rfl

theorem widePtr_run (m : Zig.Mem) :
    (GlobalPayload.widePtr.run m).run =
      some (.ok ((⟨some 0, wideOffset⟩ : Zig.Ptr), m)) := by rfl

theorem equalPtr_run (m : Zig.Mem) :
    (GlobalPayload.equalPtr.run m).run =
      some (.ok ((⟨some 0, equalOffset⟩ : Zig.Ptr), m)) := by rfl

theorem optionalSlice_run (m : Zig.Mem) :
    (GlobalPayload.optionalSlice.run m).run =
      some (.ok ((⟨(⟨some 0, optionalOffset⟩ : Zig.Ptr), 1⟩ : Zig.Slice), m)) := by rfl

theorem sameOptionalPtr_run (m : Zig.Mem) :
    (GlobalPayload.sameOptionalPtr.run m).run =
      some (.ok ((⟨some 0, optionalOffset⟩ : Zig.Ptr), m)) := by rfl

theorem sameOptional_alias :
    GlobalPayload.sameOptionalPtr = GlobalPayload.optionalPtr := by rfl

theorem optionalRead_run :
    GlobalPayload.optionalRead.run = some (.ok (7 : BitVec 8)) := by rfl

theorem smallRead_run :
    GlobalPayload.smallRead.run = some (.ok (19 : BitVec 8)) := by rfl

theorem wideRead_run :
    GlobalPayload.wideRead.run = some (.ok (41 : BitVec 64)) := by rfl

end GlobalGeneratedClients
