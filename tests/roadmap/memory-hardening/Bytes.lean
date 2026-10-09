import ZigLean

/-! MM-11 regression: pointer bytes and integer bytes reinterpret as in Zig.

A load of an integer from the bytes of a pointer gives the pointer's address (`decodeLoad`,
PNVI-ae style exposure); a load of a pointer from integer bytes gives the pointer to that
address without a block, through which an access is `.illegal`. A pointer still round-trips
through its own bytes with its block. -/

open Zig

/-- Block 0: 8 bytes; block 1: 16 bytes, where the test stores. -/
def m0 : Mem := Mem.ofGlobals [(Array.replicate 8 .undef, 8, .global), (Array.replicate 16 .undef, 8, .global)]

def target : Ptr := ⟨some 0, 3⟩
def slot : Ptr := ⟨some 1, 0⟩

/-- The address of `target` in `m0`. -/
def targetAddr : Nat := ((m0.blocks[0]?.map (·.addr)).getD 0) + 3

def outcome {α : Type} (x : MemM α) : Option (Except Error α) :=
  ((x.run m0).run).map fun r => r.map (·.1)

-- The bytes of a pointer read as a `usize`: its address.
#guard outcome (do store 8 slot target; load (BitVec 64) 8 slot) == some (.ok (BitVec.ofNat 64 targetAddr))
-- One byte of a pointer read as a `u8` (`std.mem.asBytes(&p)[1]`): that byte of the address.
#guard outcome (do store 8 slot target; load (BitVec 8) 1 (slot.add 1)) ==
  some (.ok (BitVec.ofNat 8 (targetAddr / 256)))
-- A pointer still loads back with its block.
#guard outcome (do store 8 slot target; load Ptr 8 slot) == some (.ok target)
-- Integer bytes read as a pointer: the address, without a block.
#guard outcome (do store 8 slot (BitVec.ofNat 64 targetAddr); load Ptr 8 slot) ==
  some (.ok ⟨none, targetAddr⟩)
-- An access through it is illegal (no provenance).
#guard outcome (do store 8 slot (BitVec.ofNat 64 targetAddr); let q ← load Ptr 8 slot; load (BitVec 8) 1 q) ==
  some (.error .illegal)
-- Undefined bytes stay undefined for both readings.
#guard outcome (load (BitVec 64) 8 slot) == some (.error .unspecified)
#guard outcome (load Ptr 8 slot) == some (.error .unspecified)
#guard targetAddr > 3
