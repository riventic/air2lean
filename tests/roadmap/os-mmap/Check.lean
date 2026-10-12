import ZigLean.Os.Mmap

/-! Runtime regressions of the OS page-mapping model (premise OSM-01, `docs/os-mmap.md`): every
rule of `Os.mmap`/`Os.munmap`/`Os.mremap` with its negative cases, on the `linux` target
(4 KiB pages) unless noted. `lake env lean tests/roadmap/os-mmap/Check.lean`. -/

open Zig Zig.Os

namespace OsMmapCheck

/-- For `blocks[i]!` in the checks only. -/
local instance : Inhabited Block := ⟨{ bytes := #[], align := 0, kind := .heap, live := false, addr := 0 }⟩

def lx : Target := .linux
def P := lx.pageSize

/-- `MemM` outcome as a short tag, with the final memory. -/
def run {α : Type} (c : MemM α) (m : Mem := {}) : Option (Except Error (α × Mem)) :=
  (c.run m).run

def tag {α : Type} (r : Option (Except Error (α × Mem))) : String :=
  match r with
  | none => "diverges"
  | some (.error e) => s!"{repr e}"
  | some (.ok _) => "ok"

def mmapRW (len : Nat) : MemM (Except ErrName Slice) :=
  mmap lx none (BitVec.ofNat 64 len) lx.protReadWrite lx.mapPrivateAnonymous noFd 0

def mapOk (len : Nat) : MemM Slice := do
  match ← mmapRW len with
  | .ok s => pure s
  | .error _ => throw .panic

def final {α : Type} (c : MemM α) (m : Mem := {}) : Mem :=
  match run c m with
  | some (.ok (_, m')) => m'
  | _ => {}

def value {α : Type} [Inhabited α] (c : MemM α) (m : Mem := {}) : α :=
  match run c m with
  | some (.ok (v, _)) => v
  | _ => default

/-! ## mmap -/

-- Success: `len` zero bytes, page-aligned, a `.mapped 0` block, the attempt counted.
#guard (final (mapOk 100)).blocks.size == 1
#guard ((final (mapOk 100)).blocks[0]!).bytes == Array.replicate 100 (.int 0)
#guard ((final (mapOk 100)).blocks[0]!).addr % P == 0
#guard ((final (mapOk 100)).blocks[0]!).kind == .mapped 0
#guard (final (mapOk 100)).allocs == 1
#guard (value (mapOk 100)).len == 100
-- Two mappings: disjoint, the second above the first one's last page.
#guard
  let m := final (do let _ ← mapOk 100; let _ ← mapOk 5000)
  (m.blocks[0]!).addr + 4096 ≤ (m.blocks[1]!).addr && (m.blocks[1]!).addr % P == 0
-- The bytes read back as zero and can be written.
#guard tag (run (do let s ← mapOk 16; store 1 (s.ptr.add 15) (7 : BitVec 8); load (BitVec 8) 1 (s.ptr.add 15))) == "ok"
#guard value (do let s ← mapOk 16; load (BitVec 8) 1 (s.ptr.add 3)) == 0
-- Past the length: illegal.
#guard tag (run (do let s ← mapOk 16; load (BitVec 8) 1 (s.ptr.add 16))) == "Zig.Error.illegal"
-- Failure oracle: `error.OutOfMemory`, the blocks are unchanged.
#guard
  let m0 : Mem := { allocPolicy := { fails := fun _ _ => true } }
  value (mmapRW 10) m0 == .error "OutOfMemory" && (final (mmapRW 10) m0).blocks.size == 0
#guard
  let m0 : Mem := { failAt := some 0 }
  value (mmapRW 10) m0 == .error "OutOfMemory" && (final (mmapRW 10) m0).allocs == 1
-- Unmodelled arguments: unspecified. Length 0: illegal (EINVAL is `unreachable`).
#guard tag (run (mmap lx none 4096 1 lx.mapPrivateAnonymous noFd 0)) == "Zig.Error.unspecified"
#guard tag (run (mmap lx none 4096 3 0x21 noFd 0)) == "Zig.Error.unspecified"
#guard tag (run (mmap lx none 4096 3 0x22 3 0)) == "Zig.Error.unspecified"
#guard tag (run (mmap lx none 4096 3 0x22 noFd 4096)) == "Zig.Error.unspecified"
#guard tag (run (mmapRW 0)) == "Zig.Error.illegal"
-- The address space: a mapping whose pages would end above `addrLimit` is `error.OutOfMemory`
-- (one attempt, no block), at a proposed address or at the fallback `Mem.top`; one that ends
-- exactly at it succeeds. macOS: `MACH_VM_MAX_ADDRESS`.
#guard lx.addrLimit == 2 ^ 47 && Target.macos.addrLimit == 0x7FFFFE000000
#guard
  let m0 : Mem := { place := ⟨fun _ => some (2 ^ 47 - 8192)⟩ }
  value (mmapRW 8193) m0 == .error "OutOfMemory" && (final (mmapRW 8193) m0).blocks.size == 0 &&
    (final (mmapRW 8193) m0).allocs == 1 && tag (run (mmapRW 8192) m0) == "ok" &&
    ((final (mmapRW 8192) m0).blocks[0]!).addr == 2 ^ 47 - 8192
#guard
  let dead : Block := { bytes := #[], align := 1, kind := .heap, live := false, addr := 2 ^ 64 - 4097 }
  let m0 : Mem := { blocks := #[dead] }
  value (mmapRW 1) m0 == .error "OutOfMemory"
#guard
  let m0 : Mem := { place := ⟨fun _ => some (0x7FFFFE000000 - 16384)⟩ }
  value (mmap .macos none 16385 3 0x1002 noFd 0) m0 == .error "OutOfMemory" &&
    tag (run (mmap .macos none 16384 3 0x1002 noFd 0) m0) == "ok"
-- macOS encoding.
#guard tag (run (mmap .macos none 10 3 0x1002 noFd 0)) == "ok"
#guard ((final (mmap .macos none 10 3 0x1002 noFd 0)).blocks[0]!).addr % 16384 == 0
#guard tag (run (mmap .macos none 10 3 0x22 noFd 0)) == "Zig.Error.unspecified"

/-! ## munmap -/

-- Whole mapping (exact length, or rounded up to the page): the block ends.
#guard ((final (do let s ← mapOk 8192; munmap lx s)).blocks[0]!).live == false
#guard ((final (do let s ← mapOk 100; munmap lx ⟨s.ptr, 4096⟩)).blocks[0]!).live == false
-- Use after munmap and double munmap: illegal.
#guard tag (run (do let s ← mapOk 8192; munmap lx s; load (BitVec 8) 1 s.ptr)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; munmap lx s; munmap lx s)) == "Zig.Error.illegal"
-- Prefix trim: the first page is gone, the second stays.
#guard
  let c := do let s ← mapOk 8192; munmap lx ⟨s.ptr, 4096⟩; store 1 (s.ptr.add 4096) (1 : BitVec 8)
  tag (run c) == "ok" && ((final c).blocks[0]!).kind == .mapped 4096
#guard tag (run (do let s ← mapOk 8192; munmap lx ⟨s.ptr, 4096⟩; load (BitVec 8) 1 (s.ptr.add 4095))) == "Zig.Error.illegal"
-- Tail trim: the second page is gone, the first stays.
#guard
  let c := do let s ← mapOk 8192; munmap lx ⟨s.ptr.add 4096, 4096⟩; load (BitVec 8) 1 (s.ptr.add 4095)
  tag (run c) == "ok" && ((final c).blocks[0]!).bytes.size == 4096
#guard tag (run (do let s ← mapOk 8192; munmap lx ⟨s.ptr.add 4096, 4096⟩; load (BitVec 8) 1 (s.ptr.add 4096))) == "Zig.Error.illegal"
-- Prefix then tail (PageAllocator's over-aligned map): the middle page stays.
#guard
  let c := do
    let s ← mapOk 12288
    munmap lx ⟨s.ptr, 4096⟩
    munmap lx ⟨s.ptr.add 8192, 4096⟩
    munmap lx ⟨s.ptr.add 4096, 4096⟩
  tag (run c) == "ok" && ((final c).blocks[0]!).live == false
-- A middle range, a misaligned start, an empty or overlong range, a heap block, no block: illegal.
#guard tag (run (do let s ← mapOk 12288; munmap lx ⟨s.ptr.add 4096, 4096⟩)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; munmap lx ⟨s.ptr.add 1, 4095⟩)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; munmap lx ⟨s.ptr, 0⟩)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; munmap lx ⟨s.ptr, 12288⟩)) == "Zig.Error.illegal"
#guard tag (run (do let p ← alloc .heap 4096 4096; munmap lx ⟨p, 4096⟩)) == "Zig.Error.illegal"
#guard tag (run (munmap lx ⟨⟨none, 4096⟩, 4096⟩)) == "Zig.Error.illegal"
-- After a prefix trim the old start is no longer a mapping start.
#guard tag (run (do let s ← mapOk 8192; munmap lx ⟨s.ptr, 4096⟩; munmap lx ⟨s.ptr, 4096⟩)) == "Zig.Error.illegal"

/-! ## mremap -/

def remap (s : Slice) (n : Nat) (flags : BitVec 32 := mremapMayMove) : MemM (Except ErrName Slice) :=
  mremap lx (some s.ptr) s.len (BitVec.ofNat 64 n) flags none

/-- The placement puts the second mapping (block 1) right after a one-page first mapping (block 0,
at the fallback address 4096): the first has no room to grow in place. -/
def adj : Mem := { place := ⟨fun b => if b = 1 then some 8192 else none⟩ }

-- The placement takes that address.
#guard ((final (do let _ ← mapOk 4096; mapOk 4096) adj).blocks.map (·.addr)) == #[4096, 8192]

-- Shrink in place: same pointer, fewer bytes; the cut bytes are gone.
#guard
  let c := do let s ← mapOk 8192; remap s 4096
  match value c with
  | .ok r => r.ptr == ⟨some 0, 0⟩ && r.len == 4096 && ((final c).blocks[0]!).bytes.size == 4096
  | .error _ => false
-- Grow in place (the only mapping, no move chosen): same pointer, zero bytes after the old end.
#guard
  let c := do let s ← mapOk 4096; store 1 s.ptr (9 : BitVec 8); remap s 8192
  match value c with
  | .ok r => r.ptr == ⟨some 0, 0⟩ && ((final c).blocks[0]!).bytes.size == 8192 &&
      ((final c).blocks[0]!).bytes[0]! == .int 9 && ((final c).blocks[0]!).bytes[5000]! == .int 0
  | .error _ => false
-- Grow of an unaligned length: the stale page tail is undefined.
#guard ((final (do let s ← mapOk 100; remap s 8192)).blocks[0]!).bytes[200]! == .undef
-- Grow with a block right after it and MAYMOVE: moves, copies, ends the old block.
#guard
  let c := do let s ← mapOk 4096; store 1 s.ptr (9 : BitVec 8); let _ ← mapOk 4096; remap s 8192
  let m := final c adj
  match value c adj with
  | .ok r => r.ptr == ⟨some 2, 0⟩ && (m.blocks[0]!).live == false && (m.blocks[2]!).bytes[0]! == .int 9 &&
      (m.blocks[2]!).addr % P == 0 && (m.blocks[2]!).kind == .mapped 0
  | .error _ => false
-- The oracle moves even when there is room.
#guard
  let m0 : Mem := { allocPolicy := { os := { mremapMoves := fun _ _ => true } } }
  match value (do let s ← mapOk 4096; remap s 8192) m0 with
  | .ok r => r.ptr == ⟨some 1, 0⟩
  | .error _ => false
-- Grow without MAYMOVE and without room: OutOfMemory, the mapping unchanged.
#guard
  let c := do let s ← mapOk 4096; let _ ← mapOk 4096; remap s 8192 0
  value c adj == .error "OutOfMemory" && ((final c adj).blocks[0]!).live &&
    ((final c adj).blocks[0]!).bytes.size == 4096
-- With a gap page after it (the fallback placement), the same growth stays in place.
#guard
  let c := do let s ← mapOk 4096; let _ ← mapOk 4096; remap s 8192 0
  match value c with
  | .ok r => r.ptr == ⟨some 0, 0⟩ && ((final c).blocks[0]!).bytes.size == 8192
  | .error _ => false
-- Failure oracle on a growth: `error.OutOfMemory`, the mapping unchanged.
#guard
  let m0 : Mem := { allocPolicy := { fails := fun i _ => i == 1 } }
  let c := do let s ← mapOk 4096; remap s 8192
  value c m0 == .error "OutOfMemory" && ((final c m0).blocks[0]!).bytes.size == 4096
-- The address space: an in-place growth ending exactly at `addrLimit` succeeds; one past it, and
-- a move past it, are `error.OutOfMemory` with the mapping unchanged.
#guard
  let m0 : Mem := { place := ⟨fun b => if b == 0 then some (2 ^ 47 - 8192) else none⟩ }
  let c := do let s ← mapOk 4096; remap s 8192 0
  tag (run c m0) == "ok" && ((final c m0).blocks[0]!).bytes.size == 8192
#guard
  let m0 : Mem := { place := ⟨fun b => if b == 0 then some (2 ^ 47 - 4096) else none⟩ }
  let c := do let s ← mapOk 4096; remap s 8192 0
  value c m0 == .error "OutOfMemory" && ((final c m0).blocks[0]!).bytes.size == 4096
#guard
  let m0 : Mem := { place := ⟨fun b => if b == 0 then some (2 ^ 47 - 4096) else none⟩ }
  let c := do let s ← mapOk 4096; remap s 8192
  value c m0 == .error "OutOfMemory" && ((final c m0).blocks[0]!).live &&
    (final c m0).blocks.size == 1
-- new_len = 0 (EINVAL): outside the model.
#guard tag (run (do let s ← mapOk 4096; remap s 0)) == "Zig.Error.unspecified"
-- Not a whole live mapping, a heap block, after munmap: illegal.
#guard tag (run (do let s ← mapOk 8192; remap ⟨s.ptr, 4096⟩ 100)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; remap ⟨s.ptr.add 4096, 4096⟩ 100)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; munmap lx s; remap s 100)) == "Zig.Error.illegal"
#guard tag (run (do let p ← alloc .heap 4096 4096; remap ⟨p, 4096⟩ 100)) == "Zig.Error.illegal"
-- Use of the old pointer after a move: illegal.
#guard
  tag (run (do let s ← mapOk 4096; let _ ← mapOk 4096; let _ ← remap s 8192; load (BitVec 8) 1 s.ptr)
    adj) == "Zig.Error.illegal"
-- FIXED/DONTUNMAP flags, a new address, macOS: unspecified.
#guard tag (run (do let s ← mapOk 4096; remap s 8192 2)) == "Zig.Error.unspecified"
#guard tag (run (do let s ← mapOk 4096; mremap lx (some s.ptr) s.len 8192 1 (some s.ptr))) == "Zig.Error.unspecified"
#guard tag (run (mremap .macos none 4096 8192 1 none)) == "Zig.Error.unspecified"

end OsMmapCheck
