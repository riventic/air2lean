import ZigLean.Os.Mmap

/-! Runtime regressions of the OS page-mapping model (premise OS-01, `docs/os-mmap.md`): every
rule of `Os.mmap`/`Os.munmap`/`Os.mremap` with its negative cases, on the `x86_64-linux`
profile (4 KiB pages) unless noted. `lake env lean tests/roadmap/os-mmap/Check.lean`. -/

open Zig Zig.Os

namespace OsMmapCheck

/-- For `blocks[i]!` in the checks only. -/
local instance : Inhabited Block := ⟨{ bytes := #[], align := 0, kind := .heap, live := false, addr := 0 }⟩

def lx := Profile.linuxX86_64
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
-- Failure oracle: the error is a `MMapError`, the blocks are unchanged.
#guard
  let m0 : Mem := { allocPolicy := { fails := fun _ _ => true, os := { mmapError := fun _ _ => .lockedMemoryLimitExceeded } } }
  value (mmapRW 10) m0 == .error "LockedMemoryLimitExceeded" && (final (mmapRW 10) m0).blocks.size == 0
#guard
  let m0 : Mem := { failAt := some 0 }
  value (mmapRW 10) m0 == .error "OutOfMemory" && (final (mmapRW 10) m0).allocs == 1
-- Unmodelled arguments: unspecified. Length 0: illegal (EINVAL is `unreachable`).
#guard tag (run (mmap lx none 4096 1 lx.mapPrivateAnonymous noFd 0)) == "Zig.Error.unspecified"
#guard tag (run (mmap lx none 4096 3 0x21 noFd 0)) == "Zig.Error.unspecified"
#guard tag (run (mmap lx none 4096 3 0x22 3 0)) == "Zig.Error.unspecified"
#guard tag (run (mmap lx none 4096 3 0x22 noFd 4096)) == "Zig.Error.unspecified"
#guard tag (run (mmapRW 0)) == "Zig.Error.illegal"
-- macOS encoding.
#guard tag (run (mmap .macosAarch64 none 10 3 0x1002 noFd 0)) == "ok"
#guard ((final (mmap .macosAarch64 none 10 3 0x1002 noFd 0)).blocks[0]!).addr % 16384 == 0
#guard tag (run (mmap .macosAarch64 none 10 3 0x22 noFd 0)) == "Zig.Error.unspecified"

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
-- Grow with a block above it and MAYMOVE: moves, copies, ends the old block.
#guard
  let c := do let s ← mapOk 4096; store 1 s.ptr (9 : BitVec 8); let _ ← mapOk 4096; remap s 8192
  let m := final c
  match value c with
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
  value c == .error "OutOfMemory" && ((final c).blocks[0]!).live && ((final c).blocks[0]!).bytes.size == 4096
-- Failure oracle on a growth: an `MRemapError`, the mapping unchanged.
#guard
  let m0 : Mem := { allocPolicy := { fails := fun i _ => i == 1, os := { mremapError := fun _ _ => .lockedMemoryLimitExceeded } } }
  let c := do let s ← mapOk 4096; remap s 8192
  value c m0 == .error "LockedMemoryLimitExceeded" && ((final c m0).blocks[0]!).bytes.size == 4096
-- new_len = 0: InvalidSyscallParameters.
#guard value (do let s ← mapOk 4096; remap s 0) == .error "InvalidSyscallParameters"
-- Not a whole live mapping, a heap block, after munmap: illegal.
#guard tag (run (do let s ← mapOk 8192; remap ⟨s.ptr, 4096⟩ 100)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; remap ⟨s.ptr.add 4096, 4096⟩ 100)) == "Zig.Error.illegal"
#guard tag (run (do let s ← mapOk 8192; munmap lx s; remap s 100)) == "Zig.Error.illegal"
#guard tag (run (do let p ← alloc .heap 4096 4096; remap ⟨p, 4096⟩ 100)) == "Zig.Error.illegal"
-- Use of the old pointer after a move: illegal.
#guard
  tag (run (do let s ← mapOk 4096; let _ ← mapOk 4096; let _ ← remap s 8192; load (BitVec 8) 1 s.ptr)) ==
    "Zig.Error.illegal"
-- FIXED/DONTUNMAP flags, a new address, macOS: unspecified.
#guard tag (run (do let s ← mapOk 4096; remap s 8192 2)) == "Zig.Error.unspecified"
#guard tag (run (do let s ← mapOk 4096; mremap lx (some s.ptr) s.len 8192 1 (some s.ptr))) == "Zig.Error.unspecified"
#guard tag (run (mremap .macosAarch64 none 4096 8192 1 none)) == "Zig.Error.unspecified"

end OsMmapCheck
