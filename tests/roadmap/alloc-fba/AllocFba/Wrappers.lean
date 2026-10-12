import AllocFba.Full
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch

/-!
# Contracts of the generated `std.mem.Allocator` wrappers over `FAllocSpec`

The wrappers that the translator emitted for `client.zig` (`--allocator-model translated`) call
the allocator through the `Allocator` value's vtable (`vtR`: persistent knowledge of the `const`
vtable). Each contract below holds for **every allocator invariant `I`** whose vtable entries
satisfy their `FAllocSpec` triples at the wrapper's alignment (the hypotheses `hA`, `hF`): the
wrapper's own code (the zero-length case, the length overflow check, the `@memset(_, undefined)` of
fresh and freed memory, the `@alignCast` check, `@returnAddress()`, the sentinel's `len + 1` on
`free`) is walked by `fsym`, and the
vtable call is the entry's triple. The `…_of` corollaries take the triples from `FAllocSpec` of
the translated `FixedBufferAllocator` entries (`impl`), for every invariant, in particular
`FBA.fallocSpec`'s.

No hand-written model of the wrappers is involved (`docs/alloc-spec.md`, §Retired claims).
-/

namespace AllocFba.Wrappers

open Zig Zig.Full Zig.Full.FAssn Gen

theorem mulWithOverflow_one (x : BitVec 64) :
    Zig.mulWithOverflow false (1#64) x = (x, 0#1) := by
  simp [Zig.mulWithOverflow, BitVec.umulOverflow, x.isLt]

variable (ctx vtp : Ptr) (I : FAllocInv)

/-! ## Allocation -/

/-- **`a.alloc(u8, n)`**: `n` undefined bytes granted by `I`'s allocator (none for `n = 0`), or
`error.OutOfMemory` and nothing. -/
theorem alloc_spec (n : BitVec 64) (hfit : I.fits n.toNat 0)
    (hA : ∀ len ra, 0 < len.toNat → I.fits len.toNat 0 →
      FTotalTriple I.own (heap_FixedBufferAllocator_alloc ctx len mem_Alignment.«1» ra)
        (I.allocPost len.toNat 0)) :
    FTotalTriple (I.own ⋆ vtR vtp fns.toList) (mem_Allocator_alloc__anon_a8254a5f2b74 ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (I.sliceResult 0 n n.toNat r ⋆ vtR vtp fns.toList)) := by
  fsym [hA, mulWithOverflow_one]

/-- **`a.alignedAlloc(u8, .@"4", n)`**: as `alloc`, with the grant aligned to 4 (the wrapper's
`@alignCast` check passes). -/
theorem alignedAlloc_spec (n : BitVec 64) (hfit : I.fits n.toNat 2)
    (hA : ∀ len ra, 0 < len.toNat → I.fits len.toNat 2 →
      FTotalTriple I.own (heap_FixedBufferAllocator_alloc ctx len mem_Alignment.«4» ra)
        (I.allocPost len.toNat 2)) :
    FTotalTriple (I.own ⋆ vtR vtp fns.toList)
      (mem_Allocator_alignedAlloc__anon_48ad47c7aa48 ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (I.sliceResult 2 n n.toNat r ⋆ vtR vtp fns.toList)) := by
  fsym [hA, mulWithOverflow_one]

/-- **`a.create(u32)`**: 4 undefined bytes aligned to 4, or `error.OutOfMemory`. -/
theorem create_spec (hfit : I.fits (4 : BitVec 64).toNat 2)
    (hA : ∀ len ra, 0 < len.toNat → I.fits len.toNat 2 →
      FTotalTriple I.own (heap_FixedBufferAllocator_alloc ctx len mem_Alignment.«4» ra)
        (I.allocPost len.toNat 2)) :
    FTotalTriple (I.own ⋆ vtR vtp fns.toList) (mem_Allocator_create__anon_8f6a81b88324 ⟨ctx, vtp⟩)
      (fun r => I.own ⋆ (I.allocResult 2 4 r ⋆ vtR vtp fns.toList)) := by
  fsym [hA]

/-! ## Release -/

/-- **`a.free(s)`** of a `[]u8`: the grant (nothing for an empty slice) goes back. -/
theorem free_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat = bs.size)
    (hF : ∀ (s : Slice) ra (bs : Array Byte), s.len.toNat = bs.size → 0 < bs.size →
      FTotalTriple (I.own ⋆ I.granted s.ptr 0 bs) (heap_FixedBufferAllocator_free ctx s ⟨0#6⟩ ra)
        (fun _ => I.own)) :
    FTotalTriple (I.own ⋆ (I.owned 0 s.ptr bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_1e60e7ef40f5 ⟨ctx, vtp⟩ s) (fun _ => I.own ⋆ vtR vtp fns.toList) := by
  fsym [fun (s : Slice) ra (h : 0 < s.len.toNat) =>
    hF s ra (Array.replicate s.len.toNat .undef) (by simp) (by simpa using h)]

/-- **`a.free(s)`** of a `[:7]u8` (from `allocSentinel`): the grant of `s.len + 1` bytes, the
sentinel included, goes back. -/
theorem freeSentinel_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat + 1 = bs.size)
    (hs : bs.size < 2 ^ 64)
    (hF : ∀ (s : Slice) ra (bs : Array Byte), s.len.toNat = bs.size → 0 < bs.size →
      FTotalTriple (I.own ⋆ I.granted s.ptr 0 bs) (heap_FixedBufferAllocator_free ctx s ⟨0#6⟩ ra)
        (fun _ => I.own)) :
    FTotalTriple (I.own ⋆ (I.granted s.ptr 0 bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_4cd0e3a7c1bf ⟨ctx, vtp⟩ s) (fun _ => I.own ⋆ vtR vtp fns.toList) := by
  fsym [fun (s : Slice) ra (h : 0 < s.len.toNat) =>
    hF s ra (Array.replicate s.len.toNat .undef) (by simp) (by simpa using h)]

/-- **`a.destroy(p)`** of a `*u32`: the 4-byte grant goes back. -/
theorem destroy_spec (p : Ptr) (bs : Array Byte) (hbs : bs.size = 4)
    (hF : ∀ (s : Slice) ra (bs : Array Byte), s.len.toNat = bs.size → 0 < bs.size →
      FTotalTriple (I.own ⋆ I.granted s.ptr 2 bs) (heap_FixedBufferAllocator_free ctx s ⟨2#6⟩ ra)
        (fun _ => I.own)) :
    FTotalTriple (I.own ⋆ (I.granted p 2 bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_7fa4accb9a56 ⟨ctx, vtp⟩ p) (fun _ => I.own ⋆ vtR vtp fns.toList) := by
  fsym [hF]

/-! ## For every allocator invariant of the translated `FixedBufferAllocator` entries -/

section OfSpec

variable {ctx vtp : Ptr} {I : FAllocInv} (h : FAllocSpec FLogic.total impl ctx I)
include h

theorem alloc_of (n : BitVec 64) (hfit : I.fits n.toNat 0) :
    FTotalTriple (I.own ⋆ vtR vtp fns.toList) (mem_Allocator_alloc__anon_a8254a5f2b74 ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (I.sliceResult 0 n n.toNat r ⋆ vtR vtp fns.toList)) :=
  alloc_spec ctx vtp I n hfit fun len ra h1 h2 => h.alloc len 0 ra h1 (by decide) h2

theorem alignedAlloc_of (n : BitVec 64) (hfit : I.fits n.toNat 2) :
    FTotalTriple (I.own ⋆ vtR vtp fns.toList)
      (mem_Allocator_alignedAlloc__anon_48ad47c7aa48 ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (I.sliceResult 2 n n.toNat r ⋆ vtR vtp fns.toList)) :=
  alignedAlloc_spec ctx vtp I n hfit fun len ra h1 h2 => h.alloc len 2 ra h1 (by decide) h2

theorem create_of (hfit : I.fits (4 : BitVec 64).toNat 2) :
    FTotalTriple (I.own ⋆ vtR vtp fns.toList) (mem_Allocator_create__anon_8f6a81b88324 ⟨ctx, vtp⟩)
      (fun r => I.own ⋆ (I.allocResult 2 4 r ⋆ vtR vtp fns.toList)) :=
  create_spec ctx vtp I hfit fun len ra h1 h2 => h.alloc len 2 ra h1 (by decide) h2

theorem free_of (s : Slice) (bs : Array Byte) (hlen : s.len.toNat = bs.size) :
    FTotalTriple (I.own ⋆ (I.owned 0 s.ptr bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_1e60e7ef40f5 ⟨ctx, vtp⟩ s) (fun _ => I.own ⋆ vtR vtp fns.toList) :=
  free_spec ctx vtp I s bs hlen fun s ra bs h1 h2 => h.free s 0 ra bs (by decide) h1 h2

theorem destroy_of (p : Ptr) (bs : Array Byte) (hbs : bs.size = 4) :
    FTotalTriple (I.own ⋆ (I.granted p 2 bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_destroy__anon_7fa4accb9a56 ⟨ctx, vtp⟩ p) (fun _ => I.own ⋆ vtR vtp fns.toList) :=
  destroy_spec ctx vtp I p bs hbs fun s ra bs h1 h2 => h.free s 2 ra bs (by decide) h1 h2

theorem freeSentinel_of (s : Slice) (bs : Array Byte) (hlen : s.len.toNat + 1 = bs.size)
    (hs : bs.size < 2 ^ 64) :
    FTotalTriple (I.own ⋆ (I.granted s.ptr 0 bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_4cd0e3a7c1bf ⟨ctx, vtp⟩ s) (fun _ => I.own ⋆ vtR vtp fns.toList) :=
  freeSentinel_spec ctx vtp I s bs hlen hs fun s ra bs h1 h2 => h.free s 0 ra bs (by decide) h1 h2

end OfSpec

/-- The contracts for the translated `FixedBufferAllocator` itself (`FBA.fallocSpec`). -/
example (ctx vtp : Ptr) (B : FBA.FBuf) (n : BitVec 64) (hfit : (FBA.finv ctx B).fits n.toNat 0) :
    FTotalTriple ((FBA.finv ctx B).own ⋆ vtR vtp fns.toList)
      (mem_Allocator_alloc__anon_a8254a5f2b74 ⟨ctx, vtp⟩ n)
      (fun r => (FBA.finv ctx B).own ⋆ ((FBA.finv ctx B).sliceResult 0 n n.toNat r ⋆
        vtR vtp fns.toList)) :=
  alloc_of (FBA.fallocSpec ctx B) n hfit

end AllocFba.Wrappers
