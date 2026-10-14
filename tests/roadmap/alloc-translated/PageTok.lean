import ZigLean.Sep.Full.Mmap

/-!
# The page allocator's invariant over full-state resources (both targets)

The token and the invariant of the translated `std.heap.PageAllocator` (`PageSpec.lean` for
x86_64-linux, `PageSpecMacos.lean` for aarch64-macos, `PageAlloc.lean` with `alloc`), for a page
size `P`. Only definitions: the proofs are the general symbolic executor `fsym`
(`docs/proof-automation.md`), which walks the generated code down to the OS mapping primitives
(`ZigLean/Sep/Full/Mmap.lean`, premise OSM-01).

A grant of `n` bytes at `p` is the start of the live range of a mapping (kind `.mapped p.off`)
that ends at the grant's page end (`S = p.off + alignUp n P`); addresses are page-aligned. The
token owns

* the rest of the grant's last page (`tail`, the bytes `[n, S)`),
* the authority over the mapping's extent with the fraction `qa` that the grant's extent share
  `q` leaves (`qa + q = 1`): `free` gets the full extent back and unmaps the whole mapping,
  `resize` cuts the mapping's tail, `remap` moves it (`mremap`),
* the knowledge of the mapping's address (`known`): `@intFromPtr` of the grant needs no byte,
* the claim on the mapping's bytes from the grant's end on (`[p.off + n, p.off + 2^64)`; minted with
  the mapping, `FTotalTriple.mmapC`): a growth in place takes the new bytes' claim from it, a
  shrink gives the cut bytes' claim back, `remap` hands the whole claim to `mremap`
  (`FTotalTriple.mremapMoveC`).

`fits n k := n + 2^k + P ≤ 2^64` (the upstream overflows of `PageAllocator.map` and `realloc`,
`docs/alloc-page.md`).
-/

namespace AllocTranslated.PageTok

open Zig Zig.Full Zig.Full.FAssn

/-- The page allocator's token of a grant of `n` bytes at `p` (module doc). The allocator charges
no fee (`FAllocInv.fee` is `emp`), so the token ignores it. -/
def ptok (P : Nat) (p : Ptr) (n _k A S : Nat) (K : BlockKind) (q _φ : Frac) : FAssn :=
  FAssn.ex fun b => FAssn.ex fun tail : Array Byte => FAssn.ex fun qa : Frac =>
    ⟪p.block = some b ∧ 0 ≤ p.off ∧ K = .mapped p.off.toNat ∧ S = p.off.toNat + alignUp n P ∧
      A % P = 0 ∧ p.off.toNat % P = 0 ∧ tail.size = alignUp n P - n ∧ n + P ≤ 2 ^ 64 ∧
      qa.add q = Frac.one ∧ 0 < q.val⟫ ⋆
    (up (regionIn (p.add n) A S K 1 tail) ⋆ (bauth b S K qa ⋆ (known b A ⋆ bclaim b (p.off.toNat + n) (p.off.toNat + claimEnd))))

/-- The page allocator's invariant for page size `P` and allocator state `own`. -/
def pinv (P : Nat) (own : FAssn) : FAllocInv where
  own := own
  tok := ptok P
  fits n k := n + 2 ^ k + P ≤ 2 ^ 64

/-- The page allocator takes every request up to `n` bytes that its arithmetic does not
overflow (`FAllocInv.FitsUpTo`; the arena's child at `n = 2 ^ 63`, `k = 3`). -/
theorem pinv_fitsUpTo {P : Nat} {own : FAssn} {n k : Nat} (h : n + 2 ^ k + P ≤ 2 ^ 64) :
    (pinv P own).FitsUpTo n k :=
  fun m hm => show m + 2 ^ k + P ≤ 2 ^ 64 by omega

end AllocTranslated.PageTok
