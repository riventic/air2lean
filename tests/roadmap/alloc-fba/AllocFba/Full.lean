import AllocFba.Fba
import ZigLean.Sep.Full.AutoClaims
import ZigLean.Sep.Full.AutoThread

/-!
# The translated `FixedBufferAllocator` satisfies the full-state `FAllocSpec`

`FBA.fallocSpec`: the four vtable entries of the translated `FixedBufferAllocator` (`Gen.lean`)
satisfy `FAllocSpec FLogic.total impl ctx (finv ctx B)` for every allocator struct `ctx` and every
buffer `B`, proved natively in the full-state logic (`ZigLean/Sep/Full`) from the generated code.
The legacy proof (`Fba.lean`) is not lifted: its invariant owns a pin byte of the buffer's block,
because there a cell is the only source of the block's size. Here the size comes from the
buffer's **extent share** (`docs/sep-full-state.md` §Block extents):

* The invariant `fown ctx B` owns the struct (`end_index = e` and the buffer slice, as two typed
  words), the free tail `[e, cap)` of the buffer, junk (padding and the bytes of non-last frees),
  the knowledge of the addresses of the buffer's and the struct's blocks, and a share
  `bshare b q (ptr.off + cap)` of the buffer block's extent: the block reaches the buffer's end
  even when every byte of the buffer is lent out, so `buffer.ptr + end_index` is formed
  (`ptrProject`, MM-3). A share, not the full extent: the buffer may itself lie in a grant of
  another allocator.
* The invariant holds the **claim** on the free tail `[e, cap)` (`fclaim`, `docs/sep-full-state.md`
  §Byte-range claims; the buffer's creator minted it): a grant gets the claim on its bytes carved
  from it, a `free` or shrink of the last grant joins it back, other frees drop it (like their
  bytes, which become junk). The claims planner of `fsym` (`AutoClaims.lean`) does the carving.
* A grant gets half of the invariant's share, weakened to its own end (`EUpd.weaken`), as the
  stronger `FAllocSpec` requires; `free` and `resize` take it back (`EUpd.join` at the buffer's
  bound). The token says that the grant lies in the buffer, with the buffer's address and its
  cells' labels `S`, `K` (a full-state cell's size is a label: `FMatch` ignores it).

`fits n k := cap + 2^k + n ≤ 2^64`, as in the legacy proof.

**The proofs are the invariant and the general symbolic executor `fsym`**
(`ZigLean/Sep/Full/Auto.lean`, `docs/proof-automation.md`): each entry is `fsym` on its
`FAllocSpec` field as a thread triple (`fthread_*`; the sequential field is its reading in one
thread), which walks the generated code with the library's step rules and plans the
returns (carving and joining regions, raising and weakening shares, `Junk`). Nothing here is
specific to the FixedBufferAllocator beyond the definitions of the invariant. `resize` is the
refined field (`FAllocInv.held`/`relBytes`/`rresizePost`); `remap` keeps the whole-region form.
-/

namespace AllocFba

open Zig Zig.Full Zig.Full.FAssn Gen

namespace FBA

/-! ## The invariant -/

/-- The buffer: its pointer and length, the address of its block, the size and kind labels of
its region cells, and the address of the struct's block. -/
structure FBuf where
  ptr : Ptr
  cap : Nat
  A : Nat
  S : Nat
  K : BlockKind
  cA : Nat

/-- The struct word `end_index = e`. -/
def wEnd (ctx : Ptr) (e : Nat) : FAssn := up (pts ctx 8 (BitVec.ofNat 64 e))

/-- The struct's buffer slice. -/
def wBuf (ctx : Ptr) (B : FBuf) : FAssn := up (pts (ctx.add 8) 8 (⟨B.ptr, BitVec.ofNat 64 B.cap⟩ : Slice))

/-- The buffer's bound: its block reaches the buffer's end. -/
def bnd (B : FBuf) : Nat := B.ptr.off.toNat + B.cap

def FOk (ctx : Ptr) (B : FBuf) (e : Nat) (tail : Array Byte) : Prop :=
  e ≤ B.cap ∧ tail.size = B.cap - e ∧ B.A + B.ptr.off.toNat + B.cap < 2 ^ 64 ∧ 0 ≤ B.ptr.off ∧
    (B.cA + ctx.off.toNat) % 8 = 0 ∧ 0 ≤ ctx.off

/-- The parts of the invariant that do not depend on `end_index`: the buffer slice, the
knowledge of the two blocks' addresses, the extent share of the buffer's block, junk. -/
def fparts (ctx : Ptr) (B : FBuf) (q : Frac) (b cb : BlockId) : FAssn :=
  wBuf ctx B ⋆ (known cb B.cA ⋆ (known b B.A ⋆ (bshare b q (bnd B) ⋆ Junk)))

/-- The struct with `end_index = e`, and the other parts. -/
def fst (ctx : Ptr) (B : FBuf) (e : Nat) (q : Frac) (b cb : BlockId) : FAssn :=
  wEnd ctx e ⋆ fparts ctx B q b cb

/-- The free tail `[e, cap)` of the buffer. -/
def ftail (B : FBuf) (e : Nat) (tail : Array Byte) : FAssn :=
  up (regionIn (B.ptr.add (e : Int)) B.A B.S B.K 1 tail)

/-- The claim on the free tail: a grant carved from the tail gets the claim on its bytes. -/
def fclaim (B : FBuf) (e : Nat) (b : BlockId) : FAssn :=
  bclaim b (B.ptr.off.toNat + e) (bnd B)

/-- The invariant's parts, with the block ids `b` (buffer) and `cb` (struct) named. -/
def fbody (ctx : Ptr) (B : FBuf) (e : Nat) (tail : Array Byte) (q : Frac) (b cb : BlockId) : FAssn :=
  fst ctx B e q b cb ⋆ (ftail B e tail ⋆ fclaim B e b)

def fown (ctx : Ptr) (B : FBuf) : FAssn :=
  FAssn.ex fun e => FAssn.ex fun tail => FAssn.ex fun q => FAssn.ex fun b => FAssn.ex fun cb =>
    ⟪FOk ctx B e tail ∧ B.ptr.block = some b ∧ ctx.block = some cb⟫ ⋆ fbody ctx B e tail q b cb

/-- The allocator issued the region: it lies in the buffer, with the buffer's address and labels.
The allocator charges no fee (`FAllocInv.fee` is `emp`), so the token ignores it. -/
def ftok (B : FBuf) (p : Ptr) (n _k A S : Nat) (K : BlockKind) (_q _φ : Frac) : FAssn :=
  ⟪p.block = B.ptr.block ∧ A = B.A ∧ S = B.S ∧ K = B.K ∧ B.ptr.off ≤ p.off ∧
    p.off + n ≤ B.ptr.off + B.cap⟫

def ffits (B : FBuf) (n k : Nat) : Prop := B.cap + 2 ^ k + n ≤ 2 ^ 64

def finv (ctx : Ptr) (B : FBuf) : FAllocInv where
  own := fown ctx B
  tok := ftok B
  fits := ffits B

/-- A fixed buffer takes every request up to `n` bytes when its capacity leaves room for them
(`FAllocInv.FitsUpTo`; the arena's child at `n = 2 ^ 63`, `k = 3`: `cap ≤ 2 ^ 63 - 8`). -/
theorem finv_fitsUpTo {ctx : Ptr} {B : FBuf} {n k : Nat} (h : B.cap + 2 ^ k + n ≤ 2 ^ 64) :
    (finv ctx B).FitsUpTo n k :=
  fun m hm => show B.cap + 2 ^ k + m ≤ 2 ^ 64 by omega

/-! ## The entries

Each entry is proved once, as a **total thread triple** (`FTTotalTriple`): each step of its code
is local to the thread that owns the invariant and the grant (`ThreadLocal`, discharged by
`fsym`'s locality providers), so a thread may call it while other threads run
(`CAllocSpec.ofRaw`, `ZigLean/Sep/Full/AllocBridge.lean`). The sequential triples are their
readings in one thread (`FTTotalTriple.toFTotalTriple`). -/

theorem fthread_alloc (ctx : Ptr) (B : FBuf) (n : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hn : 0 < n.toNat) (hk : k < 64) (hfit : (finv ctx B).fits n.toNat k) :
    FTTotalTriple ((finv ctx B).own ⋆ (finv ctx B).fee φ) (impl.alloc ctx n k ra)
      ((finv ctx B).allocPost n.toNat k φ) := by
  fsym

theorem fthread_resize (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat)
    (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (finv ctx B).fits n.toNat k) (hpos : 0 < s.len.toNat) :
    FTTotalTriple ((finv ctx B).own ⋆ ((finv ctx B).held s.ptr s.len.toNat k A S K q q' φ ⋆
      (finv ctx B).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (impl.resize ctx s k n ra)
      ((finv ctx B).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  fsym

theorem fthread_remap (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac)
    (bs : Array Byte) (hk : k < 64) (hn : 0 < n.toNat) (hfit : (finv ctx B).fits n.toNat k)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k φ bs) (impl.remap ctx s k n ra)
      ((finv ctx B).remapPost s.ptr k φ bs n.toNat) := by
  fsym

theorem fthread_free (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k φ bs) (impl.free ctx s k ra)
      (fun _ => (finv ctx B).own ⋆ (finv ctx B).fee φ) := by
  fsym

/-- **The translated `FixedBufferAllocator` satisfies the full-state allocator specification**,
in the total logic, for every allocator struct `ctx` and every buffer `B`: its entries' thread
triples read in one thread. -/
theorem fallocSpec (ctx : Ptr) (B : FBuf) : FAllocSpec FLogic.total impl ctx (finv ctx B) where
  alloc len k ra φ hl hk hfit := (fthread_alloc ctx B len k ra φ hl hk hfit).toFTotalTriple
  resize s k n ra A S K q q' φ tl hk hn hfit hpos _ _ :=
    (fthread_resize ctx B s k n ra A S K q q' φ tl hk hn hfit hpos).toFTotalTriple
  remap s k n ra φ bs hk hn hfit hlen hpos :=
    (fthread_remap ctx B s k n ra φ bs hk hn hfit hlen hpos).toFTotalTriple
  free s k ra φ bs _ hlen hpos := (fthread_free ctx B s k ra φ bs hlen hpos).toFTotalTriple

end FBA

end AllocFba
