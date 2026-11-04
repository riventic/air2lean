import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Region

/-!
# `fsym` with the region library (`ZigLean/Sep/Full/Region.lean`)

Library-only examples of the byte operations on regions that allocator wrappers run: the store
of a sentinel item and its read-back, `@memset(_, undefined)` of a whole region, `@memcpy`
between two separate regions, the pointer order (`ptrLe`) inside a region, and the `@memcpy`
aliasing check of `dupe` (`ptrLe(src + n, dst) or ptrLe(dst + n, src)`), whose panic is
unreachable by the memory fact `MemFacts.regions_apart` (`@[fsym_facts]`, plain `fsym`). The programs are written by hand in the
shape the translator generates.
-/

namespace SepAuto.Region

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

variable (p q : Ptr) (A S A' S' : Nat) (K K' : BlockKind)

/-- Store a sentinel at item `n` and read it back. -/
def sentinel (n : BitVec 64) : MemM (BitVec 8) := do
  Zig.store 1 (p.elem 1 n) (7 : BitVec 8)
  Zig.load (BitVec 8) 1 (p.elem 1 n)

theorem sentinel_total (n : BitVec 64) (bs : Array Byte) (h : n.toNat < bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (sentinel p n)
      (fun r => ⟪r = 7#8⟫ ⋆ up (regionIn p A S K 1
        (writeBytes bs (Enc.size (BitVec 8) * n.toNat) (Enc.encode 7#8)))) := by
  unfold sentinel
  fsym

/-- The same through a formed pointer, as generated code does it (bounds check, `ptrProject`). -/
def sentinelAt (n len : BitVec 64) : MemM (BitVec 8) := do
  let q ← Zig.checkIndex len n >>= fun _ => Zig.ptrProject p (·.elem 1 n)
  Zig.store 1 q (7 : BitVec 8)
  Zig.checkSentinelIndex len n
  Zig.load (BitVec 8) 1 q

theorem sentinelAt_total (n len : BitVec 64) (bs : Array Byte) (h : n.toNat < len.toNat)
    (hl : len.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (sentinelAt p n len)
      (fun r => ⟪r = 7#8⟫ ⋆ up (regionIn p A S K 1 (writeBytes bs n.toNat (Enc.encode 7#8)))) := by
  unfold sentinelAt
  fsym

/-- Every byte of a region becomes undefined. -/
theorem memsetUndef_total (n : BitVec 64) (bs : Array Byte) (h : n.toNat = bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K 1 (Array.replicate n.toNat .undef))) := by
  fsym

/-- Defined bytes written by memset are readable as their original value. -/
theorem memset_read (bs : Array Byte) (h : bs.size = 4) (v : BitVec 8) :
    FTotalTriple (up (regionIn p A S K 1 bs))
      (do Zig.memset 1 p 4 (some v); Zig.load (BitVec 8) 1 (p.add 3))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K 1 (memsetBytes 4 (some v)))) := by
  fsym

/-- Repeated multibyte encodings are read at both the initial pointer and an item boundary. -/
theorem memset_word_reads (bs : Array Byte) (h : bs.size = 6) (v : BitVec 16) :
    FTotalTriple (up (regionIn p A S K 2 bs))
      (do
        Zig.memset 2 p 3 (some v)
        let x ← Zig.load (BitVec 16) 2 p
        let y ← Zig.load (BitVec 16) 2 (p.add 2)
        pure (x, y))
      (fun r => ⟪r = (v, v)⟫ ⋆ up (regionIn p A S K 2 (memsetBytes 3 (some v)))) := by
  fsym

/-- A read of a memset's byte past a store to another byte (`extract_writeBytes_other`). -/
theorem read_unwritten (v w : BitVec 8) :
    FTotalTriple
      (up (regionIn p A S K 1 (writeBytes (memsetBytes 8 (some v)) 7 (Enc.encode w))))
      (Zig.load (BitVec 8) 1 (p.elem 1 0#64))
      (fun r => ⟪r = v⟫ ⋆
        up (regionIn p A S K 1 (writeBytes (memsetBytes 8 (some v)) 7 (Enc.encode w)))) := by
  fsym

/-- A word item of a memset past a store to another item (`extract_memsetBytes_item`). -/
theorem read_unwritten_word (v w : BitVec 16) :
    FTotalTriple
      (up (regionIn p A S K 2 (writeBytes (memsetBytes 4 (some v)) 6 (Enc.encode w))))
      (Zig.load (BitVec 16) 2 (p.add 2))
      (fun r => ⟪r = v⟫ ⋆
        up (regionIn p A S K 2 (writeBytes (memsetBytes 4 (some v)) 6 (Enc.encode w)))) := by
  fsym

/-- A kept prefix of one byte (`replicate 1`, not a singleton, until it is decoded). -/
theorem read_kept_one (v w : BitVec 8) (bs : Array Byte) (hs : bs.size = 8)
    (hk : keepsPrefix (memsetBytes 1 (some v)) bs) :
    FTotalTriple (up (regionIn p A S K 1 (writeBytes bs 7 (Enc.encode w))))
      (Zig.load (BitVec 8) 1 (p.elem 1 0#64))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K 1 (writeBytes bs 7 (Enc.encode w)))) := by
  fsym

/-- A read of a reallocation's kept prefix, past a store to a byte after it (`keptExtract`). -/
theorem read_kept (v w : BitVec 8) (bs : Array Byte) (hs : bs.size = 8)
    (hk : keepsPrefix (memsetBytes 4 (some v)) bs) :
    FTotalTriple (up (regionIn p A S K 1 (writeBytes bs 7 (Enc.encode w))))
      (Zig.load (BitVec 8) 1 (p.elem 1 3#64))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K 1 (writeBytes bs 7 (Enc.encode w)))) := by
  fsym

/-- A whole region copied onto a separate one of the same size. -/
theorem memcpy_total (n : BitVec 64) (bd bs : Array Byte) (h1 : n.toNat = bd.size)
    (h2 : n.toNat = bs.size) :
    FTotalTriple (up (regionIn q A' S' K' 1 bs) ⋆ up (regionIn p A S K 1 bd))
      (Zig.memcpy 1 1 1 p q n n)
      (fun _ => up (regionIn p A S K 1 bs) ⋆ up (regionIn q A' S' K' 1 bs)) := by
  fsym

/-- A pointer into a region is not below the region's start. -/
theorem ptrLe_total (n : BitVec 64) (bs : Array Byte) (hpos : 0 < bs.size) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (Zig.ptrLe p (p.elem 1 n))
      (fun r => ⟪r = true⟫ ⋆ up (regionIn p A S K 1 bs)) := by
  fsym

/-- The aliasing check of a `@memcpy` between two separate regions (`dupe`). -/
def aliasCheck (n : BitVec 64) : MemM Unit := do
  let a ← Zig.ptrLe (q.elem 1 n) p
  let b ← Zig.ptrLe (p.elem 1 n) q
  if a || b then pure () else throw .panic

/-- Its panic is unreachable: two separately owned regions lie apart (a memory fact of the pair
of regions, `@[fsym_facts] MemFacts.regions_apart`, which `fsym` adds when the panic needs it). -/
theorem aliasCheck_total (n : BitVec 64) (bd bs : Array Byte) (h1 : n.toNat = bd.size)
    (h2 : n.toNat = bs.size) (hpos : 0 < n.toNat) :
    FTotalTriple (up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) (aliasCheck p q n)
      (fun _ => up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) := by
  unfold aliasCheck
  fsym

/-- The memory fact by hand, in any logic (`MemFacts.pre`). -/
theorem aliasCheck_pre (n : BitVec 64) (bd bs : Array Byte) (h1 : n.toNat = bd.size)
    (h2 : n.toNat = bs.size) (hpos : 0 < n.toNat) :
    FTotalTriple (up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) (aliasCheck p q n)
      (fun _ => up (regionIn p A S K 1 bd) ⋆ up (regionIn q A' S' K' 1 bs)) := by
  refine MemFacts.pre FLogic.total MemFacts.regions_apart fun _ => ?_
  unfold aliasCheck
  fsym

set_option linter.unusedVariables false

/-- Rejected: a region checked against itself overlaps, so the panic is reachable (the facts of
a pair are about two separately owned atoms). -/
example (n : BitVec 64) (bd : Array Byte) (h1 : n.toNat = bd.size) (hpos : 0 < n.toNat) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bd)) (aliasCheck p p n)
        (fun _ => up (regionIn p A S K 1 bd)) := by
      unfold aliasCheck
      fsym
  trivial

/-- A copy needs the source: one region alone is not copied onto itself. -/
example (n : BitVec 64) (bd : Array Byte) (h1 : n.toNat = bd.size) (hpos : 0 < n.toNat) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bd)) (Zig.memcpy 1 1 1 p p n n)
        (fun _ => up (regionIn p A S K 1 bd)) := by
      fsym
  trivial

/-- A read-back is the stored value, not another. -/
example (n : BitVec 64) (bs : Array Byte) (h : n.toNat < bs.size) : True := by
  fail_if_success
    have : FTotalTriple (up (regionIn p A S K 1 bs)) (sentinel p n)
        (fun r => ⟪r = 8#8⟫ ⋆ up (regionIn p A S K 1
          (writeBytes bs (Enc.size (BitVec 8) * n.toNat) (Enc.encode 7#8)))) := by
      unfold sentinel
      fsym
  trivial

/-- A grant: its bytes, as a region (the child allocator's `free` precondition). -/
def Granted (p : Ptr) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K =>
    up (regionIn p A S K 8 bs) ⋆ ⟪bs.size = 40⟫

/-- An allocator's `free` (a stand-in that keeps what it is given). -/
@[irreducible] def giveBack (_p : Ptr) : MemM Unit := pure ()

theorem giveBack_spec {p : Ptr} {bs : Array Byte} :
    FTotalTriple (Granted p bs) (giveBack p) (fun _ => Granted p bs) := by
  unfold giveBack; exact FTotalTriple.ret (Q := fun _ => _) ()

set_option maxHeartbeats 800000 in
/-- **A node given back in a large state** (ledger #60, the arena's `free` of a node among the
other nodes): its words viewed and joined into the grant, next to six regions of three other
blocks. Each pair of regions is apart (`regions_apart`, a disjunction): a planner's probe that
the plain facts refute does not search their cases, the facts of all pairs are added at once,
and pointers whose offsets differ are not compared by a tactic. Over 4M heartbeats before,
about 575k now. -/
theorem free_large (r u : Ptr) (b : BlockId) (sz ei : BitVec 64) (nxt : Option Ptr)
    (buf c1 c2 c3 c4 c5 c6 : Array Byte) (hb : p.block = some b) (hal : (A + p.off.toNat) % 8 = 0)
    (hbuf : buf.size = 16) (h1 : c1.size = 16) (h2 : c2.size = 16) (h3 : c3.size = 16)
    (h4 : c4.size = 24) (h5 : c5.size = 24) (h6 : c6.size = 24) :
    FTotalTriple (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 (Enc.encode nxt)) ⋆
        up (regionIn (p.add 24) A S K 1 buf) ⋆ up (regionIn q A S K 8 c1) ⋆ up (regionIn r A S K 8 c2) ⋆
        up (regionIn u A S K 8 c3) ⋆ up (regionIn (q.add 24) A S K 8 c4) ⋆
        up (regionIn (r.add 24) A S K 8 c5) ⋆ up (regionIn (u.add 24) A S K 8 c6))
      (giveBack p) (fun _ => (FAssn.ex fun bs => Granted p bs) ⋆ up (regionIn q A S K 8 c1) ⋆
        up (regionIn r A S K 8 c2) ⋆ up (regionIn u A S K 8 c3) ⋆ up (regionIn (q.add 24) A S K 8 c4) ⋆
        up (regionIn (r.add 24) A S K 8 c5) ⋆ up (regionIn (u.add 24) A S K 8 c6)) := by
  fsym [giveBack_spec]

/-- A grant of `n` bytes. -/
def GrantedN (p : Ptr) (n : Nat) (bs : Array Byte) : FAssn :=
  FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K =>
    up (regionIn p A S K 8 bs) ⋆ ⟪bs.size = n⟫

theorem giveBackN_spec {p : Ptr} {n : Nat} {bs : Array Byte} :
    FTotalTriple (GrantedN p n bs) (giveBack p) (fun _ => GrantedN p n bs) := by
  unfold giveBack; exact FTotalTriple.ret (Q := fun _ => _) ()

set_option maxHeartbeats 800000 in
/-- **A node of a size that only its facts bound** (`24 ≤ n`, the arena's nodes) given back in
the large state of `free_large`: the planner joins its words and its buffer into the grant. Its
probes of the grant's size against the bytes joined so far (`n = 24` against the header, which
the facts allow) leave out the case facts, the disjointness of the other regions (ledger
#carve-size-probes): their failed search did not end within any budget. -/
theorem free_large_sized (r u : Ptr) (b : BlockId) (sz ei : BitVec 64) (nxt : Option Ptr) (n : Nat)
    (buf c1 c2 c3 c4 c5 c6 : Array Byte) (hb : p.block = some b) (hal : (A + p.off.toNat) % 8 = 0)
    (hn : 24 ≤ n) (hbuf : buf.size = n - 24) (h1 : c1.size = 16) (h2 : c2.size = 16)
    (h3 : c3.size = 16) (h4 : c4.size = 24) (h5 : c5.size = 24) (h6 : c6.size = 24) :
    FTotalTriple (apts p sz ⋆ apts (p.add 8) ei ⋆ up (regionIn (p.add 16) A S K 8 (Enc.encode nxt)) ⋆
        up (regionIn (p.add 24) A S K 1 buf) ⋆ up (regionIn q A S K 8 c1) ⋆ up (regionIn r A S K 8 c2) ⋆
        up (regionIn u A S K 8 c3) ⋆ up (regionIn (q.add 24) A S K 8 c4) ⋆
        up (regionIn (r.add 24) A S K 8 c5) ⋆ up (regionIn (u.add 24) A S K 8 c6))
      (giveBack p) (fun _ => (FAssn.ex fun bs => GrantedN p n bs) ⋆ up (regionIn q A S K 8 c1) ⋆
        up (regionIn r A S K 8 c2) ⋆ up (regionIn u A S K 8 c3) ⋆ up (regionIn (q.add 24) A S K 8 c4) ⋆
        up (regionIn (r.add 24) A S K 8 c5) ⋆ up (regionIn (u.add 24) A S K 8 c6)) := by
  fsym [giveBackN_spec]

/-- A grant behind a definition: a token that names its size, and its bytes. -/
def TokGrant (T : Nat → FAssn) (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) : FAssn :=
  T bs.size ⋆ up (regionIn p A S K 1 bs)

/-- **A token does not fix the bytes of the region whose size it names** (`abstractMeasures`):
the state's token `T old.size` names an array of the grant's size, not the bytes its region holds
(`cur`, as after a write). The rule's bytes behind `TokGrant` come from the region, carved at the
token's size, and the token matches up to arithmetic. -/
theorem hidden_bytes_from_region (T : Nat → FAssn) (s : Slice) (old cur : Array Byte) (n : Nat)
    (c : MemM Unit) (hn : s.len.toNat = n) (hold : old.size = n) (hcur : cur.size = n)
    (rule : ∀ bs : Array Byte, s.len.toNat = bs.size →
      FTotalTriple (TokGrant T s.ptr A S K bs) c (fun _ => TokGrant T s.ptr A S K bs)) :
    FTotalTriple (T old.size ⋆ up (regionIn s.ptr A S K 1 cur)) c
      (fun _ => TokGrant T s.ptr A S K cur) := by
  fsym [rule]

/-- The same without a size premise of the rule: the token alone defers the bytes. -/
theorem hidden_bytes_no_premise (T : Nat → FAssn) (p : Ptr) (old cur : Array Byte) (n : Nat)
    (c : MemM Unit) (hold : old.size = n) (hcur : cur.size = n)
    (rule : ∀ bs : Array Byte,
      FTotalTriple (TokGrant T p A S K bs) c (fun _ => TokGrant T p A S K bs)) :
    FTotalTriple (T old.size ⋆ up (regionIn p A S K 1 cur)) c
      (fun _ => TokGrant T p A S K cur) := by
  fsym [rule]

/-- A grant whose token names its size in a field of an argument, as a ledger fragment keys a
grant by `(p, bs.size, …)`. -/
def TupGrant (T : Ptr × Nat → FAssn) (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) :
    FAssn :=
  T (p, bs.size) ⋆ up (regionIn p A S K 1 bs)

/-- The same with the size in a tuple that the token takes. -/
theorem hidden_bytes_in_tuple (T : Ptr × Nat → FAssn) (p : Ptr) (old cur : Array Byte) (n : Nat)
    (c : MemM Unit) (hold : old.size = n) (hcur : cur.size = n)
    (rule : ∀ bs : Array Byte,
      FTotalTriple (TupGrant T p A S K bs) c (fun _ => TupGrant T p A S K bs)) :
    FTotalTriple (T (p, old.size) ⋆ up (regionIn p A S K 1 cur)) c
      (fun _ => TupGrant T p A S K cur) := by
  fsym [rule]

/-- A grant's key, a structure with the size as a field. -/
structure GrantKey where
  ptr : Ptr
  len : Nat

/-- A grant whose token takes a structure with its size as a field. -/
def KeyGrant (T : GrantKey → FAssn) (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) :
    FAssn :=
  T ⟨p, bs.size⟩ ⋆ up (regionIn p A S K 1 bs)

/-- The same with the size in a field of a structure that the token takes. -/
theorem hidden_bytes_in_field (T : GrantKey → FAssn) (p : Ptr) (old cur : Array Byte) (n : Nat)
    (c : MemM Unit) (hold : old.size = n) (hcur : cur.size = n)
    (rule : ∀ bs : Array Byte,
      FTotalTriple (KeyGrant T p A S K bs) c (fun _ => KeyGrant T p A S K bs)) :
    FTotalTriple (T ⟨p, old.size⟩ ⋆ up (regionIn p A S K 1 cur)) c
      (fun _ => KeyGrant T p A S K cur) := by
  fsym [rule]

/-- A grant whose token names its size under arithmetic (a header's length). -/
def HdrGrant (T : Nat → FAssn) (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) : FAssn :=
  T (bs.size + 8) ⋆ up (regionIn p A S K 1 bs)

/-- The same with the size under arithmetic, not a constructor. -/
theorem hidden_bytes_in_sum (T : Nat → FAssn) (p : Ptr) (old cur : Array Byte) (n : Nat)
    (c : MemM Unit) (hold : old.size = n) (hcur : cur.size = n)
    (rule : ∀ bs : Array Byte,
      FTotalTriple (HdrGrant T p A S K bs) c (fun _ => HdrGrant T p A S K bs)) :
    FTotalTriple (T (old.size + 8) ⋆ up (regionIn p A S K 1 cur)) c
      (fun _ => HdrGrant T p A S K cur) := by
  fsym [rule]

/-- Two grants under one token: the first one's bytes a size the rule demands (the token waits
for them), the second one's named by the token alone. -/
def TwoGrant (T : Nat → Nat → FAssn) (p q : Ptr) (A S : Nat) (K : BlockKind) (bs cs : Array Byte) :
    FAssn :=
  T bs.size cs.size ⋆ (up (regionIn p A S K 1 bs) ⋆ up (regionIn q A S K 1 cs))

/-- The token that waits for demanded bytes does not fix the other grant's bytes either. -/
theorem hidden_bytes_waiting (T : Nat → Nat → FAssn) (p q : Ptr) (b0 old cur : Array Byte)
    (n m : Nat) (c : MemM Unit) (hb0 : b0.size = n) (hold : old.size = m) (hcur : cur.size = m)
    (rule : ∀ bs cs : Array Byte, bs.size = n →
      FTotalTriple (TwoGrant T p q A S K bs cs) c (fun _ => TwoGrant T p q A S K bs cs)) :
    FTotalTriple (T b0.size old.size ⋆ (up (regionIn p A S K 1 b0) ⋆ up (regionIn q A S K 1 cur))) c
      (fun _ => TwoGrant T p q A S K b0 cur) := by
  fsym [rule]

/-- A measure of an unknown that nothing else determines: the final match still takes the
state's array (any array of that size is a witness). -/
theorem measure_only (T : Nat → FAssn) (old : Array Byte) (c : MemM Unit)
    (rule : ∀ bs : Array Byte, FTotalTriple (T bs.size) c (fun _ => T bs.size)) :
    FTotalTriple (T old.size) c (fun _ => T old.size) := by
  fsym [rule]

/-- A store and a load through a literal pointer (generated code's address of a global's item,
evaluated) into a region of the state: the walk restates the pointer from the region's
(`rebaseLitPtr?`). -/
theorem literal_store_load (bs : Array Byte) (hs : bs.size = 4) (x : BitVec 8) :
    FTotalTriple (up (regionIn ((⟨some 0, 0⟩ : Ptr).add 12) A 16 .global 1 bs))
      (do Zig.store 1 (⟨some 0, 15⟩ : Ptr) x; Zig.load (BitVec 8) 1 (⟨some 0, 15⟩ : Ptr))
      (fun r => ⟪r = x⟫ ⋆ FAssn.ex fun t : Array Byte =>
        up (regionIn ((⟨some 0, 0⟩ : Ptr).add 12) A 16 .global 1 t)) := by
  fsym

/-- The same into a region that starts at an offset of a pointer the facts place. -/
theorem literal_store_offset (p : Ptr) (hb : p.block = some 0) (ho : p.off = 0)
    (bs cs : Array Byte) (hs : bs.size = 16) (hc : cs.size = 4) (x : BitVec 8) :
    FTotalTriple (up (regionIn (p.add (bs.extract 0 12).size) A 16 .global 1 cs))
      (Zig.store 1 (⟨some 0, 15⟩ : Ptr) x)
      (fun _ => up (regionIn (p.add (bs.extract 0 12).size) A 16 .global 1
        (writeBytes cs 3 (Enc.encode x)))) := by
  fsym

end SepAuto.Region
