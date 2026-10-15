import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Arr
import ZigLean.Sep.Full.Mmap
import ZigLean.Sep.Full.ThreadLoop
import ZigLean.Sep.Full.Tick

/-!
# `fsym` in a thread (`ZigLean/Sep/Full/AutoThread.lean`)

A thread's step (`FTTotalTriple`, `FTTriple`) is walked as a sequential program: each sequential
`@[fsym]` rule applies with the locality of its command (`FTTotalTriple.ofSeq` and a
`ThreadLocal` side goal, proved by the locality providers from the bytes the precondition
owns). The thread rules below were hand-written copies of their sequential rules (`Full/Ops`,
`Full/Region`, `Full/Typed`, `Full/Arr`); each is now one `fsym` call, with the sequential rule
named where it is not `@[fsym]`. Programs of several commands walk with a frame in a thread
logic, total and partial, and a command whose bytes the precondition does not own gets no
thread rule (fail closed). A loop in a thread is a thread loop rule (`Full/ThreadLoop.lean`),
its body walked in the thread logic.
-/

namespace SepAuto.Threads

open Zig Zig.Full Zig.Full.FAssn

section Ops

variable {T : Type} [Enc T] {q : Ptr} {a k al : Nat} {A S : Nat} {K' : BlockKind} {bs : Array Byte}

/-- **Load** of a typed value (`pts`) in a thread. -/
theorem load {v : T} (hn : 0 < Enc.size T) :
    FTTotalTriple (up (pts q a v)) (Zig.load T a q) (fun x => ⟪x = v⟫ ⋆ up (pts q a v)) := by
  fsym

/-- **Store** of a typed value (`pts`) in a thread. -/
theorem store [LawfulEnc T] {v : T} (hn : 0 < Enc.size T) (w : T) :
    FTTotalTriple (up (pts q a v)) (Zig.store a q w) (fun _ => up (pts q a w)) := by
  fsym

theorem loadBytes_bytesAt {n : Nat} (hn : 0 < n) (hk : k + n ≤ bs.size)
    (ha : (A + q.off.toNat + k) % al = 0) :
    FTTotalTriple (up (bytesAt q A S K' bs)) (Zig.loadBytes (q.add k) n al)
      (fun x => ⟪x = bs.extract k (k + n)⟫ ⋆ up (bytesAt q A S K' bs)) := by
  fsym [FTotalTriple.loadBytes_bytesAt hn hk ha]

theorem store_bytesAt (w : T) (hn : 0 < (Enc.encode w).size)
    (hk : k + (Enc.encode w).size ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hK : K' ≠ .constGlobal) :
    FTTotalTriple (up (bytesAt q A S K' bs)) (Zig.store al (q.add k) w)
      (fun _ => up (bytesAt q A S K' (writeBytes bs k (Enc.encode w)))) := by
  fsym [FTotalTriple.store_bytesAt w hn hk ha hK]

theorem memset_bytesAt {n : BitVec 64} {v : Option T}
    (hsz : (memsetBytes n.toNat v).size = n.toNat * Enc.size T)
    (hk : k + n.toNat * Enc.size T ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hK : K' ≠ .constGlobal) :
    FTTotalTriple (up (bytesAt q A S K' bs)) (Zig.memset al (q.add k) n v)
      (fun _ => up (bytesAt q A S K' (writeBytes bs k (memsetBytes n.toNat v)))) := by
  fsym [FTotalTriple.memset_bytesAt hsz hk ha hK]

theorem memmove_bytesAt {d s : Ptr} {A' S' sz da sa j : Nat} {K'' : BlockKind}
    {bd bsrc : Array Byte} {n : BitVec 64} (hkd : k + n.toNat * sz ≤ bd.size)
    (hjs : j + n.toNat * sz ≤ bsrc.size) (had : (A + d.off.toNat + k) % da = 0)
    (has : (A' + s.off.toNat + j) % sa = 0) (hK : K' ≠ .constGlobal) :
    FTTotalTriple (up (bytesAt d A S K' bd) ⋆ up (bytesAt s A' S' K'' bsrc))
      (Zig.memmove sz da sa (d.add k) (s.add j) n)
      (fun _ => up (bytesAt d A S K' (writeBytes bd k (bsrc.extract j (j + n.toNat * sz)))) ⋆
        up (bytesAt s A' S' K'' bsrc)) := by
  fsym [FTotalTriple.memmove_bytesAt hkd hjs had has hK]

/-- **A slice's bounds check** in a thread: `checkSliceEnd` has no locality lemma of its own; its
definition (`if … then pure () else throw …`) is local (`ThreadLocal.ite`, `pure`, `throw`). -/
theorem sliceEnd {v : T} (srcLen start len : BitVec 64) (h : start.toNat + len.toNat ≤ srcLen.toNat) :
    FTTotalTriple (up (pts q a v)) (checkSliceEnd srcLen start len 0) (fun _ => up (pts q a v)) := by
  fsym

/-- **An index check** in a thread, as `sliceEnd`. -/
theorem index {v : T} (len i : BitVec 64) (h : i.toNat < len.toNat) :
    FTTotalTriple (up (pts q a v)) (checkIndex len i) (fun _ => up (pts q a v)) := by
  fsym

/-- **`@memcpy` of no items** in a thread: its bytes are none, owned by any precondition
(`OwnsPtr.of_zero`). -/
theorem memcpy_none (d s : Ptr) (n : BitVec 64) (hn : n.toNat = 0)
    (hr : FTotalTriple emp (Zig.memcpy 8 1 1 d s n n) (fun _ => emp)) :
    FTTotalTriple emp (Zig.memcpy 8 1 1 d s n n) (fun _ => emp) := by
  fsym [hr]

/-- **The pointer to item `i` of no items** in a thread (lists' `.empty` buffer, known only by its
block's address): pointer formation is local whatever the precondition owns
(`ThreadLocal.ptrProject`), so the sequential rule applies. -/
theorem elem_none (p : Ptr) (b : BlockId) (A : Nat) (i : BitVec 64) (hi : i.toNat = 0)
    (hr : ∀ P : FAssn, FTotalTriple P (ptrProject p (·.elem 4 i)) (fun q => ⟪q = p⟫ ⋆ P)) :
    FTTotalTriple (known b A) (ptrProject p (·.elem 4 i)) (fun q => ⟪q = p⟫ ⋆ known b A) := by
  fsym [hr]

end Ops

section Region

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

theorem memsetUndef {n : BitVec 64} (hn : n.toNat = bs.size) :
    FTTotalTriple (up (regionIn p A S K a bs)) (Zig.memset (α := BitVec 8) 1 p n none)
      (fun _ => up (regionIn p A S K a (Array.replicate n.toNat .undef))) := by
  fsym

theorem regionStore {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (ho : Enc.size T * i.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ Enc.size T * i.toNat) :
    FTTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.elem (Enc.size T) i) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs (Enc.size T * i.toNat) (Enc.encode v)))) := by
  fsym

theorem regionLoadWritten {T : Type} [Enc T] [LawfulEnc T] {i : BitVec 64} {al o : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hoi : Enc.size T * i.toNat = o)
    (hal : al ∣ a) (halo : al ∣ o) :
    FTTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.elem (Enc.size T) i))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  fsym

theorem regionStoreAdd {T : Type} [Enc T] [LawfulEnc T] {k : Int} {al : Nat} (v : T)
    (hpos : 0 < Enc.size T) (h0 : 0 ≤ k) (ho : k.toNat + Enc.size T ≤ bs.size) (hal : al ∣ a)
    (halo : al ∣ k.toNat) :
    FTTotalTriple (up (regionIn p A S K a bs)) (Zig.store al (p.add k) v)
      (fun _ => up (regionIn p A S K a (writeBytes bs k.toNat (Enc.encode v)))) := by
  fsym

theorem regionLoadWrittenAdd {T : Type} [Enc T] [LawfulEnc T] {k : Int} {al o : Nat} {v : T}
    (hpos : 0 < Enc.size T) (ho : o + Enc.size T ≤ bs.size) (hko : k = (o : Int))
    (hal : al ∣ a) (halo : al ∣ o) :
    FTTotalTriple (up (regionIn p A S K a (writeBytes bs o (Enc.encode v))))
      (Zig.load T al (p.add k))
      (fun r => ⟪r = v⟫ ⋆ up (regionIn p A S K a (writeBytes bs o (Enc.encode v)))) := by
  fsym

theorem memcpyRegions {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' sz da sa : Nat}
    {bd bsrc : Array Byte} {n m : BitVec 64} (hm : n.toNat = m.toNat) (hnd : n.toNat * sz ≤ bd.size)
    (hns : n.toNat * sz ≤ bsrc.size) (hda : da ∣ a) (hsa : sa ∣ a') :
    FTTotalTriple (up (regionIn d A S K a bd) ⋆ up (regionIn s A' S' K' a' bsrc))
      (Zig.memcpy sz da sa d s n m)
      (fun _ => up (regionIn d A S K a (writeBytes bd 0 (bsrc.extract 0 (n.toNat * sz)))) ⋆
        up (regionIn s A' S' K' a' bsrc)) := by
  fsym [FTotalTriple.memcpyRegions hm hnd hns hda hsa]

theorem memcpyRegionsAll {d s : Ptr} {A' S' : Nat} {K' : BlockKind} {a' sz da sa : Nat}
    {bd bsrc : Array Byte} {n m : BitVec 64} (hm : n.toNat = m.toNat) (hnd : n.toNat * sz = bd.size)
    (hns : n.toNat * sz = bsrc.size) (hda : da ∣ a) (hsa : sa ∣ a') :
    FTTotalTriple (up (regionIn d A S K a bd) ⋆ up (regionIn s A' S' K' a' bsrc))
      (Zig.memcpy sz da sa d s n m)
      (fun _ => up (regionIn d A S K a bsrc) ⋆ up (regionIn s A' S' K' a' bsrc)) := by
  fsym [FTotalTriple.memcpyRegionsAll hm hnd hns hda hsa]

end Region

section Typed

variable {T U : Type} [Enc T] [Enc U] {q : Ptr} {a b o : Nat} {bs : Array Byte}

theorem region_loadAt {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a) (ho : b ∣ o)
    (hfit : o + Enc.size U ≤ bs.size) (hv : Enc.decode (bs.extract o (o + Enc.size U)) = pure v) :
    FTTotalTriple (up (Zig.region q a bs)) (Zig.load U b (q.add o))
      (fun x => ⟪x = v⟫ ⋆ up (Zig.region q a bs)) := by
  fsym [FTotalTriple.region_loadAt hn hb ho hfit hv]

theorem region_storeAt [LawfulEnc U] (w : U) (hn : 0 < Enc.size U) (hb : b ∣ a)
    (ho : b ∣ o) (hfit : o + Enc.size U ≤ bs.size) :
    FTTotalTriple (up (Zig.region q a bs)) (Zig.store b (q.add o) w)
      (fun _ => up (Zig.region q a (writeBytes bs o (Enc.encode w)))) := by
  fsym [FTotalTriple.region_storeAt w hn hb ho hfit]

theorem region_load {k : Int} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ bs.size)
    (hv : Enc.decode (bs.extract k.toNat (k.toNat + Enc.size U)) = pure v) :
    FTTotalTriple (up (Zig.region q a bs)) (Zig.load U b (q.add k))
      (fun x => ⟪x = v⟫ ⋆ up (Zig.region q a bs)) := by
  fsym [FTotalTriple.region_load hn hb h0 ho hfit hv]

theorem region_store [LawfulEnc U] {k : Int} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ bs.size) :
    FTTotalTriple (up (Zig.region q a bs)) (Zig.store b (q.add k) w)
      (fun _ => up (Zig.region q a (writeBytes bs k.toNat (Enc.encode w)))) := by
  fsym

theorem region_load0 {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (hfit : Enc.size U ≤ bs.size) (hv : Enc.decode (bs.extract 0 (Enc.size U)) = pure v) :
    FTTotalTriple (up (Zig.region q a bs)) (Zig.load U b q) (fun x => ⟪x = v⟫ ⋆ up (Zig.region q a bs)) := by
  fsym [FTotalTriple.region_load0 hn hb hfit hv]

theorem region_store0 [LawfulEnc U] (w : U) (hn : 0 < Enc.size U) (hb : b ∣ a)
    (hfit : Enc.size U ≤ bs.size) :
    FTTotalTriple (up (Zig.region q a bs)) (Zig.store b q w)
      (fun _ => up (Zig.region q a (writeBytes bs 0 (Enc.encode w)))) := by
  fsym

theorem field_loadAt {s : T} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a) (ho : b ∣ o)
    (hfit : o + Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract o (o + Enc.size U)) = pure v) :
    FTTotalTriple (up (pts q a s)) (Zig.load U b (q.add o)) (fun x => ⟪x = v⟫ ⋆ up (pts q a s)) := by
  fsym [FTotalTriple.field_loadAt hn hb ho hfit hv]

theorem field_storeAt [LawfulEnc U] {s s' : T} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (ho : b ∣ o) (hfit : o + Enc.size U ≤ Enc.size T)
    (hw : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (writeBytes bs o (Enc.encode w)) = pure s') :
    FTTotalTriple (up (pts q a s)) (Zig.store b (q.add o) w) (fun _ => up (pts q a s')) := by
  fsym [FTotalTriple.field_storeAt w hn hb ho hfit hw]

theorem field_load {k : Int} {s : T} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract k.toNat (k.toNat + Enc.size U)) = pure v) :
    FTTotalTriple (up (pts q a s)) (Zig.load U b (q.add k)) (fun x => ⟪x = v⟫ ⋆ up (pts q a s)) := by
  fsym [FTotalTriple.field_load hn hb h0 ho hfit hv]

theorem field_store [LawfulEnc U] {k : Int} {s s' : T} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ Enc.size T)
    (hw : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (writeBytes bs k.toNat (Enc.encode w)) = pure s') :
    FTTotalTriple (up (pts q a s)) (Zig.store b (q.add k) w) (fun _ => up (pts q a s')) := by
  fsym [FTotalTriple.field_store w hn hb h0 ho hfit hw]

theorem field_load0 {s : T} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (hfit : Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract 0 (Enc.size U)) = pure v) :
    FTTotalTriple (up (pts q a s)) (Zig.load U b q) (fun x => ⟪x = v⟫ ⋆ up (pts q a s)) := by
  fsym [FTotalTriple.field_load0 hn hb hfit hv]

theorem field_store0 [LawfulEnc U] {s s' : T} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (hfit : Enc.size U ≤ Enc.size T)
    (hw : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (writeBytes bs 0 (Enc.encode w)) = pure s') :
    FTTotalTriple (up (pts q a s)) (Zig.store b q w) (fun _ => up (pts q a s')) := by
  fsym [FTotalTriple.field_store0 w hn hb hfit hw]

theorem errPayload_load {x : T} (hn : 0 < Enc.size T) (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size T) (Enc.align T)).2) :
    FTTotalTriple (up (pts q a (Except.ok x : Except ErrName T))) (Zig.load T b (errPayloadPtr T q))
      (fun r => ⟪r = x⟫ ⋆ up (pts q a (Except.ok x : Except ErrName T))) := by
  fsym

theorem errPayload_store [LawfulEnc T] {x : T} (y : T) (hn : 0 < Enc.size T)
    (hb : b ∣ a) (hpo : b ∣ (errUnionOffsets (Enc.size T) (Enc.align T)).2) :
    FTTotalTriple (up (pts q a (Except.ok x : Except ErrName T))) (Zig.store b (errPayloadPtr T q) y)
      (fun _ => up (pts q a (Except.ok y : Except ErrName T))) := by
  fsym

end Typed

section Arr

variable {T : Type} [Enc T] {p : Ptr} {vs : List T}

theorem arr_load {i : BitVec 64} (hn : 0 < Enc.size T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) :
    FTTotalTriple (up (Zig.arr p vs)) (Zig.load T (Enc.align T) (p.elem (Enc.size T) i))
      (fun v => ⟪v = vs[i.toNat]⟫ ⋆ up (Zig.arr p vs)) := by
  fsym

theorem arr_store [LawfulEnc T] {i : BitVec 64} (hn : 0 < Enc.size T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) (w : T) :
    FTTotalTriple (up (Zig.arr p vs)) (Zig.store (Enc.align T) (p.elem (Enc.size T) i) w)
      (fun _ => up (Zig.arr p (vs.set i.toNat w))) := by
  fsym

end Arr

/-! ## Programs in a thread -/

/-- Copy one cell to another. -/
def copy (p q : Ptr) : MemM Unit := do
  let v ← Zig.load (BitVec 32) 4 p
  Zig.store 4 q v

/-- Both cells and the frame `R` are found in any order; total. -/
theorem copy_total (p q : Ptr) (x y : BitVec 32) (R : FAssn) :
    FTTotalTriple (R ⋆ (up (pts q 4 y) ⋆ up (pts p 4 x))) (copy p q)
      (fun _ => up (pts p 4 x) ⋆ (up (pts q 4 x) ⋆ R)) := by
  unfold copy
  fsym

/-- The same program, partial. -/
theorem copy_partial (p q : Ptr) (x y : BitVec 32) (R : FAssn) :
    FTTriple (R ⋆ (up (pts q 4 y) ⋆ up (pts p 4 x))) (copy p q)
      (fun _ => up (pts p 4 x) ⋆ (up (pts q 4 x) ⋆ R)) := by
  unfold copy
  fsym

/-- A pointer formed into a region (a thread's own rule: it reads only the blocks), then a
store through it and a load back. -/
theorem region_roundtrip (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte)
    (hs : bs.size = 16) (w : BitVec 64) :
    FTTotalTriple (up (regionIn p A S K 8 bs))
      (do let q ← ptrProject p (·.add 8); Zig.store 8 q w; Zig.load (BitVec 64) 8 q)
      (fun r => ⟪r = w⟫ ⋆ up (regionIn p A S K 8 (writeBytes bs 8 (Enc.encode w)))) := by
  fsym

/-! ## Mappings (`Full/Mmap`)

The former hand-written thread rules of `munmap`, `mmap` and the `mremap` shrink: the sequential
rule with the locality providers `ThreadLocal.mmap`, `munmap_of`, `mremapShrink_of` (bytes owned,
block size and kind from the extent, `BlockIs.bauth`). -/

section Mmap

variable (os : Os.Target)

theorem munmapTail' {p : Ptr} {b : BlockId} {A S S' lo k : Nat}
    {K' : BlockKind} {tail : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : p.off = ((lo + k : Nat) : Int)) (hk : 0 < k) (hS : S = lo + k + tail.size)
    (htl : 0 < tail.size) (hal : (A + (lo + k)) % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : k + alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTTotalTriple (up (bytesAt p A S' K' tail) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b (lo + k) (.mapped lo)) := by
  fsym [FTotalTriple.munmapTail' os hpb hp0 hk hS htl hal hlen heq]

theorem munmapPrefix' {p : Ptr} {b : BlockId} {A S S' lo : Nat}
    {K' : BlockKind} {pre : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : p.off = (lo : Int)) (hlen : 0 < len.toNat)
    (hk : pre.size = alignUp len.toNat os.pageSize) (hlt : lo + pre.size < S)
    (hal : (A + lo) % os.pageSize = 0) :
    FTTotalTriple (up (bytesAt p A S' K' pre) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b S (.mapped (lo + pre.size))) := by
  fsym [FTotalTriple.munmapPrefix' os hpb hp0 hlen hk hlt hal]

theorem munmapWhole' {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {len : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.munmap os ⟨p, len⟩) (fun _ => FAssn.emp) := by
  fsym [FTotalTriple.munmapWhole' os hpb hp0 hlt hA hlo hlen heq]

theorem munmapTailR {p : Ptr} {b : BlockId} {A S S' lo a : Nat}
    {K' : BlockKind} {tail : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : 0 ≤ p.off) (hk : lo < p.off.toNat) (hS : S = p.off.toNat + tail.size)
    (htl : 0 < tail.size) (hal : (A + p.off.toNat) % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : p.off.toNat - lo + alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTTotalTriple (up (regionIn p A S' K' a tail) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b p.off.toNat (.mapped lo)) := by
  fsym [FTotalTriple.munmapTailR os hpb hp0 hk hS htl hal hlen heq]

theorem mmap' (hint : Option Ptr) (len : BitVec 64) (hlen : 0 < len.toNat) :
    FTTotalTriple FAssn.emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (fmmapPost os.pageSize os.addrLimit len) := by
  fsym [FTotalTriple.mmap' os hint len hlen]

theorem mmapC (hint : Option Ptr) (len : BitVec 64) (hlen : 0 < len.toNat) :
    FTTotalTriple FAssn.emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (fmmapPostC os.pageSize os.addrLimit len) := by
  fsym [FTotalTriple.mmapC os hint len hlen]

theorem mremapShrink' (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {b : BlockId} {A S S' lo : Nat} {K' : BlockKind}
    {cut : Array Byte} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : lo + newLen.toNat ≤ S) (hcut : cut.size = S - (lo + newLen.toNat)) :
    FTTotalTriple (up (bytesAt ⟨some b, ((lo + newLen.toNat : Nat) : Int)⟩ A S' K' cut) ⋆
        bext b S (.mapped lo))
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen flags none)
      (fun x => ⟪x = .ok ⟨⟨some b, (lo : Int)⟩, newLen⟩⟫ ⋆ bext b (lo + newLen.toNat) (.mapped lo)) := by
  fsym [FTotalTriple.mremapShrink' os hhas hfl hold0 hold hn0 hn hcut]

theorem mremapShrinkR (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {b : BlockId} {A S S' lo a : Nat} {K' : BlockKind}
    {cut : Array Byte} {oldLen newLen : BitVec 64} {p : Ptr} (hpb : p.block = some b)
    (hp0 : p.off = (lo : Int)) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : lo + newLen.toNat ≤ S) (hcut : cut.size = S - (lo + newLen.toNat)) :
    FTTotalTriple (up (regionIn (p.add newLen.toNat) A S' K' a cut) ⋆ bext b S (.mapped lo))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fun x => ⟪x = .ok ⟨p, newLen⟩⟫ ⋆ bext b (lo + newLen.toNat) (.mapped lo)) := by
  fsym [FTotalTriple.mremapShrinkR os hhas hfl hpb hp0 hold0 hold hn0 hn hcut]

theorem mremapGrow' (hhas : os.hasMremap = true) {b : BlockId} {S lo : Nat} {q : Frac}
    {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTTotalTriple (bauth b S (.mapped lo) q)
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none)
      (mremapGrowPost os.pageSize b S lo newLen.toNat q newLen) := by
  fsym [FTotalTriple.mremapGrow' os hhas hold0 hold hn]

theorem mremapMove' (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPost os.pageSize p b A S lo a bs newLen) := by
  fsym [FTotalTriple.mremapMove' os hhas hfl hpb hp0 hlt hA hlo hold0 hold hn]

theorem mremapMoveC (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆
        (bext b S (.mapped lo) ⋆ bclaim b lo (lo + claimEnd))))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPostC os.pageSize p b A S lo a bs newLen) := by
  fsym [FTotalTriple.mremapMoveC os hhas hfl hpb hp0 hlt hA hlo hold0 hold hn]

end Mmap

/-! ## A case of the rule that its locality needs (ledger #75)

A command with two sequential rules, one per case of a side condition the facts do not decide
(`S < n`, `n ≤ S`, as the `mremap` move and shrink at the page allocator's `remap`), whose
locality providers need the same case and the block's size from a later provider goal
(`BlockIs`). In a thread the rule's undecided goal and the provider's hypothesis are one goal:
the walk splits on it as the sequential walk does, and the provider's hypothesis about the
unknown size waits for the `BlockIs` goal that fixes it. -/

section Cases

/-- A command about block `b` and a length `n`; only its rules below describe it (its body
reads and writes the whole memory, which `fsym` does not step). -/
def resizeTo (_b : BlockId) (_n : Nat) : MemM Unit := do set (← get)

variable {b : BlockId} {S n : Nat} {K : BlockKind} {P : FAssn}

theorem resizeTo_eq : resizeTo b n = pure () := rfl

theorem resizeTo_grow (_hn : S < n) :
    FTotalTriple (bext b S K) (resizeTo b n) (fun _ => bext b S K) := by
  rw [resizeTo_eq]; fsym

theorem resizeTo_shrink (_hn : n ≤ S) :
    FTotalTriple (bext b S K) (resizeTo b n) (fun _ => bext b S K) := by
  rw [resizeTo_eq]; fsym

theorem ThreadLocal.resizeTo_grow (_hn : S < n) (_h : BlockIs b S K P) :
    ThreadLocal P (resizeTo b n) := resizeTo_eq ▸ ThreadLocal.pure ()

theorem ThreadLocal.resizeTo_shrink (_hn : n ≤ S) (_h : BlockIs b S K P) :
    ThreadLocal P (resizeTo b n) := resizeTo_eq ▸ ThreadLocal.pure ()

attribute [fsym_provider] ThreadLocal.resizeTo_grow ThreadLocal.resizeTo_shrink

theorem resizeTo_cases :
    FTotalTriple (bext b S K) (resizeTo b n) (fun _ => bext b S K) := by
  fsym [resizeTo_grow, resizeTo_shrink]

theorem resizeTo_thread :
    FTTotalTriple (bext b S K) (resizeTo b n) (fun _ => bext b S K) := by
  fsym [resizeTo_grow, resizeTo_shrink]

end Cases

section Tick

/-! A step tick in a thread: the sequential tick rules (`Full/Tick`) with the provider
`ThreadLocal.tick`; no hand-written thread rule. -/

theorem tick_plain : FTTotalTriple plain Zig.tick (fun _ => plain ⋆ spent 1) := by
  fsym

theorem tick_unmetered : FTTotalTriple unmetered Zig.tick (fun _ => unmetered ⋆ spent 1) := by
  fsym

theorem tick_credit : FTTotalTriple (credits 1) Zig.tick (fun _ => spent 1) := by
  fsym

end Tick

/-! ## `const` reads (MM-20) -/

/-- A read of a `const` global in a thread: the native thread rule `FTTotalTriple.cload` (a
`const` read records nothing, so it races with nothing and keeps every frame). -/
example (p : Ptr) (v : BitVec 32) :
    FTTotalTriple (cpts p 4 v) (Zig.load (BitVec 32) 4 p) (fun x => ⟪x = v⟫ ⋆ cpts p 4 v) := by
  fsym

/-- The same read, sequential. -/
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (cpts p 4 v) (Zig.load (BitVec 32) 4 p) (fun x => ⟪x = v⟫ ⋆ cpts p 4 v) := by
  fsym

/-- A `const` read, then an owned store of the value read, in a thread. -/
example (p q : Ptr) (v x : BitVec 32) :
    FTTotalTriple (cpts p 4 v ⋆ up (pts q 4 x))
      (do let y ← Zig.load (BitVec 32) 4 p; Zig.store 4 q y)
      (fun _ => cpts p 4 v ⋆ up (pts q 4 v)) := by
  fsym

/-! ## Loops in a thread (`Full/ThreadLoop.lean`) -/

/-- A generated loop over its locals. -/
def tcnt.loop6 : MM Nat Bool := do
  let s ← get
  if s == 0 then pure false else
    set (s - 1)
    pure true

def tcnt (n : Nat) : MemM Nat := do
  let r ← (Zig.loop tcnt.loop6 (fun b : Bool => b)).run n
  pure r.2

/-- **A thread's loop** by its invariant and a measure on the locals: the body walked in the
thread logic. -/
theorem tcnt_loop (R : FAssn) (k : Nat) :
    FTTotalTriple R ((Zig.loop tcnt.loop6 (fun b : Bool => b)).run k) (fun r => ⟪r.2 = 0⟫ ⋆ R) :=
  FTTotalTriple.loop_measure (fun _ => R) (fun s => s) _ (fun s => by unfold tcnt.loop6; fsym) k

/-- **The thread's loop as a rule** of the walk of its caller. -/
theorem tcnt_spec (R : FAssn) (n : Nat) :
    FTTotalTriple R (tcnt n) (fun r => ⟪r = 0⟫ ⋆ R) := by
  unfold tcnt
  fsym [tcnt_loop]

/-- The partial thread rule (fixpoint induction). -/
theorem tcnt_loop_partial (R : FAssn) (k : Nat) :
    FTTriple R ((Zig.loop tcnt.loop6 (fun b : Bool => b)).run k) (fun r => ⟪r.2 = 0⟫ ⋆ R) :=
  FTTriple.loop (fun _ => R) _ (fun s => by unfold tcnt.loop6; fsym) k

/-! ## Rejected -/

set_option linter.unusedVariables false

/-- Rejected: a store of 8 bytes into a cell of 4 (bytes the precondition does not own). -/
example (p : Ptr) (x : BitVec 32) (w : BitVec 64) : True := by
  fail_if_success
    have : FTTotalTriple (up (pts p 4 x)) (Zig.store 4 p w) (fun _ => up (pts p 4 x)) := by
      fsym
  trivial

end SepAuto.Threads
