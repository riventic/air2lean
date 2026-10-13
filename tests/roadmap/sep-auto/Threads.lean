import ZigLean.Sep.Full.Auto

/-!
# `fsym` in a thread (`ZigLean/Sep/Full/AutoThread.lean`)

A thread's step (`FTTotalTriple`, `FTTriple`) is walked as a sequential program: each sequential
`@[fsym]` rule applies with the locality of its command (`FTTotalTriple.ofSeq` and a
`ThreadLocal` side goal, proved by the locality providers from the bytes the precondition
owns). The thread rules below were hand-written copies of their sequential rules (`Full/Ops`,
`Full/Region`, `Full/Typed`, `Full/Arr`); each is now one `fsym` call, with the sequential rule
named where it is not `@[fsym]`. Programs of several commands walk with a frame in a thread
logic, total and partial, and a command whose bytes the precondition does not own gets no
thread rule (fail closed).
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

/-! ## Rejected -/

/-- Rejected: a read of a `const` global in a thread. Its sequential rule holds (`cload`), but no
provider shows the read local (a concurrent memory does not exclude recorded writes to `const`
bytes), so the thread gets no rule from it. -/
example (p : Ptr) (v : BitVec 32) : True := by
  fail_if_success
    have : FTTotalTriple (cpts p 4 v) (Zig.load (BitVec 32) 4 p) (fun x => ⟪x = v⟫ ⋆ cpts p 4 v) := by
      fsym
  trivial

/-- The same read, sequential: the rule applies. -/
example (p : Ptr) (v : BitVec 32) :
    FTotalTriple (cpts p 4 v) (Zig.load (BitVec 32) 4 p) (fun x => ⟪x = v⟫ ⋆ cpts p 4 v) := by
  fsym

/-- Rejected: a store into bytes another part does not cover (one byte past the cell). -/
example (p : Ptr) (x : BitVec 32) (w : BitVec 64) : True := by
  fail_if_success
    have : FTTotalTriple (up (pts p 4 x)) (Zig.store 4 p w) (fun _ => up (pts p 4 x)) := by
      fsym
  trivial

end SepAuto.Threads
