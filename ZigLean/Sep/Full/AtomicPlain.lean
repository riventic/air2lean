import ZigLean.Sep.Full.AutoRules
import ZigLean.Sep.Full.AtomicPtr

/-!
# Plain accesses of atomic words (`docs/proof-automation.md` §Atomic words)

A word that atomic ops use (`apts p v`, `aptsE p v`: owned bytes `abytesAt` with the atomic tag
`(p.off, 8)`) is also read and written by plain loads and stores (the arena's `reset` stores its
list heads, `allocatedSliceUnsafe` loads a node's size). A plain access checks no tag: it reads the
bytes, and a write keeps every cell's tag (`Holds.write`). So the rules below keep the word's tag,
and the atomic ops still apply afterwards:

* bytes (`abytesAt`, any tag): `loadBytes_abytesAt`, `load_abytesAt`, `storeBytes_abytesAt`,
  `store_abytesAt`, the analogues of `Ops.lean`'s `…_bytesAt` rules;
* `aptsE p v` (`@[fsym]`): a load of the value (`aptsE_load`), a store of a value
  (`aptsE_store`), and a store of bytes that decode to one (`aptsE_storeBytes`);
* `apts p v` (`@[fsym]`): a load and a store of the word (`apts_load`, `apts_store`), and of a
  packed struct over it (`apts_loadPacked`, `apts_storePacked`: the generated `Enc` of a packed
  struct is its bits' `BitVec 64` encoding);
* in a thread (`@[fsym_provider]`): a word's 8 bytes are owned (`OwnsPtr.apts`, `OwnsPtr.aptsE`),
  so the rules above are local (`ThreadLocal.load`/`store`); adjacent owned ranges join
  (`OwnsPtr.join`).
-/

namespace Zig.Full

open FAssn

section Bytes

variable {p q : Ptr} {A S k al : Nat} {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)}

/-- Owned tagged bytes, read as plain owned bytes (the tags erased). -/
theorem up_of_abytesAt {r : Res} (h : abytesAt p A S K bs tg r) : up (bytesAt p A S K bs) r :=
  ⟨abytesAt_bytesAt h, h.1, h.2.1⟩

/-- Owned tagged bytes after a write of `bs'` at byte `k` of them: `writeBytes bs k bs'`, with
the same tag. -/
theorem abytesAt_writeAt {r : Res} {b : BlockId} {bs' : Array Byte}
    (hp : abytesAt p A S K bs tg r) (hpb : p.block = some b) (hk : k + bs'.size ≤ bs.size) :
    abytesAt p A S K (writeBytes bs k bs') tg (r.writeAt b (p.off.toNat + k) bs') := by
  obtain ⟨hkn, hg, b', hb', h0, hl⟩ := hp
  rw [hpb] at hb'; cases hb'
  refine ⟨hkn, hg, b, hpb, h0, fun l => ?_⟩
  have e := hl l
  have hs := writeBytes_size bs k bs' hk
  simp only [Res.writeAt]
  rw [hs]
  by_cases hc : l.1 = b ∧ p.off.toNat + k ≤ l.2 ∧ l.2 < p.off.toNat + k + bs'.size
  · have hin : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size :=
      ⟨hc.1, by omega, by omega⟩
    rw [ite_eq_left hc, e, ite_eq_left hin, ite_eq_left hin, writeBytes_getElem! bs k bs' hk,
      ite_eq_left (by omega : k ≤ l.2 - p.off.toNat ∧ l.2 - p.off.toNat < k + bs'.size),
      Option.map_some, show l.2 - (p.off.toNat + k) = l.2 - p.off.toNat - k by omega]
  · rw [ite_eq_right hc, e]
    by_cases hin : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    · rw [ite_eq_left hin, ite_eq_left hin, writeBytes_getElem! bs k bs' hk,
        ite_eq_right (fun h => hc ⟨hin.1, by omega, by omega⟩ :
          ¬ (k ≤ l.2 - p.off.toNat ∧ l.2 - p.off.toNat < k + bs'.size))]
    · rw [ite_eq_right hin, ite_eq_right hin]

namespace FTotalTriple

/-- **Read of `n` owned tagged bytes** from byte `k` on: they stay, with their tag. -/
theorem loadBytes_abytesAt {n : Nat} (hn : 0 < n) (hk : k + n ≤ bs.size)
    (ha : (A + q.off.toNat + k) % al = 0) :
    FTotalTriple (abytesAt q A S K bs tg) (Zig.loadBytes (q.add k) n al)
      (fun x => ⟪x = bs.extract k (k + n)⟫ ⋆ abytesAt q A S K bs tg) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, -, -, hx⟩ := hh.bytesAt_access (up_of_abytesAt hp) hn hk ha
    exact ⟨_, _, r, loadBytes_read hacc (fun _ => rfl)
      (noRace_of_singleThread hs.1.single _ _ _ _),
      hh.readAt _ _ _ _ _, sep_lift.mpr ⟨hx, hp⟩, hs.readAt _ _ _ _ _⟩

/-- **Load of a `T`** at byte `k` of owned tagged bytes that decode to `v` there. -/
theorem load_abytesAt {T : Type} [Enc T] {v : T} (hn : 0 < Enc.size T)
    (hk : k + Enc.size T ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hv : Enc.decode (bs.extract k (k + Enc.size T)) = pure v) :
    FTotalTriple (abytesAt q A S K bs tg) (Zig.load T al (q.add k))
      (fun x => ⟪x = v⟫ ⋆ abytesAt q A S K bs tg) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, -, -, hx⟩ := hh.bytesAt_access (up_of_abytesAt hp) hn hk ha
    exact ⟨v, _, r, load_read hacc (by rw [hx]; exact hv)
      (noRace_of_singleThread hs.1.single _ _ _ _), hh.readAt _ _ _ _ _, sep_lift.mpr ⟨rfl, hp⟩,
      hs.readAt _ _ _ _ _⟩

/-- **Store of the bytes `bs'`** at byte `k` of owned tagged bytes, not of a `const` global: the
bytes become `writeBytes bs k bs'`, the tag stays. -/
theorem storeBytes_abytesAt {bs' : Array Byte} (hn : 0 < bs'.size) (hk : k + bs'.size ≤ bs.size)
    (ha : (A + q.off.toNat + k) % al = 0) (hK : K ≠ .constGlobal) :
    FTotalTriple (abytesAt q A S K bs tg) (Zig.storeBytes (q.add k) al bs')
      (fun _ => abytesAt q A S K (writeBytes bs k bs') tg) :=
  of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hacc, hb, hKn, -⟩ := hh.bytesAt_access (up_of_abytesAt hp) hn hk ha
    obtain ⟨hpb, -, hl, -, hfit, -, -⟩ := access_eq hacc
    have hlo := access_lo hacc
    have hK' : blk.kind ≠ .constGlobal := fun e => hK (by
      have h : K.norm = .constGlobal := by rw [← hKn, e]; rfl
      cases K <;> simp_all [BlockKind.norm])
    have hrun := storeBytes_run (kind := .write) hacc hK' (noRace_of_singleThread hs.1.single _ _ _ _)
    have hpb' : q.block = some b := by simpa using hpb
    obtain ⟨-, -, -, -, h0, -⟩ := id hp
    have hfit' : q.off.toNat + k + bs'.size ≤ blk.bytes.size := by
      simp only [Ptr.add] at hfit; omega
    refine ⟨(), _, _, hrun, (hh.recordAt _ _ _ _).write hb hl hfit' hlo hK' fun i hi => ?_,
      abytesAt_writeAt hp hpb' hk, ?_⟩
    · rw [abytesAt_cell hp hpb' (l := (b, q.off.toNat + k + i)) ⟨rfl, by omega, by omega⟩]; simp
    · exact ⟨⟨singleThread_write (singleThread_recordAt hs.1.single _ _ _ _) _ _ _ _⟩, hs.2.1,
        (LDMono.set (nb := { blk with bytes := writeBytes blk.bytes (q.off.toNat + k) bs' }) hb id
          rfl (by simp only; rw [writeBytes_size _ _ _ hfit']; exact Nat.le_refl _) rfl) hs.2.2⟩

/-- **Store of a `T`** at byte `k` of owned tagged bytes, not of a `const` global. -/
theorem store_abytesAt {T : Type} [Enc T] (w : T) (hn : 0 < (Enc.encode w).size)
    (hk : k + (Enc.encode w).size ≤ bs.size) (ha : (A + q.off.toNat + k) % al = 0)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (abytesAt q A S K bs tg) (Zig.store al (q.add k) w)
      (fun _ => abytesAt q A S K (writeBytes bs k (Enc.encode w)) tg) :=
  storeBytes_abytesAt hn hk ha hK

end FTotalTriple

end Bytes

/-! ## Atomic words (`@[fsym]`) -/

section Words

variable {α : Type} [Enc α] {p : Ptr} {al : Nat}

namespace FTotalTriple

/-- **Plain load of an atomic value** `aptsE p v`: `v`, the word keeps its tag. -/
@[fsym] theorem aptsE_load {v : α} (hs : Enc.size α = 8) (hal : al ∣ 8) :
    FTotalTriple (aptsE p v) (Zig.load α al p) (fun x => ⟪x = v⟫ ⋆ aptsE p v) :=
  of_cases fun _ ⟨A, S, K, bs, ha, hK, hsz, hv, hab⟩ => by
    have t := load_abytesAt (q := p) (k := 0) (al := al) (A := A) (S := S) (K := K) (bs := bs)
      (tg := some (p.off.toNat, 8)) (v := v) (by omega) (by omega)
      (mod_add_dvd ha hal (Nat.dvd_zero al))
      (by rw [Nat.zero_add, hs, ← hsz, Array.extract_size]; exact hv)
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, hab, fun x _ h => by
      obtain ⟨hx, hab'⟩ := sep_lift.mp h
      exact sep_lift.mpr ⟨hx, A, S, K, bs, ha, hK, hsz, hv, hab'⟩⟩

/-- **Plain store of bytes that decode to `x`** into an atomic value: the word holds `x`, with
its tag. -/
@[fsym] theorem aptsE_storeBytes {v x : α} {cs : Array Byte} (hc : cs.size = 8)
    (hx : Enc.decode cs = pure x) (hal : al ∣ 8) :
    FTotalTriple (aptsE p v) (Zig.storeBytes p al cs) (fun _ => aptsE p x) :=
  of_cases fun _ ⟨A, S, K, bs, ha, hK, hsz, _, hab⟩ => by
    have t := storeBytes_abytesAt (q := p) (k := 0) (al := al) (A := A) (S := S) (K := K)
      (bs := bs) (tg := some (p.off.toNat, 8)) (bs' := cs) (by omega) (by omega)
      (mod_add_dvd ha hal (Nat.dvd_zero al))
      hK
    simp only [Int.natCast_zero, Ptr.add_zero, writeBytes_all (hc.trans hsz.symm)] at t
    exact ⟨_, _, t, hab, fun _ _ h => ⟨A, S, K, cs, ha, hK, hc, hx, h⟩⟩

/-- **Plain store of a value** into an atomic value: the word holds it, with its tag. -/
@[fsym] theorem aptsE_store [LawfulEnc α] {v : α} (x : α) (hs : Enc.size α = 8) (hal : al ∣ 8) :
    FTotalTriple (aptsE p v) (Zig.store al p x) (fun _ => aptsE p x) :=
  aptsE_storeBytes ((LawfulEnc.size_encode x).trans hs) (LawfulEnc.decode_encode x) hal

/-- **Plain load of an atomic word** (an atomic value of `BitVec 64`, definitionally). -/
@[fsym] theorem apts_load {v : BitVec 64} (hal : al ∣ 8) :
    FTotalTriple (apts p v) (Zig.load (BitVec 64) al p) (fun x => ⟪x = v⟫ ⋆ apts p v) :=
  aptsE_load rfl hal

/-- **Plain store of a word** into an atomic word. -/
@[fsym] theorem apts_store {v : BitVec 64} (x : BitVec 64) (hal : al ∣ 8) :
    FTotalTriple (apts p v) (Zig.store al p x) (fun _ => apts p x) :=
  aptsE_store x rfl hal

/-- **Plain load of a packed struct** over an atomic word: the struct of the word's bits (if
they are valid for it). `hd`: the struct's `Enc` decodes its bits' `BitVec 64` encoding (the
generated `Enc` of a packed struct, definitionally). -/
@[fsym] theorem apts_loadPacked {T : Type} [Enc T] [Packed T 64] {v : BitVec 64}
    (hd : (Enc.decode : Array Byte → Result T) =
      fun bs => (Enc.decode bs : Result (BitVec 64)) >>= Packed.ofBits?)
    (hs : Enc.size T = 8) (hval : Packed.valid (α := T) v = true) (hal : al ∣ 8) :
    FTotalTriple (apts p v) (Zig.load T al p) (fun x => ⟪x = Packed.ofBits v⟫ ⋆ apts p v) :=
  of_cases fun _ ⟨A, S, K, bs, ha, hK, hsz, hv, hab⟩ => by
    have hv' : (Enc.decode bs : Result T) = pure (Packed.ofBits v) := by
      rw [hd]
      show (intOfBytes 64 bs >>= Packed.ofBits?) = _
      rw [hv]
      show Packed.ofBits? v = _
      simp [Packed.ofBits?, hval]
    have t := load_abytesAt (q := p) (k := 0) (al := al) (A := A) (S := S) (K := K) (bs := bs)
      (tg := some (p.off.toNat, 8)) (v := Packed.ofBits (α := T) v) (by omega) (by omega)
      (mod_add_dvd ha hal (Nat.dvd_zero al))
      (by rw [Nat.zero_add, hs, ← hsz, Array.extract_size]; exact hv')
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, hab, fun x _ h => by
      obtain ⟨hx, hab'⟩ := sep_lift.mp h
      exact sep_lift.mpr ⟨hx, A, S, K, bs, ha, hK, hsz, hv, hab'⟩⟩

/-- **Plain store of a packed struct** into an atomic word: the word holds its bits. `he`: the
struct's `Enc` encodes its bits (the generated `Enc` of a packed struct, definitionally). -/
@[fsym] theorem apts_storePacked {T : Type} [Enc T] [Packed T 64] {v : BitVec 64} (w : T)
    (he : (Enc.encode : T → Array Byte) = fun x => Enc.encode (Packed.toBits x)) (hal : al ∣ 8) :
    FTotalTriple (apts p v) (Zig.store al p w) (fun _ => apts p (Packed.toBits w)) := by
  have e : Zig.store al p w = Zig.store al p (Packed.toBits w) := by
    show Zig.storeBytes p al (Enc.encode w) = Zig.storeBytes p al (Enc.encode (Packed.toBits w))
    rw [he]
  rw [e]; exact apts_store _ hal

end FTotalTriple

/-! ## Atomic words as plain bytes (`@[fsym_view]`)

A word given away as plain bytes (a node's header words, joined with the node's other bytes into
the region the child allocator's `free` takes): the region of its bytes, with what it held. The
view is one-way: the region does not say the bytes' tag, so it gives no atomic word back. -/

/-- **An atomic value as a region** of its 8 bytes, which decode to it. -/
@[fsym_view] theorem aptsE_view {v : α} :
    EUpd (aptsE p v) (FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun bs =>
      ⟪bs.size = 8 ∧ Enc.decode bs = pure v⟫ ⋆ up (regionIn p A S K 8 bs)) :=
  EUpd.of_imp fun _ ⟨A, S, K, bs, ha, hK, hsz, hv, hab⟩ =>
    have hb := up_of_abytesAt hab
    ⟨A, S, K, bs, sep_lift.mpr ⟨⟨hsz, hv⟩, ⟨ha, hK, hb.1⟩, hb.2⟩⟩

/-- **An atomic word as a region** of its 8 bytes, which hold it. -/
@[fsym_view] theorem apts_view {v : BitVec 64} :
    EUpd (apts p v) (FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun bs =>
      ⟪bs.size = 8 ∧ intOfBytes 64 bs = pure v⟫ ⋆ up (regionIn p A S K 8 bs)) :=
  EUpd.of_imp fun _ ⟨A, S, K, bs, ha, hK, hsz, hv, hab⟩ =>
    have hb := up_of_abytesAt hab
    ⟨A, S, K, bs, sep_lift.mpr ⟨⟨hsz, hv⟩, ⟨ha, hK, hb.1⟩, hb.2⟩⟩

end Words

/-! ## The bytes of an atomic word (`@[fsym_provider]`)

A plain access of an owned atomic word is local to its thread (`ThreadLocal.load`/`store`), so
the plain rules above apply in a thread goal too (`FTTotalTriple.ofSeq`, `Full/AutoThread.lean`):
the word's 8 bytes are bytes of the precondition. -/

/-- The 8 bytes of an `apts` word. -/
theorem OwnsPtr.apts {p : Ptr} {v : BitVec 64} : OwnsPtr (apts p v) p 8 := by
  rintro b hb r ⟨A, S, K, bs, -, -, hs, -, hab⟩
  rw [← hs]; exact bytesAt_has (abytesAt_bytesAt hab) hb

/-- The 8 bytes of an `aptsE` word. -/
theorem OwnsPtr.aptsE {α : Type} [Enc α] {p : Ptr} {v : α} : OwnsPtr (aptsE p v) p 8 := by
  rintro b hb r ⟨A, S, K, bs, -, -, hs, -, hab⟩
  rw [← hs]; exact bytesAt_has (abytesAt_bytesAt hab) hb

attribute [fsym_provider] OwnsPtr.apts OwnsPtr.aptsE

/-- **Adjacent owned bytes are owned together**: `p`'s `n` bytes and the `k` bytes after them. A
struct whose fields several parts own (`Parts.lean`) is owned this way, field by field. -/
theorem OwnsPtr.join {P : FAssn} {p : Ptr} {n k : Nat} (h0 : 0 ≤ p.off) (h1 : OwnsPtr P p n)
    (h2 : OwnsPtr P (p.add n) k) : OwnsPtr P p (n + k) := by
  intro b hb r hr x hx hx'
  by_cases hlt : x < p.off.toNat + n
  · exact h1 b hb r hr x hx hlt
  · have hb' : (p.add n).block = some b := hb
    have ho : (p.add n).off.toNat = p.off.toNat + n := by simp only [Ptr.add]; omega
    exact h2 b hb' r hr x (by rw [ho]; omega) (by rw [ho]; omega)

/-- `OwnsPtr.join` with the second range at a pointer `q` of `p`'s block `n` bytes past it, as a
part names it (`fsym` composes a struct's ownership from its parts this way). -/
theorem OwnsPtr.join_at {P : FAssn} {p q : Ptr} {n k : Nat} (h0 : 0 ≤ p.off) (h1 : OwnsPtr P p n)
    (hb : q.block = p.block) (ho : q.off = p.off + n) (h2 : OwnsPtr P q k) :
    OwnsPtr P p (n + k) := by
  have e : q = p.add n := by
    obtain ⟨qb, qo⟩ := q
    simp only [Ptr.add] at hb ho ⊢
    rw [hb, ho]
  exact OwnsPtr.join h0 h1 (e ▸ h2)

end Zig.Full
