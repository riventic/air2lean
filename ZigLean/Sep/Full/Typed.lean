import ZigLean.Sep.Full.Const
import ZigLean.Sep.Full.AutoRules

/-!
# Typed values in the full-state logic: bytes, fields, payloads (Plan A library lane A1)

`pts q a v` (`ZigLean/Sep/Triple.lean`) owns the bytes of a typed value `v : T` at `q`, for any
encoding `Enc T`. A part of the value is read or written through a pointer `q.add o` with
another type `U` (a struct field, the payload of an error union or of an optional, the active
field of a union): such an access sees only the bytes `[o, o + Enc.size U)`. Here:

* **Bytes view**: `pts_iff_region`, `up_pts_iff`: a typed value is a byte region (`region`,
  `ZigLean/Sep/AllocSpec/Region.lean`) whose bytes decode to it. `up_pts_of_region` packs a
  region back.
* **Byte rules**: `FTotalTriple.region_load` (a `U` at byte `o` of a region, decoding to `v`)
  and `FTotalTriple.region_store` (`@[fsym]`: the region's bytes become `writeBytes bs o
  (Enc.encode w)`), also at offset 0 (`region_load0`, `region_store0`).
* **Fields** of a typed value, from the byte rules: `FTotalTriple.field_load` reads `v` at byte
  `o` of `pts q a s` if every byte string of `s` has `v` there; `FTotalTriple.field_store`
  writes `w` there and gives `pts q a s'` if every byte string of `s` with `w` written there
  decodes to `s'`. With the field's `EncField` (`AutoRules.lean`) the value is determined:
  `FTotalTriple.encField_load`/`_store` (`@[fsym]`) read `get s` and write `set s w`, and `fsym`
  derives the `EncField` of the structs of generated code (`docs/proof-automation.md` §Fields).
  A write that leaves the value undecodable in between (a tag and a payload written one after
  the other) goes through the bytes view: `up_pts_iff`, the byte rules, `up_pts_of_region`.
* **Payloads** (`@[fsym]`): the payload of an error union holding `.ok x`
  (`errPayload_load`/`errPayload_store` through `errPayloadPtr`).
* **Read-only fields** of a `const` global (`cpts`, `Full/Const.lean`): `FTotalTriple.cfield_load`
  from the provider `ConstAt.add` (a part of known `const` bytes).
* **In a thread** (`docs/sep-threads.md` S2) the byte, field and payload rules apply with the
  locality of their access (`fsym`'s `ofSeq` step, `Full/AutoThread.lean`); the read-only ones
  do not (a `const` read owns no bytes, S2 "Open").

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

open Assn

section Bytes

variable {T U : Type} [Enc T] [Enc U] {q : Ptr} {a b o : Nat} {bs : Array Byte}

/-- **The bytes view of a typed value**: a region whose bytes decode to it. -/
theorem pts_iff_region {v : T} {h : Heap} :
    pts q a v h ↔ ∃ bs, bs.size = Enc.size T ∧ Enc.decode bs = pure v ∧ region q a bs h :=
  ⟨fun ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩ => ⟨bs, hs, hv, A, S, K, ha, hK, hb⟩,
    fun ⟨bs, hs, hv, A, S, K, ha, hK, hb⟩ => ⟨A, S, K, bs, ha, hs, hv, hb, hK⟩⟩

end Bytes

namespace Full

open FAssn

section Bytes

variable {T U : Type} [Enc T] [Enc U] {q : Ptr} {a b o : Nat} {bs : Array Byte}

/-- **The bytes view** of an owned typed value. -/
theorem up_pts_iff {v : T} {r : Res} :
    up (pts q a v) r ↔ (FAssn.ex fun bs : Array Byte =>
      ⟪bs.size = Enc.size T ∧ Enc.decode bs = pure v⟫ ⋆ up (Zig.region q a bs)) r := by
  constructor
  · rintro ⟨hp, hk, hg⟩
    obtain ⟨bs, hs, hv, hr⟩ := pts_iff_region.mp hp
    exact ⟨bs, sep_lift.mpr ⟨⟨hs, hv⟩, hr, hk, hg⟩⟩
  · rintro ⟨bs, hx⟩
    obtain ⟨⟨hs, hv⟩, hr, hk, hg⟩ := sep_lift.mp hx
    exact ⟨pts_iff_region.mpr ⟨bs, hs, hv, hr⟩, hk, hg⟩

/-- A region whose bytes decode to `v` is the typed value `v`. -/
theorem up_pts_of_region {v : T} {r : Res} (hs : bs.size = Enc.size T)
    (hv : Enc.decode bs = pure v) (h : up (Zig.region q a bs) r) : up (pts q a v) r :=
  up_pts_iff.mpr ⟨bs, sep_lift.mpr ⟨⟨hs, hv⟩, h⟩⟩

/-! ## Byte rules -/

/-- **Load** of a `U` at byte `o` of a region whose bytes there decode to `v`. -/
theorem FTotalTriple.region_loadAt {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a) (ho : b ∣ o)
    (hfit : o + Enc.size U ≤ bs.size) (hv : Enc.decode (bs.extract o (o + Enc.size U)) = pure v) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.load U b (q.add o))
      (fun x => ⟪x = v⟫ ⋆ up (Zig.region q a bs)) :=
  FTotalTriple.of_cases fun _ ⟨⟨A, S, K, ha, hK, hbs⟩, hk, hg⟩ =>
    ⟨_, _, FTotalTriple.load_bytesAt hn hfit (mod_add_dvd ha hb ho) hv, ⟨hbs, hk, hg⟩,
      fun _ _ h => by
        obtain ⟨hx, hb', hk', hg'⟩ := sep_lift.mp h
        exact sep_lift.mpr ⟨hx, ⟨A, S, K, ha, hK, hb'⟩, hk', hg'⟩⟩

/-- **Store** of a `U` at byte `o` of a region. -/
theorem FTotalTriple.region_storeAt [LawfulEnc U] (w : U) (hn : 0 < Enc.size U) (hb : b ∣ a)
    (ho : b ∣ o) (hfit : o + Enc.size U ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.store b (q.add o) w)
      (fun _ => up (Zig.region q a (writeBytes bs o (Enc.encode w)))) :=
  FTotalTriple.of_cases fun _ ⟨⟨A, S, K, ha, hK, hbs⟩, hk, hg⟩ =>
    ⟨_, _, FTotalTriple.store_bytesAt w (by rw [LawfulEnc.size_encode]; exact hn)
        (by rw [LawfulEnc.size_encode]; exact hfit) (mod_add_dvd ha hb ho) hK, ⟨hbs, hk, hg⟩,
      fun _ _ ⟨hb', hk', hg'⟩ => ⟨⟨A, S, K, ha, hK, hb'⟩, hk', hg'⟩⟩

/-- `region_loadAt` at the offset `k` of generated code (`p.add 2`: an `Int` literal). -/
theorem FTotalTriple.region_load {k : Int} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ bs.size)
    (hv : Enc.decode (bs.extract k.toNat (k.toNat + Enc.size U)) = pure v) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.load U b (q.add k))
      (fun x => ⟪x = v⟫ ⋆ up (Zig.region q a bs)) := by
  have t := FTotalTriple.region_loadAt (q := q) hn hb ho hfit hv
  rwa [Int.toNat_of_nonneg h0] at t

/-- `region_storeAt` at the offset `k` of generated code. -/
@[fsym] theorem FTotalTriple.region_store [LawfulEnc U] {k : Int} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.store b (q.add k) w)
      (fun _ => up (Zig.region q a (writeBytes bs k.toNat (Enc.encode w)))) := by
  have t := FTotalTriple.region_storeAt (q := q) w hn hb ho hfit
  rwa [Int.toNat_of_nonneg h0] at t

/-- `region_loadAt` at byte 0. -/
theorem FTotalTriple.region_load0 {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (hfit : Enc.size U ≤ bs.size) (hv : Enc.decode (bs.extract 0 (Enc.size U)) = pure v) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.load U b q) (fun x => ⟪x = v⟫ ⋆ up (Zig.region q a bs)) := by
  have t := FTotalTriple.region_loadAt (q := q) (bs := bs) (o := 0) hn hb (Nat.dvd_zero b) (by omega)
    (by rwa [Nat.zero_add])
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

/-- `region_storeAt` at byte 0. -/
@[fsym] theorem FTotalTriple.region_store0 [LawfulEnc U] (w : U) (hn : 0 < Enc.size U) (hb : b ∣ a)
    (hfit : Enc.size U ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.store b q w)
      (fun _ => up (Zig.region q a (writeBytes bs 0 (Enc.encode w)))) := by
  have t := FTotalTriple.region_storeAt (q := q) (bs := bs) (o := 0) w hn hb (Nat.dvd_zero b) (by omega)
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

/-! ## Fields -/

/-- **Load of a field**: a `U` at byte `o` of a typed value `s`, where every byte string of `s`
holds `v`. -/
theorem FTotalTriple.field_loadAt {s : T} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a) (ho : b ∣ o)
    (hfit : o + Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract o (o + Enc.size U)) = pure v) :
    FTotalTriple (up (pts q a s)) (Zig.load U b (q.add o)) (fun x => ⟪x = v⟫ ⋆ up (pts q a s)) :=
  (FTotalTriple.ex fun bs => FTotalTriple.lift fun ⟨hs, hd⟩ =>
    (FTotalTriple.region_loadAt (q := q) hn hb ho (hs ▸ hfit) (hv bs hs hd)).post fun _ _ hx => by
      obtain ⟨e, hr⟩ := sep_lift.mp hx
      exact sep_lift.mpr ⟨e, up_pts_of_region hs hd hr⟩).pre fun _ h => up_pts_iff.mp h

/-- **Store of a field**: `w` at byte `o` of a typed value `s`; every byte string of `s` with
`w` written there decodes to `s'`. -/
theorem FTotalTriple.field_storeAt [LawfulEnc U] {s s' : T} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (ho : b ∣ o) (hfit : o + Enc.size U ≤ Enc.size T)
    (hw : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (writeBytes bs o (Enc.encode w)) = pure s') :
    FTotalTriple (up (pts q a s)) (Zig.store b (q.add o) w) (fun _ => up (pts q a s')) :=
  (FTotalTriple.ex fun bs => FTotalTriple.lift fun ⟨hs, hd⟩ =>
    (FTotalTriple.region_storeAt (q := q) w hn hb ho (hs ▸ hfit)).post fun _ _ hr =>
      up_pts_of_region (by rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; omega), hs])
        (hw bs hs hd) hr).pre fun _ h => up_pts_iff.mp h

/-- `field_loadAt` at the offset `k` of generated code. -/
theorem FTotalTriple.field_load {k : Int} {s : T} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract k.toNat (k.toNat + Enc.size U)) = pure v) :
    FTotalTriple (up (pts q a s)) (Zig.load U b (q.add k)) (fun x => ⟪x = v⟫ ⋆ up (pts q a s)) := by
  have t := FTotalTriple.field_loadAt (q := q) hn hb ho hfit hv
  rwa [Int.toNat_of_nonneg h0] at t

/-- `field_storeAt` at the offset `k` of generated code. -/
theorem FTotalTriple.field_store [LawfulEnc U] {k : Int} {s s' : T} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (h0 : 0 ≤ k) (ho : b ∣ k.toNat) (hfit : k.toNat + Enc.size U ≤ Enc.size T)
    (hw : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (writeBytes bs k.toNat (Enc.encode w)) = pure s') :
    FTotalTriple (up (pts q a s)) (Zig.store b (q.add k) w) (fun _ => up (pts q a s')) := by
  have t := FTotalTriple.field_storeAt (q := q) w hn hb ho hfit hw
  rwa [Int.toNat_of_nonneg h0] at t

/-- `field_loadAt` at byte 0. -/
theorem FTotalTriple.field_load0 {s : T} {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a)
    (hfit : Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract 0 (Enc.size U)) = pure v) :
    FTotalTriple (up (pts q a s)) (Zig.load U b q) (fun x => ⟪x = v⟫ ⋆ up (pts q a s)) := by
  have t := FTotalTriple.field_loadAt (T := T) (q := q) (o := 0) hn hb (Nat.dvd_zero b) (by omega)
    (fun bs hs hd => by rw [Nat.zero_add]; exact hv bs hs hd)
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

/-- `field_storeAt` at byte 0. -/
theorem FTotalTriple.field_store0 [LawfulEnc U] {s s' : T} (w : U) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (hfit : Enc.size U ≤ Enc.size T)
    (hw : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (writeBytes bs 0 (Enc.encode w)) = pure s') :
    FTotalTriple (up (pts q a s)) (Zig.store b q w) (fun _ => up (pts q a s')) := by
  have t := FTotalTriple.field_storeAt (T := T) (q := q) (o := 0) w hn hb (Nat.dvd_zero b) (by omega) hw
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

/-! ### Fields by `EncField` (`@[fsym]`)

The field rules with the field's value from its `EncField` (`AutoRules.lean`): a read gives
`get s`, a write `set s w`. `fsym` derives the `EncField` of the structs of generated code (and
of `Slice`), a field of a field included, so a stored struct is read and written whole and by
field alike. -/

/-- **Load of a field** `get s`. -/
@[fsym] theorem FTotalTriple.encField_load {k : Int} {s : T} {get : T → U} {set : T → U → T}
    (hf : EncField T U k.toNat get set) (hn : 0 < Enc.size U) (hb : b ∣ a) (h0 : 0 ≤ k)
    (ho : b ∣ k.toNat) :
    FTotalTriple (up (pts q a s)) (Zig.load U b (q.add k)) (fun x => ⟪x = get s⟫ ⋆ up (pts q a s)) :=
  FTotalTriple.field_load hn hb h0 ho hf.fit fun _ hs hd => hf.get_dec hs hd

/-- **Store of a field**: the value becomes `set s w`. -/
@[fsym] theorem FTotalTriple.encField_store [LawfulEnc U] {k : Int} {s : T} {get : T → U}
    {set : T → U → T} (w : U) (hf : EncField T U k.toNat get set) (hn : 0 < Enc.size U)
    (hb : b ∣ a) (h0 : 0 ≤ k) (ho : b ∣ k.toNat) :
    FTotalTriple (up (pts q a s)) (Zig.store b (q.add k) w) (fun _ => up (pts q a (set s w))) :=
  FTotalTriple.field_store w hn hb h0 ho hf.fit fun _ hs hd =>
    hf.set_dec hs hd (LawfulEnc.size_encode w) (LawfulEnc.decode_encode w)

/-- `encField_load` at byte 0. -/
@[fsym] theorem FTotalTriple.encField_load0 {s : T} {get : T → U} {set : T → U → T}
    (hf : EncField T U 0 get set) (hn : 0 < Enc.size U) (hb : b ∣ a) :
    FTotalTriple (up (pts q a s)) (Zig.load U b q) (fun x => ⟪x = get s⟫ ⋆ up (pts q a s)) :=
  FTotalTriple.field_load0 hn hb (by have := hf.fit; omega) fun _ hs hd => by
    simpa using hf.get_dec hs hd

/-- `encField_store` at byte 0. -/
@[fsym] theorem FTotalTriple.encField_store0 [LawfulEnc U] {s : T} {get : T → U}
    {set : T → U → T} (w : U) (hf : EncField T U 0 get set) (hn : 0 < Enc.size U) (hb : b ∣ a) :
    FTotalTriple (up (pts q a s)) (Zig.store b q w) (fun _ => up (pts q a (set s w))) :=
  FTotalTriple.field_store0 w hn hb (by have := hf.fit; omega) fun _ hs hd =>
    hf.set_dec hs hd (LawfulEnc.size_encode w) (LawfulEnc.decode_encode w)

end Bytes

/-! ## Payloads of error unions -/

section ErrUnion

variable {α : Type} [Enc α] {q : Ptr} {a b : Nat} {x : α}

/-- **Load of the payload** of an error union that holds `.ok x`, through its payload pointer. -/
@[fsym] theorem FTotalTriple.errPayload_load (hn : 0 < Enc.size α) (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) :
    FTotalTriple (up (pts q a (Except.ok x : Except ErrName α))) (Zig.load α b (errPayloadPtr α q))
      (fun r => ⟪r = x⟫ ⋆ up (pts q a (Except.ok x : Except ErrName α))) :=
  FTotalTriple.field_loadAt hn hb hpo (errUnion_bounds _ _).2.1 fun _ _ h => (errUnion_decode_ok h).2

/-- **Store of the payload** of an error union that holds `.ok x`: it then holds `.ok y` (the
error code is not written). -/
@[fsym] theorem FTotalTriple.errPayload_store [LawfulEnc α] (y : α) (hn : 0 < Enc.size α)
    (hb : b ∣ a) (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) :
    FTotalTriple (up (pts q a (Except.ok x : Except ErrName α))) (Zig.store b (errPayloadPtr α q) y)
      (fun _ => up (pts q a (Except.ok y : Except ErrName α))) :=
  FTotalTriple.field_storeAt y hn hb hpo (errUnion_bounds _ _).2.1 fun _ hs h =>
    errUnion_decode_setPayload y hs (errUnion_decode_ok h).1

end ErrUnion

/-! ## Owned bytes (locality in a thread, `ThreadStep.lean`) -/

section Thread

variable {T : Type} [Enc T] {q : Ptr} {a : Nat}

/-- The bytes `[k, k + n)` of a typed value. -/
theorem OwnsPtr.pts_add {s : T} {k n : Nat} (hk : k + n ≤ Enc.size T) :
    OwnsPtr (up (Zig.pts q a s)) (q.add k) n := by
  rintro b hb r ⟨⟨_, _, _, bs, -, hs, -, hbt, -⟩, hk', hg⟩
  exact OwnsPtr.bytesAt_add (by omega) b hb r ⟨hbt, hk', hg⟩

end Thread

/-! ## Read-only fields -/

section Const

variable {p : Ptr} {φ : Nat → Array Byte → Prop} {P : FAssn}

/-- **A part of known `const` bytes**: the `n` bytes from byte `o` on. -/
theorem ConstAt.add {o n : Nat} (h : ConstAt p φ P) (hn : 0 < n)
    (hfit : ∀ A bs, φ A bs → o + n ≤ bs.size) :
    ConstAt (p.add o) (fun A bs' => 0 ≤ p.off ∧ ∃ bs, φ A bs ∧ bs' = bs.extract o (o + n)) P :=
  fun m r rF hh hp => by
    obtain ⟨b, blk, bs, hpb, hblk, hk, hl, h0, -, hφ, hx⟩ := h m r rF hh hp
    have hf := hfit _ _ hφ
    have hoff : (p.add o).off.toNat = p.off.toNat + o := by simp [Ptr.add]; omega
    refine ⟨b, blk, bs.extract o (o + n), by simpa [Ptr.add] using hpb, hblk, hk, hl,
      by simp [Ptr.add]; omega, by simp; omega, ⟨h0, bs, hφ, rfl⟩, fun i hi => ?_⟩
    simp only [Array.size_extract] at hi
    rw [hoff, Nat.add_assoc, hx (o + i) (by omega)]
    simp [Array.getElem_extract]

/-- **Load of a read-only field**: a `U` at byte `o` of a `const` typed value `s`, where every
byte string of `s` holds `v`; the knowledge stays. -/
theorem FTotalTriple.cfield_loadAt {T U : Type} [Enc T] [Enc U] {a b o : Nat} {s : T} {v : U}
    (hn : 0 < Enc.size U) (hb : b ∣ a) (ho : b ∣ o) (hfit : o + Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract o (o + Enc.size U)) = pure v) :
    FTotalTriple (cpts p a s) (Zig.load U b (p.add o)) (fun x => ⟪x = v⟫ ⋆ cpts p a s) :=
  FTotalTriple.load_const ((ConstAt.cpts (by omega)).add hn fun _ _ h => by omega)
    fun A _ ⟨h0, bs, ⟨ha, hs, hd⟩, e⟩ => by
      subst e
      refine ⟨?_, by simp; omega, hv bs hs hd⟩
      have hoff : (p.add o).off.toNat = p.off.toNat + o := by simp [Ptr.add]; omega
      rw [hoff, ← Nat.add_assoc]
      exact mod_add_dvd ha hb ho

/-- `cfield_loadAt` at the offset `k` of generated code. -/
theorem FTotalTriple.cfield_load {T U : Type} [Enc T] [Enc U] {a b : Nat} {k : Int} {s : T}
    {v : U} (hn : 0 < Enc.size U) (hb : b ∣ a) (h0 : 0 ≤ k) (ho : b ∣ k.toNat)
    (hfit : k.toNat + Enc.size U ≤ Enc.size T)
    (hv : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      Enc.decode (bs.extract k.toNat (k.toNat + Enc.size U)) = pure v) :
    FTotalTriple (cpts p a s) (Zig.load U b (p.add k)) (fun x => ⟪x = v⟫ ⋆ cpts p a s) := by
  have t := FTotalTriple.cfield_loadAt (p := p) hn hb ho hfit hv
  rwa [Int.toNat_of_nonneg h0] at t

end Const

end Full
end Zig
