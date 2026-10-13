import ZigLean.Sep.Full.AtomicPlain
import ZigLean.Sep.Full.OwnedBound

/-!
# Plain accesses of owned words with any tag constraint (`wpts`)

`wpts p v` (`Atomic.lean`) is an owned 8-aligned word holding `v` whose bytes carry **some** tag
constraint `tg`: what is true of a word in memory that some allocator handed out as a plain
region (the arena's node headers, `tests/roadmap/alloc-arena/HeaderTagCX.lean`: an older atomic
location of another size may lie over the bytes, and plain stores keep it). Every atomic rule
takes a `wpts` (`FTriple.atomicLoadW`, `cmpxchgHitW`, …) and leaves an `apts`. The plain rules
below keep the word's constraint, as `AtomicPlain.lean`'s do for `apts`:

* `wpts_load`, `wpts_store` (`@[fsym]`): a plain load and store of the word;
* `wpts_loadPacked`, `wpts_storePacked` (`@[fsym]`): of a packed struct over it;
* `wpts_view` (`@[fsym_view]`): the word as a region of its 8 bytes;
* `wpts_of_region`: back from such a region (its constraints dropped, `Holds.untag`): an update,
  not a view, since `fsym` would otherwise go round in circles;
* `facts_wpts` (`@[fsym_facts]`): its block and a nonnegative offset; `OwnsList.wpts`: its 8
  bytes, for `Holds.owned_length_le`.
-/

namespace Zig.Full

open FAssn

section Words

variable {p : Ptr} {al : Nat}

/-- An owned word with any tag constraint: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem facts_wpts {v : BitVec 64} :
    Auto.AtomFacts (wpts p v) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨-, -, -, -, -, -, -, -, -, -, -, b, hb, h0, -⟩; exact ⟨⟨b, hb⟩, h0⟩

namespace FTotalTriple

/-- **Plain load of a word** with any tag constraint: the word keeps it. -/
@[fsym] theorem wpts_load {v : BitVec 64} (hal : al ∣ 8) :
    FTotalTriple (wpts p v) (Zig.load (BitVec 64) al p) (fun x => ⟪x = v⟫ ⋆ wpts p v) :=
  of_cases fun _ ⟨A, S, K, bs, tg, ha, hK, hsz, hv, hab⟩ => by
    have t := load_abytesAt (q := p) (k := 0) (al := al) (A := A) (S := S) (K := K) (bs := bs)
      (tg := tg) (v := v) (by decide) (by rw [hsz]; decide)
      (mod_add_dvd ha hal (Nat.dvd_zero al))
      (by rw [Nat.zero_add, show Enc.size (BitVec 64) = bs.size by rw [hsz]; rfl,
        Array.extract_size]; exact hv)
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, hab, fun x _ h => by
      obtain ⟨hx, hab'⟩ := sep_lift.mp h
      exact sep_lift.mpr ⟨hx, A, S, K, bs, tg, ha, hK, hsz, hv, hab'⟩⟩

/-- **Plain store of a word** into a word with any tag constraint: it keeps the constraint. -/
@[fsym] theorem wpts_store {v : BitVec 64} (x : BitVec 64) (hal : al ∣ 8) :
    FTotalTriple (wpts p v) (Zig.store al p x) (fun _ => wpts p x) :=
  of_cases fun _ ⟨A, S, K, bs, tg, ha, hK, hsz, _, hab⟩ => by
    have hc : (Enc.encode x).size = 8 := LawfulEnc.size_encode x
    have t := storeBytes_abytesAt (q := p) (k := 0) (al := al) (A := A) (S := S) (K := K)
      (bs := bs) (tg := tg) (bs' := Enc.encode x) (by omega) (by omega)
      (mod_add_dvd ha hal (Nat.dvd_zero al)) hK
    simp only [Int.natCast_zero, Ptr.add_zero, writeBytes_all (hc.trans hsz.symm)] at t
    exact ⟨_, _, t, hab, fun _ _ h => ⟨A, S, K, _, tg, ha, hK, hc, LawfulEnc.decode_encode x, h⟩⟩

/-- **Plain load of a packed struct** over a word with any tag constraint (`apts_loadPacked`). -/
@[fsym] theorem wpts_loadPacked {T : Type} [Enc T] [Packed T 64] {v : BitVec 64}
    (hd : (Enc.decode : Array Byte → Result T) =
      fun bs => (Enc.decode bs : Result (BitVec 64)) >>= Packed.ofBits?)
    (hs : Enc.size T = 8) (hval : Packed.valid (α := T) v = true) (hal : al ∣ 8) :
    FTotalTriple (wpts p v) (Zig.load T al p) (fun x => ⟪x = Packed.ofBits v⟫ ⋆ wpts p v) :=
  of_cases fun _ ⟨A, S, K, bs, tg, ha, hK, hsz, hv, hab⟩ => by
    have hv' : (Enc.decode bs : Result T) = pure (Packed.ofBits v) := by
      rw [hd]
      show (intOfBytes 64 bs >>= Packed.ofBits?) = _
      rw [hv]
      show Packed.ofBits? v = _
      simp [Packed.ofBits?, hval]
    have t := load_abytesAt (q := p) (k := 0) (al := al) (A := A) (S := S) (K := K) (bs := bs)
      (tg := tg) (v := Packed.ofBits (α := T) v) (by omega) (by omega)
      (mod_add_dvd ha hal (Nat.dvd_zero al))
      (by rw [Nat.zero_add, hs, ← hsz, Array.extract_size]; exact hv')
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    exact ⟨_, _, t, hab, fun x _ h => by
      obtain ⟨hx, hab'⟩ := sep_lift.mp h
      exact sep_lift.mpr ⟨hx, A, S, K, bs, tg, ha, hK, hsz, hv, hab'⟩⟩

/-- **Plain store of a packed struct** into a word with any tag constraint (`apts_storePacked`). -/
@[fsym] theorem wpts_storePacked {T : Type} [Enc T] [Packed T 64] {v : BitVec 64} (w : T)
    (he : (Enc.encode : T → Array Byte) = fun x => Enc.encode (Packed.toBits x)) (hal : al ∣ 8) :
    FTotalTriple (wpts p v) (Zig.store al p w) (fun _ => wpts p (Packed.toBits w)) := by
  have e : Zig.store al p w = Zig.store al p (Packed.toBits w) := by
    show Zig.storeBytes p al (Enc.encode w) = Zig.storeBytes p al (Enc.encode (Packed.toBits w))
    rw [he]
  rw [e]; exact wpts_store _ hal

end FTotalTriple

/-- **A word as a region** of its 8 bytes, which hold it (`apts_view`). -/
@[fsym_view] theorem wpts_view {v : BitVec 64} :
    EUpd (wpts p v) (FAssn.ex fun A => FAssn.ex fun S => FAssn.ex fun K => FAssn.ex fun bs =>
      ⟪bs.size = 8 ∧ intOfBytes 64 bs = pure v⟫ ⋆ up (regionIn p A S K 8 bs)) :=
  EUpd.of_imp fun _ ⟨A, S, K, bs, _, ha, hK, hsz, hv, hab⟩ =>
    have hb := up_of_abytesAt hab
    ⟨A, S, K, bs, sep_lift.mpr ⟨⟨hsz, hv⟩, ⟨ha, hK, hb.1⟩, hb.2⟩⟩

/-- **A region of 8 bytes is a word** with any tag constraint: its constraints dropped
(`Holds.untag`), whatever the atomic layout over it. -/
theorem wpts_of_region {A S : Nat} {K : BlockKind} {bs : Array Byte} {v : BitVec 64}
    (hsz : bs.size = 8) (hv : intOfBytes 64 bs = pure v) :
    EUpd (up (regionIn p A S K 8 bs)) (wpts p v) := fun _ r _ hh h _ =>
  ⟨r.untag, hh.untag, wpts_of_up h.1.1 h.1.2.1 hsz hv ⟨h.1.2.2, h.2⟩⟩

/-- A word with any tag constraint owns its 8 bytes (`OwnedBound.lean`). -/
theorem OwnsList.wpts {b : BlockId} {v : BitVec 64} (hb : p.block = some b) :
    OwnsList (locRange b p.off.toNat 8) (wpts p v) := by
  rintro r ⟨A, S, K, bs, tg, -, -, hs, -, hab⟩
  exact hs ▸ ownsList_bytes hb (abytesAt_bytesAt hab)

end Words

end Zig.Full
