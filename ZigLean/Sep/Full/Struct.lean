import ZigLean.Sep.Full.Parts
import ZigLean.Sep.Full.Arr

/-!
# Structs in the full-state logic (engine ledger rows #78, #79)

A struct's encoding, as the translator writes it (`Enc.fields N [(o, Enc.encode x), …]`, decoded
field by field with `Enc.decodeAt`), is described once for all structs by a `StructLayout`: its
bytes `[0, N)` cut, in address order, into **pieces**, each a field (`SField`: its type's
encoding, offset, the alignment its `pts` claims, its value) or a gap of padding. The layout says
that the bytes of an encoding hold each field (`get`) and that bytes holding each field decode to
the struct (`join`: the decoding reads no padding byte). Everything else is stated once here:

* `StructLayout.lawfulEnc`: a struct whose encoding holds its fields' encodings, all of lawful
  types, reads back what it writes (`LawfulEnc`, row #78);
* `StructLayout.split`: a struct's `pts` is its pieces (`piecesF`): each field's `pts` and each
  gap's bytes (row #79);
* `pts_fold_encode`, `pts_fold_write` (`@[fsym_view]`): owned bytes that are a lawful value's
  encoding (a stored struct) are that value's `pts` (row #78).

**Padding.** `Enc.fields` writes `.undef` into padding and the generated decoding never reads it,
so `decode (encode v) = v` holds with padding, and a `pts` (existential over its bytes) does not
pin padding bytes. A split gives each gap as `padBytes` (owned bytes of any content, not a
`const` global), which a join needs back.

The per-struct obligations (`StructLayout`'s fields, the encoding's pieces) are discharged by
`fsym` for any struct the translator generates, from the decoding it reads (`structFields?`,
`encFieldOf?`); a struct of another shape (packed, a union, a storage-wrapped field) gets no
layout, so these rules do not apply to it (fail closed).
-/

namespace Zig.Full

open FAssn

/-- A field of a struct value: its type's encoding, its offset, the alignment its `pts` claims and
its value. -/
structure SField : Type 1 where
  U : Type
  enc : Enc U
  off : Nat
  al : Nat
  val : U

namespace SField

/-- The field's size. -/
def size (f : SField) : Nat := @Enc.size f.U f.enc

/-- The field's bytes of the struct's bytes `bs` decode to its value. -/
def Dec (f : SField) (bs : Array Byte) : Prop :=
  @Enc.decode f.U f.enc (bs.extract f.off (f.off + f.size)) = pure f.val

end SField

/-- `n` owned bytes at `q` of any content, not of a `const` global (a struct's padding). -/
def padBytes (q : Ptr) (n : Nat) : Assn := fun h =>
  ∃ A S K bs, bs.size = n ∧ K ≠ .constGlobal ∧ bytesAt q A S K bs h

/-- A piece of a struct's bytes: a field, or a gap of padding (offset, size). -/
inductive SPiece : Type 1
  | field (f : SField)
  | gap (off n : Nat)

namespace SPiece

def off : SPiece → Nat
  | .field f => f.off
  | .gap o _ => o

def size : SPiece → Nat
  | .field f => f.size
  | .gap _ n => n

/-- The alignment that the piece's assertion claims (a gap claims none). -/
def al : SPiece → Nat
  | .field f => f.al
  | .gap _ _ => 1

/-- The piece's bytes of the struct's bytes `bs` hold it (a gap: any bytes). -/
def Dec : SPiece → Array Byte → Prop
  | .field f, bs => f.Dec bs
  | .gap _ _, _ => True

/-- The piece of the struct's encoding `bs` is its field's encoding, of a lawful type. -/
def Encd (bs : Array Byte) : SPiece → Prop
  | .field f => bs.extract f.off (f.off + f.size) = @Enc.encode f.U f.enc f.val ∧
      @LawfulEnc f.U f.enc
  | .gap _ _ => True

/-- The piece of a struct at `p`: its field's `pts`, or its gap's bytes. -/
def assn (p : Ptr) : SPiece → Assn
  | .field f => @Zig.pts f.U f.enc (p.add f.off) f.al f.val
  | .gap o n => padBytes (p.add o) n

/-- The piece as an atom of the full-state logic. -/
def atom (p : Ptr) (x : SPiece) : FAssn := up (x.assn p)

theorem dec_of_encd {bs : Array Byte} : ∀ {x : SPiece}, x.Encd bs → x.Dec bs
  | .field f, ⟨he, hl⟩ => by
    show @Enc.decode f.U f.enc (bs.extract f.off (f.off + f.size)) = pure f.val
    rw [he]; exact @LawfulEnc.decode_encode f.U f.enc hl f.val
  | .gap _ _, _ => trivial

end SPiece

/-- Every item of the list has `P`. -/
def All {α : Type 1} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ All P xs

theorem All.imp {α : Type 1} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ {xs : List α}, All P xs → All Q xs
  | [], _ => trivial
  | _ :: _, ⟨hx, hxs⟩ => ⟨h _ hx, All.imp h hxs⟩

/-- The ranges `(offset, size)` tile the bytes `[c, N)` in address order, each nonempty. -/
def Tiles (N : Nat) : Nat → List (Nat × Nat) → Bool
  | c, [] => c == N
  | c, (o, n) :: ps => o == c && decide (0 < n) && Tiles N (c + n) ps

theorem Tiles.le {N : Nat} : ∀ {c : Nat} {ps : List (Nat × Nat)}, Tiles N c ps = true → c ≤ N
  | c, [], h => by simp only [Tiles, beq_iff_eq] at h; omega
  | c, (o, n) :: ps, h => by
    simp only [Tiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have := Tiles.le h.2; omega

/-- The pieces of a struct at `p`, as one heap assertion. -/
def piecesA (p : Ptr) : List SPiece → Assn
  | [] => Assn.emp
  | x :: xs => x.assn p ∗ piecesA p xs

/-- The pieces of a struct at `p`, one atom each (what a split gives and a join takes). -/
def piecesF (p : Ptr) : List SPiece → FAssn
  | [] => FAssn.emp
  | [x] => x.atom p
  | x :: y :: ys => x.atom p ⋆ piecesF p (y :: ys)

theorem up_piecesF {p : Ptr} : ∀ {ps : List SPiece} {r : Res}, up (piecesA p ps) r → piecesF p ps r
  | [], _, h => up_emp.mp h
  | [_], _, h => up_imp (fun _ hh => Zig.sep_emp.mp hh) h
  | _ :: _ :: _, _, h => sep_mono_right (fun _ h' => up_piecesF h') (up_sep h)

/-- **A struct's layout** (`T`'s encoding of size `N = Enc.size T`): the pieces of each value in
address order, with a shape (offset, size, alignment) that no value changes and that tiles the
bytes; the bytes of every encoding hold each piece (`get`), and bytes that hold each piece decode
to the value (`join`). `fsym` derives it for the structs the translator generates. -/
structure StructLayout (T : Type) [Enc T] : Type 1 where
  pieces : T → List SPiece
  shape : List (Nat × Nat × Nat)
  shape_eq : ∀ v, (pieces v).map (fun x => (x.off, x.size, x.al)) = shape
  tiles : Tiles (Enc.size T) 0 (shape.map fun x => (x.1, x.2.1)) = true
  get : ∀ bs v, bs.size = Enc.size T → Enc.decode bs = pure v → All (·.Dec bs) (pieces v)
  join : ∀ bs v, bs.size = Enc.size T → All (·.Dec bs) (pieces v) → Enc.decode bs = pure v

namespace StructLayout

variable {T : Type} [Enc T] (L : StructLayout T)

theorem tiles_of (v : T) :
    Tiles (Enc.size T) 0 ((L.pieces v).map fun x => (x.off, x.size)) = true := by
  have e : (L.pieces v).map (fun x => (x.off, x.size)) = L.shape.map fun x => (x.1, x.2.1) := by
    rw [← L.shape_eq v, List.map_map]; rfl
  rw [e]; exact L.tiles

/-- **A struct's encoding reads back** (row #78): its size is the type's, and each field piece of
it is that field's encoding, of a lawful type. -/
theorem lawfulEnc (hsize : ∀ v : T, (Enc.encode v).size = Enc.size T)
    (henc : ∀ v : T, All (SPiece.Encd (Enc.encode v)) (L.pieces v)) : LawfulEnc T where
  size_encode := hsize
  decode_encode v := L.join _ v (hsize v) (All.imp (fun _ h => SPiece.dec_of_encd h) (henc v))

end StructLayout

/-! ## Splitting a struct's `pts` into its pieces -/

section Split

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {a N : Nat}

/-- A piece at byte `c` from owned bytes that hold it there. -/
theorem SPiece.assn_of_bytes (hK : K ≠ .constGlobal) (hA : (A + p.off.toNat) % a = 0)
    (h0 : 0 ≤ p.off) (hN : bs.size = N) :
    ∀ {x : SPiece} {c : Nat} {h : Heap}, x.off = c → c + x.size ≤ N → x.al ∣ a ∧ x.al ∣ x.off →
      x.Dec bs → bytesAt (p.add c) A S K (bs.extract c (c + x.size)) h → x.assn p h
  | .field f, c, h, hc, hle, ⟨ha, ho⟩, hd, hb => by
    simp only [SPiece.off] at hc
    subst hc
    refine ⟨A, S, K, bs.extract f.off (f.off + f.size), ?_, ?_, hd, hb, hK⟩
    · have e : (p.add f.off).off.toNat = p.off.toNat + f.off := by simp only [Ptr.add]; omega
      rw [e, ← Nat.add_assoc]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans ha (Nat.dvd_of_mod_eq_zero hA)) ho)
    · simp only [SPiece.size] at hle
      show (bs.extract f.off (f.off + f.size)).size = f.size
      simp only [Array.size_extract]; omega
  | .gap o n, c, h, hc, hle, _, _, hb => by
    simp only [SPiece.off] at hc
    subst hc
    simp only [SPiece.size] at hle hb
    exact ⟨A, S, K, _, by simp only [Array.size_extract]; omega, hK, hb⟩

theorem split_aux (hK : K ≠ .constGlobal) (hA : (A + p.off.toNat) % a = 0) (h0 : 0 ≤ p.off)
    (hN : bs.size = N) :
    ∀ (ps : List SPiece) (c : Nat) (h : Heap), Tiles N c (ps.map fun x => (x.off, x.size)) = true →
      All (fun x => x.al ∣ a ∧ x.al ∣ x.off) ps → All (·.Dec bs) ps →
      bytesAt (p.add c) A S K (bs.extract c N) h → piecesA p ps h
  | [], c, h, ht, _, _, hb => by
    simp only [List.map, Tiles, beq_iff_eq] at ht
    subst ht
    exact bytesAt_heap_empty hb (by simp only [Array.size_extract]; omega)
  | x :: ps, c, h, ht, ⟨hal, hals⟩, ⟨hd, hds⟩, hb => by
    simp only [List.map, Tiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
    obtain ⟨⟨hoc, -⟩, ht⟩ := ht
    have hle := Tiles.le ht
    obtain ⟨h₁, h₂, hdj, he, hb₁, hb₂⟩ := bytesAt_split hb (k := x.size)
      (by simp only [Array.size_extract]; omega)
    have e₁ : (bs.extract c N).extract 0 x.size = bs.extract c (c + x.size) := by
      simp only [Array.extract_extract]; congr 1 <;> omega
    have e₂ : (bs.extract c N).extract x.size (bs.extract c N).size = bs.extract (c + x.size) N := by
      simp only [Array.extract_extract, Array.size_extract]; congr 1 <;> omega
    rw [e₁] at hb₁
    rw [e₂, Ptr.add_add, ← Int.natCast_add] at hb₂
    exact ⟨h₁, h₂, hdj, he, SPiece.assn_of_bytes hK hA h0 hN hoc hle hal hd hb₁,
      split_aux hK hA h0 hN ps _ h₂ ht hals hds hb₂⟩

theorem all_of_shape {Q : Nat × Nat × Nat → Bool} :
    ∀ {ps : List SPiece}, ((ps.map fun x => (x.off, x.size, x.al)).all Q) = true →
      All (fun x => Q (x.off, x.size, x.al) = true) ps
  | [], _ => trivial
  | _ :: _, h => by
    simp only [List.map, List.all_cons, Bool.and_eq_true] at h
    exact ⟨h.1, all_of_shape h.2⟩

/-- **A struct's `pts` is its pieces** (row #79): each field's `pts` at its offset, at the
alignment the layout gives it (dividing the struct's and the field's offset: a decided check),
and each gap's bytes. -/
theorem StructLayout.split {T : Type} [Enc T] (L : StructLayout T) {v : T}
    (hal : (L.shape.all fun x => a % x.2.2 == 0 && x.1 % x.2.2 == 0) = true) :
    EUpd (up (Zig.pts p a v)) (piecesF p (L.pieces v)) :=
  EUpd.of_imp fun r hr => by
    obtain ⟨A, S, K, bs, ⟨ha, hs, hv, hK⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
    have h0 : 0 ≤ p.off := by obtain ⟨_, _, h0, _⟩ := hb.1; exact h0
    rw [← L.shape_eq v] at hal
    have hal' := All.imp (Q := fun x : SPiece => x.al ∣ a ∧ x.al ∣ x.off) (fun (x : SPiece) (hx : (a % x.al == 0 && x.off % x.al == 0) = true) => by
        simp only [Bool.and_eq_true, beq_iff_eq] at hx
        exact ⟨Nat.dvd_of_mod_eq_zero hx.1, Nat.dvd_of_mod_eq_zero hx.2⟩)
      (all_of_shape hal)
    have hb' : bytesAt (p.add ((0 : Nat) : Int)) A S K (bs.extract 0 (Enc.size T)) r.heap.erase := by
      rw [← hs, Array.extract_size]; simpa using hb.1
    exact up_piecesF ⟨split_aux hK ha h0 hs (L.pieces v) 0 _ (L.tiles_of v) hal'
      (L.get bs v hs hv) hb', hb.2⟩

end Split

/-! ## Folding a stored value's bytes into its `pts` (`@[fsym_view]`) -/

section Fold

variable {T : Type} [Enc T] [LawfulEnc T] {p : Ptr} {A S a : Nat} {K : BlockKind} {v : T}

/-- **Owned bytes that are a lawful value's encoding are its `pts`** (row #78). -/
@[fsym_view] theorem pts_fold_encode (ha : (A + p.off.toNat) % a = 0) (hK : K ≠ .constGlobal) :
    EUpd (up (bytesAt p A S K (Enc.encode v))) (up (Zig.pts p a v)) :=
  EUpd.of_imp fun _ h => FTotalTriple.up_pts_iff_bytesAt.mpr
    ⟨A, S, K, _, ⟨ha, LawfulEnc.size_encode v, LawfulEnc.decode_encode v, hK⟩, h⟩

/-- **A value stored over all of a block's bytes is its `pts`** (`FTotalTriple.storeBlock`'s
post, the bytes exactly the value's size). -/
@[fsym_view] theorem pts_fold_write {bs : Array Byte} (hs : bs.size = Enc.size T)
    (ha : (A + p.off.toNat) % a = 0) (hK : K ≠ .constGlobal) :
    EUpd (up (bytesAt p A S K (writeBytes bs 0 (Enc.encode v)))) (up (Zig.pts p a v)) := by
  rw [writeBytes_all (by rw [LawfulEnc.size_encode v, hs])]
  exact pts_fold_encode ha hK

end Fold

end Zig.Full
