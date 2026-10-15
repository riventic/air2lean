import ZigLean.Sep.Full.Parts
import ZigLean.Sep.Full.Arr

/-!
# Structs in the full-state logic (engine ledger rows #78, #79)

A struct's encoding, as the translator writes it (`Enc.fields N [(o, Enc.encode x), …]`, decoded
field by field with `Enc.decodeAt`), is described once for all structs by a `StructLayout`: its
bytes `[0, N)` cut, in address order, into **pieces**, each a field (`SField`: its type's
encoding, offset, the alignment its `pts` claims, its value) or a gap of padding. The layout says
that the bytes of an encoding hold each field (`get`) and that bytes holding each field decode to
the struct (`of_pieces`: the decoding reads no padding byte). Everything else is stated once here:

* `StructLayout.lawfulEnc`: a struct whose encoding holds its fields' encodings, all of lawful
  types, reads back what it writes (`LawfulEnc`, row #78);
* `StructLayout.split`: a struct's `pts` is its pieces (`piecesF`): each field's `pts` and each
  gap's bytes (row #79);
* `StructLayout.join`: the converse, the pieces' labels read from the memory (row #79);
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

/-- The pointer `o` bytes past `p`, `p` itself at `0` (as a specification writes a struct's first
field: `pts p …`, not `pts (p.add 0) …`). -/
def pieceAt (p : Ptr) (o : Nat) : Ptr := if o = 0 then p else p.add o

theorem pieceAt_eq (p : Ptr) (o : Nat) : pieceAt p o = p.add o := by
  unfold pieceAt; split <;> simp_all

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
  | .field f => @Zig.pts f.U f.enc (pieceAt p f.off) f.al f.val
  | .gap o n => padBytes (pieceAt p o) n

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
to the value (`of_pieces`). `fsym` derives it for the structs the translator generates. -/
structure StructLayout (T : Type) [Enc T] : Type 1 where
  pieces : T → List SPiece
  shape : List (Nat × Nat × Nat)
  shape_eq : ∀ v, (pieces v).map (fun x => (x.off, x.size, x.al)) = shape
  tiles : Tiles (Enc.size T) 0 (shape.map fun x => (x.1, x.2.1)) = true
  get : ∀ bs v, bs.size = Enc.size T → Enc.decode bs = pure v → All (·.Dec bs) (pieces v)
  of_pieces : ∀ bs v, bs.size = Enc.size T → All (·.Dec bs) (pieces v) → Enc.decode bs = pure v

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
  decode_encode v := L.of_pieces _ v (hsize v) (All.imp (fun _ h => SPiece.dec_of_encd h) (henc v))

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
    show @Zig.pts f.U f.enc (pieceAt p f.off) f.al f.val h
    rw [pieceAt_eq]
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
    show padBytes (pieceAt p o) n h
    rw [pieceAt_eq]
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

/-! ## Joining a struct's pieces into its `pts` -/

section Join

variable {p : Ptr} {a N : Nat}

theorem SizeFree.padBytes (q : Ptr) (n : Nat) : SizeFree (fun _ => none) (padBytes q n) := by
  intro h h' ⟨A, S, K, bs, hs, hK, hb⟩ hn hE hco
  obtain ⟨A', S', K', hK', hb'⟩ := SizeFree.bytesAt_ex (p := q) (bs := bs)
    (φ := fun _ _ K => K ≠ .constGlobal)
    (fun A S K S' K' h2 hk e => h2 (by subst e; cases K <;> simp_all [BlockKind.norm]))
    h h' ⟨A, S, K, hK, hb⟩ hn hE hco
  exact ⟨A', S', K', bs, hs, hK', hb'⟩

theorem SizeFree.piecesA (p : Ptr) : ∀ ps : List SPiece, SizeFree (fun _ => none) (piecesA p ps)
  | [] => SizeFree.emp
  | .field f :: ps => SizeFree.sep (@SizeFree.pts f.U f.enc _ _ _) (SizeFree.piecesA p ps)
  | .gap _ _ :: ps => SizeFree.sep (SizeFree.padBytes _ _) (SizeFree.piecesA p ps)

theorem piecesF_up : ∀ {ps : List SPiece} {r : Res}, piecesF p ps r → up (piecesA p ps) r
  | [], _, h => up_emp.mpr h
  | [_], _, h => up_imp (fun _ hh => Zig.sep_emp.mpr hh) h
  | _ :: _ :: _, _, h => sep_up (sep_mono_right (fun _ h' => piecesF_up h') h)

theorem All.imp₂ {α : Type 1} {P Q R : α → Prop} (h : ∀ x, P x → Q x → R x) :
    ∀ {xs : List α}, All P xs → All Q xs → All R xs
  | [], _, _ => trivial
  | _ :: _, ⟨hp, hps⟩, ⟨hq, hqs⟩ => ⟨h _ hp hq, All.imp₂ h hps hqs⟩

theorem All.exists_of_any {α : Type 1} {β : Type} {P : α → Prop} {f : α → β} {Q : β → Bool} :
    ∀ {xs : List α}, All P xs → ((xs.map f).any Q) = true → ∃ x, P x ∧ Q (f x) = true
  | [], _, h => by simp at h
  | x :: _, ⟨hp, hps⟩, h => by
    simp only [List.map, List.any_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨x, hp, h⟩
    · exact All.exists_of_any hps h

/-- The pieces after byte `c` start at or after it. -/
theorem Tiles.ge : ∀ {c : Nat} {ps : List SPiece},
    Tiles N c (ps.map fun x => (x.off, x.size)) = true → All (fun y => c ≤ y.off) ps
  | _, [], _ => trivial
  | c, _ :: _, h => by
    simp only [List.map, Tiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hoc, -⟩, ht⟩ := h
    exact ⟨by omega, All.imp (fun _ hy => by omega) (Tiles.ge ht)⟩

/-- A piece reads only its own bytes: bytes before it do not matter. -/
theorem SPiece.dec_shift {as bs cs : Array Byte} (hs : as.size = bs.size) :
    ∀ {x : SPiece}, as.size ≤ x.off → x.Dec (as ++ cs) → x.Dec (bs ++ cs)
  | .field f, ho, hd => by
    have e : ∀ zs : Array Byte, zs.size = as.size →
        (zs ++ cs).extract f.off (f.off + f.size) = cs.extract (f.off - as.size) (f.off + f.size - as.size) := by
      intro zs hz
      rw [Array.extract_append, hz]
      have : zs.extract f.off (f.off + f.size) = #[] := by
        apply Array.eq_empty_of_size_eq_zero; simp only [Array.size_extract]; simp only [SPiece.off] at ho; omega
      rw [this, Array.empty_append]
    show @Enc.decode f.U f.enc _ = _
    rw [e bs hs.symm]
    have hd' : @Enc.decode f.U f.enc ((as ++ cs).extract f.off (f.off + f.size)) = pure f.val := hd
    rwa [e as rfl] at hd'
  | .gap _ _, _, _ => trivial

/-- The pieces from byte `c` on, of heap `h`, part of the memory's heap: bytes `cs` from `c` on, with
the labels of the block, that hold each piece (bytes before `c` do not matter), each field
aligned as its `pts` says. -/
theorem join_aux {m : Mem} {b : BlockId} {blk : Block} (hpb : p.block = some b) (h0 : 0 ≤ p.off)
    (hblk : m.blocks[b]? = some blk) :
    ∀ (ps : List SPiece) (c : Nat) (h hF : Heap), m.heap = h ∪ hF →
      Tiles N c (ps.map fun x => (x.off, x.size)) = true → piecesA p ps h →
      ∃ cs : Array Byte, cs.size = N - c ∧
        bytesAt (p.add c) blk.addr blk.bytes.size blk.kind cs h ∧
        All (·.Dec (Array.replicate c .undef ++ cs)) ps ∧
        All (fun x => (blk.addr + (p.off.toNat + x.off)) % x.al = 0) ps
  | [], c, h, _, _, ht, hp => by
    simp only [List.map, Tiles, beq_iff_eq] at ht
    subst ht
    have he : h = Heap.empty := hp
    subst he
    refine ⟨#[], by simp, ⟨b, by simpa [Ptr.add] using hpb, by simp only [Ptr.add]; omega,
      fun l => by simp [Heap.empty]⟩, trivial, trivial⟩
  | x :: ps, c, _, hF, hm, ht, hp => by
    obtain ⟨h₁, h₂, hd, rfl, hx, hps⟩ := hp
    simp only [List.map, Tiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
    obtain ⟨⟨hoc, hpos⟩, ht⟩ := ht
    have hle := Tiles.le ht
    have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
    have hm₂ : m.heap = h₂ ∪ (h₁ ∪ hF) := by rw [hm, Heap.union_comm hd, Heap.union_assoc]
    obtain ⟨cs, hcs, hb, hdec, hal⟩ := join_aux hpb h0 hblk ps (c + x.size) h₂ (h₁ ∪ hF) hm₂ ht hps
    have hpc : (p.add c).block = some b := by simpa [Ptr.add] using hpb
    have hoff : (p.add c).off.toNat = p.off.toNat + c := by simp only [Ptr.add]; omega
    -- the piece's bytes, with the block's labels
    obtain ⟨xs, hxs, hbx, hdx, hax⟩ : ∃ xs : Array Byte, xs.size = x.size ∧
        bytesAt (p.add c) blk.addr blk.bytes.size blk.kind xs h₁ ∧
        x.Dec (Array.replicate c .undef ++ (xs ++ cs)) ∧
        (blk.addr + (p.off.toNat + x.off)) % x.al = 0 := by
      have emid : ∀ xs : Array Byte, (Array.replicate c Byte.undef ++ (xs ++ cs)).extract c
          (c + xs.size) = xs := by
        intro xs
        rw [← Array.append_assoc, Array.extract_append]
        simp [Array.extract_append]
      cases x with
      | field f =>
        obtain ⟨A, S, K, bs, ha, hs, hv, hbb, _⟩ := hx
        rw [pieceAt_eq] at ha hbb
        simp only [SPiece.off, SPiece.size] at hoc hpos ⊢
        subst hoc
        have hs' : bs.size = f.size := hs
        obtain ⟨rfl, -, -⟩ := bytesAt_metadata hbb hm₁ hpc hblk (by omega)
        refine ⟨bs, hs', bytesAt_retag_of_heap hbb hm₁ hpc hblk, ?_, ?_⟩
        · show @Enc.decode f.U f.enc _ = _
          rw [← hs', emid]; exact hv
        · rwa [hoff] at ha
      | gap o n =>
        obtain ⟨A, S, K, bs, hs, -, hbb⟩ := hx
        rw [pieceAt_eq] at hbb
        simp only [SPiece.off] at hoc
        subst hoc
        exact ⟨bs, hs, bytesAt_retag_of_heap hbb hm₁ hpc hblk, trivial, Nat.mod_one _⟩
    refine ⟨xs ++ cs, by simp only [Array.size_append]; omega, ?_, ⟨hdx, ?_⟩, ⟨hax, hal⟩⟩
    · refine bytesAt_append (h := h₁ ∪ h₂) ⟨h₁, h₂, hd, rfl, hbx, ?_⟩
      rw [Ptr.add_add, hxs, ← Int.natCast_add]; exact hb
    · refine All.imp₂ (fun y hy hge => ?_) hdec (Tiles.ge ht)
      rw [← Array.append_assoc]
      exact SPiece.dec_shift (by simp only [Array.size_append, Array.size_replicate]; omega)
        (by simp only [Array.size_replicate]; exact hge) hy

theorem SPiece.assn_bytes {h : Heap} : ∀ {x : SPiece}, x.assn p h →
    ∃ A S K bs, bs.size = x.size ∧ K ≠ .constGlobal ∧ bytesAt (p.add x.off) A S K bs h
  | .field _, ⟨A, S, K, bs, _, hs, _, hb, hK⟩ => ⟨A, S, K, bs, hs, hK, pieceAt_eq .. ▸ hb⟩
  | .gap _ _, ⟨A, S, K, bs, hs, hK, hb⟩ => ⟨A, S, K, bs, hs, hK, pieceAt_eq .. ▸ hb⟩

/-- **A struct's pieces are its `pts`** (row #79), at an alignment that one field's alignment and
offset give (a decided check); the pieces' labels are read from the memory. -/
theorem StructLayout.join {T : Type} [Enc T] (L : StructLayout T) {v : T}
    (hal : (L.shape.any fun x => x.2.2 % a == 0 && x.1 % a == 0) = true) :
    EUpd (piecesF p (L.pieces v)) (up (Zig.pts p a v)) :=
  EUpd.trans (EUpd.of_imp fun _ => piecesF_up)
    (EUpd.up_of_heap (SizeFree.piecesA _ _) fun m hP hF hm hp => by
      have ht := L.tiles_of v
      rw [← L.shape_eq v] at hal
      -- the first piece gives the block
      obtain ⟨x, ps, hxs⟩ : ∃ x ps, L.pieces v = x :: ps := by
        cases e : L.pieces v with
        | nil => rw [e] at hal; simp at hal
        | cons x ps => exact ⟨x, ps, rfl⟩
      have hp' := hp
      rw [hxs] at hp' ht
      simp only [List.map, Tiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
      obtain ⟨⟨hx0, hpos⟩, -⟩ := ht
      obtain ⟨h₁, h₂, -, rfl, hx, -⟩ := hp'
      obtain ⟨A, S, K, bs, hs, hK, hb⟩ := SPiece.assn_bytes hx
      rw [hx0] at hb
      simp only [Int.natCast_zero, Ptr.add_zero] at hb
      obtain ⟨b, hpb, h0, -⟩ := id hb
      have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
      obtain ⟨blk, hblk, -⟩ := Mem.heap_some (bytesAt_cell hb hm₁ hpb (j := 0) (by omega))
      obtain ⟨-, -, rfl⟩ := bytesAt_metadata hb hm₁ hpb hblk (by omega)
      obtain ⟨cs, hcs, hbc, hdec, hals⟩ := join_aux (N := Enc.size T) hpb h0 hblk (L.pieces v) 0 _ hF
        hm (L.tiles_of v) hp
      obtain ⟨y, hy, hq⟩ := All.exists_of_any hals hal
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      have hA : a ∣ blk.addr + p.off.toNat + y.off :=
        Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hq.1) (Nat.dvd_of_mod_eq_zero (by rwa [Nat.add_assoc]))
      refine ⟨blk.addr, blk.bytes.size, blk.kind, cs,
        Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_left (Nat.dvd_of_mod_eq_zero hq.2)).mp hA),
        by simpa using hcs, L.of_pieces cs v (by simpa using hcs) (by simpa using hdec),
        by simpa using hbc, hK⟩)

end Join

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
