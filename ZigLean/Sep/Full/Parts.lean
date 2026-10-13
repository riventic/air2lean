import ZigLean.Sep.Full.AtomicPlain

/-!
# Accesses over several owned parts (`docs/proof-automation.md` §Parts)

A typed access of a struct whose bytes are owned by several parts of the precondition (a region
and atomic words, or one atom per field): no single part's rule covers it. The access is served
by the parts' own rules, each on the bytes it owns, so each part keeps its view (and its atomic
tag):

* **Loads** read: `ReadsAt q n D P` (a provider kind, like `Reaches`) says that in every memory
  that holds `P` the `n` bytes at `q` are in a live block and satisfy `D`. The parts provide it
  for the bytes they own (`ReadsAt.pts`, `.aptsE`, `.apts`, `.regionIn`, …: they decode to the
  part's value), `ReadsAt.field` puts a part's into a struct's bytes, and `fsym` composes the
  struct's from its fields (`Auto.lean`); `FTotalTriple.load_reads` loads the struct whose bytes
  decode to its fields' values, at an address that a part aligns (`AlignedAt`, a provider kind).
* **Stores** write: `FTotalTriple.storeBytes_parts` splits a write of `bs` into writes of its
  pieces (`Parts`, `storeParts`), each executed by the rule of the part that owns those bytes.
  The single write and the pieces leave the same blocks (`storeBytes_two_run`); only the record
  of accesses differs, which no assertion reads. `fsym` cuts a struct's encoding at its fields
  (`Enc.fields`: `fields_extract`, `fields_size` from a checked layout `LayoutOk`).
-/

namespace Zig.Full

open FAssn

/-! ## Encodings of structs (`Enc.fields`) -/

/-- The parts `(offset, size)` of a struct's encoding fit in `N` bytes and do not overlap. -/
def LayoutOk (N : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | x :: ps => decide (x.1 + x.2 ≤ N) &&
      ps.all (fun y => decide (x.1 + x.2 ≤ y.1 ∨ y.1 + y.2 ≤ x.1)) && LayoutOk N ps

theorem layoutOk_cons {N : Nat} {x : Nat × Nat} {ps : List (Nat × Nat)}
    (h : LayoutOk N (x :: ps) = true) : x.1 + x.2 ≤ N ∧
      (∀ y ∈ ps, x.1 + x.2 ≤ y.1 ∨ y.1 + y.2 ≤ x.1) ∧ LayoutOk N ps = true := by
  simp only [LayoutOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem layoutOk_fit {N : Nat} : ∀ {ps : List (Nat × Nat)}, LayoutOk N ps = true →
    ∀ {x : Nat × Nat}, x ∈ ps → x.1 + x.2 ≤ N
  | [], _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, h, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (layoutOk_cons h).1
    · exact layoutOk_fit (layoutOk_cons h).2.2 hx

/-- The parts of `Enc.fields` with their sizes. -/
def partSizes (parts : List (Nat × Array Byte)) : List (Nat × Nat) :=
  parts.map fun x => (x.1, x.2.size)

/-- A write of a part (`Enc.fields`'s step). -/
def writePart (acc : Array Byte) (x : Nat × Array Byte) : Array Byte := writeBytes acc x.1 x.2

theorem fields_eq (N : Nat) (parts : List (Nat × Array Byte)) :
    Enc.fields N parts = parts.foldl writePart (Array.replicate N .undef) := rfl

theorem foldl_write_size {N : Nat} :
    ∀ (parts : List (Nat × Array Byte)) (acc : Array Byte), acc.size = N →
      (∀ x ∈ parts, x.1 + x.2.size ≤ N) → (parts.foldl writePart acc).size = N
  | [], _, h, _ => h
  | x :: ps, acc, h, hf => by
    have hx := hf x List.mem_cons_self
    exact foldl_write_size ps _ (by rw [writePart, writeBytes_size _ _ _ (by omega), h])
      fun y hy => hf y (List.mem_cons_of_mem _ hy)

/-- A struct's encoding has its size. -/
theorem fields_size {N : Nat} {parts : List (Nat × Array Byte)}
    (h : LayoutOk N (partSizes parts) = true) : (Enc.fields N parts).size = N := by
  rw [fields_eq]
  exact foldl_write_size parts _ (Array.size_replicate ..) fun x hx =>
    layoutOk_fit h (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem foldl_write_extract {N o : Nat} {cs : Array Byte} :
    ∀ (parts : List (Nat × Array Byte)) (acc : Array Byte), acc.size = N → o + cs.size ≤ N →
      acc.extract o (o + cs.size) = cs →
      (∀ x ∈ parts, x.1 + x.2.size ≤ N ∧ (x.1 + x.2.size ≤ o ∨ o + cs.size ≤ x.1)) →
      (parts.foldl writePart acc).extract o (o + cs.size) = cs
  | [], _, _, _, he, _ => he
  | x :: ps, acc, h, hc, he, hf => by
    have ⟨h1, h2⟩ := hf x List.mem_cons_self
    refine foldl_write_extract ps _ (by rw [writePart, writeBytes_size _ _ _ (by omega), h]) hc ?_
      fun y hy => hf y (List.mem_cons_of_mem _ hy)
    rw [writePart, extract_writeBytes_disjoint acc x.1 x.2 o cs.size (by omega) (by omega)
      (by omega), he]

/-- **A field of a struct's encoding** (`Enc.fields`, parts that fit and do not overlap): the
bytes of a part are the part's. -/
theorem fields_extract {N o : Nat} {cs : Array Byte} {pre post : List (Nat × Array Byte)}
    (h : LayoutOk N (partSizes (pre ++ (o, cs) :: post)) = true) :
    (Enc.fields N (pre ++ (o, cs) :: post)).extract o (o + cs.size) = cs := by
  rw [fields_eq, List.foldl_append, List.foldl_cons]
  have hall : ∀ x ∈ pre ++ (o, cs) :: post, x.1 + x.2.size ≤ N := fun x hx =>
    layoutOk_fit h (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hc : o + cs.size ≤ N := hall _ (List.mem_append_right _ List.mem_cons_self)
  have hpre := foldl_write_size pre (Array.replicate N .undef) (Array.size_replicate ..)
    fun x hx => hall x (List.mem_append_left _ hx)
  -- the later parts are apart from the part
  have hl : LayoutOk N (partSizes ((o, cs) :: post)) = true := by
    clear hall hc hpre
    induction pre with
    | nil => exact h
    | cons x xs ih => exact ih (layoutOk_cons h).2.2
  have hap := (layoutOk_cons hl).2.1
  simp only [writePart]
  refine foldl_write_extract post _ (by rw [writeBytes_size _ _ _ (by omega), hpre]) hc
    (extract_writeBytes _ _ _ (by omega)) fun x hx => ⟨hall x (List.mem_append_right _
      (List.mem_cons_of_mem _ hx)), ?_⟩
  have := hap _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  simp only at this; omega

/-- A checked layout of the parts, with their sizes known (`fsym` checks the numbers). -/
theorem layoutOk_of_eq {N : Nat} {parts : List (Nat × Array Byte)} {L : List (Nat × Nat)}
    (hmap : partSizes parts = L) (h : LayoutOk N L = true) : LayoutOk N (partSizes parts) = true :=
  hmap ▸ h

/-- Bytes whose `n` bytes from byte 0 decode to `a`, of size `n`, decode to `a`. -/
theorem decode_of_extract_all {U : Type} [Enc U] {bs : Array Byte} {n : Nat} {a : U}
    (hs : bs.size = n) (h : Enc.decode (bs.extract 0 (0 + n)) = pure a) : Enc.decode bs = pure a := by
  rwa [Nat.zero_add, ← hs, Array.extract_size] at h

/-- `fields_extract` with the part's size. -/
theorem fields_extract_sz {N o n : Nat} {cs : Array Byte} {pre post : List (Nat × Array Byte)}
    (h : LayoutOk N (partSizes (pre ++ (o, cs) :: post)) = true) (hs : cs.size = n) :
    (Enc.fields N (pre ++ (o, cs) :: post)).extract o (o + n) = cs := by
  rw [← hs]; exact fields_extract h

/-! ## Stores over parts -/

/-- Bytes written at `o`, then bytes right after them: both at `o`. -/
theorem writeBytes_append {a cs ds : Array Byte} {o : Nat} (h : o + cs.size + ds.size ≤ a.size) :
    writeBytes (writeBytes a o cs) (o + cs.size) ds = writeBytes a o (cs ++ ds) := by
  have h1 : o + cs.size ≤ a.size := by omega
  have hs := writeBytes_size a o cs h1
  apply Array.ext_getElem?
  intro i
  rw [writeBytes_getElem? _ _ _ (by rw [hs]; omega), writeBytes_getElem? _ _ _ h1,
    writeBytes_getElem? _ _ _ (by simp only [Array.size_append]; omega)]
  simp only [Array.size_append]
  by_cases hi1 : o ≤ i ∧ i < o + cs.size
  · rw [ite_eq_right (by omega), ite_eq_left hi1, ite_eq_left (by omega),
      Array.getElem?_append_left (by omega)]
  · by_cases hi2 : o + cs.size ≤ i ∧ i < o + cs.size + ds.size
    · rw [ite_eq_left hi2, ite_eq_left (by omega), Array.getElem?_append_right (by omega)]
      congr 1; omega
    · rw [ite_eq_right hi2, ite_eq_right hi1, ite_eq_right (by omega)]

/-- **Two writes of adjacent bytes**, the first at `p`, are one write of both: it succeeds and
leaves the same blocks and atomic layout (the record of accesses differs). -/
theorem storeBytes_two_run {m m₁ m₂ : Mem} {p p' : Ptr} {al : Nat} {cs ds : Array Byte}
    (hs : m.SingleThread) (hb : p'.block = p.block) (ho : p'.off = p.off + cs.size)
    (h1 : ((Zig.storeBytes p al cs).run m).run = some (.ok ((), m₁)))
    (h2 : ((Zig.storeBytes p' 1 ds).run m₁).run = some (.ok ((), m₂))) :
    ∃ m₃, ((Zig.storeBytes p al (cs ++ ds)).run m).run = some (.ok ((), m₃)) ∧
      m₃.blocks = m₂.blocks ∧ m₃.atomics = m₂.atomics ∧ m₃.SingleThread := by
  obtain ⟨b, blk, o, ha, hK, -, rfl⟩ := Conc.Proto.storeBytes_ok h1
  obtain ⟨b', blk', o', ha', -, -, rfl⟩ := Conc.Proto.storeBytes_ok h2
  obtain ⟨hpb, hblk, hl, h0, hfit, hal, rfl⟩ := access_eq ha
  have hlo := access_lo ha
  obtain ⟨hpb', hblk', -, -, hfit', -, rfl⟩ := access_eq ha'
  rw [hb, hpb, Option.some.injEq] at hpb'
  subst hpb'
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have e1 : blk' = { blk with bytes := writeBytes blk.bytes p.off.toNat cs } := by
    simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt hlt, Option.some.injEq] at hblk'
    exact hblk'.symm
  subst e1
  have hsz : (writeBytes blk.bytes p.off.toNat cs).size = blk.bytes.size :=
    writeBytes_size _ _ _ (by omega)
  have hoff : p'.off.toNat = p.off.toNat + cs.size := by omega
  simp only [hsz] at hfit'
  have ha3 : m.access p (cs ++ ds).size al = pure (b, blk, p.off.toNat) :=
    access_of hpb hblk hl h0 (by simp only [Array.size_append]; omega) hal hlo
  refine ⟨(m.recordAt b p.off.toNat (cs ++ ds).size .write).write b blk p.off.toNat (cs ++ ds),
    by rw [storeBytes_run ha3 hK (noRace_of_singleThread hs _ _ _ _)]; rfl, ?_, rfl,
    singleThread_write (singleThread_recordAt hs _ _ _ _) _ _ _ _⟩
  simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
    Array.setIfInBounds_setIfInBounds, hoff]
  rw [writeBytes_append (by simp only [Array.size_append] at ha3 ⊢; omega)]

/-- The pieces `ps` (each a pointer, the end offset of its bytes, its bytes) write `bs` at `q`
from byte `i` on: each is at `q`'s block and offset plus its start, nonempty, and holds the
bytes of `bs` from its start to its end, which is the next piece's start (the last one's is
`bs`'s size). -/
def Parts (q : Ptr) (bs : Array Byte) : Nat → List (Ptr × Nat × Array Byte) → Prop
  | i, [] => i = bs.size
  | i, (p, j, cs) :: ps =>
    p.block = q.block ∧ p.off = q.off + (i : Int) ∧ i < j ∧ bs.extract i j = cs ∧ Parts q bs j ps

/-- The writes of the pieces: the first with the access's alignment, the others with none. -/
def storeParts (al : Nat) : List (Ptr × Nat × Array Byte) → MemM Unit
  | [] => pure ()
  | (p, _, cs) :: ps => Zig.storeBytes p al cs >>= fun _ => storeParts 1 ps

theorem Parts.nil_intro {q : Ptr} {bs : Array Byte} {i : Nat} (h : i = bs.size) :
    Parts q bs i [] := h

theorem Parts.cons_intro {q p : Ptr} {bs cs : Array Byte} {i j : Nat}
    {ps : List (Ptr × Nat × Array Byte)} (hb : p.block = q.block) (ho : p.off = q.off + (i : Int))
    (hij : i < j) (he : bs.extract i j = cs) (h : Parts q bs j ps) : Parts q bs i ((p, j, cs) :: ps) :=
  ⟨hb, ho, hij, he, h⟩

theorem Parts.le {q : Ptr} {bs : Array Byte} : ∀ {i : Nat} {ps : List (Ptr × Nat × Array Byte)},
    Parts q bs i ps → i ≤ bs.size
  | _, [], h => Nat.le_of_eq h
  | _, (_, _, _) :: _, ⟨_, _, hij, _, h⟩ => Nat.le_of_lt (Nat.lt_of_lt_of_le hij h.le)

theorem storeParts_run {q : Ptr} {bs : Array Byte} :
    ∀ (ps : List (Ptr × Nat × Array Byte)) {i al : Nat} {m m' : Mem} {p : Ptr} {j : Nat}
      {cs : Array Byte}, Parts q bs i ((p, j, cs) :: ps) → m.SingleThread →
      ((storeParts al ((p, j, cs) :: ps)).run m).run = some (.ok ((), m')) →
      ∃ m₃, ((Zig.storeBytes p al (bs.extract i bs.size)).run m).run = some (.ok ((), m₃)) ∧
        m₃.blocks = m'.blocks ∧ m₃.atomics = m'.atomics ∧ m₃.SingleThread
  | [], i, al, m, m', p, j, cs, ⟨_, _, _, hcs, hj⟩, hs, h => by
    obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h2
    obtain ⟨b, blk, o, -, -, -, rfl⟩ := Conc.Proto.storeBytes_ok h1
    have hj' : j = bs.size := hj
    subst hj'
    exact ⟨_, by rw [hcs]; exact h1, rfl, rfl,singleThread_write (singleThread_recordAt hs _ _ _ _) _ _ _ _⟩
  | (p₂, j₂, cs₂) :: ps, i, al, m, m', p, j, cs, ⟨hb, ho, hij, hcs, hp⟩, hs, h => by
    obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨b, blk, o, -, -, -, rfl⟩ := Conc.Proto.storeBytes_ok h1
    have hs₁ := singleThread_write (singleThread_recordAt hs b o cs.size .write) b blk o cs
    obtain ⟨m₃, h3, hb3, ha3, hs3⟩ := storeParts_run ps hp hs₁ h2
    have hjb := hp.le
    obtain ⟨hb₂, ho₂, -⟩ := hp
    have hsz : cs.size = j - i := by rw [← hcs]; simp only [Array.size_extract]; omega
    obtain ⟨m₄, h4, hb4, ha4, hs4⟩ := storeBytes_two_run hs (hb₂.trans hb.symm)
      (by rw [ho₂, ho, hsz]; omega) h1 h3
    refine ⟨m₄, ?_, hb4.trans hb3, ha4.trans ha3, hs4⟩
    rwa [← hcs, Array.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right hjb] at h4

/-- **A write of `bs` at `q` by pieces** (`Parts`): the writes of the pieces, each by the rule of
the part that owns its bytes, give the write's triple. -/
theorem FTotalTriple.storeBytes_parts {P : FAssn} {Q : Unit → FAssn} {q p : Ptr} {al j : Nat}
    {bs cs : Array Byte} {ps : List (Ptr × Nat × Array Byte)} (hp : Parts q bs 0 ((p, j, cs) :: ps))
    (h : FTotalTriple P (storeParts al ((p, j, cs) :: ps)) Q) :
    FTotalTriple P (Zig.storeBytes q al bs) Q :=
  FTotalTriple.of_run fun m r rF hh hpr hs => by
    obtain ⟨v, m', r', hrun, hh', hq, hs'⟩ := h.runs hh hpr hs
    have hrun' : ((storeParts al ((p, j, cs) :: ps)).run m).run = some (.ok ((), m')) := by
      rw [hrun]; rfl
    obtain ⟨m₃, h3, hb3, ha3, hs3⟩ := storeParts_run ps hp hs.1.single hrun'
    have hpq : p = q := by
      obtain ⟨hb, ho, -⟩ := hp
      cases p; cases q; simp only at hb ho; subst hb; simp only [Int.natCast_zero, Int.add_zero] at ho
      subst ho; rfl
    subst hpq
    rw [Array.extract_size] at h3
    refine ⟨(), m₃, r', ?_, Holds.congrMem hb3 ha3 hh', hq, ⟨⟨hs3⟩, ?_, ?_⟩⟩
    · exact h3
    · have e : shapes m₃ = shapes m' := by simp only [shapes, ha3]
      rw [e]; exact hs'.2.1
    · have hl := hs'.2.2
      unfold Mem.LiveLayout Mem.LiveDisjoint Mem.LiveBounded at hl ⊢
      rw [hb3]; exact hl

/-! ## Loads over parts -/

/-- **Bytes that a precondition reads** (a provider kind): every memory that holds `P` has the
`n` bytes at `q` in a live block, at or above its first live offset, and they satisfy `D`. -/
def ReadsAt (q : Ptr) (n : Nat) (D : Array Byte → Prop) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ b blk, q.block = some b ∧ m.blocks[b]? = some blk ∧
    blk.live = true ∧ 0 ≤ q.off ∧ blk.kind.mappedLo ≤ q.off.toNat ∧
    q.off.toNat + n ≤ blk.bytes.size ∧ D (blk.bytes.extract q.off.toNat (q.off.toNat + n))

namespace ReadsAt

variable {q q' : Ptr} {n k j : Nat} {D E : Array Byte → Prop} {P X : FAssn}

theorem of_within (h : ReadsAt q n D X) (hw : Within X P) : ReadsAt q n D P :=
  fun m r rF hh hp => by
    obtain ⟨_, r₁, r₂, hd, rfl, h1, -⟩ := hw r hp
    exact h m r₁ _ (Holds.split hd hh) h1

theorem mono {D' : Array Byte → Prop} (h : ReadsAt q n D P)
    (hd : ∀ bs, bs.size = n → D bs → D' bs) : ReadsAt q n D' P := fun m r rF hh hp => by
  obtain ⟨b, blk, hb, hblk, hl, h0, hlo, hn, hD⟩ := h m r rF hh hp
  exact ⟨b, blk, hb, hblk, hl, h0, hlo, hn, hd _ (by simp only [Array.size_extract]; omega) hD⟩

/-- **A part's bytes in a whole's**: the bytes at `q'`, byte `j` of the `n` bytes at `q`. -/
theorem field (hall : ReadsAt q n D P) (hf : ReadsAt q' k E P) (hb : q'.block = q.block)
    (ho : q'.off = q.off + (j : Int)) (hk : j + k ≤ n) :
    ReadsAt q n (fun bs => E (bs.extract j (j + k)) ∧ D bs) P := fun m r rF hh hp => by
  obtain ⟨b, blk, hqb, hblk, hl, h0, hlo, hn, hD⟩ := hall m r rF hh hp
  obtain ⟨b', blk', hqb', hblk', -, -, -, -, hE⟩ := hf m r rF hh hp
  rw [hb, hqb, Option.some.injEq] at hqb'
  subst hqb'
  rw [hblk, Option.some.injEq] at hblk'
  subst hblk'
  have e : q'.off.toNat = q.off.toNat + j := by omega
  refine ⟨b, blk, hqb, hblk, hl, h0, hlo, hn, ?_, hD⟩
  rw [Array.extract_extract, Nat.min_eq_left (by omega), ← Nat.add_assoc, ← e]
  exact hE

/-- The bytes at `q` up to a bound of their block: in bounds and live where a part at `q` is. -/
theorem base {b : BlockId} {K : Nat} (h : ReadsAt q k D P) (hqb : q.block = some b)
    (hr : Reaches b K P) (hn : q.off.toNat + n ≤ K) : ReadsAt q n (fun _ => True) P :=
  fun m r rF hh hp => by
    obtain ⟨b', blk, hqb', hblk, hl, h0, hlo, -, -⟩ := h m r rF hh hp
    rw [hqb, Option.some.injEq] at hqb'
    subst hqb'
    obtain ⟨blk', hblk', hK⟩ := hr m r rF hh hp
    rw [hblk, Option.some.injEq] at hblk'
    subst hblk'
    exact ⟨b, blk, hqb, hblk, hl, h0, hlo, by omega, trivial⟩

/-- Owned bytes `bs` at `p`, from byte `k` on. -/
theorem of_up_at {p : Ptr} (hx : ∀ r, X r → ∃ A S K bs, up (bytesAt p A S K bs) r ∧ 0 < n ∧
    k + n ≤ bs.size ∧ D (bs.extract k (k + n))) : ReadsAt (p.add k) n D X := fun m r rF hh hr => by
  obtain ⟨A, S, K, bs, hu, hn, hk, hD⟩ := hx r hr
  obtain ⟨b, blk, hpb, hblk, hl, h0, hlo, hfit, -, -, hbs⟩ := hh.bytesAt_block hu (by omega)
  have e : (p.add k).off.toNat = p.off.toNat + k := by simp only [Ptr.add]; omega
  refine ⟨b, blk, hpb, hblk, hl, by simp only [Ptr.add]; omega, by rw [e]; omega, by rw [e]; omega, ?_⟩
  have ex : blk.bytes.extract (p.off.toNat + k) (p.off.toNat + k + n) = bs.extract k (k + n) := by
    rw [← hbs, Array.extract_extract, Nat.min_eq_left (by omega), Nat.add_assoc]
  rw [e, ex]; exact hD

/-- Owned bytes `bs` at `p`, from byte 0 on. -/
theorem of_up {p : Ptr} (hx : ∀ r, X r → ∃ A S K bs, up (bytesAt p A S K bs) r ∧ 0 < n ∧
    n ≤ bs.size ∧ D (bs.extract 0 n)) : ReadsAt p n D X := by
  have t := of_up_at (p := p) (k := 0) (X := X) (n := n) (D := D) fun r hr => by
    obtain ⟨A, S, K, bs, hu, hn, hk, hD⟩ := hx r hr
    exact ⟨A, S, K, bs, hu, hn, by omega, by rwa [Nat.zero_add]⟩
  simpa only [Int.natCast_zero, Ptr.add_zero] using t

/-! ### Parts that provide their bytes (`@[fsym_provider]`) -/

/-- A typed value: its bytes decode to it. -/
theorem pts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    ReadsAt p (Enc.size T) (fun cs => Enc.decode cs = pure v) (up (Zig.pts p a v)) :=
  of_up fun _ hr => by
    obtain ⟨A, S, K, bs, ⟨-, hsz, hv, -⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
    exact ⟨A, S, K, bs, hb, hn, by omega, by rw [← hsz, Array.extract_size]; exact hv⟩

/-- A field (at byte `k`) of a typed value (`EncField`): its bytes decode to the field. -/
theorem ptsField {T U : Type} [Enc T] [Enc U] {p : Ptr} {a : Nat} {s : T} {k : Int}
    {get : T → U} {set : T → U → T} (hf : EncField T U k.toNat get set) (hn : 0 < Enc.size U)
    (h0 : 0 ≤ k) :
    ReadsAt (p.add k) (Enc.size U) (fun cs => Enc.decode cs = pure (get s)) (up (Zig.pts p a s)) := by
  have e : p.add k = p.add ((k.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]
  rw [e]
  exact of_up_at fun _ hr => by
    obtain ⟨A, S, K, bs, ⟨-, hsz, hv, -⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
    exact ⟨A, S, K, bs, hb, hn, by have := hf.fit; omega, hf.get_dec hsz hv⟩

/-- `ptsField` at byte 0. -/
theorem ptsField0 {T U : Type} [Enc T] [Enc U] {p : Ptr} {a : Nat} {s : T} {get : T → U}
    {set : T → U → T} (hf : EncField T U 0 get set) (hn : 0 < Enc.size U) :
    ReadsAt p (Enc.size U) (fun cs => Enc.decode cs = pure (get s)) (up (Zig.pts p a s)) :=
  of_up fun _ hr => by
    obtain ⟨A, S, K, bs, ⟨-, hsz, hv, -⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
    exact ⟨A, S, K, bs, hb, hn, by have := hf.fit; omega, by
      simpa only [Nat.zero_add] using hf.get_dec hsz hv⟩

/-- An atomic value: its bytes decode to it. -/
theorem aptsE {α : Type} [Enc α] {p : Ptr} {v : α} :
    ReadsAt p 8 (fun cs => Enc.decode cs = pure v) (Zig.Full.aptsE p v) :=
  of_up fun _ ⟨A, S, K, bs, _, _, hsz, hv, hab⟩ =>
    ⟨A, S, K, bs, up_of_abytesAt hab, by decide, by omega, by rw [← hsz, Array.extract_size]; exact hv⟩

/-- An atomic word: its bytes decode to it. -/
theorem apts {p : Ptr} {v : BitVec 64} :
    ReadsAt p 8 (fun cs => (Enc.decode cs : Result (BitVec 64)) = pure v) (Zig.Full.apts p v) :=
  aptsE

/-- Bytes from byte `k` of a region that decode to `v`. -/
theorem regionIn {U : Type} [Enc U] {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte}
    {k : Int} {v : U} (h0 : 0 ≤ k) (hn : 0 < n) (hk : k.toNat + n ≤ bs.size)
    (hv : Enc.decode (bs.extract k.toNat (k.toNat + n)) = pure v) :
    ReadsAt (p.add k) n (fun cs => Enc.decode cs = pure v) (up (Zig.regionIn p A S K a bs)) := by
  have e : p.add k = p.add ((k.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]
  rw [e]
  exact of_up_at fun _ hr => ⟨A, S, K, bs, ⟨hr.1.2.2, hr.2⟩, hn, hk, hv⟩

/-- A whole region whose bytes decode to `v`. -/
theorem regionInAll {U : Type} [Enc U] {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte}
    {v : U} (hn : bs.size = n) (hpos : 0 < n) (hv : Enc.decode bs = pure v) :
    ReadsAt p n (fun cs => Enc.decode cs = pure v) (up (Zig.regionIn p A S K a bs)) :=
  of_up fun _ hr => ⟨A, S, K, bs, ⟨hr.1.2.2, hr.2⟩, hpos, by omega, by
    rw [← hn, Array.extract_size]; exact hv⟩

end ReadsAt

attribute [fsym_provider] ReadsAt.pts ReadsAt.ptsField ReadsAt.ptsField0 ReadsAt.aptsE
  ReadsAt.apts ReadsAt.regionIn ReadsAt.regionInAll

/-- **An aligned address** (a provider kind): every memory that holds `P` has the address of
`q` a multiple of `al`. Owned bytes that are aligned give it (`AlignedAt.pts`, `.aptsE`, …),
and so does a known address (`AlignedAt.addr`). -/
def AlignedAt (q : Ptr) (al : Nat) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ b blk, q.block = some b ∧ m.blocks[b]? = some blk ∧
    (blk.addr + q.off.toNat) % al = 0

namespace AlignedAt

variable {q : Ptr} {al : Nat} {P X : FAssn}

theorem of_within (h : AlignedAt q al X) (hw : Within X P) : AlignedAt q al P :=
  fun m r rF hh hp => by
    obtain ⟨_, r₁, r₂, hd, rfl, h1, -⟩ := hw r hp
    exact h m r₁ _ (Holds.split hd hh) h1

/-- A known address of the block. -/
theorem addr {b : BlockId} {A : Nat} (hqb : q.block = some b) (ha : AddrOf b A P)
    (hal : (A + q.off.toNat) % al = 0) : AlignedAt q al P := fun m r rF hh hp => by
  obtain ⟨blk, hblk, hA⟩ := ha m r rF hh hp
  exact ⟨b, blk, hqb, hblk, by rw [hA]; exact hal⟩

/-- Owned bytes at an aligned address. -/
theorem of_up {p : Ptr} (hx : ∀ r, X r → ∃ A S K bs, up (bytesAt p A S K bs) r ∧ 0 < bs.size ∧
    (A + p.off.toNat) % al = 0) : AlignedAt p al X := fun m r rF hh hr => by
  obtain ⟨A, S, K, bs, hu, hn, ha⟩ := hx r hr
  obtain ⟨b, blk, hpb, hblk, -, -, -, -, hA, -, -⟩ := hh.bytesAt_block hu hn
  exact ⟨b, blk, hpb, hblk, by rw [hA]; exact ha⟩

theorem pts {T : Type} [Enc T] {p : Ptr} {a : Nat} {v : T} (hn : 0 < Enc.size T) (hal : al ∣ a) :
    AlignedAt p al (up (Zig.pts p a v)) :=
  of_up fun _ hr => by
    obtain ⟨A, S, K, bs, ⟨ha, hsz, -, -⟩, hb⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hr
    exact ⟨A, S, K, bs, hb, by omega, Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero ha))⟩

theorem aptsE {α : Type} [Enc α] {p : Ptr} {v : α} (hal : al ∣ 8) :
    AlignedAt p al (Zig.Full.aptsE p v) :=
  of_up fun _ ⟨A, S, K, bs, ha, _, hsz, _, hab⟩ => ⟨A, S, K, bs, up_of_abytesAt hab, by omega,
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero ha))⟩

theorem apts {p : Ptr} {v : BitVec 64} (hal : al ∣ 8) : AlignedAt p al (Zig.Full.apts p v) :=
  aptsE (p := p) (v := v) hal

theorem regionIn {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte} (hpos : 0 < bs.size)
    (hal : al ∣ a) : AlignedAt p al (up (Zig.regionIn p A S K a bs)) :=
  of_up fun _ hr => ⟨A, S, K, bs, ⟨hr.1.2.2, hr.2⟩, hpos,
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hal (Nat.dvd_of_mod_eq_zero hr.1.1))⟩

end AlignedAt

attribute [fsym_provider] AlignedAt.pts AlignedAt.aptsE AlignedAt.apts AlignedAt.regionIn
  AlignedAt.addr

/-- **Load of a value whose bytes the precondition reads** (`ReadsAt`, from several parts: a
struct whose fields are owned apart), at an aligned address: the value they decode to. -/
theorem FTotalTriple.load_reads {T : Type} [Enc T] {q : Ptr} {al : Nat} {v : T}
    {P : FAssn} (h : ReadsAt q (Enc.size T) (fun bs => Enc.decode bs = pure v) P)
    (ha : AlignedAt q al P) :
    FTotalTriple P (Zig.load T al q) (fun x => ⟪x = v⟫ ⋆ P) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    obtain ⟨b, blk, hqb, hblk, hl, h0, hlo, hn, hv⟩ := h m r rF hh hp
    obtain ⟨b', blk', hqb', hblk', hal⟩ := ha m r rF hh hp
    rw [hqb, Option.some.injEq] at hqb'
    subst hqb'
    rw [hblk, Option.some.injEq] at hblk'
    subst hblk'
    have hacc := access_of (m := m) (n := Enc.size T) (a := al) hqb hblk hl h0 (by omega) hal hlo
    exact ⟨v, _, r, load_read hacc hv (noRace_of_singleThread hs.1.single _ _ _ _),
      hh.readAt _ _ _ _ _, sep_lift.mpr ⟨rfl, hp⟩, hs.readAt _ _ _ _ _⟩

end Zig.Full
