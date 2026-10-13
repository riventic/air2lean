import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Local

/-!
# Error unions and optionals through pointers in the full-state logic (Plan A library lane A1)

The pointer forms of `try`, `catch`, `orelse` and `if (x) |*p|` that generated code uses
(`ZigLean/Mem/Enc.lean`, `ZigLean/Mem/Basic.lean`), as total rules over an owned value
`pts q a v`, from the bytes view of `Full/Typed.lean` (`up_pts_iff`):

* **Bytes**: `FTotalTriple.region_loadBytes`/`region_storeBytes`, `n` bytes at byte `o` of a region.
* **Error unions `E!T`**: `tryPayloadPtr` (the payload pointer or the error, `tryView`),
  `errCodeAt`, `errIsErrAt`, and their checked forms for a declared finite error set
  (`finiteTryPayloadPtr`, `finiteErrCodeAt`, `finiteErrIsErrAt`, and the whole-union
  `load_finite`/`store_finite` with `errorUnionEnc`: the error must be in the set); the payload
  pointer (`ptrProject_errPayload`); `errSetOk` (`errunion_payload_ptr_set`): the error code
  becomes 0 and the union an `errOkSlot` until the payload is written (`errOkSlot_store`), or
  stays `.ok x` (`errSetOk_ok`). Each also on the bytes (`…_region`), for an error code read from
  bytes the owned value does not describe.
* **Optionals `?T`** (`T` not a pointer): `optIsSome` (`is_non_null_ptr`), `optSetSome`
  (`optional_payload_ptr_set`, then `optSomeSlot_store`, or `optSetSome_some`), and the payload
  through the payload pointer (the optional's address): `optPayload_load`/`optPayload_store`. The
  payload of `?T` is decoded from the whole optional's bytes (`Enc (Option α)`), so these need
  **prefix decoding** of `T` (`PrefixDecode`): every encoding of the model has it, and a
  generated struct or union gets it from `decodeAt_extract`.
* **Optional error sets `?E`**: `optionalErrorIsSome`.
* **Readable bytes** (`ReadAt`): one provider for every way bytes can be read, owned bytes of
  any block kind (`ReadAt.bytesAt`, `ReadAt.region`) and the persistent bytes of a `const` global
  (`ReadAt.ofConst`), and the read rules over it: `loadBytes_of`, `loadDiscard_of`, and the
  error code reads `tryPayloadPtr_of`, `errCodeAt_of`, `finiteTryPayloadPtr_of`,
  `finiteErrCodeAt_of` from the two bytes of the code (`ReadAt.shift` cuts them out of a whole
  union's bytes). These are native rules (no legacy lifting).

`@[fsym]` rules are about owned values; the `…_region` and `…_some`/`…_ok` forms are for
`fsym [r]`. Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

open Assn

/-- The result of a pointer-form try on a union holding `u` at `p`. -/
def tryView (α : Type) [Enc α] (p : Ptr) : Except ErrName α → Except ErrName Ptr
  | .ok _ => .ok (errPayloadPtr α p)
  | .error e => .error e

/-- The error tag of a union value: `none` on success. -/
def errTagOf {α : Type} : Except ErrName α → Option ErrName
  | .ok _ => none
  | .error e => some e

/-- The union after a payload write of `y`: an error union is unchanged (no write happens). -/
def writeView {α : Type} (y : α) : Except ErrName α → Except ErrName α
  | .ok _ => .ok y
  | .error e => .error e

/-- Membership in a literal array (a declared error set) element by element. -/
theorem contains_toArray_cons {β : Type} [BEq β] (a b : β) (l : List β) :
    (b :: l).toArray.contains a = if a == b then true else l.toArray.contains a := by
  simp only [List.contains_toArray, List.contains_cons]
  cases a == b <;> rfl

theorem contains_toArray_nil {β : Type} [BEq β] (a : β) :
    (([] : List β).toArray).contains a = false := by
  simp only [List.contains_toArray, List.contains_nil]

-- `fsym` reduces the views of a known union in programs (a `match` on a `try`'s result) and in
-- side goals (the error domain check of `errTagOf u`); a declared error set is a literal array,
-- whose membership `String.reduceBEq` decides name by name.
attribute [fsym_norm, fsym_arith] tryView errTagOf writeView
attribute [fsym_arith] Option.all_none Option.all_some contains_toArray_cons contains_toArray_nil

/-- The bytes of an error union `u`: the error code reads `u`'s tag, and on success the payload
bytes decode to the payload. -/
theorem errUnion_decode_tag {α : Type} [Enc α] {bs : Array Byte} {u : Except ErrName α}
    (h : Enc.decode bs = pure u) :
    errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
        ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure (errTagOf u) ∧
      ∀ x, u = .ok x → Enc.decode (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).2
        ((errUnionOffsets (Enc.size α) (Enc.align α)).2 + Enc.size α)) = pure x := by
  simp only [Enc.decode] at h
  generalize errUnionOffsets (Enc.size α) (Enc.align α) = r at h ⊢
  obtain ⟨eo, po⟩ := r
  simp only at h ⊢
  generalize ht : errOfBytes (bs.extract eo (eo + 2)) = r at h
  generalize hq : (Enc.decode (bs.extract po (po + Enc.size α)) : Result α) = q at h
  match r, q, h with
  | (none : Option _), _, h => simp [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure] at h
  | some (.error _), _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure] at h
    cases h
  | some (.ok none), none, h => simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure,
      ExceptT.pure, Functor.map, ExceptT.map] at h
  | some (.ok none), some (.error _), h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, Functor.map,
      ExceptT.map] at h
    cases h
  | some (.ok none), some (.ok x), h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, Functor.map,
      ExceptT.map] at h
    cases h
    exact ⟨rfl, fun y hy => by cases hy; rfl⟩
  | some (.ok (some e)), _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure] at h
    cases h
    exact ⟨rfl, fun y hy => by cases hy⟩

/-! ## Prefix decoding -/

/-- **Prefix decoding**: an encoding reads only the first `Enc.size α` bytes of what it decodes,
so a value decodes the same at the start of a longer byte string. The payload of an optional
`?T` (`T` not a pointer) is decoded from the bytes of the whole optional (`Enc (Option α)`), so a
payload read or write through the payload pointer needs this of `T`. Every encoding of the model
has it (the instances below); a generated struct or union decodes its fields with
`Enc.decodeAt` inside its size (`decodeAt_extract`). -/
class PrefixDecode (α : Type) [Enc α] : Prop where
  decode_prefix : ∀ bs : Array Byte, Enc.size α ≤ bs.size →
    (Enc.decode bs : Result α) = Enc.decode (bs.extract 0 (Enc.size α))

/-- A part inside the first `n` bytes reads the same from the first `n` bytes. -/
theorem decodeAt_extract {β : Type} [Enc β] {bs : Array Byte} {n o : Nat}
    (ho : o + Enc.size β ≤ n) :
    (Enc.decodeAt (bs.extract 0 n) o : Result β) = Enc.decodeAt bs o := by
  simp only [Enc.decodeAt, Array.extract_extract, Nat.zero_add, Nat.min_eq_left ho]

theorem extract_extract_prefix {bs : Array Byte} {i j n : Nat} (h : j ≤ n) :
    (bs.extract 0 n).extract i j = bs.extract i j := by
  simp only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left h]

theorem getElem?_extract_prefix {bs : Array Byte} {i n : Nat} (h : i < n) :
    (bs.extract 0 n)[i]? = bs[i]? := by
  simp only [Array.getElem?_extract, Nat.zero_add]
  split <;> simp_all; omega

theorem intOfBytes_prefix {n k : Nat} {trunc : Bool} {bs : Array Byte} (hk : (n + 7) / 8 ≤ k) :
    intOfBytes n (bs.extract 0 k) trunc = intOfBytes n bs trunc := by
  unfold intOfBytes; rw [extract_extract_prefix hk]

theorem intSize_ge (n : Nat) : (n + 7) / 8 ≤ intSize n := le_alignUp _ _

instance {n : Nat} : PrefixDecode (BitVec n) where
  decode_prefix _ _ := (intOfBytes_prefix (intSize_ge n)).symm

instance {fmt : FloatFmt} : PrefixDecode (Float fmt) where
  decode_prefix bs _ := by
    show (do pure ⟨← intOfBytes fmt.width bs⟩ : Result (Float fmt)) = do
      pure ⟨← intOfBytes fmt.width (bs.extract 0 (intSize fmt.width))⟩
    rw [intOfBytes_prefix (intSize_ge _)]

instance : PrefixDecode Bool where
  decode_prefix _ h := by
    simp only [Enc.decode, Enc.size]
    simp only [getElem?_extract_prefix (by decide : 0 < 1)]

instance : PrefixDecode Unit where
  decode_prefix _ _ := rfl

instance : PrefixDecode Ptr where
  decode_prefix bs _ := by
    simp only [Enc.decode, Enc.size]
    simp only [getElem?_extract_prefix (by decide : 0 < 8), extract_extract_prefix (Nat.le_refl 8),
      intOfBytes_prefix (by decide : (64 + 7) / 8 ≤ 8)]

instance : PrefixDecode Slice where
  decode_prefix bs _ := by
    show (do pure ⟨← Enc.decode (bs.extract 0 8), ← Enc.decode (bs.extract 8 16)⟩ : Result Slice) =
      do pure ⟨← Enc.decode ((bs.extract 0 16).extract 0 8),
        ← Enc.decode ((bs.extract 0 16).extract 8 16)⟩
    rw [extract_extract_prefix (by decide : 8 ≤ 16), extract_extract_prefix (Nat.le_refl 16)]

instance {α : Type} [Enc α] : PrefixDecode (Except ErrName α) where
  decode_prefix bs _ := by
    obtain ⟨h1, h2, -⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
    show (do
        match ← errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
          ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) with
        | none => Except.ok <$> (Enc.decode (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).2
            ((errUnionOffsets (Enc.size α) (Enc.align α)).2 + Enc.size α)) : Result α)
        | some e => pure (Except.error e)) = (do
        match ← errOfBytes ((bs.extract 0 (errUnionSize (Enc.size α) (Enc.align α))).extract
          (errUnionOffsets (Enc.size α) (Enc.align α)).1
          ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) with
        | none => Except.ok <$> (Enc.decode ((bs.extract 0 (errUnionSize (Enc.size α) (Enc.align α))).extract
            (errUnionOffsets (Enc.size α) (Enc.align α)).2
            ((errUnionOffsets (Enc.size α) (Enc.align α)).2 + Enc.size α)) : Result α)
        | some e => pure (Except.error e))
    rw [extract_extract_prefix h1, extract_extract_prefix h2]

theorem mapM_congr_mem {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {f g : α → m β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.mapM_cons]
    rw [h x (by simp), mapM_congr_mem fun y hy => h y (by simp [hy])]

instance {α : Type} {n : Nat} [Enc α] : PrefixDecode (Vector α n) where
  decode_prefix bs _ := by
    simp only [Enc.decode, Enc.size]
    have e : (Array.range n).mapM (fun i =>
          (Enc.decode (bs.extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)) =
        (Array.range n).mapM (fun i => (Enc.decode ((bs.extract 0 (n * Enc.size α)).extract
          (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)) := by
      rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
      congr 1
      apply mapM_congr_mem
      intro i hi
      simp only [Array.toList_range, List.mem_range] at hi
      rw [extract_extract_prefix (Nat.mul_le_mul_right _ hi)]
    rw [e]

/-- `?T` for a `T` that is not a pointer: the flag byte after the payload, and the payload. -/
theorem opt_decode {α : Type} [Enc α] {bs : Array Byte} {o : Option α}
    (h : (Enc.decode bs : Result (Option α)) = pure o) :
    bs[Enc.size α]? = some (.int (if o.isSome then 1 else 0)) ∧
      ∀ x, o = some x → (Enc.decode bs : Result α) = pure x := by
  simp only [Enc.decode] at h
  split at h
  · rename_i e
    cases h
    exact ⟨e, fun _ h => by cases h⟩
  · rename_i e
    generalize hq : (Enc.decode bs : Result α) = r at h
    rcases r with _ | _ | y
    · simp [Functor.map, ExceptT.map, ExceptT.mk, pure, ExceptT.pure, bind, Option.bind] at h
    · simp [Functor.map, ExceptT.map, ExceptT.mk, pure, ExceptT.pure, bind, Option.bind] at h
      cases h
    · simp [Functor.map, ExceptT.map, ExceptT.mk, pure, ExceptT.pure, bind, Option.bind] at h
      cases h
      exact ⟨e, fun x hx => by cases hx; rfl⟩
  · cases h
  · cases h

/-- The bytes of `some x`: the flag byte 1, and the payload's bytes at the start. -/
theorem opt_decode_of {α : Type} [Enc α] [PrefixDecode α] {bs : Array Byte} {x : α}
    (hs : Enc.size α < bs.size) (hf : bs[Enc.size α]? = some (.int 1))
    (hx : (Enc.decode (bs.extract 0 (Enc.size α)) : Result α) = pure x) :
    (Enc.decode bs : Result (Option α)) = pure (some x) := by
  simp only [Enc.decode]
  rw [hf]
  show some <$> (Enc.decode bs : Result α) = _
  rw [PrefixDecode.decode_prefix bs (Nat.le_of_lt hs), hx]
  rfl

instance {α : Type} [Enc α] [PrefixDecode α] : PrefixDecode (Option α) where
  decode_prefix bs hs := by
    have hlt : Enc.size α < alignUp (Enc.size α + 1) (Enc.align α) :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_alignUp _ _)
    simp only [Enc.decode, Enc.size] at hs ⊢
    have hs' : alignUp (Enc.size α + 1) (Enc.align α) ≤ bs.size := hs
    have e1 : (Enc.decode bs : Result α) = Enc.decode (bs.extract 0 (Enc.size α)) :=
      PrefixDecode.decode_prefix bs (by omega)
    have e2 : (Enc.decode (bs.extract 0 (alignUp (Enc.size α + 1) (Enc.align α))) : Result α) =
        Enc.decode (bs.extract 0 (Enc.size α)) := by
      rw [PrefixDecode.decode_prefix _ (by simp; omega), extract_extract_prefix (Nat.le_of_lt hlt)]
    rw [getElem?_extract_prefix hlt]
    simp only [e1, e2]

namespace Full

open FAssn

section Bytes

variable {q : Ptr} {a al o n : Nat} {bs : Array Byte}

/-- **Read of bytes** at byte `o` of a region. -/
theorem FTotalTriple.region_loadBytes (hn : 0 < n) (hb : al ∣ a) (ho : al ∣ o)
    (hfit : o + n ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.loadBytes (q.add o) n al)
      (fun x => ⟪x = bs.extract o (o + n)⟫ ⋆ up (Zig.region q a bs)) :=
  FTotalTriple.up_view fun _ ⟨A, S, K, ha, hK, hbs⟩ =>
    ⟨_, _, FTotalTriple.loadBytes_bytesAt hn hfit (mod_add_dvd ha hb ho), hbs,
      fun _ _ hb' => ⟨A, S, K, ha, hK, hb'⟩⟩

/-- **Write of bytes** at byte `o` of a region. -/
theorem FTotalTriple.region_storeBytes {bs' : Array Byte} (hn : 0 < bs'.size) (hb : al ∣ a)
    (ho : al ∣ o) (hfit : o + bs'.size ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.storeBytes (q.add o) al bs')
      (fun _ => up (Zig.region q a (writeBytes bs o bs'))) :=
  FTotalTriple.up_view' fun _ ⟨A, S, K, ha, hK, hbs⟩ =>
    ⟨_, _, FTotalTriple.storeBytes_bytesAt hn hfit (mod_add_dvd ha hb ho) hK, hbs,
      fun _ _ hb' => ⟨A, S, K, ha, hK, hb'⟩⟩

/-- **Pointer formation** (`ptrProject`, MM-3) of a byte offset `k` of a nonempty region, up to
one past its end. -/
theorem FTotalTriple.region_ptrProject {k : Int} (hpos : 0 < bs.size) (hk0 : 0 ≤ k)
    (hk : k ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (ptrProject q (·.add k))
      (fun r => ⟪r = q.add k⟫ ⋆ up (Zig.region q a bs)) :=
  FTotalTriple.of_read fun m r rF hh hp _ => by
    obtain ⟨⟨A, S, K, hr⟩, hk', hg⟩ := hp
    obtain ⟨b, hpb, h0, -⟩ := hr.2.2
    obtain ⟨blk, hblk, hK⟩ := Reaches.of_live (Live.region (a := a) hpb hpos) m r rF hh ⟨hr, hk', hg⟩
    exact ptrProject_add_run (inBounds_of hpb hblk h0 (by omega))
      (inBounds_of (p := q.add k) hpb hblk (by simp [Ptr.add]; omega) (by simp [Ptr.add]; omega))

end Bytes

/-- A returned value, as a fact. -/
theorem FTotalTriple.pure_read {β : Type} {P : FAssn} {v w : β} (h : v = w) :
    FTotalTriple P (pure v : MemM β) (fun r => ⟪r = w⟫ ⋆ P) :=
  (FTotalTriple.ret (Q := fun r => ⟪r = w⟫ ⋆ P) v).pre fun _ hp => sep_lift.mpr ⟨h, hp⟩

/-- A lifted `Result` that succeeds. -/
theorem liftM_pure {β : Type} (v : β) : (liftM (pure v : Result β) : MemM β) = pure v := rfl

section Pts

variable {T β : Type} [Enc T] {q : Ptr} {a : Nat} {s : T}

/-- A step on a typed value from the step on each of its byte strings. -/
theorem FTotalTriple.pts_bytes {c : MemM β} {Q : β → FAssn}
    (h : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      FTotalTriple (up (Zig.region q a bs)) c Q) :
    FTotalTriple (up (pts q a s)) c Q :=
  (FTotalTriple.ex fun bs => FTotalTriple.lift fun ⟨hs, hd⟩ => h bs hs hd).pre
    fun _ h => up_pts_iff.mp h

/-- A read of a typed value from the read of each of its byte strings. -/
theorem FTotalTriple.pts_read {c : MemM β} {v : β}
    (h : ∀ bs : Array Byte, bs.size = Enc.size T → Enc.decode bs = pure s →
      FTotalTriple (up (Zig.region q a bs)) c (fun r => ⟪r = v⟫ ⋆ up (Zig.region q a bs))) :
    FTotalTriple (up (pts q a s)) c (fun r => ⟪r = v⟫ ⋆ up (pts q a s)) :=
  FTotalTriple.pts_bytes fun bs hs hd => (h bs hs hd).post fun _ _ hx => by
    obtain ⟨e, hr⟩ := sep_lift.mp hx
    exact sep_lift.mpr ⟨e, up_pts_of_region hs hd hr⟩

/-- **An unused load** (`loadDiscardBytes`) of the first `n` bytes of an owned typed value. -/
@[fsym] theorem FTotalTriple.loadDiscard {n al : Nat} (hn : 0 < n) (hfit : n ≤ Enc.size T)
    (hb : al ∣ a) :
    FTotalTriple (up (pts q a s)) (Zig.loadDiscardBytes n al q) (fun _ => up (pts q a s)) := by
  rw [Zig.loadDiscardBytes_eq]
  refine FTotalTriple.pts_bytes fun bs hs hd => ?_
  have t := FTotalTriple.region_loadBytes (q := q) (o := 0) (bs := bs) hn hb (Nat.dvd_zero _)
    (by omega)
  simp only [Int.natCast_zero, Ptr.add_zero] at t
  exact FTotalTriple.bind t fun _ => FTotalTriple.lift fun _ =>
    (FTotalTriple.ret (Q := fun _ => up (pts q a s)) ()).pre fun _ hr =>
      up_pts_of_region hs hd hr

end Pts

/-! ## Error unions: the error code -/

section ErrUnion

variable {α : Type} [Enc α] {q : Ptr} {a al : Nat} {bs : Array Byte}

/-- The bytes of the error code of an error union, read through a pointer of alignment `al`. -/
theorem FTotalTriple.errCode_bytes (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hfit : (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs))
      (Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2 (Nat.min al 2))
      (fun x => ⟪x = bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
        ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)⟫ ⋆ up (Zig.region q a bs)) :=
  FTotalTriple.region_loadBytes (by decide) hal heo hfit

/-- **Pointer-form `try`** on the bytes of an error union whose error code reads `t`. -/
theorem FTotalTriple.tryPayloadPtr_region {t : Option ErrName} (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hfit : (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size)
    (hpo : (errUnionOffsets (Enc.size α) (Enc.align α)).2 ≤ bs.size)
    (ht : errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure t) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.tryPayloadPtr α al q)
      (fun r => ⟪r = t.elim (.ok (errPayloadPtr α q)) .error⟫ ⋆ up (Zig.region q a bs)) := by
  show FTotalTriple _ (do
    match ← liftM (errOfBytes (← Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1)
      2 (Nat.min al 2))) with
    | some e => pure (Except.error e : Except ErrName Ptr)
    | none => (Except.ok <$> ptrProject q fun x =>
        x.add ((errUnionOffsets (Enc.size α) (Enc.align α)).2 : Int) : MemM (Except ErrName Ptr))) _
  refine FTotalTriple.bind (FTotalTriple.errCode_bytes hal heo hfit) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  rw [ht, liftM_pure, pure_bind]
  cases t with
  | some e => exact FTotalTriple.pure_read rfl
  | none =>
    rw [map_eq_pure_bind]
    exact FTotalTriple.bind (FTotalTriple.region_ptrProject (by omega) (by omega) (by omega))
      fun y => FTotalTriple.lift fun hy => FTotalTriple.pure_read (by subst hy; rfl)

/-- **The error** of the bytes of an error union whose error code reads `e`. -/
theorem FTotalTriple.errCodeAt_region {e : ErrName} (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hfit : (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size)
    (ht : errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure (some e)) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.errCodeAt α al q)
      (fun r => ⟪r = e⟫ ⋆ up (Zig.region q a bs)) := by
  show FTotalTriple _ (do
    match ← liftM (errOfBytes (← Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1)
      2 (Nat.min al 2))) with
    | some e => pure e
    | none => throw .unspecified) _
  refine FTotalTriple.bind (FTotalTriple.errCode_bytes hal heo hfit) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  rw [ht, liftM_pure, pure_bind]
  exact FTotalTriple.pure_read rfl

/-- **Is it an error** (`is_err_ptr`): the bytes of an error union whose error code reads `t`. -/
theorem FTotalTriple.errIsErrAt_region {t : Option ErrName} (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hfit : (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size)
    (ht : errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure t) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.errIsErrAt α al q)
      (fun r => ⟪r = t.isSome⟫ ⋆ up (Zig.region q a bs)) := by
  show FTotalTriple _ (do
    let x ← liftM (errOfBytes (← Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1)
      2 (Nat.min al 2)))
    pure x.isSome) _
  refine FTotalTriple.bind (FTotalTriple.errCode_bytes hal heo hfit) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  rw [ht, liftM_pure, pure_bind]
  exact FTotalTriple.pure_read rfl

/-! ## Error unions: owned values -/

variable {u : Except ErrName α}

theorem errCode_fit {bs : Array Byte} (hs : bs.size = Enc.size (Except ErrName α)) :
    (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size := by
  rw [hs]; exact (errUnion_bounds _ _).1

theorem errPayload_fit {bs : Array Byte} (hs : bs.size = Enc.size (Except ErrName α)) :
    (errUnionOffsets (Enc.size α) (Enc.align α)).2 ≤ bs.size := by
  have := (errUnion_bounds (Enc.size α) (Enc.align α)).2.1
  rw [hs]; show _ ≤ errUnionSize _ _; omega

/-- **Pointer-form `try`** on an owned error union: its payload pointer or its error. -/
@[fsym] theorem FTotalTriple.tryPayloadPtr (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    FTotalTriple (up (pts q a u)) (Zig.tryPayloadPtr α al q)
      (fun r => ⟪r = tryView α q u⟫ ⋆ up (pts q a u)) :=
  FTotalTriple.pts_read fun _ hs hd => by
    have t := FTotalTriple.tryPayloadPtr_region (q := q) hal heo (errCode_fit hs) (errPayload_fit hs)
      (errUnion_decode_tag hd).1
    cases u <;> exact t

/-- **The error** of an owned error union that holds one (`unwrap_errunion_err_ptr`). -/
@[fsym] theorem FTotalTriple.errCodeAt {e : ErrName} (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    FTotalTriple (up (pts q a (Except.error e : Except ErrName α))) (Zig.errCodeAt α al q)
      (fun r => ⟪r = e⟫ ⋆ up (pts q a (Except.error e : Except ErrName α))) :=
  FTotalTriple.pts_read fun _ hs hd =>
    FTotalTriple.errCodeAt_region hal heo (errCode_fit hs) (errUnion_decode_tag hd).1

/-- **Is it an error** (`is_err_ptr`) of an owned error union. -/
@[fsym] theorem FTotalTriple.errIsErrAt (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    FTotalTriple (up (pts q a u)) (Zig.errIsErrAt α al q)
      (fun r => ⟪r = (errTagOf u).isSome⟫ ⋆ up (pts q a u)) :=
  FTotalTriple.pts_read fun _ hs hd =>
    FTotalTriple.errIsErrAt_region hal heo (errCode_fit hs) (errUnion_decode_tag hd).1

/-! ### A declared finite error domain

Generated code checks that an error read from memory belongs to the declared error set
(`finiteTryPayloadPtr`, `finiteErrCodeAt`, `finiteErrIsErrAt`, and the whole-union load and
store with `errorUnionEnc`): an owned union whose error is in the domain passes the check. -/

variable {d : ErrorDomain}

/-- **Pointer-form `try`** with a finite error domain. -/
@[fsym] theorem FTotalTriple.finiteTryPayloadPtr (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hdom : (errTagOf u).all d.names.contains = true) :
    FTotalTriple (up (pts q a u)) (Zig.finiteTryPayloadPtr d α al q)
      (fun r => ⟪r = tryView α q u⟫ ⋆ up (pts q a u)) := by
  unfold Zig.finiteTryPayloadPtr
  refine FTotalTriple.bind (FTotalTriple.tryPayloadPtr hal heo) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  have e : requireErrorUnion d (tryView α q u) = pure (tryView α q u) := by
    cases u with
    | ok => rfl
    | error e =>
      simp only [errTagOf, Option.all_some] at hdom
      show (if d.names.contains e then _ else _) = _
      simp only [hdom, ↓reduceIte]
  rw [e]
  exact FTotalTriple.pure_read rfl

/-- **The error** with a finite error domain. -/
@[fsym] theorem FTotalTriple.finiteErrCodeAt {e : ErrName} (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hdom : d.names.contains e = true) :
    FTotalTriple (up (pts q a (Except.error e : Except ErrName α))) (Zig.finiteErrCodeAt d α al q)
      (fun r => ⟪r = e⟫ ⋆ up (pts q a (Except.error e : Except ErrName α))) := by
  unfold Zig.finiteErrCodeAt
  refine FTotalTriple.bind (FTotalTriple.errCodeAt hal heo) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  have e' : requireError d x = pure x := by unfold requireError; simp only [hdom, ↓reduceIte]
  rw [e']
  exact FTotalTriple.pure_read rfl

/-- **Is it an error** with a finite error domain. -/
@[fsym] theorem FTotalTriple.finiteErrIsErrAt (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hdom : (errTagOf u).all d.names.contains = true) :
    FTotalTriple (up (pts q a u)) (Zig.finiteErrIsErrAt d α al q)
      (fun r => ⟪r = (errTagOf u).isSome⟫ ⋆ up (pts q a u)) :=
  FTotalTriple.pts_read fun bs hs hd => by
    have ht := (errUnion_decode_tag hd).1
    show FTotalTriple _ (do
      let x ← liftM ((optionalErrorEnc d).decode
        (← Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2 (Nat.min al 2)))
      pure x.isSome) _
    refine FTotalTriple.bind (FTotalTriple.errCode_bytes hal heo (errCode_fit hs)) fun x =>
      FTotalTriple.lift fun hx => ?_
    subst hx
    have e : (optionalErrorEnc d).decode (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
        ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure (errTagOf u) := by
      show (do match ← errOfBytes _ with
        | none => pure none
        | some e => if d.names.contains e then pure (some e) else throw Error.unspecified) = _
      rw [ht]
      cases u with
      | ok => rfl
      | error e =>
        simp only [errTagOf, Option.all_some] at hdom
        show (if d.names.contains e then _ else _) = _
        simp only [hdom, ↓reduceIte]
        rfl
    rw [e, liftM_pure, pure_bind]
    exact FTotalTriple.pure_read rfl

/-- The error union's encoding with a finite domain writes a value whose error is in the domain
as the plain encoding does. -/
theorem errorUnionEnc_encode {w : Except ErrName α}
    (hdom : (errTagOf w).all d.names.contains = true) :
    (errorUnionEnc d inferInstance).encode w = Enc.encode w := by
  cases w with
  | ok => rfl
  | error e =>
    simp only [errTagOf, Option.all_some] at hdom
    show (if d.names.contains e then _ else _) = _
    simp only [hdom, ↓reduceIte]
    rfl

/-- … and reads such a value as the plain encoding does. -/
theorem errorUnionEnc_decode {bs : Array Byte} {w : Except ErrName α}
    (h : Enc.decode bs = pure w) (hdom : (errTagOf w).all d.names.contains = true) :
    (errorUnionEnc d inferInstance).decode bs = pure w := by
  have hb : (Enc.errorUnionWith (inferInstance : Enc α)).decode bs = pure w := h
  unfold errorUnionEnc
  show (do let v ← (Enc.errorUnionWith (inferInstance : Enc α)).decode bs; _) = _
  rw [hb]
  cases w with
  | ok => rfl
  | error e =>
    simp only [errTagOf, Option.all_some] at hdom
    show (if d.names.contains e then _ else _) = _
    simp only [hdom, ↓reduceIte]

theorem errUnion_size_pos : 0 < Enc.size (Except ErrName α) := by
  have := (errUnion_bounds (Enc.size α) (Enc.align α)).1
  show 0 < errUnionSize _ _
  omega

/-- **Load of a whole error union** with a finite error domain. -/
@[fsym] theorem FTotalTriple.load_finite {b : Nat} (hb : b ∣ a)
    (hdom : (errTagOf u).all d.names.contains = true) :
    FTotalTriple (up (pts q a u)) (@Zig.load (Except ErrName α) (errorUnionEnc d inferInstance) b q)
      (fun r => ⟪r = u⟫ ⋆ up (pts q a u)) := by
  letI : Enc (Except ErrName α) := instEncExceptErrName
  have hv : ∀ bs : Array Byte, bs.size = Enc.size (Except ErrName α) →
      Enc.decode bs = pure u →
      (errorUnionEnc d inferInstance).decode (bs.extract 0 (Enc.size (Except ErrName α))) = pure u :=
    fun bs hs hd => by
      rw [← hs, Array.extract_size]
      exact errorUnionEnc_decode hd hdom
  exact @FTotalTriple.field_load0 (Except ErrName α) (Except ErrName α) _ (errorUnionEnc d inferInstance)
    q a b u u errUnion_size_pos hb (Nat.le_refl _) hv

/-- **Store of a whole error union** with a finite error domain. -/
@[fsym] theorem FTotalTriple.store_finite [LawfulEnc α] {b : Nat} (w : Except ErrName α)
    (hb : b ∣ a) (hdom : (errTagOf w).all d.names.contains = true) :
    FTotalTriple (up (pts q a u)) (@Zig.store (Except ErrName α) (errorUnionEnc d inferInstance) b q w)
      (fun _ => up (pts q a w)) := by
  have e : @Zig.store (Except ErrName α) (errorUnionEnc d inferInstance) b q w = Zig.store b q w := by
    unfold Zig.store; rw [errorUnionEnc_encode hdom]
  rw [e]
  refine FTotalTriple.field_store0 w
    errUnion_size_pos
    hb (Nat.le_refl _) fun bs hs _ => ?_
  have hw := LawfulEnc.size_encode w
  have e2 : writeBytes bs 0 (Enc.encode w) = Enc.encode w := by
    simp [writeBytes, hw, hs]
  rw [e2]; exact LawfulEnc.decode_encode w

section Block

variable {p : Ptr} {A S : Nat} {K : BlockKind} {b : BlockId}

/-- **Store of a whole error union** with a finite error domain at the start of a block's bytes
held with the block's extent (an escaping local, `Full/Local.lean`). -/
@[fsym] theorem FTotalTriple.storeBlock_finite [LawfulEnc α] (w : Except ErrName α)
    (hpb : p.block = some b) (hk : Enc.size (Except ErrName α) ≤ bs.size)
    (ha : (A + p.off.toNat) % al = 0) (hK : K ≠ .constGlobal)
    (hdom : (errTagOf w).all d.names.contains = true) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K)
      (@Zig.store (Except ErrName α) (errorUnionEnc d inferInstance) al p w)
      (fun _ => up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K) := by
  have e : @Zig.store (Except ErrName α) (errorUnionEnc d inferInstance) al p w = Zig.store al p w := by
    unfold Zig.store; rw [errorUnionEnc_encode hdom]
  rw [e]
  have hw := LawfulEnc.size_encode w
  exact FTotalTriple.storeBlock w hpb (by rw [hw]; exact errUnion_size_pos) (by rw [hw]; exact hk) ha hK

/-- **Load of the error union stored** at the start of a block's bytes, with a finite error
domain: it reads back what was stored. -/
@[fsym] theorem FTotalTriple.loadBlock_finite [LawfulEnc α] {w : Except ErrName α}
    (hpb : p.block = some b) (hk : Enc.size (Except ErrName α) ≤ bs.size)
    (ha : (A + p.off.toNat) % al = 0) (hdom : (errTagOf w).all d.names.contains = true) :
    FTotalTriple (up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K)
      (@Zig.load (Except ErrName α) (errorUnionEnc d inferInstance) al p)
      (fun x => ⟪x = w⟫ ⋆ (up (bytesAt p A S K (writeBytes bs 0 (Enc.encode w))) ⋆ bext b S K)) := by
  have hw := LawfulEnc.size_encode w
  refine @FTotalTriple.loadBlock (Except ErrName α) (errorUnionEnc d inferInstance) p A S K _ b al w
    hpb errUnion_size_pos (by rw [writeBytes_size _ _ _ (by omega)]; exact hk) ?_ ha
  have e := extract_writeBytes bs 0 (Enc.encode w) (by omega)
  rw [hw, Nat.zero_add] at e
  have hd : Enc.decode ((writeBytes bs 0 (Enc.encode w)).extract 0 (Enc.size (Except ErrName α))) =
      pure w := by rw [e]; exact LawfulEnc.decode_encode w
  exact errorUnionEnc_decode hd hdom

end Block

/-! ### Payload pointers -/

/-- **The payload pointer** (`unwrap_errunion_payload_ptr`) of an error union in block `b`, which
reaches past the union. -/
@[fsym] theorem FTotalTriple.ptrProject_errPayload {P : FAssn} {b : BlockId} {K : Nat}
    (hqb : q.block = some b) (h : Reaches b K P) (h0 : 0 ≤ q.off)
    (hk : q.off + (Enc.size (Except ErrName α) : Nat) ≤ K) :
    FTotalTriple P (ptrProject q (errPayloadPtr α)) (fun r => ⟪r = errPayloadPtr α q⟫ ⋆ P) := by
  have := (errUnion_bounds (Enc.size α) (Enc.align α)).2.1
  have hs : Enc.size (Except ErrName α) = errUnionSize (Enc.size α) (Enc.align α) := rfl
  exact FTotalTriple.ptrProject_of (k := ((errUnionOffsets (Enc.size α) (Enc.align α)).2 : Int))
    hqb h h0 (by omega) (by omega) (by omega)

/-! ### Setting the error code to "no error" (`errunion_payload_ptr_set`) -/

/-- **`errSetOk`** on the bytes of an error union: its error code becomes 0. -/
theorem FTotalTriple.errSetOk_region (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hfit : (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 ≤ bs.size)
    (hpo : (errUnionOffsets (Enc.size α) (Enc.align α)).2 ≤ bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.errSetOk α al q)
      (fun r => ⟪r = errPayloadPtr α q⟫ ⋆ up (Zig.region q a
        (writeBytes bs (errUnionOffsets (Enc.size α) (Enc.align α)).1 (errBytes none)))) := by
  show FTotalTriple _ (do
    Zig.storeBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min al 2)
      (errBytes none)
    ptrProject q (·.add ((errUnionOffsets (Enc.size α) (Enc.align α)).2 : Int))) _
  have hw : (writeBytes bs (errUnionOffsets (Enc.size α) (Enc.align α)).1 (errBytes none)).size =
      bs.size := writeBytes_size _ _ _ (by simpa [errBytes] using hfit)
  exact FTotalTriple.bind (FTotalTriple.region_storeBytes (by decide) hal heo hfit) fun _ =>
    FTotalTriple.region_ptrProject (by omega) (by omega) (by omega)

/-- An error union whose error code is 0, with any payload bytes: the result of `errSetOk`,
until the payload is written (`errOkSlot_store`). -/
def errOkSlot (α : Type) [Enc α] (q : Ptr) (a : Nat) : FAssn :=
  FAssn.ex fun bs : Array Byte => ⟪bs.size = Enc.size (Except ErrName α) ∧
    errOfBytes (bs.extract (errUnionOffsets (Enc.size α) (Enc.align α)).1
      ((errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2)) = pure none⟫ ⋆ up (Zig.region q a bs)

/-- **`errSetOk`** on an owned error union. -/
@[fsym] theorem FTotalTriple.errSetOk (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    FTotalTriple (up (pts q a u)) (Zig.errSetOk α al q)
      (fun r => ⟪r = errPayloadPtr α q⟫ ⋆ errOkSlot α q a) :=
  FTotalTriple.pts_bytes fun bs hs _ =>
    (FTotalTriple.errSetOk_region hal heo (errCode_fit hs) (errPayload_fit hs)).post fun _ _ h => by
      obtain ⟨e, hr⟩ := sep_lift.mp h
      have hfit := errCode_fit (α := α) hs
      refine sep_lift.mpr ⟨e, _, sep_lift.mpr ⟨⟨?_, ?_⟩, hr⟩⟩
      · rw [writeBytes_size _ _ _ (by simpa [errBytes] using hfit), hs]
      · rw [show (errUnionOffsets (Enc.size α) (Enc.align α)).1 + 2 =
          (errUnionOffsets (Enc.size α) (Enc.align α)).1 + (errBytes none).size from rfl,
          extract_writeBytes _ _ _ (by simpa [errBytes] using hfit)]
        rfl

/-- **The payload write** after `errSetOk`: the union holds the payload. -/
@[fsym] theorem FTotalTriple.errOkSlot_store [LawfulEnc α] {b : Nat} (y : α)
    (hn : 0 < Enc.size α) (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) :
    FTotalTriple (errOkSlot α q a) (Zig.store b (errPayloadPtr α q) y)
      (fun _ => up (pts q a (Except.ok y : Except ErrName α))) :=
  FTotalTriple.ex fun bs => FTotalTriple.lift fun ⟨hs, hc⟩ =>
    (FTotalTriple.region_storeAt (q := q) y hn hb hpo
      (by rw [hs]; exact (errUnion_bounds _ _).2.1)).post fun _ _ hr =>
      up_pts_of_region (by
          rw [writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode, hs]; exact (errUnion_bounds _ _).2.1),
            hs])
        (errUnion_decode_setPayload y hs hc) hr

/-- `errSetOk` keeps an error union that holds a payload. -/
theorem errUnion_decode_setOk {bs : Array Byte} {x : α}
    (hs : bs.size = Enc.size (Except ErrName α))
    (h : Enc.decode bs = pure (Except.ok x : Except ErrName α)) :
    Enc.decode (writeBytes bs (errUnionOffsets (Enc.size α) (Enc.align α)).1 (errBytes none)) =
      pure (Except.ok x : Except ErrName α) := by
  obtain ⟨-, hp⟩ := errUnion_decode_ok h
  obtain ⟨h1, h2, hd⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  have hsz : bs.size = errUnionSize (Enc.size α) (Enc.align α) := hs
  simp only [Enc.decode]
  revert hp h1 h2 hd
  generalize errUnionOffsets (Enc.size α) (Enc.align α) = r
  obtain ⟨eo, po⟩ := r
  intro hp h1 h2 hd
  simp only at hp h1 h2 hd ⊢
  have he : (errBytes none).size = 2 := rfl
  rw [extract_writeBytes_disjoint bs eo (errBytes none) po (Enc.size α) (by omega) (by omega)
    (by omega), hp]
  have hc := extract_writeBytes bs eo (errBytes none) (by omega)
  rw [he] at hc
  rw [hc]
  rfl

/-- **`errSetOk`** on an error union that holds a payload keeps it. -/
theorem FTotalTriple.errSetOk_ok {x : α} (hal : Nat.min al 2 ∣ a)
    (heo : Nat.min al 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    FTotalTriple (up (pts q a (Except.ok x : Except ErrName α))) (Zig.errSetOk α al q)
      (fun r => ⟪r = errPayloadPtr α q⟫ ⋆ up (pts q a (Except.ok x : Except ErrName α))) :=
  FTotalTriple.pts_bytes fun bs hs hd =>
    (FTotalTriple.errSetOk_region hal heo (errCode_fit hs) (errPayload_fit hs)).post fun _ _ h => by
      obtain ⟨e, hr⟩ := sep_lift.mp h
      have hfit := errCode_fit (α := α) hs
      exact sep_lift.mpr ⟨e, up_pts_of_region
        (by rw [writeBytes_size _ _ _ (by simpa [errBytes] using hfit), hs])
        (errUnion_decode_setOk hs hd) hr⟩

end ErrUnion

/-! ## Optionals `?T` (`T` not a pointer): the flag byte after the payload -/

section Optional

variable {α : Type} [Enc α] {q : Ptr} {a b : Nat} {bs : Array Byte} {o : Option α}

theorem opt_size_lt : Enc.size α < Enc.size (Option α) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_alignUp _ _)

/-- **`is_non_null_ptr`** on the bytes of an optional whose flag byte is `.int x`, `x` 0 or 1. -/
theorem FTotalTriple.optIsSome_region {x : BitVec 8} (hfit : Enc.size α < bs.size)
    (hf : bs[Enc.size α]? = some (.int x)) (hx : x = 0 ∨ x = 1) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.optIsSome α q)
      (fun r => ⟪r = decide (x = 1)⟫ ⋆ up (Zig.region q a bs)) := by
  unfold Zig.optIsSome
  refine FTotalTriple.bind (FTotalTriple.region_loadBytes (o := Enc.size α) (n := 1) (al := 1)
    (by decide) (Nat.one_dvd _) (Nat.one_dvd _) hfit) fun y => FTotalTriple.lift fun hy => ?_
  subst hy
  have e : (bs.extract (Enc.size α) (Enc.size α + 1))[0]? = some (Byte.int x) := by
    rw [← hf]; simp [Array.getElem?_extract]; omega
  rw [e]
  rcases hx with rfl | rfl
  · exact FTotalTriple.pure_read (by decide)
  · exact FTotalTriple.pure_read (by decide)

/-- **`is_non_null_ptr`** on an owned optional. -/
@[fsym] theorem FTotalTriple.optIsSome :
    FTotalTriple (up (pts q a o)) (Zig.optIsSome α q)
      (fun r => ⟪r = o.isSome⟫ ⋆ up (pts q a o)) :=
  FTotalTriple.pts_read fun _ hs hd => by
    have hf := (opt_decode hd).1
    have t := FTotalTriple.optIsSome_region (q := q) (a := a) (hs ▸ opt_size_lt) hf
      (by cases o <;> simp)
    cases o <;> exact t

/-- **`optional_payload_ptr_set`** on the bytes of an optional: the flag byte becomes 1. -/
theorem FTotalTriple.optSetSome_region (hfit : Enc.size α < bs.size) :
    FTotalTriple (up (Zig.region q a bs)) (Zig.optSetSome α q)
      (fun r => ⟪r = q⟫ ⋆ up (Zig.region q a (writeBytes bs (Enc.size α) #[.int 1]))) := by
  unfold Zig.optSetSome
  exact FTotalTriple.bind (FTotalTriple.region_storeBytes (o := Enc.size α) (al := 1)
    (bs' := #[.int 1]) (by decide) (Nat.one_dvd _) (Nat.one_dvd _) hfit) fun _ =>
    FTotalTriple.pure_read rfl

theorem getElem?_writeBytes_flag {bs : Array Byte} {o : Nat} {x : Byte} (h : o < bs.size) :
    (writeBytes bs o #[x])[o]? = some x := by
  have hw : (writeBytes bs o #[x]).size = bs.size := writeBytes_size _ _ _ (by simp; omega)
  have h1 : (writeBytes bs o #[x]).extract o (o + 1) = #[x] :=
    extract_writeBytes bs o #[x] (by simp; omega)
  have h2 : ((writeBytes bs o #[x]).extract o (o + 1))[0]? = (writeBytes bs o #[x])[o]? := by
    simp [Array.getElem?_extract]; omega
  rw [← h2, h1]; rfl

/-- An optional whose flag byte is 1, with any payload bytes: the result of `optSetSome`, until
the payload is written (`optSomeSlot_store`). -/
def optSomeSlot (α : Type) [Enc α] (q : Ptr) (a : Nat) : FAssn :=
  FAssn.ex fun bs : Array Byte =>
    ⟪bs.size = Enc.size (Option α) ∧ bs[Enc.size α]? = some (.int 1)⟫ ⋆ up (Zig.region q a bs)

/-- **`optional_payload_ptr_set`** on an owned optional. -/
@[fsym] theorem FTotalTriple.optSetSome :
    FTotalTriple (up (pts q a o)) (Zig.optSetSome α q) (fun r => ⟪r = q⟫ ⋆ optSomeSlot α q a) :=
  FTotalTriple.pts_bytes fun bs hs _ =>
    (FTotalTriple.optSetSome_region (hs ▸ opt_size_lt)).post fun _ _ h => by
      obtain ⟨e, hr⟩ := sep_lift.mp h
      have hlt : Enc.size α < bs.size := hs ▸ opt_size_lt
      refine sep_lift.mpr ⟨e, _, sep_lift.mpr ⟨⟨?_, getElem?_writeBytes_flag hlt⟩, hr⟩⟩
      rw [writeBytes_size _ _ _ (by simp; omega), hs]

/-- The flag byte of an optional's bytes, through a prefix that holds it. -/
theorem getElem?_flag {bs bs' : Array Byte} {s : Nat}
    (h : bs.extract s (s + 1) = bs'.extract s (s + 1)) (hs : s < bs.size) (hs' : s < bs'.size) :
    bs[s]? = bs'[s]? := by
  have h1 : (bs.extract s (s + 1))[0]? = bs[s]? := by simp [Array.getElem?_extract]; omega
  have h2 : (bs'.extract s (s + 1))[0]? = bs'[s]? := by simp [Array.getElem?_extract]; omega
  rw [← h1, ← h2, h]

/-- The bytes of an optional with the flag byte 1 and `y` written at byte 0. -/
theorem opt_decode_write [LawfulEnc α] [PrefixDecode α] {bs : Array Byte} (y : α)
    (hs : bs.size = Enc.size (Option α)) (hf : bs[Enc.size α]? = some (.int 1)) :
    (Enc.decode (writeBytes bs 0 (Enc.encode y)) : Result (Option α)) = pure (some y) := by
  have hy := LawfulEnc.size_encode y
  have hlt : Enc.size α < bs.size := hs ▸ opt_size_lt
  have hw : (writeBytes bs 0 (Enc.encode y)).size = bs.size :=
    writeBytes_size _ _ _ (by omega)
  refine opt_decode_of (by omega) ?_ ?_
  · rw [← hf]
    exact getElem?_flag (extract_writeBytes_disjoint bs 0 (Enc.encode y) (Enc.size α) 1 (by omega)
      (by omega) (by omega)) (by omega) hlt
  · have := extract_writeBytes bs 0 (Enc.encode y) (by omega)
    rw [hy, Nat.zero_add] at this
    rw [this]; exact LawfulEnc.decode_encode y

/-- **The payload write** after `optSetSome`: the optional holds the payload. -/
@[fsym] theorem FTotalTriple.optSomeSlot_store [LawfulEnc α] [PrefixDecode α] (y : α)
    (hn : 0 < Enc.size α) (hb : b ∣ a) :
    FTotalTriple (optSomeSlot α q a) (Zig.store b q y) (fun _ => up (pts q a (some y))) :=
  FTotalTriple.ex fun bs => FTotalTriple.lift fun ⟨hs, hf⟩ => by
    have hfit : Enc.size α ≤ bs.size := by rw [hs]; exact Nat.le_of_lt opt_size_lt
    have hws : (writeBytes bs 0 (Enc.encode y)).size = bs.size :=
      writeBytes_size _ _ _ (by rw [LawfulEnc.size_encode]; omega)
    exact (FTotalTriple.region_store0 (q := q) y hn hb hfit).post fun _ _ hr =>
      up_pts_of_region (hws.trans hs) (opt_decode_write y hs hf) hr

/-- **`optional_payload_ptr_set`** on an optional that holds a payload keeps it. -/
theorem FTotalTriple.optSetSome_some [PrefixDecode α] {x : α} :
    FTotalTriple (up (pts q a (some x))) (Zig.optSetSome α q)
      (fun r => ⟪r = q⟫ ⋆ up (pts q a (some x))) :=
  FTotalTriple.pts_bytes fun bs hs hd =>
    (FTotalTriple.optSetSome_region (hs ▸ opt_size_lt)).post fun _ _ h => by
      obtain ⟨e, hr⟩ := sep_lift.mp h
      have hlt : Enc.size α < bs.size := hs ▸ opt_size_lt
      have hws : (writeBytes bs (Enc.size α) #[.int 1]).size = bs.size :=
        writeBytes_size _ _ _ (by simp; omega)
      refine sep_lift.mpr ⟨e, up_pts_of_region (hws.trans hs) ?_ hr⟩
      refine opt_decode_of (by omega) (getElem?_writeBytes_flag hlt) ?_
      have e1 := extract_writeBytes_disjoint bs (Enc.size α) #[.int 1] 0 (Enc.size α)
        (by simp; omega) (by omega) (by simp)
      rw [Nat.zero_add] at e1
      rw [e1, ← PrefixDecode.decode_prefix bs (Nat.le_of_lt hlt)]
      exact (opt_decode hd).2 x rfl

/-- **Load of the payload** of an optional that holds `some x`, through its payload pointer
(the optional's address: `optional_payload_ptr`). -/
@[fsym] theorem FTotalTriple.optPayload_load [PrefixDecode α] {x : α} (hn : 0 < Enc.size α)
    (hb : b ∣ a) :
    FTotalTriple (up (pts q a (some x))) (Zig.load α b q)
      (fun r => ⟪r = x⟫ ⋆ up (pts q a (some x))) :=
  FTotalTriple.field_load0 hn hb (Nat.le_of_lt opt_size_lt) fun bs hs hd => by
    rw [← PrefixDecode.decode_prefix bs (hs ▸ Nat.le_of_lt opt_size_lt)]
    exact (opt_decode hd).2 x rfl

/-- **Store of the payload** of an optional that holds a payload: it then holds `some y`. -/
@[fsym] theorem FTotalTriple.optPayload_store [LawfulEnc α] [PrefixDecode α] {x : α} (y : α)
    (hn : 0 < Enc.size α) (hb : b ∣ a) :
    FTotalTriple (up (pts q a (some x))) (Zig.store b q y) (fun _ => up (pts q a (some y))) :=
  FTotalTriple.field_store0 y hn hb (Nat.le_of_lt opt_size_lt) fun _ hs hd =>
    opt_decode_write y hs (by simpa using (opt_decode hd).1)

end Optional

/-! ## Optional error sets `?E`: the error code, 0 for `null` -/

section OptionalError

variable {d : ErrorDomain} {q : Ptr} {a al : Nat} {o : Option ErrName}

/-- **`is_non_null_ptr`** of an owned `?E`. -/
@[fsym] theorem FTotalTriple.optionalErrorIsSome (hb : al ∣ a) :
    FTotalTriple (up (@pts (Option ErrName) (optionalErrorEnc d) q a o))
      (Zig.optionalErrorIsSome d al q)
      (fun r => ⟪r = o.isSome⟫ ⋆ up (@pts (Option ErrName) (optionalErrorEnc d) q a o)) :=
  @FTotalTriple.pts_read (Option ErrName) Bool (optionalErrorEnc d) q a o _ _ fun bs hs hd => by
    have t := FTotalTriple.region_loadBytes (q := q) (o := 0) (n := 2) (bs := bs) (by decide) hb
      (Nat.dvd_zero _) (by rw [hs]; exact Nat.le_refl _)
    simp only [Int.natCast_zero, Ptr.add_zero] at t
    unfold Zig.optionalErrorIsSome
    refine FTotalTriple.bind t fun x => FTotalTriple.lift fun hx => ?_
    subst hx
    have e : bs.extract 0 (0 + 2) = bs := by
      rw [Nat.zero_add, show 2 = bs.size from hs.symm, Array.extract_size]
    rw [e, hd, liftM_pure, pure_bind]
    exact FTotalTriple.pure_read rfl

end OptionalError

/-! ## Readable bytes: owned or `const`

`ReadAt p a bs P`: every memory that holds `P` has the bytes `bs` at `p`, readable with
alignment `a`. Owned bytes give it whatever their block's kind (`ReadAt.bytesAt`,
`ReadAt.region`), and so do the persistent bytes of a `const` global (`ReadAt.ofConst`,
`ReadAt.cbytesAt`); it frames (`sepL`, `sepR`) and cuts (`shift`). The read rules take it, so an
owned read and a `const` read are one rule, and a read leaves `P` as it was. -/

section Readable

variable {p : Ptr} {a al : Nat} {bs : Array Byte} {P R : FAssn}

/-- Every memory that holds `P` has the bytes `bs` at `p` in a live block, at or above its first
live offset, at an address that keeps `p` aligned to `a`. -/
def ReadAt (p : Ptr) (a : Nat) (bs : Array Byte) (P : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧
    blk.live = true ∧ 0 ≤ p.off ∧ blk.kind.mappedLo ≤ p.off.toNat ∧
    (blk.addr + p.off.toNat) % a = 0 ∧ ∀ i (h : i < bs.size), blk.bytes[p.off.toNat + i]? = some bs[i]

theorem ReadAt.sepL (h : ReadAt p a bs P) : ReadAt p a bs (P ⋆ R) := fun m _ rF hh hp => by
  obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hp
  exact h m r₁ _ (Holds.split hd hh) h1

theorem ReadAt.sepR (h : ReadAt p a bs P) : ReadAt p a bs (R ⋆ P) := fun m r rF hh hp =>
  h.sepL m r rF hh (sep_comm hp)

theorem ReadAt.of_imp {P' : FAssn} (h : ReadAt p a bs P) (hp : ∀ r, P' r → P r) :
    ReadAt p a bs P' := fun m r rF hh h' => h m r rF hh (hp r h')

/-- **Part of readable bytes**: `n` bytes at byte `o`, with an alignment that divides both. -/
theorem ReadAt.shift {o n : Nat} (h : ReadAt p a bs P) (hal : al ∣ a) (ho : al ∣ o)
    (hfit : o + n ≤ bs.size) : ReadAt (p.add o) al (bs.extract o (o + n)) P :=
  fun m r rF hh hp => by
    obtain ⟨b, blk, hpb, hblk, hl, h0, hlo, ha, hx⟩ := h m r rF hh hp
    have e : (p.add o).off.toNat = p.off.toNat + o := by simp only [Ptr.add]; omega
    refine ⟨b, blk, hpb, hblk, hl, by simp only [Ptr.add]; omega, by rw [e]; omega, ?_,
      fun i hi => ?_⟩
    · rw [e, ← Nat.add_assoc]; exact mod_add_dvd ha hal ho
    · simp only [Array.size_extract] at hi
      rw [e, Nat.add_assoc, hx (o + i) (by omega), Array.getElem_extract]

/-- **Part of owned bytes of any block kind** is readable: `n` bytes at byte `o`, aligned to
`al` at the block address `A` the bytes carry. -/
theorem ReadAt.bytesAt_part {A S o n : Nat} {K : BlockKind} (hA : (A + p.off.toNat + o) % al = 0)
    (hn : 0 < n) (hfit : o + n ≤ bs.size) :
    ReadAt (p.add o) al (bs.extract o (o + n)) (up (Zig.bytesAt p A S K bs)) := fun m r rF hh hp => by
  obtain ⟨⟨b, hpb, h0, hbs⟩, -, -⟩ := hp
  have cell : ∀ i, i < bs.size → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      blk.kind.mappedLo ≤ p.off.toNat + i ∧ blk.addr = A ∧
      blk.bytes[p.off.toNat + i]? = some bs[i]! := by
    intro i hi
    have e := hbs (b, p.off.toNat + i)
    rw [ite_eq_left ⟨rfl, by omega, by omega⟩, Nat.add_sub_cancel_left] at e
    obtain ⟨fc, hfc, hc⟩ := erase_cell e
    obtain ⟨blk, hb, hl, hx, hlo, ha, -⟩ := hh.block hfc
    obtain ⟨c', hc', hn⟩ := hh.cellN hfc
    obtain ⟨blk', hb', -, hx', rfl⟩ := Mem.heap_some hc'
    rw [hb] at hb'; cases hb'
    have hbyte := congrArg Cell.byte hn
    simp only [Cell.norm, hc] at hbyte
    refine ⟨blk, hb, hl, hlo, by rw [← ha, hc], ?_⟩
    rw [Array.getElem?_eq_getElem hx', hbyte]
  have e : (p.add o).off.toNat = p.off.toNat + o := by simp only [Ptr.add]; omega
  obtain ⟨blk, hblk, hl, hlo, hA', -⟩ := cell o (by omega)
  refine ⟨b, blk, hpb, hblk, hl, by simp only [Ptr.add]; omega, by rw [e]; exact hlo,
    by rw [e, hA', ← Nat.add_assoc]; exact hA, fun i hi => ?_⟩
  simp only [Array.size_extract] at hi
  obtain ⟨blk', hb', -, -, -, hx⟩ := cell (o + i) (by omega)
  rw [hblk] at hb'; cases hb'
  rw [e, Nat.add_assoc, hx, getElem!_pos bs (o + i) (by omega), Array.getElem_extract]

/-- **Owned bytes of any block kind** are readable. -/
theorem ReadAt.bytesAt {A S : Nat} {K : BlockKind} (hA : (A + p.off.toNat) % a = 0)
    (hpos : 0 < bs.size) : ReadAt p a bs (up (Zig.bytesAt p A S K bs)) := by
  have h := ReadAt.bytesAt_part (p := p) (bs := bs) (S := S) (K := K) (o := 0) (n := bs.size)
    (by simpa using hA) hpos (by omega)
  simpa only [Int.natCast_zero, Ptr.add_zero, Nat.zero_add, Array.extract_size] using h

/-- Owned bytes `bs` of any block kind at `p`, aligned to `a` (`region` without the kind
restriction: what a read needs). -/
def ownedBytes (p : Ptr) (a : Nat) (bs : Array Byte) : Assn := fun h =>
  ∃ A S K, (A + p.off.toNat) % a = 0 ∧ Zig.bytesAt p A S K bs h

theorem SizeFree.ownedBytes : SizeFree (fun _ => none) (Full.ownedBytes p a bs) :=
  SizeFree.bytesAt_ex fun _ _ _ _ _ h _ => h

/-- **Owned bytes** are readable. -/
theorem ReadAt.ownedBytes (hpos : 0 < bs.size) : ReadAt p a bs (up (ownedBytes p a bs)) :=
  fun m r rF hh hp => by
    obtain ⟨⟨A, S, K, hA, hb⟩, hk, hg⟩ := hp
    exact ReadAt.bytesAt hA hpos m r rF hh ⟨hb, hk, hg⟩

/-- **An owned region** is readable. -/
theorem ReadAt.region (hpos : 0 < bs.size) : ReadAt p a bs (up (Zig.region p a bs)) :=
  fun m r rF hh hp => by
    obtain ⟨⟨A, S, K, hA, -, hb⟩, hk, hg⟩ := hp
    exact ReadAt.bytesAt hA hpos m r rF hh ⟨hb, hk, hg⟩

/-- **The bytes of a `const` global** that a `ConstAt` provider gives are readable. -/
theorem ReadAt.ofConst {φ : Nat → Array Byte → Prop} (h : ConstAt p φ P)
    (hφ : ∀ A bs', φ A bs' → (A + p.off.toNat) % a = 0 ∧ bs' = bs) : ReadAt p a bs P :=
  fun m r rF hh hp => by
    obtain ⟨b, blk, bs', hpb, hblk, hk, hl, h0, -, h7, hx⟩ := h m r rF hh hp
    obtain ⟨ha, rfl⟩ := hφ _ _ h7
    exact ⟨b, blk, hpb, hblk, hl, h0, by rw [hk]; simp [BlockKind.mappedLo], ha, hx⟩

/-- **Persistent `const` bytes** are readable. -/
theorem ReadAt.cbytesAt {A : Nat} (hA : (A + p.off.toNat) % a = 0) (hpos : 0 < bs.size) :
    ReadAt p a bs (Zig.Full.cbytesAt p A bs) :=
  ReadAt.ofConst (ConstAt.cbytesAt hpos) fun _ _ ⟨e1, e2⟩ => ⟨e1 ▸ hA, e2⟩

/-- The block, offset and bytes of a read that a provider allows. -/
private theorem ReadAt.access {n : Nat} (h : ReadAt p al bs P) (hn : 0 < n) (hs : bs.size = n)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r) :
    ∃ b blk, m.access p n al = pure (b, blk, p.off.toNat) ∧
      blk.bytes.extract p.off.toNat (p.off.toNat + n) = bs := by
  obtain ⟨b, blk, hpb, hblk, hl, h0, hlo, ha, hx⟩ := h m r rF hh hp
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp (hx (n - 1) (by omega))
  refine ⟨b, blk, access_of hpb hblk hl h0 (by omega) ha hlo, ?_⟩
  apply Array.ext
  · simp only [Array.size_extract]; omega
  · intro i h1 h2
    obtain ⟨_, he⟩ := Array.getElem?_eq_some_iff.mp (hx i h2)
    simp only [Array.getElem_extract]; exact he

/-- **Read of readable bytes**: owned or `const`, `P` stays. -/
theorem FTotalTriple.loadBytes_of {n : Nat} (h : ReadAt p al bs P) (hn : 0 < n) (hs : bs.size = n) :
    FTotalTriple P (Zig.loadBytes p n al) (fun x => ⟪x = bs⟫ ⋆ P) :=
  FTotalTriple.of_run fun m r rF hh hp hst => by
    obtain ⟨b, blk, hacc, hx⟩ := h.access hn hs hh hp
    refine ⟨bs, m.recordAt b p.off.toNat n .read, r, ?_, ⟨hh.1, hh.2, hh.3, hh.4, hh.5⟩,
      sep_lift.mpr ⟨rfl, hp⟩, ⟨hst.1.recordAt _ _ _ _, hst.2.1, hst.2.2⟩⟩
    rw [loadBytes_run hacc (noRace_of_singleThread hst.1.single _ _ _ _), hx]

/-- **An unused load** (`loadDiscardBytes`) of readable bytes. -/
theorem FTotalTriple.loadDiscard_of {n : Nat} (h : ReadAt p al bs P) (hn : 0 < n)
    (hs : bs.size = n) : FTotalTriple P (Zig.loadDiscardBytes n al p) (fun _ => P) :=
  FTotalTriple.of_run fun m r rF hh hp hst => by
    obtain ⟨b, blk, hacc, -⟩ := h.access hn hs hh hp
    exact ⟨(), _, r, loadDiscardBytes_run hacc (noRace_of_singleThread hst.1.single _ _ _ _),
      ⟨hh.1, hh.2, hh.3, hh.4, hh.5⟩, hp, ⟨hst.1.recordAt _ _ _ _, hst.2.1, hst.2.2⟩⟩

variable {α : Type} [Enc α] {q : Ptr} {tb : Array Byte} {d : ErrorDomain}

/-- **Pointer-form `try`** from the readable bytes `tb` of the error code at `q`. -/
theorem FTotalTriple.tryPayloadPtr_of {t : Option ErrName}
    (h : ReadAt (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min al 2) tb P)
    (hs : tb.size = 2) (ht : errOfBytes tb = pure t) :
    FTotalTriple P (Zig.tryPayloadPtr α al q)
      (fun r => ⟪r = t.elim (.ok (errPayloadPtr α q)) .error⟫ ⋆ P) := by
  show FTotalTriple _ (do
    match ← liftM (errOfBytes (← Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1)
      2 (Nat.min al 2))) with
    | some e => pure (Except.error e : Except ErrName Ptr)
    | none => (Except.ok <$> ptrProject q (errPayloadPtr α) : MemM (Except ErrName Ptr))) _
  refine FTotalTriple.bind (FTotalTriple.loadBytes_of h (by decide) hs) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  rw [ht, liftM_pure, pure_bind]
  cases t with
  | some e => exact FTotalTriple.pure_read rfl
  | none =>
    -- The code's bytes are readable, so the payload pointer is formed (MM-3).
    rw [map_eq_pure_bind]
    refine FTotalTriple.bind (FTotalTriple.of_read fun m r rF hh hp _ => ?_) fun y =>
      FTotalTriple.lift fun hy => FTotalTriple.pure_read (by subst hy; rfl)
    obtain ⟨b, blk, hacc, -⟩ := h.access (by decide) hs hh hp
    exact errPayloadPtr_formed hacc

/-- **The error** from the readable bytes `tb` of an error code that holds one. -/
theorem FTotalTriple.errCodeAt_of {e : ErrName}
    (h : ReadAt (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min al 2) tb P)
    (hs : tb.size = 2) (ht : errOfBytes tb = pure (some e)) :
    FTotalTriple P (Zig.errCodeAt α al q) (fun r => ⟪r = e⟫ ⋆ P) := by
  show FTotalTriple _ (do
    match ← liftM (errOfBytes (← Zig.loadBytes (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1)
      2 (Nat.min al 2))) with
    | some e => pure e
    | none => throw .unspecified) _
  refine FTotalTriple.bind (FTotalTriple.loadBytes_of h (by decide) hs) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  rw [ht, liftM_pure, pure_bind]
  exact FTotalTriple.pure_read rfl

/-- **Pointer-form `try`** with a finite error domain, from readable error code bytes. -/
theorem FTotalTriple.finiteTryPayloadPtr_of {t : Option ErrName}
    (h : ReadAt (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min al 2) tb P)
    (hs : tb.size = 2) (ht : errOfBytes tb = pure t) (hdom : t.all d.names.contains = true) :
    FTotalTriple P (Zig.finiteTryPayloadPtr d α al q)
      (fun r => ⟪r = t.elim (.ok (errPayloadPtr α q)) .error⟫ ⋆ P) := by
  unfold Zig.finiteTryPayloadPtr
  refine FTotalTriple.bind (FTotalTriple.tryPayloadPtr_of h hs ht) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  have e : requireErrorUnion d (t.elim (.ok (errPayloadPtr α q)) .error) =
      pure (t.elim (.ok (errPayloadPtr α q)) .error) := by
    cases t with
    | none => rfl
    | some e =>
      simp only [Option.all_some] at hdom
      show (if d.names.contains e then _ else _) = _
      simp only [hdom, ↓reduceIte]
  rw [e]
  exact FTotalTriple.pure_read rfl

/-- **The error** with a finite error domain, from readable error code bytes. -/
theorem FTotalTriple.finiteErrCodeAt_of {e : ErrName}
    (h : ReadAt (q.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) (Nat.min al 2) tb P)
    (hs : tb.size = 2) (ht : errOfBytes tb = pure (some e)) (hdom : d.names.contains e = true) :
    FTotalTriple P (Zig.finiteErrCodeAt d α al q) (fun r => ⟪r = e⟫ ⋆ P) := by
  unfold Zig.finiteErrCodeAt
  refine FTotalTriple.bind (FTotalTriple.errCodeAt_of h hs ht) fun x =>
    FTotalTriple.lift fun hx => ?_
  subst hx
  have e' : requireError d x = pure x := by unfold requireError; simp only [hdom, ↓reduceIte]
  rw [e']
  exact FTotalTriple.pure_read rfl

end Readable

end Full
end Zig
