import ZigLean.Mem.ErrWidth
import ZigLean.Mem.Lemmas
import ZigLean.VecMem

/-!
# Error identity at every admitted error-integer width

Proof-only (it imports `ZigLean.Mem.Lemmas`, so it stays out of the `ZigLean` umbrella). All
statements quantify over the profile's `error_set_bits` (`bits`, `ValidErrBits bits`: 1 to 32):

* width selection: `errorLimitBits` is the least width holding `--error-limit` nonzero codes,
  and the default limit gives 16 bits;
* the 16-bit instance is the existing storage model (`errOfBytesW_sixteen`,
  `errorEncW_sixteen`, `errorUnionWithW_sixteen`, ...);
* stores and loads: `errorEncW`, `optionalErrorEncW`, `FiniteErrorW` and finite error unions
  read back the stored name (`*_store_load`);
* error unions: wrap/unwrap round trips and the code slice that pointer-form `try` reads;
* casts: `@errorFromInt (@intFromError e) = e` for any numbering that fits the width, the code
  survives an integer store/load, `@errorCast` round trips through a superset, and out-of-range
  codes (zero, unused, too wide for a narrower configuration) are explicit errors.
-/

namespace Zig

/-! ## Width selection -/

theorem errorLimitBits_default : errorLimitBits defaultErrorLimit = 16 := by
  have : Nat.log2 65534 = 15 := by
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt (by decide)).mpr (by decide))
    · exact Nat.le_log2 (by decide) |>.mpr (by decide)
  simp [errorLimitBits, defaultErrorLimit, this]

/-- Every error count the limit allows has a nonzero code at the selected width. -/
theorem errorLimitBits_capacity (limit : Nat) : limit ≤ errCapacity (errorLimitBits limit) := by
  unfold errorLimitBits errCapacity
  split
  · omega
  · have := @Nat.lt_log2_self limit; omega

/-- The selected width is the least one: one bit fewer cannot hold the limit. -/
theorem errorLimitBits_least (limit : Nat) (h : limit ≠ 0) :
    errCapacity (errorLimitBits limit - 1) < limit := by
  unfold errorLimitBits errCapacity
  rw [if_neg h, Nat.add_sub_cancel]
  have := Nat.log2_self_le h
  have : 0 < 2 ^ limit.log2 := Nat.two_pow_pos _
  omega

/-- `ErrorInt = u32`: every `--error-limit` value selects an admitted width, except 0. -/
theorem errorLimitBits_valid (limit : Nat) (h0 : limit ≠ 0) (h : limit < 2 ^ 32) :
    ValidErrBits (errorLimitBits limit) := by
  unfold errorLimitBits ValidErrBits
  rw [if_neg h0]
  have := (Nat.log2_lt h0).mpr h
  omega

private theorem codeSize_table :
    ∀ b, b < 33 → 0 < b →
      (intSize b = 1 ∨ intSize b = 2 ∨ intSize b = 4) ∧ intAlign b = intSize b := by
  decide

theorem errCodeSize_cases {bits : Nat} (h : ValidErrBits bits) :
    errCodeSize bits = 1 ∨ errCodeSize bits = 2 ∨ errCodeSize bits = 4 :=
  (codeSize_table bits (by have := h.2; omega) h.1).1

theorem errCodeAlign_eq {bits : Nat} (h : ValidErrBits bits) :
    errCodeAlign bits = errCodeSize bits :=
  (codeSize_table bits (by have := h.2; omega) h.1).2

theorem errCodeSize_pos {bits : Nat} (h : ValidErrBits bits) : 0 < errCodeSize bits := by
  rcases errCodeSize_cases h with h | h | h <;> omega

theorem errCodeSize_le_four {bits : Nat} (h : ValidErrBits bits) : errCodeSize bits ≤ 4 := by
  rcases errCodeSize_cases h with h | h | h <;> omega

theorem errCodeSize_sixteen : errCodeSize 16 = 2 := by decide
theorem errCodeAlign_sixteen : errCodeAlign 16 = 2 := by decide

/-! ## Code bytes -/

@[simp] theorem errBytesW_size (bits : Nat) (e : Option ErrName) :
    (errBytesW bits e).size = errCodeSize bits := by
  cases e <;> simp [errBytesW]

theorem errBytesW_some_ne_none {bits : Nat} (h : ValidErrBits bits) (e : ErrName) :
    errBytesW bits (some e) ≠ errBytesW bits none := by
  intro heq
  have hp := errCodeSize_pos h
  have h4 := errCodeSize_le_four h
  have := congrArg (fun a : Array Byte => a[0]?) heq
  simp [errBytesW, hp] at this

theorem errBytesW_some_get0 {bits : Nat} (h : ValidErrBits bits) (e : ErrName) :
    (errBytesW bits (some e))[0]? = some (.errFrag e ⟨0, by decide⟩) := by
  have hp := errCodeSize_pos h
  simp [errBytesW, hp]

/-- The code reads back from any bytes that start with it. -/
theorem errOfBytesW_of_extract {bits : Nat} (h : ValidErrBits bits) {bs : Array Byte}
    {e : Option ErrName} (hx : bs.extract 0 (errCodeSize bits) = errBytesW bits e) :
    errOfBytesW bits bs = pure e := by
  have h4 := errCodeSize_le_four h
  unfold errOfBytesW
  simp only [hx]
  rw [if_neg (by omega)]
  cases e with
  | none => simp
  | some x =>
    rw [if_neg (errBytesW_some_ne_none h x), errBytesW_some_get0 h x]
    simp

@[simp] theorem errBytesW_extract (bits : Nat) (e : Option ErrName) :
    (errBytesW bits e).extract 0 (errCodeSize bits) = errBytesW bits e := by
  rw [← errBytesW_size bits e]; simp

@[simp] theorem errOfBytesW_errBytesW {bits : Nat} (h : ValidErrBits bits) (e : Option ErrName) :
    errOfBytesW bits (errBytesW bits e) = pure e :=
  errOfBytesW_of_extract h (errBytesW_extract bits e)

/-- Undefined bytes (a foreign name's storage) are no code. -/
theorem errOfBytesW_undef {bits : Nat} (h : ValidErrBits bits) :
    errOfBytesW bits (Array.replicate (errCodeSize bits) .undef) = throw .unspecified := by
  have hp := errCodeSize_pos h
  have h4 := errCodeSize_le_four h
  unfold errOfBytesW
  have hne : (Array.replicate (errCodeSize bits) Byte.undef) ≠ errBytesW bits none := by
    intro heq
    have := congrArg (fun a : Array Byte => a[0]?) heq
    simp [errBytesW, hp] at this
  rw [if_neg (by omega), if_neg (by simpa using hne)]
  simp [hp]

/-! ## The default width is the existing model -/

theorem errBytesW_sixteen : errBytesW 16 = errBytes := by
  funext e
  cases e with
  | none => decide
  | some e =>
    apply Array.ext
    · simp [errBytes, errCodeSize_sixteen]
    · intro i h1 _
      have hi : i < 2 := by simpa [errCodeSize_sixteen] using h1
      simp only [errBytesW, Array.getElem_ofFn, errBytes]
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

theorem errOfBytesW_sixteen (bs : Array Byte) : errOfBytesW 16 bs = errOfBytes bs := by
  have hz : errBytesW 16 none = #[.int 0, .int 0] := by decide
  have hs : ∀ e, errBytesW 16 (some e) = #[.errFrag e 0, .errFrag e 1] := fun e => by
    rw [errBytesW_sixteen]; rfl
  unfold errOfBytesW errOfBytes
  rw [errCodeSize_sixteen]
  simp only [hz, hs, errBytes]
  rcases bs with ⟨l⟩
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp
  · cases x <;> simp
  · cases x <;> cases y <;> simp <;> (try split) <;> (try split) <;> simp_all

theorem errUnionOffsetsW_sixteen : errUnionOffsetsW 16 = errUnionOffsets := by
  funext s a
  simp only [errUnionOffsetsW, errUnionOffsets, errCodeAlign_sixteen, errCodeSize_sixteen]

theorem errUnionSizeW_sixteen : errUnionSizeW 16 = errUnionSize := by
  funext s a
  simp only [errUnionSizeW, errUnionSize, errUnionOffsetsW_sixteen, errCodeAlign_sixteen,
    errCodeSize_sixteen]

theorem errorEncW_sixteen (d : ErrorDomain) : errorEncW 16 d = errorEnc d := by
  simp only [errorEncW, errorEnc, errCodeSize_sixteen, errCodeAlign_sixteen, errBytesW_sixteen,
    errOfBytesW_sixteen]
  rfl

theorem optionalErrorEncW_sixteen (d : ErrorDomain) : optionalErrorEncW 16 d = optionalErrorEnc d := by
  simp only [optionalErrorEncW, optionalErrorEnc, errCodeSize_sixteen,
    errCodeAlign_sixteen, errBytesW_sixteen, errOfBytesW_sixteen]
  rfl

theorem errorUnionWithW_sixteen {α : Type} (payload : Enc α) :
    Enc.errorUnionWithW 16 payload = Enc.errorUnionWith payload := by
  simp only [Enc.errorUnionWithW, Enc.errorUnionWith, errUnionSizeW_sixteen,
    errUnionOffsetsW_sixteen, errCodeAlign_sixteen, errCodeSize_sixteen, errBytesW_sixteen,
    errOfBytesW_sixteen]
  rfl

theorem errorUnionEncW_sixteen {α : Type} (d : ErrorDomain) (payload : Enc α) :
    errorUnionEncW 16 d payload = errorUnionEnc d payload := by
  unfold errorUnionEncW
  rw [errorUnionWithW_sixteen]
  rfl

/-! ## Finite domains: encode/decode -/

theorem errorEncW_size_encode (bits : Nat) (d : ErrorDomain) (e : ErrName) :
    ((errorEncW bits d).encode e).size = (errorEncW bits d).size := by
  change (if d.names.contains e then errBytesW bits (some e)
    else Array.replicate (errCodeSize bits) .undef).size = errCodeSize bits
  split <;> simp

theorem errorEncW_roundtrip {bits : Nat} (h : ValidErrBits bits) (d : ErrorDomain) (e : ErrName)
    (hm : d.names.contains e = true) :
    (errorEncW bits d).decode ((errorEncW bits d).encode e) = pure e := by
  change (do
    match ← errOfBytesW bits (if d.names.contains e then errBytesW bits (some e)
      else Array.replicate (errCodeSize bits) .undef) with
    | some e => if d.names.contains e then pure e else throw .unspecified
    | none => throw .unspecified : Result ErrName) = pure e
  have hmem : e ∈ d.names := Array.contains_iff_mem.mp hm
  simp [hmem, errOfBytesW_errBytesW h]

/-- A name outside the declared domain never survives a store. -/
theorem errorEncW_foreign {bits : Nat} (h : ValidErrBits bits) (d : ErrorDomain) (e : ErrName)
    (hm : d.names.contains e = false) :
    (errorEncW bits d).decode ((errorEncW bits d).encode e) = throw .unspecified := by
  change (do
    match ← errOfBytesW bits (if d.names.contains e then errBytesW bits (some e)
      else Array.replicate (errCodeSize bits) .undef) with
    | some e => if d.names.contains e then pure e else throw .unspecified
    | none => throw .unspecified : Result ErrName) = throw .unspecified
  simp only [hm, Bool.false_eq_true, if_false, errOfBytesW_undef h]
  rfl

/-- The zero code is not an error. -/
theorem errorEncW_reject_zero {bits : Nat} (h : ValidErrBits bits) (d : ErrorDomain) :
    (errorEncW bits d).decode (errBytesW bits none) = throw .unspecified := by
  change (do
    match ← errOfBytesW bits (errBytesW bits none) with
    | some e => if d.names.contains e then pure e else throw .unspecified
    | none => throw .unspecified : Result ErrName) = throw .unspecified
  simp only [errOfBytesW_errBytesW h]
  rfl

theorem optionalErrorEncW_roundtrip {bits : Nat} (h : ValidErrBits bits) (d : ErrorDomain)
    (e : Option ErrName) (hm : ∀ x, e = some x → d.names.contains x = true) :
    (optionalErrorEncW bits d).decode ((optionalErrorEncW bits d).encode e) = pure e := by
  cases e with
  | none =>
    change (do
      match ← errOfBytesW bits (errBytesW bits none) with
      | none => pure none
      | some e => if d.names.contains e then pure (some e) else throw .unspecified :
        Result (Option ErrName)) = pure none
    simp [errOfBytesW_errBytesW h]
  | some x =>
    change (do
      match ← errOfBytesW bits (if d.names.contains x then errBytesW bits (some x)
        else Array.replicate (errCodeSize bits) .undef) with
      | none => pure none
      | some e => if d.names.contains e then pure (some e) else throw .unspecified :
        Result (Option ErrName)) = pure (some x)
    have hmem : x ∈ d.names := Array.contains_iff_mem.mp (hm x rfl)
    simp [hmem, errOfBytesW_errBytesW h]

theorem optionalErrorEncW_size_encode (bits : Nat) (d : ErrorDomain) (e : Option ErrName) :
    ((optionalErrorEncW bits d).encode e).size = (optionalErrorEncW bits d).size := by
  cases e with
  | none => exact errBytesW_size bits none
  | some x => exact errorEncW_size_encode bits d x

/-- `FiniteErrorW bits d` is lawful at every admitted width. -/
theorem finiteErrorW_lawful {bits : Nat} (h : ValidErrBits bits) (d : ErrorDomain) :
    LawfulEnc (FiniteErrorW bits d) where
  size_encode _ := errBytesW_size bits _
  decode_encode e := by
    change (do
      match ← errOfBytesW bits (errBytesW bits (some e.val)) with
      | some x => if h : d.names.contains x = true then pure ⟨x, h⟩ else throw .unspecified
      | none => throw .unspecified : Result (FiniteErrorW bits d)) = pure e
    have hmem : e.val ∈ d.names := Array.contains_iff_mem.mp e.property
    simp [errOfBytesW_errBytesW h, hmem]
    rfl

/-! ## Stores and loads under an explicit dictionary -/

/-- `load_store_same` for one value of a dictionary that need not be lawful everywhere. -/
theorem load_store_same_of {α : Type} [Enc α] {m : Mem} {p : Ptr} {a a' : Nat}
    {b : BlockId} {blk : Block} {o : Nat} (v : α)
    (hs : (Enc.encode v).size = Enc.size α) (hv : Enc.decode (Enc.encode v) = pure v)
    (h : m.access p (Enc.size α) a = pure (b, blk, o))
    (h' : m.access p (Enc.size α) a' = pure (b, blk, o))
    (hnr : NoRace (m.write b blk o (Enc.encode v)) b o (Enc.size α) .read) :
    (load α a' p).run (m.write b blk o (Enc.encode v)) =
      pure (v, (m.write b blk o (Enc.encode v)).recordAt b o (Enc.size α) .read) := by
  have hw := h
  rw [← hs] at hw
  have h0 := (access_eq h).2.2.2.1
  have hn := (access_eq h).2.2.2.2.1
  have ho := (access_eq h).2.2.2.2.2.2
  have hx := extract_writeBytes blk.bytes o (Enc.encode v) (by rw [hs]; omega)
  rw [hs] at hx
  exact load_run (access_write_same hw h') (by simp only [hx, hv]) hnr

/-- A store followed by a load at the same pointer returns the stored value, for any value
whose dictionary round-trips it. -/
theorem store_load_of {α : Type} [Enc α] {m : Mem} {p : Ptr} {a : Nat}
    {b : BlockId} {blk : Block} {o : Nat} (v : α)
    (hs : (Enc.encode v).size = Enc.size α) (hv : Enc.decode (Enc.encode v) = pure v)
    (h : m.access p (Enc.size α) a = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hnw : NoRace m b o (Enc.size α) .write)
    (hnr : NoRace ((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) b o
      (Enc.size α) .read) :
    ∃ m', (do store a p v; load α a p : MemM α).run m = pure (v, m') := by
  have hst : (store a p v).run m =
      pure ((), (m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)) := by
    rw [← hs] at h hnw
    have := storeBytes_run h hK hnw
    rw [hs] at this
    exact this
  have hacc : (m.recordAt b o (Enc.size α) .write).access p (Enc.size α) a = pure (b, blk, o) :=
    access_recordAt.trans h
  have hld := load_store_same_of v hs hv hacc hacc hnr
  refine ⟨((m.recordAt b o (Enc.size α) .write).write b blk o (Enc.encode v)).recordAt b o
    (Enc.size α) .read, ?_⟩
  rw [StateT.run_bind, hst]
  simp only [pure_bind]
  exact hld

/-- `E` at any admitted width: a stored member of the domain reloads as the same name. -/
theorem errorEncW_store_load {bits : Nat} (hb : ValidErrBits bits) (d : ErrorDomain)
    (e : ErrName) (hm : d.names.contains e = true) {m : Mem} {p : Ptr} {a : Nat}
    {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (errCodeSize bits) a = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hnw : NoRace m b o (errCodeSize bits) .write)
    (hnr : NoRace ((m.recordAt b o (errCodeSize bits) .write).write b blk o
      ((errorEncW bits d).encode e)) b o (errCodeSize bits) .read) :
    letI := errorEncW bits d
    ∃ m', (do store a p e; load ErrName a p : MemM ErrName).run m = pure (e, m') :=
  @store_load_of ErrName (errorEncW bits d) m p a b blk o e (errorEncW_size_encode bits d e)
    (errorEncW_roundtrip hb d e hm) h hK hnw hnr

/-- `?E` at any admitted width: `null` and members reload as themselves. -/
theorem optionalErrorEncW_store_load {bits : Nat} (hb : ValidErrBits bits) (d : ErrorDomain)
    (e : Option ErrName) (hm : ∀ x, e = some x → d.names.contains x = true) {m : Mem} {p : Ptr}
    {a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (errCodeSize bits) a = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hnw : NoRace m b o (errCodeSize bits) .write)
    (hnr : NoRace ((m.recordAt b o (errCodeSize bits) .write).write b blk o
      ((optionalErrorEncW bits d).encode e)) b o (errCodeSize bits) .read) :
    letI := optionalErrorEncW bits d
    ∃ m', (do store a p e; load (Option ErrName) a p : MemM (Option ErrName)).run m =
      pure (e, m') :=
  @store_load_of (Option ErrName) (optionalErrorEncW bits d) m p a b blk o e
    (optionalErrorEncW_size_encode bits d e) (optionalErrorEncW_roundtrip hb d e hm) h hK hnw hnr

/-! ## Error unions -/

/-- The error code and the payload of `E!T` at width `bits` do not overlap and fit. -/
theorem errUnionW_bounds (bits s a : Nat) :
    (errUnionOffsetsW bits s a).1 + errCodeSize bits ≤ errUnionSizeW bits s a ∧
      (errUnionOffsetsW bits s a).2 + s ≤ errUnionSizeW bits s a ∧
      ((errUnionOffsetsW bits s a).1 + errCodeSize bits ≤ (errUnionOffsetsW bits s a).2 ∨
        (errUnionOffsetsW bits s a).2 + s ≤ (errUnionOffsetsW bits s a).1) := by
  have hd : (errUnionOffsetsW bits s a).1 + errCodeSize bits ≤ (errUnionOffsetsW bits s a).2 ∨
      (errUnionOffsetsW bits s a).2 + s ≤ (errUnionOffsetsW bits s a).1 := by
    unfold errUnionOffsetsW
    split
    · right; simp_all
    · split
      · right; simpa using le_alignUp s (errCodeAlign bits)
      · left; simpa using le_alignUp (errCodeSize bits) a
  have hsz : errUnionSizeW bits s a =
      alignUp (Max.max ((errUnionOffsetsW bits s a).1 + errCodeSize bits)
        ((errUnionOffsetsW bits s a).2 + s)) (Nat.max a (errCodeAlign bits)) := by
    unfold errUnionSizeW
    generalize errUnionOffsetsW bits s a = r
    obtain ⟨eo, po⟩ := r
    rfl
  rw [hsz]
  have hS := le_alignUp (Max.max ((errUnionOffsetsW bits s a).1 + errCodeSize bits)
    ((errUnionOffsetsW bits s a).2 + s)) (Nat.max a (errCodeAlign bits))
  have := Nat.le_max_left ((errUnionOffsetsW bits s a).1 + errCodeSize bits)
    ((errUnionOffsetsW bits s a).2 + s)
  have := Nat.le_max_right ((errUnionOffsetsW bits s a).1 + errCodeSize bits)
    ((errUnionOffsetsW bits s a).2 + s)
  exact ⟨by omega, by omega, hd⟩

/-- The error of an error-union value, if any. -/
def errOfExcept {α : Type} : Except ErrName α → Option ErrName
  | .ok _ => none
  | .error e => some e

/-- The code slice of a stored union is the code of its value: what pointer-form `try`,
`is_err_ptr` and `unwrap_errunion_err_ptr` read. -/
theorem errorUnionWithW_code {α : Type} (bits : Nat) (payload : Enc α)
    (hps : ∀ x : α, (payload.encode x).size = payload.size) (v : Except ErrName α) :
    ((Enc.errorUnionWithW bits payload).encode v).extract
        (errUnionOffsetsW bits payload.size payload.align).1
        ((errUnionOffsetsW bits payload.size payload.align).1 + errCodeSize bits) =
      errBytesW bits (errOfExcept v) := by
  obtain ⟨h1, h2, hd⟩ := errUnionW_bounds bits payload.size payload.align
  unfold Enc.errorUnionWithW; dsimp only
  generalize errUnionSizeW bits payload.size payload.align = S at h1 h2 ⊢
  generalize errUnionOffsetsW bits payload.size payload.align = r at h1 h2 hd ⊢
  obtain ⟨eo, po⟩ := r
  simp only at h1 h2 hd ⊢
  cases v with
  | error e =>
    have hx := extract_writeBytes (Array.replicate S .undef) eo (errBytesW bits (some e))
      (by simp; omega)
    rw [errBytesW_size] at hx
    exact hx
  | ok x =>
    have ha1 : (writeBytes (Array.replicate S Byte.undef) eo (errBytesW bits none)).size = S := by
      rw [writeBytes_size _ _ _ (by simp; omega)]; simp
    have hc := extract_writeBytes_disjoint
      (writeBytes (Array.replicate S Byte.undef) eo (errBytesW bits none)) po (payload.encode x)
      eo (errCodeSize bits) (by rw [ha1, hps]; omega) (by omega) (by rw [hps]; omega)
    have hc' := extract_writeBytes (Array.replicate S Byte.undef) eo (errBytesW bits none)
      (by simp; omega)
    rw [errBytesW_size] at hc'
    simp only
    rw [hc, hc']
    rfl

/-- The payload slice of a stored success is the payload's encoding. -/
theorem errorUnionWithW_payload {α : Type} (bits : Nat) (payload : Enc α)
    (hps : ∀ x : α, (payload.encode x).size = payload.size) (x : α) :
    ((Enc.errorUnionWithW bits payload).encode (.ok x)).extract
        (errUnionOffsetsW bits payload.size payload.align).2
        ((errUnionOffsetsW bits payload.size payload.align).2 + payload.size) = payload.encode x := by
  obtain ⟨h1, h2, hd⟩ := errUnionW_bounds bits payload.size payload.align
  unfold Enc.errorUnionWithW; dsimp only
  generalize errUnionSizeW bits payload.size payload.align = S at h1 h2 ⊢
  generalize errUnionOffsetsW bits payload.size payload.align = r at h1 h2 hd ⊢
  obtain ⟨eo, po⟩ := r
  simp only at h1 h2 hd ⊢
  have ha1 : (writeBytes (Array.replicate S Byte.undef) eo (errBytesW bits none)).size = S := by
    rw [writeBytes_size _ _ _ (by simp; omega)]; simp
  have hw := extract_writeBytes (writeBytes (Array.replicate S Byte.undef) eo
    (errBytesW bits none)) po (payload.encode x) (by rw [ha1, hps]; omega)
  rw [hps] at hw
  exact hw

/-- `E!T` at any admitted width: wrap then unwrap is the identity (lawful payload). -/
theorem errorUnionWithW_lawful {bits : Nat} (hb : ValidErrBits bits) {α : Type}
    (payload : Enc α) (hl : @LawfulEnc α payload) :
    @LawfulEnc (Except ErrName α) (Enc.errorUnionWithW bits payload) := by
  have hps : ∀ x : α, (payload.encode x).size = payload.size := hl.size_encode
  refine @LawfulEnc.mk _ (Enc.errorUnionWithW bits payload) ?_ ?_
  · intro v
    show ((Enc.errorUnionWithW bits payload).encode v).size = (Enc.errorUnionWithW bits payload).size
    obtain ⟨h1, h2, -⟩ := errUnionW_bounds bits payload.size payload.align
    unfold Enc.errorUnionWithW; dsimp only
    generalize errUnionSizeW bits payload.size payload.align = S at h1 h2 ⊢
    generalize errUnionOffsetsW bits payload.size payload.align = r at h1 h2 ⊢
    obtain ⟨eo, po⟩ := r
    cases v with
    | error e => simp only; rw [writeBytes_size _ _ _ (by simp; omega)]; simp
    | ok x =>
      simp only
      rw [writeBytes_size _ _ _ (by rw [writeBytes_size _ _ _ (by simp; omega), hps]; simp; omega),
        writeBytes_size _ _ _ (by simp; omega)]
      simp
  · intro v
    show (Enc.errorUnionWithW bits payload).decode ((Enc.errorUnionWithW bits payload).encode v) =
      pure v
    have hcode := errorUnionWithW_code bits payload hps v
    have hpay : ∀ x, v = .ok x → ((Enc.errorUnionWithW bits payload).encode v).extract
        (errUnionOffsetsW bits payload.size payload.align).2
        ((errUnionOffsetsW bits payload.size payload.align).2 + payload.size) = payload.encode x := by
      intro x hx; subst hx; exact errorUnionWithW_payload bits payload hps x
    generalize (Enc.errorUnionWithW bits payload).encode v = E at hcode hpay
    unfold Enc.errorUnionWithW; dsimp only
    generalize errUnionOffsetsW bits payload.size payload.align = r at hcode hpay
    obtain ⟨eo, po⟩ := r
    simp only at hcode hpay ⊢
    have hc : (E.extract eo (eo + errCodeSize bits)).extract 0 (errCodeSize bits) =
        errBytesW bits (errOfExcept v) := by
      rw [hcode]; exact errBytesW_extract bits _
    rw [errOfBytesW_of_extract hb hc]
    cases v with
    | error e => rfl
    | ok x =>
      simp only [errOfExcept, hpay x rfl, hl.decode_encode x]
      rfl

/-- A declared finite union round-trips success and its own errors at any admitted width. -/
theorem errorUnionEncW_roundtrip {bits : Nat} (hb : ValidErrBits bits) {α : Type}
    (d : ErrorDomain) (payload : Enc α) (hl : @LawfulEnc α payload) (v : Except ErrName α)
    (hm : ∀ e, v = .error e → d.names.contains e = true) :
    (errorUnionEncW bits d payload).decode ((errorUnionEncW bits d payload).encode v) = pure v ∧
      ((errorUnionEncW bits d payload).encode v).size = (errorUnionEncW bits d payload).size := by
  have hw := errorUnionWithW_lawful hb payload hl
  have henc : (errorUnionEncW bits d payload).encode v = (Enc.errorUnionWithW bits payload).encode v := by
    cases v with
    | ok _ => rfl
    | error e =>
      show (if d.names.contains e then (Enc.errorUnionWithW bits payload).encode (.error e)
        else _) = _
      rw [if_pos (hm e rfl)]
  rw [henc]
  refine ⟨?_, @LawfulEnc.size_encode _ (Enc.errorUnionWithW bits payload) hw v⟩
  show (do
    let w ← (Enc.errorUnionWithW bits payload).decode ((Enc.errorUnionWithW bits payload).encode v)
    match w with
    | .ok _ => pure w
    | .error e => if d.names.contains e then pure w else throw .unspecified : Result _) = pure v
  rw [@LawfulEnc.decode_encode _ (Enc.errorUnionWithW bits payload) hw v]
  cases v with
  | ok _ => rfl
  | error e =>
    have hmem : e ∈ d.names := Array.contains_iff_mem.mp (hm e rfl)
    simp [hmem]

/-- `E!T` in memory at any admitted width: a stored success or member error reloads as itself. -/
theorem errorUnionEncW_store_load {bits : Nat} (hb : ValidErrBits bits) {α : Type}
    (d : ErrorDomain) (payload : Enc α) (hl : @LawfulEnc α payload) (v : Except ErrName α)
    (hm : ∀ e, v = .error e → d.names.contains e = true) {m : Mem} {p : Ptr} {a : Nat}
    {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (errorUnionEncW bits d payload).size a = pure (b, blk, o))
    (hK : blk.kind ≠ .constGlobal)
    (hnw : NoRace m b o (errorUnionEncW bits d payload).size .write)
    (hnr : NoRace ((m.recordAt b o (errorUnionEncW bits d payload).size .write).write b blk o
      ((errorUnionEncW bits d payload).encode v)) b o (errorUnionEncW bits d payload).size .read) :
    letI := errorUnionEncW bits d payload
    ∃ m', (do store a p v; load (Except ErrName α) a p : MemM (Except ErrName α)).run m =
      pure (v, m') :=
  have hr := errorUnionEncW_roundtrip hb d payload hl v hm
  @store_load_of (Except ErrName α) (errorUnionEncW bits d payload) m p a b blk o v hr.2 hr.1
    h hK hnw hnr

/-! ## Integer/error casts -/

theorem errIndex_lt {e : ErrName} {l : List ErrName} {i : Nat} (h : errIndex e l = some i) :
    i < l.length := by
  induction l generalizing i with
  | nil => simp [errIndex] at h
  | cons x xs ih =>
    simp only [errIndex] at h
    split at h
    · cases h; simp
    · cases hq : errIndex e xs with
      | none => simp [hq] at h
      | some j => simp [hq] at h; have := ih hq; simp; omega

theorem errIndex_getElem {e : ErrName} {l : List ErrName} {i : Nat} (h : errIndex e l = some i) :
    l[i]'(errIndex_lt h) = e := by
  induction l generalizing i with
  | nil => simp [errIndex] at h
  | cons x xs ih =>
    simp only [errIndex] at h
    split at h
    · cases h; simpa
    · cases hq : errIndex e xs with
      | none => simp [hq] at h
      | some j =>
        simp [hq] at h; subst h
        simpa using ih hq

theorem errIndex_of_mem {e : ErrName} {l : List ErrName} (h : e ∈ l) : ∃ i, errIndex e l = some i := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [errIndex]
    split
    · exact ⟨0, rfl⟩
    · rcases List.mem_cons.mp h with h | h
      · subst h; contradiction
      · obtain ⟨i, hi⟩ := ih h; exact ⟨i + 1, by simp [hi]⟩

theorem errIndex_of_getElem {l : List ErrName} (hl : l.Nodup) (i : Nat) (hi : i < l.length) :
    errIndex l[i] l = some i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.mp hl).1
    cases i with
    | zero => simp [errIndex]
    | succ j =>
      have hj : j < xs.length := by simp at hi; omega
      simp only [errIndex, List.getElem_cons_succ]
      have hne : x ≠ xs[j] := fun heq => hx (heq ▸ List.getElem_mem _)
      rw [if_neg hne, ih (List.nodup_cons.mp hl).2 j (by simpa using hi)]
      rfl

/-- `@intFromError` gives a nonzero code below `2 ^ bits` for every numbered error of a
fitting table. -/
theorem intFromErrorW_spec {bits : Nat} (t : ErrorTable) (ht : t.fits bits) {e : ErrName}
    (he : e ∈ t.names) : ∃ c : BitVec bits, intFromErrorW bits t e = pure c ∧
      0 < c.toNat ∧ c.toNat ≤ t.names.size ∧ t.names[c.toNat - 1]? = some e := by
  obtain ⟨i, hi⟩ := errIndex_of_mem (Array.mem_toList_iff.mpr he)
  have hlt := errIndex_lt hi
  have hget := errIndex_getElem hi
  simp only [Array.length_toList] at hlt
  unfold ErrorTable.fits errCapacity at ht
  have hpow : i + 1 < 2 ^ bits := by have := Nat.two_pow_pos bits; omega
  refine ⟨BitVec.ofNat bits (i + 1), ?_, ?_⟩
  · have hcap : i + 1 ≤ errCapacity bits := by unfold errCapacity; omega
    unfold intFromErrorW
    simp only [hi, hcap, if_true]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow]
    refine ⟨by omega, by omega, ?_⟩
    simp only [Nat.add_sub_cancel]
    rw [Array.getElem?_eq_getElem hlt]
    simpa using hget

/-- `@errorFromInt (@intFromError e) = e` at every width, for any numbering that fits it. -/
theorem errorFromIntW_intFromErrorW {bits : Nat} (t : ErrorTable) (ht : t.fits bits)
    {e : ErrName} (he : e ∈ t.names) :
    (intFromErrorW bits t e >>= errorFromIntW bits t) = pure e := by
  obtain ⟨c, hc, h0, hle, hget⟩ := intFromErrorW_spec t ht he
  rw [hc]
  simp only [pure_bind, errorFromIntW]
  rw [dif_pos ⟨h0, hle⟩]
  rw [Array.getElem?_eq_getElem (by omega)] at hget
  simp only [Option.some.injEq] at hget
  rw [hget]

/-- `@intFromError (@errorFromInt c) = c` for every valid code: codes are not renumbered. -/
theorem intFromErrorW_errorFromIntW {bits : Nat} (t : ErrorTable) (ht : t.fits bits)
    {c : BitVec bits} {e : ErrName} (h : errorFromIntW bits t c = pure e) :
    intFromErrorW bits t e = pure c := by
  unfold errorFromIntW at h
  split at h
  · rename_i hc
    cases h
    have hi := errIndex_of_getElem t.unique (c.toNat - 1) (by simp; omega)
    simp only [Array.getElem_toList] at hi
    unfold ErrorTable.fits errCapacity at ht
    simp only [intFromErrorW, hi]
    rw [if_pos (by unfold errCapacity; omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.sub_add_cancel hc.1]
    exact Nat.mod_eq_of_lt c.isLt
  · cases h

/-- The zero code is no error. -/
theorem errorFromIntW_zero (bits : Nat) (t : ErrorTable) :
    errorFromIntW bits t 0 = throw .panic := by
  simp [errorFromIntW]

/-- A code above the compilation's error count is no error. -/
theorem errorFromIntW_unused {bits : Nat} (t : ErrorTable) {c : BitVec bits}
    (hc : t.names.size < c.toNat) : errorFromIntW bits t c = throw .panic := by
  unfold errorFromIntW
  rw [dif_neg (by omega)]

/-- A code that does not fit a narrower width is an explicit overflow, never truncated
into another error's code. -/
theorem errorCodeOfNat_out_of_range {bits x : Nat} (hx : 2 ^ bits ≤ x) :
    errorCodeOfNat bits x = throw .overflow := by
  unfold errorCodeOfNat
  rw [if_neg (by omega)]

theorem errorCodeOfNat_in_range {bits x : Nat} (hx : x < 2 ^ bits) :
    errorCodeOfNat bits x = pure (BitVec.ofNat bits x) := by
  unfold errorCodeOfNat
  rw [if_pos hx]

/-- Concretely: the 16-bit code 256 is valid at the default width and an overflow on an
8-bit (`--error-limit 255`) configuration. -/
example : errorLimitBits 255 = 8 ∧ errorCodeOfNat 8 256 = throw .overflow ∧
    errorCodeOfNat 16 256 = pure 256 := by
  have : Nat.log2 255 = 7 := by
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt (by decide)).mpr (by decide))
    · exact Nat.le_log2 (by decide) |>.mpr (by decide)
  refine ⟨by simp [errorLimitBits, this], errorCodeOfNat_out_of_range (by decide),
    errorCodeOfNat_in_range (by decide)⟩

/-- A numbering with more errors than the width's codes is rejected, not wrapped. -/
theorem ErrorTable.check_capacity {names : Array ErrName} {bits : Nat}
    (h : errCapacity bits < names.size) : ∃ msg, ErrorTable.check names bits = .error msg := by
  unfold ErrorTable.check
  split
  · rw [if_neg (by omega)]; exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem ErrorTable.check_fits {names : Array ErrName} {bits : Nat} {t : ErrorTable}
    (h : ErrorTable.check names bits = .ok t) : t.fits bits ∧ t.names = names := by
  unfold ErrorTable.check at h
  split at h
  · split at h
    · cases h; exact ⟨by assumption, rfl⟩
    · cases h
  · cases h

/-- Any width's integers round-trip through memory (`intOfBytes_intBytes`). -/
theorem bitVec_lawful (n : Nat) : LawfulEnc (BitVec n) where
  size_encode v := by
    simp only [Enc.encode, Enc.size, padTo, Array.size_append, Array.size_replicate]
    have : (intBytes v).size = (n + 7) / 8 := by simp [intBytes]
    have := le_alignUp ((n + 7) / 8) (intAlign n)
    simp only [intSize] at *
    omega
  decode_encode v := by
    have hb : (intBytes v).size = (n + 7) / 8 := by simp [intBytes]
    exact intOfBytes_of_extract v (by simp [Enc.encode, padTo, ← hb])

/-- The integer code of an error survives a store and a load as a `u<bits>`, and converts back
to the same error: `@errorFromInt (load (store (@intFromError e))) = e`. -/
theorem intFromErrorW_store_load {bits : Nat} (t : ErrorTable) (ht : t.fits bits)
    {e : ErrName} (he : e ∈ t.names) {m : Mem} {p : Ptr} {a : Nat}
    {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p (intSize bits) a = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hnw : NoRace m b o (intSize bits) .write)
    (hnr : ∀ c : BitVec bits, NoRace ((m.recordAt b o (intSize bits) .write).write b blk o
      (Enc.encode c)) b o (intSize bits) .read) :
    ∃ c : BitVec bits, intFromErrorW bits t e = pure c ∧
      (∃ m', (do store a p c; load (BitVec bits) a p : MemM (BitVec bits)).run m = pure (c, m')) ∧
      errorFromIntW bits t c = pure e := by
  obtain ⟨c, hc, -, -, -⟩ := intFromErrorW_spec t ht he
  have hl := bitVec_lawful bits
  refine ⟨c, hc, store_load_of c (hl.size_encode c) (hl.decode_encode c) h hK hnw (hnr c), ?_⟩
  have := errorFromIntW_intFromErrorW t ht he
  rw [hc] at this
  simpa using this

/-- `@errorCast` to a declared set keeps exactly its members. -/
theorem errorCastW_spec (d : ErrorDomain) (e : ErrName) :
    errorCastW d e = (if d.names.contains e then pure e else throw .panic) := rfl

/-- Widening then narrowing back with `@errorCast` is the identity on the narrow set. -/
theorem errorCastW_roundtrip {small big : ErrorDomain}
    (hsub : ∀ x, small.names.contains x = true → big.names.contains x = true)
    {e : ErrName} (he : small.names.contains e = true) :
    (errorCastW big e >>= errorCastW small) = pure e := by
  have hbig : e ∈ big.names := Array.contains_iff_mem.mp (hsub e he)
  have hsm : e ∈ small.names := Array.contains_iff_mem.mp he
  simp [errorCastW, hbig, hsm]

theorem errorCastW_foreign (d : ErrorDomain) {e : ErrName} (he : d.names.contains e = false) :
    errorCastW d e = throw .panic := by
  unfold errorCastW; rw [he]; rfl

end Zig
