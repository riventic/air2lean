import ZigLean.Mem.Null
import ZigLean.Mem.Lemmas

/-!
# The C-ABI conversion of a pointer at a bound extern call (X01)

An extern declaration and the program's definition of its symbol may type a pointer
differently where the C ABI agrees: `zig translate-c` declares `strcmp` with `[*c]const u8`
and `free` with `?*anyopaque`, and Zig's libc defines them with `[*:0]const c_char` and
`?[*]align(16) u8` (`docs/c-frontend.md` §libc boundary). Natively the value crosses the call
unchanged: a pointer is an address in a register. The model converts it once at the call
(`Air2Lean/Check.lean`'s `externAbiCall` chooses the forms and the requirements, `Emit.lean`
applies them): the source's form becomes a `Ptr` (`ptrOfOptional` for `?*T`, the pointer
itself for `*T`, `[*]T` and a C/allowzero pointer), `abiPtrCheck` checks what the target type
asserts about the value, and the target's form is made from it (`ptrToOptional` for `?*T`, the
pointer itself otherwise). These are the conversions of the cast rules (`ZigLean/Mem/Null.lean`);
`abiPtr_nonNull_eq`, `abiPtr_align_eq` and `abiPtrOpt_eq` state the agreement.

A value that the target type does not admit is illegal behaviour that nothing checks natively:
`.illegal`. The target type asserts
* non-null, for a single or many pointer (not optional, not C/allowzero);
* its alignment, where it is stricter than the source's (`?[*]align(16) u8`);
* its sentinel byte, where the source does not assert the same one (`[*:0]const c_char`): a
  byte of that value at or after the pointer in its live block (`Mem.sentinelFrom`).

A null value has no alignment or sentinel requirement. The test reads the block's bytes
without recording an access (natively nothing reads them at the call), so it changes no state
(`abiPtrCheck_run`). The sentinel test is conservative where the callee would stop earlier (a
`strcmp` that finds a difference before the end of an unterminated buffer): the model says
`.illegal` there, and native code does not fail.
-/

namespace Zig

/-- What a C-ABI conversion's target pointer type asserts about a value (`abiPtrCheck`):
`nonNull`, and for a non-null value its alignment (1 asserts nothing) and its sentinel byte. -/
structure AbiPtrReq where
  nonNull : Bool := false
  align : Nat := 1
  sentinel : Option (BitVec 8) := none
  deriving DecidableEq, Repr, Inhabited

/-- The byte `s` lies at or after `p` in `p`'s live block (at or above its first live offset):
the sentinel that a `[*:s]T` of `p` asserts, for an item of one byte. -/
def Mem.sentinelFrom (m : Mem) (p : Ptr) (s : BitVec 8) : Bool :=
  match p.block with
  | none => false
  | some b =>
    match m.blocks[b]? with
    | none => false
    | some blk =>
      blk.live && decide (0 ≤ p.off) && decide (blk.kind.mappedLo ≤ p.off.toNat) &&
        (blk.bytes.extract p.off.toNat blk.bytes.size).any (· == .int s)

/-- `p` satisfies `r` in `m` (module doc). `false` for a pointer into a block that does not
exist, whose address `ptrAddr` refuses too. -/
def Mem.abiPtrOk (m : Mem) (r : AbiPtrReq) (p : Ptr) : Bool :=
  match addrIn m.blocks p with
  | none => false
  | some a =>
    if a = 0 then !r.nonNull
    else decide (a % r.align = 0) && (r.sentinel.all (m.sentinelFrom p ·))

/-- The check of a C-ABI pointer conversion: `.illegal` unless the value satisfies the target
type's requirements (`Mem.abiPtrOk`). -/
def abiPtrCheck (r : AbiPtrReq) (p : Ptr) : MemM Unit := do
  unless (← get).abiPtrOk r p do throw .illegal

/-- A C-ABI conversion to a pointer that is not optional (`*T`, `[*]T`, `[*c]T`). -/
def abiPtr (r : AbiPtrReq) (p : Ptr) : MemM Ptr := do
  abiPtrCheck r p
  pure p

/-- A C-ABI conversion to an optional pointer (`?*T`, `?[*]T`): address zero is `none`. -/
def abiPtrOpt (r : AbiPtrReq) (p : Ptr) : MemM (Option Ptr) := do
  abiPtrCheck r p
  ptrToOptional p

/-! ## Outcomes -/

/-- **The check reads only**: it passes with the memory unchanged, or throws `.illegal`. -/
theorem abiPtrCheck_run (m : Mem) (r : AbiPtrReq) (p : Ptr) :
    (abiPtrCheck r p).run m = if m.abiPtrOk r p then pure ((), m) else throw .illegal := by
  unfold abiPtrCheck
  split <;> rename_i h <;>
    simp [h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, throw, throwThe,
      MonadExceptOf.throw, StateT.lift] <;> rfl

/-- **Null into a pointer that does not admit it** is `.illegal`. -/
theorem abiPtrCheck_null_nonNull (m : Mem) (r : AbiPtrReq) (h : r.nonNull = true) :
    (abiPtrCheck r Ptr.null).run m = throw .illegal := by
  rw [abiPtrCheck_run]; simp [Mem.abiPtrOk, addrIn, Ptr.null, h]

/-- Null into a pointer that admits it passes, whatever the alignment and sentinel. -/
theorem abiPtrCheck_null (m : Mem) (r : AbiPtrReq) (h : r.nonNull = false) :
    (abiPtrCheck r Ptr.null).run m = pure ((), m) := by
  rw [abiPtrCheck_run]; simp [Mem.abiPtrOk, addrIn, Ptr.null, h]

/-- **A misaligned non-null value** is `.illegal`. -/
theorem abiPtrCheck_misaligned {m : Mem} {r : AbiPtrReq} {p : Ptr} {a : Int}
    (ha : addrIn m.blocks p = some a) (h0 : a ≠ 0) (hal : a % r.align ≠ 0) :
    (abiPtrCheck r p).run m = throw .illegal := by
  rw [abiPtrCheck_run]; simp [Mem.abiPtrOk, ha, h0, hal]

/-- **A non-null value without its sentinel** is `.illegal`. -/
theorem abiPtrCheck_no_sentinel {m : Mem} {r : AbiPtrReq} {p : Ptr} {a : Int} {s : BitVec 8}
    (ha : addrIn m.blocks p = some a) (h0 : a ≠ 0) (hs : r.sentinel = some s)
    (hno : m.sentinelFrom p s = false) :
    (abiPtrCheck r p).run m = throw .illegal := by
  rw [abiPtrCheck_run]; simp [Mem.abiPtrOk, ha, h0, hs, hno]

/-- **A pointer into a block that does not exist** is `.illegal`, as its address is. -/
theorem abiPtrCheck_no_block {m : Mem} {r : AbiPtrReq} {p : Ptr} (ha : addrIn m.blocks p = none) :
    (abiPtrCheck r p).run m = throw .illegal := by
  rw [abiPtrCheck_run]; simp [Mem.abiPtrOk, ha]

/-- **A value the target admits passes** with the memory unchanged: non-null, aligned and (if
the target asserts one) followed by its sentinel. -/
theorem abiPtrCheck_ok {m : Mem} {r : AbiPtrReq} {p : Ptr} {a : Int}
    (ha : addrIn m.blocks p = some a) (h0 : a ≠ 0) (hal : a % r.align = 0)
    (hs : ∀ s, r.sentinel = some s → m.sentinelFrom p s = true) :
    (abiPtrCheck r p).run m = pure ((), m) := by
  rw [abiPtrCheck_run]
  cases hr : r.sentinel <;> simp_all [Mem.abiPtrOk]

/-- A sentinel found at the pointer itself satisfies the sentinel test. -/
theorem sentinelFrom_of_at {m : Mem} {p : Ptr} {b : BlockId} {blk : Block} {s : BitVec 8}
    (hp : p.block = some b) (hb : m.blocks[b]? = some blk) (hl : blk.live = true)
    (h0 : 0 ≤ p.off) (hlo : blk.kind.mappedLo ≤ p.off.toNat)
    (hk : blk.bytes[p.off.toNat]? = some (.int s)) : m.sentinelFrom p s = true := by
  obtain ⟨pb, po⟩ := p
  simp only at hp h0 hlo hk; subst hp
  have hlt : po.toNat < blk.bytes.size := by
    rcases Nat.lt_or_ge po.toNat blk.bytes.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hk
  simp only [Mem.sentinelFrom, hb, hl, h0, hlo, decide_true, Bool.true_and, Array.any_eq_true]
  refine ⟨0, by simp [Array.size_extract]; omega, ?_⟩
  simp [Array.getElem_extract]
  rw [Array.getElem?_eq_getElem hlt] at hk
  simpa using hk

/-! ## Agreement with the cast rules -/

private theorem ptrIsNull_run (m : Mem) (p : Ptr) :
    (ptrIsNull p).run m = match addrIn m.blocks p with
      | some a => pure (decide (a = 0), m)
      | none => throw .illegal := by
  obtain ⟨pb, po⟩ := p
  cases pb with
  | none => rfl
  | some b =>
    cases hb : m.blocks[b]? <;>
      simp [ptrIsNull, ptrAddr, addrIn, hb, StateT.run, bind, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.bind,
        ExceptT.bindCont, throw, throwThe, MonadExceptOf.throw] <;> rfl

/-- Only non-null asserted: the C-pointer unwrap of the cast rules (`ptrRequireNonNull`). -/
theorem abiPtr_nonNull_eq (m : Mem) (p : Ptr) :
    (abiPtr { nonNull := true } p).run m = (ptrRequireNonNull p).run m := by
  simp only [abiPtr, ptrRequireNonNull, StateT.run_bind, abiPtrCheck_run, ptrIsNull_run]
  cases ha : addrIn m.blocks p <;> simp [Mem.abiPtrOk, ha] <;> split <;> simp_all <;> rfl

/-- Only an alignment asserted, of a non-null value: the `@alignCast` check of the cast rules
(`checkAlign`). -/
theorem abiPtr_align_eq (m : Mem) (p : Ptr) (al : Nat) (h0 : addrIn m.blocks p ≠ some 0) :
    (abiPtr { align := al } p).run m = (do checkAlign al p; pure p : MemM Ptr).run m := by
  simp only [abiPtr, checkAlign, StateT.run_bind, abiPtrCheck_run, ptrAddr_run_addrIn]
  cases ha : addrIn m.blocks p with
  | none => simp [Mem.abiPtrOk, ha]
  | some a =>
    have : a ≠ 0 := fun h => h0 (by rw [ha, h])
    by_cases hal : a % (al : Int) = 0 <;> simp [Mem.abiPtrOk, ha, this, hal] <;> rfl

/-- To an optional pointer with nothing asserted: the cast rules' C-pointer-to-optional
conversion (`ptrToOptional`). -/
theorem abiPtrOpt_eq (m : Mem) (p : Ptr) :
    (abiPtrOpt {} p).run m = (ptrToOptional p).run m := by
  simp only [abiPtrOpt, ptrToOptional, StateT.run_bind, abiPtrCheck_run, ptrIsNull_run]
  cases ha : addrIn m.blocks p <;> simp [Mem.abiPtrOk, ha] <;> rfl

end Zig
