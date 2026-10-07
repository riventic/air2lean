import ZigLean.Sep.Try
import ZigLean.Sep.Discard

/-! Whole-object ownership rules for pointer-form try, aliasing and in-place payload updates.

`ZigLean/Sep/Try.lean` owns only the error tag. These rules own the complete typed error
union `pts p a u`, so several views of the same object can be reasoned about at once:
every pointer-try on `p` returns the same payload address (`tryView`), and a store or load
through *any* such address updates or reads the union's payload in place. The error tag is
never written: a payload store keeps it, so later pointer-tries on either alias still succeed.
The error path neither reads nor writes payload bytes and leaves the union unchanged.

Alignment is explicit: `Nat.min a 2 ∣ a` (tag access), `b ∣ a` and `b ∣ po` (payload
access with alignment `b` at payload offset `po`). All rules require sequential memory. -/

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

section ErrUnion

variable {α : Type} [Enc α]

private theorem errUnion_decode_eq {bs : Array Byte} {u : Except ErrName α}
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

private theorem errUnion_decode_write [LawfulEnc α] {bs : Array Byte} {x : α}
    (hs : bs.size = Enc.size (Except ErrName α))
    (h : Enc.decode bs = pure (Except.ok x : Except ErrName α)) (y : α) :
    Enc.decode (writeBytes bs (errUnionOffsets (Enc.size α) (Enc.align α)).2 (Enc.encode y)) =
      pure (Except.ok y : Except ErrName α) := by
  obtain ⟨htag, -⟩ := errUnion_decode_eq h
  obtain ⟨h1, h2, hd⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  have hy := LawfulEnc.size_encode y
  have hsz : bs.size = errUnionSize (Enc.size α) (Enc.align α) := hs
  simp only [Enc.decode]
  revert htag h1 h2 hd
  generalize errUnionOffsets (Enc.size α) (Enc.align α) = r
  obtain ⟨eo, po⟩ := r
  intro htag h1 h2 hd
  simp only at htag h1 h2 hd ⊢
  rw [extract_writeBytes_disjoint bs po (Enc.encode y) eo 2 (by omega) (by omega)
    (by rw [hy]; omega), htag]
  have hp := extract_writeBytes bs po (Enc.encode y) (by omega)
  rw [hy] at hp
  simp [errTagOf, bind, pure, hp, LawfulEnc.decode_encode, Functor.map, ExceptT.bind,
    ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.map]

private theorem dvd_add_off {A o k b a : Nat} (ha : (A + o) % a = 0) (hb : b ∣ a) (hk : b ∣ k) :
    (A + o + k) % b = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans hb (Nat.dvd_of_mod_eq_zero ha)) hk)

/-- The tag of an owned typed union: the access is aligned and in bounds, and the read
bytes decode to the union's tag. Payload bytes are not accessed. -/
private theorem pts_tag_access {p : Ptr} {a : Nat} {u : Except ErrName α} {m : Mem} {h hF : Heap}
    (hp : pts p a u h) (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ block tb, (loadBytes (p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2
        (Nat.min a 2)).run m = pure (tb, m.recordAt block
          (p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2 .read) ∧
      errOfBytes tb = pure (errTagOf u) := by
  obtain ⟨A, S, K, bs, ha, hsz, hdec, hb, -⟩ := hp
  obtain ⟨h1, -, -⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  obtain ⟨htag, -⟩ := errUnion_decode_eq hdec
  obtain ⟨block, blk, hacc, -, -, -, hx⟩ := bytesAt_access
    (p := p) (q := p.add (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (k := (errUnionOffsets (Enc.size α) (Enc.align α)).1) (n := 2) (a := Nat.min a 2) hb hm rfl
    (by decide) (by rw [hsz]; exact h1) (dvd_add_off ha ht heo)
  have hl := loadBytes_run hacc (noRace_of_singleThread hs.single block
    (p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2 .read)
  rw [hx] at hl
  exact ⟨block, _, hl, htag⟩

/-- Pointer-form try on a wholly owned union: the exact `tryView` result; heap unchanged. -/
theorem pts_try_run {p : Ptr} {a : Nat} {u : Except ErrName α} {m : Mem} {h hF : Heap}
    (hp : pts p a u h) (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (tryPayloadPtr α a p).run m = pure (tryView α p u, m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨block, tb, hl, htag⟩ := pts_tag_access hp ht heo hm hs
  refine ⟨m.recordAt block (p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2 .read,
    ?_, ?_, hs.recordAt _ _ _ _⟩
  · simp only [StateT.run] at hl
    cases u <;> simp_all [tryPayloadPtr, tryView, errTagOf, zig_unfold, StateT.run]
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- The error code of a wholly owned error union is its original name; heap unchanged. -/
theorem pts_errCode_run {p : Ptr} {a : Nat} {e : ErrName} {m : Mem} {h hF : Heap}
    (hp : pts p a (Except.error e : Except ErrName α) h) (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (errCodeAt α a p).run m = pure (e, m') ∧ m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨block, tb, hl, htag⟩ := pts_tag_access hp ht heo hm hs
  refine ⟨m.recordAt block (p.off.toNat + (errUnionOffsets (Enc.size α) (Enc.align α)).1) 2 .read,
    ?_, ?_, hs.recordAt _ _ _ _⟩
  · simp only [StateT.run] at hl
    simp_all [errCodeAt, errTagOf, zig_unfold, StateT.run]
  · funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- The generated whole-object unused read of an owned typed union. -/
theorem pts_discard_run {p : Ptr} {a : Nat} {u : Except ErrName α} {m : Mem} {h hF : Heap}
    (hp : pts p a u h) (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (loadDiscardBytes (Enc.size (Except ErrName α)) a p).run m = pure ((), m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨A, S, K, bs, ha, hsz, -, hb, -⟩ := hp
  obtain ⟨h1, -, -⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  exact readableBytes_discard_run ⟨A, S, K, bs, ha, hsz, hb⟩ hm
    (show 0 < errUnionSize (Enc.size α) (Enc.align α) by omega) hs

/-- A load through a pointer-try payload address reads the union's payload in place. -/
theorem pts_payload_load_run {p : Ptr} {a b : Nat} {x : α} {m : Mem} {h hF : Heap}
    (hp : pts p a (Except.ok x : Except ErrName α) h) (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) (hn : 0 < Enc.size α)
    (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (load α b (errPayloadPtr α p)).run m = pure (x, m') ∧ m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨A, S, K, bs, ha, hsz, hdec, hbs, -⟩ := hp
  obtain ⟨-, h2, -⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  obtain ⟨-, hpay⟩ := errUnion_decode_eq hdec
  obtain ⟨block, blk, hacc, -, -, -, hx⟩ := bytesAt_access
    (p := p) (q := errPayloadPtr α p) (k := (errUnionOffsets (Enc.size α) (Enc.align α)).2)
    (n := Enc.size α) (a := b) hbs hm rfl hn (by rw [hsz]; exact h2) (dvd_add_off ha hb hpo)
  refine ⟨_, load_run hacc (by rw [hx]; exact hpay x rfl)
    (noRace_of_singleThread hs.single _ _ _ _), ?_, hs.recordAt _ _ _ _⟩
  funext l; rw [Mem.heap_recordAt]; exact congrFun hm l

/-- A store through a pointer-try payload address updates the owned union in place.
The tag bytes are untouched, so the union still holds a success value. -/
theorem pts_payload_store_run [LawfulEnc α] {p : Ptr} {a b : Nat} {x : α} {m : Mem}
    {h hF : Heap} (hp : pts p a (Except.ok x : Except ErrName α) h) (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) (hn : 0 < Enc.size α)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) (y : α) :
    ∃ m', (store b (errPayloadPtr α p) y).run m = pure ((), m') ∧ m'.Seq ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
        pts p a (Except.ok y : Except ErrName α) h' := by
  obtain ⟨A, S, K, bs, ha, hsz, hdec, hbs, hK⟩ := hp
  obtain ⟨-, h2, -⟩ := errUnion_bounds (Enc.size α) (Enc.align α)
  have hy := LawfulEnc.size_encode y
  obtain ⟨m', hrun, hs', h', hd', hm', hb'⟩ := bytesAt_store
    (q := errPayloadPtr α p) (k := (errUnionOffsets (Enc.size α) (Enc.align α)).2) (a := b)
    (bs' := Enc.encode y) hbs hm hd rfl (by omega) (by rw [hy, hsz]; exact h2)
    (dvd_add_off ha hb hpo) hs hK
  refine ⟨m', hrun, hs', h', hd', hm', A, S, K, _, ha, ?_, ?_, hb', hK⟩
  · rw [writeBytes_size _ _ _ (by rw [hy, hsz]; exact h2)]; exact hsz
  · exact errUnion_decode_write hsz hdec y

/-- The finite-domain pointer try used by generated code: a present error must belong to
the declared domain. -/
theorem pts_finiteTry_run {d : ErrorDomain} {p : Ptr} {a : Nat} {u : Except ErrName α} {m : Mem}
    {h hF : Heap} (hp : pts p a u h) (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hdom : ∀ e, u = .error e → d.names.contains e = true)
    (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (finiteTryPayloadPtr d α a p).run m = pure (tryView α p u, m') ∧
      m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨m', hr, hm', hs'⟩ := pts_try_run hp ht heo hm hs
  refine ⟨m', ?_, hm', hs'⟩
  simp only [StateT.run] at hr
  cases u with
  | ok x => simp_all [finiteTryPayloadPtr, requireErrorUnion, tryView, zig_unfold, StateT.run]
  | error e =>
    have he := hdom e rfl
    simp_all [finiteTryPayloadPtr, requireErrorUnion, tryView, zig_unfold, StateT.run]

theorem pts_finiteErrCode_run {d : ErrorDomain} {p : Ptr} {a : Nat} {e : ErrName} {m : Mem}
    {h hF : Heap} (hp : pts p a (Except.error e : Except ErrName α) h) (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hdom : d.names.contains e = true) (hm : m.heap = h ∪ hF) (hs : m.Seq) :
    ∃ m', (finiteErrCodeAt d α a p).run m = pure (e, m') ∧ m'.heap = h ∪ hF ∧ m'.Seq := by
  obtain ⟨m', hr, hm', hs'⟩ := pts_errCode_run hp ht heo hm hs
  refine ⟨m', ?_, hm', hs'⟩
  simp only [StateT.run] at hr
  simp_all [finiteErrCodeAt, requireError, zig_unfold, StateT.run]

/-! ### Triples -/

theorem Triple.errUnion_try {p : Ptr} {a : Nat} {u : Except ErrName α} (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    Triple (pts p a u) (Zig.tryPayloadPtr α a p) (fun r => ⌜r = tryView α p u⌝ ∗ pts p a u) :=
  Triple.of_run fun _ hP _ hd hm hp hs => by
    obtain ⟨m', hr, hm', hs'⟩ := pts_try_run hp ht heo hm hs
    exact ⟨_, m', hP, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

theorem Triple.errUnion_errCode {p : Ptr} {a : Nat} {e : ErrName} (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) :
    Triple (pts p a (Except.error e : Except ErrName α)) (errCodeAt α a p)
      (fun r => ⌜r = e⌝ ∗ pts p a (Except.error e : Except ErrName α)) :=
  Triple.of_run fun _ hP _ hd hm hp hs => by
    obtain ⟨m', hr, hm', hs'⟩ := pts_errCode_run hp ht heo hm hs
    exact ⟨_, m', hP, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

/-- Read through any pointer-try payload address of the owned union. -/
theorem Triple.errUnion_payload_load {p : Ptr} {a b : Nat} {x : α} (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) (hn : 0 < Enc.size α) :
    Triple (pts p a (Except.ok x : Except ErrName α)) (Zig.load α b (errPayloadPtr α p))
      (fun r => ⌜r = x⌝ ∗ pts p a (Except.ok x : Except ErrName α)) :=
  Triple.of_run fun _ hP _ hd hm hp hs => by
    obtain ⟨m', hr, hm', hs'⟩ := pts_payload_load_run hp hb hpo hn hm hs
    exact ⟨_, m', hP, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hs'⟩

/-- Write through any pointer-try payload address: the owned union now holds `.ok y`. -/
theorem Triple.errUnion_payload_store [LawfulEnc α] {p : Ptr} {a b : Nat} {x : α} (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) (hn : 0 < Enc.size α) (y : α) :
    Triple (pts p a (Except.ok x : Except ErrName α)) (Zig.store b (errPayloadPtr α p) y)
      (fun _ => pts p a (Except.ok y : Except ErrName α)) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', hr, hs', h', hd', hm', hp'⟩ := pts_payload_store_run hp hb hpo hn hm hd hs y
    exact ⟨(), m', h', hr, hd', hm', hp', hs'⟩

/-! ### Two pointer-tries on one union -/

/-- Two pointer-tries on the same union, a store through the first result and a load
through the second. Both results address the same payload bytes. -/
def tryAliasWriteRead (α : Type) [Enc α] (a b : Nat) (p : Ptr) (y : α) :
    MemM (Except ErrName α) := do
  match ← tryPayloadPtr α a p with
  | .error e => pure (.error e)
  | .ok q₁ =>
    match ← tryPayloadPtr α a p with
    | .error e => pure (.error e)
    | .ok q₂ =>
      store b q₁ y
      pure (.ok (← load α b q₂))

/-- The aliasing rule: a write through one pointer-try result is observed through the other;
on error, nothing is written and the original error is returned. -/
theorem tryAliasWriteRead_run [LawfulEnc α] {p : Ptr} {a b : Nat} {u : Except ErrName α}
    {m : Mem} {h hF : Heap} (hp : pts p a u h) (ht : Nat.min a 2 ∣ a)
    (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1) (hb : b ∣ a)
    (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2) (hn : 0 < Enc.size α)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hs : m.Seq) (y : α) :
    ∃ m' h', (tryAliasWriteRead α a b p y).run m = pure (writeView y u, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ pts p a (writeView y u) h' ∧ m'.Seq := by
  obtain ⟨m₁, h₁, hm₁, hs₁⟩ := pts_try_run hp ht heo hm hs
  cases u with
  | error e =>
    refine ⟨m₁, h, ?_, hd, hm₁, hp, hs₁⟩
    simp only [StateT.run] at h₁
    simp [tryAliasWriteRead, tryView, writeView, zig_unfold, h₁]
  | ok x =>
    obtain ⟨m₂, h₂, hm₂, hs₂⟩ := pts_try_run hp ht heo hm₁ hs₁
    obtain ⟨m₃, h₃, hs₃, h', hd', hm₃, hp'⟩ := pts_payload_store_run hp hb hpo hn hm₂ hd hs₂ y
    obtain ⟨m₄, h₄, hm₄, hs₄⟩ := pts_payload_load_run hp' hb hpo hn hm₃ hs₃
    refine ⟨m₄, h', ?_, hd', hm₄, hp', hs₄⟩
    simp only [StateT.run] at h₁ h₂ h₃ h₄
    simp [tryAliasWriteRead, tryView, writeView, zig_unfold, h₁, h₂, h₃, h₄]

theorem Triple.tryAliasWriteRead [LawfulEnc α] {p : Ptr} {a b : Nat} {u : Except ErrName α}
    (ht : Nat.min a 2 ∣ a) (heo : Nat.min a 2 ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).1)
    (hb : b ∣ a) (hpo : b ∣ (errUnionOffsets (Enc.size α) (Enc.align α)).2)
    (hn : 0 < Enc.size α) (y : α) :
    Triple (pts p a u) (Zig.tryAliasWriteRead α a b p y)
      (fun r => ⌜r = writeView y u⌝ ∗ pts p a (writeView y u)) :=
  Triple.of_run fun _ _ _ hd hm hp hs => by
    obtain ⟨m', h', hr, hd', hm', hp', hs'⟩ :=
      tryAliasWriteRead_run hp ht heo hb hpo hn hm hd hs y
    exact ⟨_, m', h', hr, hd', hm', sep_lift.mpr ⟨rfl, hp'⟩, hs'⟩

end ErrUnion

end Zig
