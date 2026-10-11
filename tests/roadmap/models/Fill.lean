import ZigLean.External
import ZigLean.Sep.Heap
import ZigLean.Conc.Logic

/-! A buffer-filling external with a declared write footprint (E01). `fill`, `contract`,
`footprint` and `evidence` are the project model module a registry entry binds. The client
theorems use only the contract and footprint, so they hold for every implementation that
satisfies them, including an assumed one. -/
namespace FillExample
open Zig

/-- Every byte of `s` holds `v` in `m`. -/
def Filled (m : Mem) (s : Slice) (v : BitVec 8) : Prop :=
  ∃ b blk, s.ptr.block = some b ∧ m.blocks[b]? = some blk ∧
    ∀ i, i < s.len.toNat → blk.bytes[s.ptr.off.toNat + i]? = some (Byte.int v)

def fill (args : Slice × BitVec 8) : MemM Unit :=
  storeBytes args.1.ptr 1 (Array.replicate args.1.len.toNat (Byte.int args.2))

def contract : External.Contract (Slice × BitVec 8) Unit where
  pre := fun _ _ => True
  post := fun args _ _ after => Filled after args.1 args.2
  frame := fun args before after =>
    ∀ b, some b ≠ args.1.ptr.block → after.blocks[b]? = before.blocks[b]?
  access := fun args _ entry => some entry.block = args.1.ptr.block ∧ entry.kind = .write
  failure := fun _ _ error => error = .illegal
  divergence := fun _ _ => False

/-- Registry footprint `{"reads": [], "writes": [0]}`: only the buffer's block is written. -/
def footprint : External.Footprint (Slice × BitVec 8) where
  reads := fun _ => []
  writes := fun args => [External.Region.block args.1]

/-! ## Implementation evidence -/

theorem raceAt_illegal {fp : Array FootprintEntry} {clock : VClock} {block off len : Nat}
    {kind : AccessKind} {error : Error} (h : raceAt fp clock block off len kind = some error) :
    error = .illegal := by
  obtain ⟨entry, _, hentry⟩ := Array.exists_of_findSome?_eq_some h
  split at hentry
  · unfold racePair at hentry
    split at hentry
    · exact (Option.some.inj hentry).symm
    · cases hentry
  · cases hentry

theorem access_cases (m : Mem) (p : Ptr) (n a : Nat) :
    m.access p n a = throw .illegal ∨ ∃ b blk o, m.access p n a = pure (b, blk, o) := by
  unfold Mem.access
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inr ⟨_, _, _, rfl⟩
      · exact .inl rfl

/-- A store either fails with `.illegal` (access or race) or performs the checked write. -/
theorem storeBytes_cases (p : Ptr) (a : Nat) (bs : Array Byte) (m : Mem) :
    (storeBytes p a bs).run m = some (.error .illegal) ∨
    ∃ b blk o, m.access p bs.size a = pure (b, blk, o) ∧
      (storeBytes p a bs).run m = pure ((), (m.recordAt b o bs.size .write).write b blk o bs) := by
  rcases access_cases m p bs.size a with h | ⟨b, blk, o, h⟩
  · left
    simp [storeBytes, Mem.accessW, h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, throw, throwThe,
      MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure]
  · by_cases hK : blk.kind = .constGlobal
    · left
      simp [storeBytes, Mem.accessW, h, hK, StateT.run, bind, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, throw,
        throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure,
        ExceptT.pure]
    · cases hr : raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o bs.size .write with
      | none => exact .inr ⟨b, blk, o, h, storeBytes_run h hK hr⟩
      | some e =>
        left
        have he : e = .illegal := by
          unfold raceCheck at hr
          split at hr
          · cases hr
          · exact raceAt_illegal hr
        subst he
        simp [storeBytes, recordAccess, Mem.accessW, h, hK, hr, StateT.run, bind, StateT.bind, get,
          getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift,
          throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure,
          ExceptT.pure]

/-- Registry `proof`: the implementation satisfies the contract and declared footprint. -/
theorem evidence : contract.Holds .total [.illegal] .tracked fill ∧ contract.Respects footprint := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨s, v⟩ before _
    let bs := Array.replicate s.len.toNat (Byte.int v)
    rw [show fill (s, v) before = (storeBytes s.ptr 1 bs).run before from rfl]
    rcases storeBytes_cases s.ptr 1 bs before with h | ⟨b, blk, o, hacc, h⟩
    · rw [h]; exact ⟨by simp, rfl⟩
    · rw [h]
      obtain ⟨hb, hblk, -, h0, hn, -, ho⟩ := access_eq hacc
      have hlt : b < before.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
      have hsize : bs.size = s.len.toNat := Array.size_replicate
      refine ⟨?_, ?_, ?_, fun h => nomatch h⟩
      · refine ⟨b, { blk with bytes := writeBytes blk.bytes o bs }, hb, ?_, ?_⟩
        · simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
          exact Array.getElem?_setIfInBounds_self_of_lt hlt
        · intro i hi
          dsimp only at hi ⊢
          subst ho
          rw [writeBytes_getElem? _ _ _ (by omega)]
          simp [bs, hi, hsize]
      · intro b' hne
        have : b ≠ b' := fun e => hne (e ▸ hb.symm)
        simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne this]
      · refine ⟨#[_], rfl, fun entry mem => ?_⟩
        simp only [List.mem_singleton] at mem
        subst mem
        exact ⟨hb.symm, rfl⟩
  · intro args _ entry ⟨hblock, hkind⟩
    exact .inl (by simp [footprint, External.Region.block, hblock])
  · intro args before after _ frame b outside
    exact frame b fun h => outside (by simp [footprint, External.Region.block, h])

/-! ## Client reasoning from the contract alone -/

theorem Filled.transport {m m' : Mem} {s : Slice} {v : BitVec 8} (h : Filled m s v)
    (same : ∀ b, s.ptr.block = some b → m'.blocks[b]? = m.blocks[b]?) : Filled m' s v := by
  obtain ⟨b, blk, hb, hblk, hbytes⟩ := h
  exact ⟨b, blk, hb, (same b hb).trans hblk, hbytes⟩

/-- Two calls on separate buffers: `fill a x; fill c y`. -/
def client (impl : Slice × BitVec 8 → MemM Unit) (a c : Slice) (x y : BitVec 8) : MemM Unit := do
  impl (a, x)
  impl (c, y)

/-- Frame preservation: the second call writes only `c`'s block, so `a` stays filled with `x`.
Any implementation that satisfies the contract and footprint qualifies. -/
theorem client_fills_both {impl : Slice × BitVec 8 → MemM Unit}
    (h : contract.Holds .total [.illegal] .tracked impl ∧ contract.Respects footprint)
    {a c : Slice} {x y : BitVec 8} {before after : Mem}
    (separate : a.ptr.block ≠ c.ptr.block)
    (run : client impl a c x y before = some (.ok ((), after))) :
    Filled after a x ∧ Filled after c y := by
  obtain ⟨_, mid, first, second⟩ := Conc.Proto.MemM.bind_ok run
  have filledA : Filled mid a x := contract.success h.1 trivial first
  refine ⟨filledA.transport fun b hb => ?_, contract.success h.1 trivial second⟩
  apply contract.frame_outside h.1 h.2 trivial second
  simp only [footprint, External.Region.block, List.mem_singleton]
  exact fun e => separate (hb.trans e)

/-- The proved model instantiates the client rule. -/
theorem fill_client_fills_both {a c : Slice} {x y : BitVec 8} {before after : Mem}
    (separate : a.ptr.block ≠ c.ptr.block)
    (run : client fill a c x y before = some (.ok ((), after))) :
    Filled after a x ∧ Filled after c y :=
  client_fills_both evidence separate run

/-- Total contract: the client's first call never diverges. -/
theorem fill_terminates (args : Slice × BitVec 8) (before : Mem) : fill args before ≠ none :=
  contract.terminates evidence.1 trivial

end FillExample
