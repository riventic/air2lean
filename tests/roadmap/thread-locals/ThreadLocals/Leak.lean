import ThreadLocals.Gen
import ZigLean.Conc.TlsLemmas

/-!
# A thread-local pointer used after its thread ended

`leaked` (the retained translation of `thread_locals.leaked`) spawns `leak(&p)`, which stores
the address of its own `counter` in `p`, joins it and reads `p.*`. The worker's instance died
with the worker (`tlsExit`, the last step of its dispatcher), so the read is a use after free.

`leaked_never_ok`: under every schedule and every fuel, no run returns a result: each run
throws or runs out of fuel. `ThreadLocals/Runtime.lean` runs it: it throws `.illegal`.

The protocol is not strict (a run throws). Main's ghost value says whether it spawned; the kid's
says, once it ended, which block its leaked pointer names: `p` holds that pointer and the block
is dead (`Inv.done`). Main learns both at the join, reads the pointer back from `p`, and the
second read throws (`load_dead`).
-/

open Zig Zig.Conc Zig.Conc.Proto

namespace ThreadLocals.Leak

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main`, before (`false`) or after (`true`) its spawn. -/
  | main (spawned : Bool)
  /-- The kid; `some c` once it ended, having leaked a pointer to block `c`. -/
  | kid (leaked : Option BlockId)

/-- `p`, `main`'s stack slot: the first block after `mem0`'s one global. -/
def pBlk : Ptr := ⟨some 1, 0⟩

structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  pre : G 0 = .main false → (∀ v, v ≠ 0 → G v = .none) ∧ m.threads.size = 1
  post : G 0 = .main true → m.threads.size = 2 ∧ (∃ b, G 1 = .kid b) ∧
    ∀ v, v ≠ 0 → v ≠ 1 → G v = .none
  main : G 0 = .main false ∨ G 0 = .main true
  done : ∀ c, G 1 = .kid (some c) →
    (m.bytesOf 1).map (·.extract 0 8) = some (Enc.encode (⟨some c, 0⟩ : Ptr)) ∧ m.Dead c

def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := match tgt with
    | .leak out => out = pBlk ∧ g = .kid none
    | .bumpTwice _ => False
  fin g := ∃ c, g = .kid (some c)

/-- `main` never returns. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop := fun _ _ _ _ => False

theorem leak_eq (p : Ptr) : leak p = (tlsPtr 0 >>= fun i => store (α := Ptr) 8 p i) := by
  unfold leak
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]

theorem decode_ptr (c : BlockId) :
    (Enc.decode (Enc.encode (⟨some c, 0⟩ : Ptr)) : Result Ptr) = pure ⟨some c, 0⟩ :=
  LawfulEnc.decode_encode _

/-! ## The kid -/

theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : Inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | bumpTwice _ => exact hg.elim
  | leak out =>
    obtain ⟨rfl, rfl⟩ := hg
    have h0 : G 0 = .main true := by
      rcases hi.main with h | h
      · have := (hi.pre h).1 u (Nat.pos_iff_ne_zero.mp hu); rw [hgu] at this; cases this
      · exact h
    obtain ⟨hsz, -, hoth⟩ := hi.post h0
    have hu1 : u = 1 := by
      apply Classical.byContradiction; intro hne
      have := hoth u (Nat.pos_iff_ne_zero.mp hu) hne; rw [hgu] at this; cases this
    subst hu1
    show proto.WP 1 (ConcM.tlsThread tlsInit (discard (ConcM.liftMem (leak pBlk)))) _ _ _ _
    unfold ConcM.tlsThread
    have ht : ({ m with current := 1 } : Mem).current < ({ m with current := 1 } : Mem).threads.size := by
      show 1 < m.threads.size; rw [hsz]; decide
    refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₁ h₁ => ?_)
    obtain ⟨hc1, hs1, -, -, -, -, hi1⟩ := tlsEnter_init ht h₁
    obtain ⟨hreg, -⟩ := hi1 0 (by decide)
    simp only [show ({ m with current := 1 } : Mem).current = 1 from rfl] at hc1 hreg
    have hinst : m₁.tlsInstance 1 0 = some m.blocks.size := Mem.tlsInstance_head hreg
    refine ⟨hs1, WP.bind (WP.map (WP.liftMem (fun _ _ => rfl) fun _ m₂ h₂ => ?_))⟩
    rw [leak_eq] at h₂
    obtain ⟨q, m₁', hq, h₂'⟩ := MemM.bind_ok h₂
    obtain ⟨b, hb, rfl, hm⟩ := tlsPtr_ok hq
    subst m₁'
    rw [hc1, hinst, Option.some.injEq] at hb
    subst hb
    obtain ⟨bo, blk, o, hacc, -, rfl⟩ := Proto.store_ok h₂'
    obtain ⟨hpb, hblk, -, -, hfit, -, ho⟩ := access_eq hacc
    simp only [pBlk, Option.some.injEq] at hpb
    subst hpb
    simp only [pBlk, Int.toNat_zero] at ho hfit
    subst ho
    refine ⟨by simp [Mem.write, Mem.recordAt], ?_⟩
    refine WP.liftMem (fun _ _ => rfl) fun _ m₃ h₃ => ?_
    obtain ⟨ht3, hc3, -, hby3, -, hdead3⟩ := tlsExit_dead h₃
    have hth3 : m₃.threads.size = 2 := by
      rw [ht3]; show m₁.threads.size = 2; rw [hs1]; exact hsz
    refine ⟨by rw [ht3], .kid (some m.blocks.size), ⟨fun h => ?_, fun _ => ?_, ?_, fun c hc => ?_⟩,
      ⟨_, rfl⟩, fun h => (by cases h)⟩
    · rw [upd_ne _ _ (by decide), h0] at h; cases h
    · refine ⟨?_, ⟨_, upd_self _ _ _⟩, fun v hv0 hv1 => ?_⟩
      · exact hth3
      · rw [upd_ne _ _ hv1]; exact hoth v hv0 hv1
    · rw [upd_ne _ _ (by decide)]; exact .inr h0
    · rw [upd_self] at hc
      cases hc
      refine ⟨?_, ?_⟩
      · rw [hby3]
        simp only [Mem.bytesOf, Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hblk).1,
          Option.map_some]
        rw [LawfulEnc.size_encode] at hfit
        have := extract_writeBytes blk.bytes 0 (Enc.encode (⟨some m.blocks.size, 0⟩ : Ptr))
          (by rw [LawfulEnc.size_encode]; omega)
        rw [LawfulEnc.size_encode] at this
        simpa [show Enc.size Ptr = 8 from rfl] using this
      · have hmem : (0, m.blocks.size) ∈ m₁.tlsOf m₁.current := by
          rw [hc1]; exact Array.mem_of_getElem? hreg
        exact hdead3 _ hmem

/-! ## `main` -/

theorem mem0_threads : (mem0 .fresh).threads.size = 1 := by decide

set_option maxHeartbeats 1000000 in
theorem main_spec (d : Nat) : proto.WP 0 leaked QM (fun _ => .none) { (mem0 .fresh) with current := 0 } d := by
  unfold leaked
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s0 m₁ h₁ => ?_)
  obtain ⟨rfl, rfl⟩ := Proto.alloc_ok h₁
  refine ⟨rfl, ?_⟩
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₂ h₂ => ?_)
  obtain ⟨b, blk, o, -, -, rfl⟩ := Proto.storeUndef_ok h₂
  refine ⟨rfl, ?_⟩
  have hs0 : (⟨some ({ (mem0 .fresh) with current := 0 } : Mem).blocks.size, 0⟩ : Ptr) = pBlk := by decide
  simp only [StateT.run_bind]
  refine WP.bind (WP.spawnC fun k _ => ⟨.main false, ⟨fun _ => ⟨fun v hv => ?_, ?_⟩,
    fun h => (by rw [upd_self] at h; cases h), .inl (upd_self _ _ _), fun c hc => ?_⟩,
    fun G₁ m₃ hg₁ hi₃ => ⟨.kid none, ⟨hs0, rfl⟩, fun child m₄ hf => ?_⟩⟩)
  · rw [upd_ne _ _ hv]
  · simp [Mem.write, Mem.recordAt, Mem.afterAlloc, mem0_threads]
  · rw [upd_ne _ _ (by decide)] at hc; cases hc
  obtain ⟨hnone, hsz₃⟩ := hi₃.pre hg₁
  obtain ⟨hchild, hsz₄⟩ := Proto.fork_ok hf
  simp only [hsz₃] at hchild hsz₄
  subst hchild
  simp only [StateT.run_bind]
  -- The join.
  refine WP.bind (WP.joinC fun k _ => ⟨.main true, ⟨fun h => (by rw [upd_self] at h; cases h),
    fun _ => ⟨hsz₄, ⟨_, (by rw [upd_ne _ _ (by decide), upd_self])⟩, fun v hv0 hv1 => ?_⟩,
    .inr (upd_self _ _ _), fun c hc => ?_⟩, fun G₂ m₅ hg₂ hi₅ =>
      ⟨fun h => (by cases h), fun hfin => ⟨fun h => (by cases h), fun m₆ hj => ?_⟩⟩⟩)
  · rw [upd_ne _ _ hv0, upd_ne _ _ hv1]; exact hnone v hv0
  · rw [upd_ne _ _ (by decide), upd_self] at hc; cases hc
  obtain ⟨c, hc⟩ := hfin
  obtain ⟨hbytes, hdead⟩ := hi₅.done c hc
  obtain ⟨rec, -, -, rfl⟩ := Proto.join_eq hj
  -- `p.*`: the leaked pointer.
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun a m₇ h₇ => ?_)
  obtain ⟨bo, blk', o', hacc, -, hdec, rfl⟩ := Proto.load_ok h₇
  obtain ⟨hpb, hblk, -, -, -, -, ho⟩ := access_eq hacc
  simp only [Option.some.injEq] at hpb
  subst hpb
  simp only [Int.toNat_zero] at ho
  subst ho
  have hblk5 : m₅.blocks[1]? = some blk' := hblk
  simp only [Mem.bytesOf, hblk5, Option.map_some, Option.some.injEq] at hbytes
  rw [show Enc.size Ptr = 8 from rfl, hbytes, decodeLoad_encode] at hdec
  simp only [pure, ExceptT.pure, ExceptT.run, ExceptT.mk, Option.some.injEq,
    Except.ok.injEq] at hdec
  subst hdec
  refine ⟨rfl, ?_⟩
  -- `.*` of it: a use after free.
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun a' m₈ h₈ => ?_)
  refine (load_dead ?_ rfl h₈).elim
  exact hdead

/-! ## The results -/

/-- **A pointer to a thread-local used after its thread ended never gives a result**, under
every schedule and every fuel: each run throws or runs out of fuel. -/
theorem leaked_never_ok {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem} :
    (Sched.run dispatch fuel o leaked (mem0 .fresh)).run ≠ some (.ok (v, m)) := fun h => by
  obtain ⟨_, _, hq⟩ := proto.run_sound dispatch (fun _ => .none) dispatch_spec
    (fun h => by cases h) mem0_threads main_spec h
  exact hq

end ThreadLocals.Leak
