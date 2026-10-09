import ZigLean.Sep.Full.Triple
import ZigLean.Os.Mmap

/-!
# More `Tame` programs, and the `tame` tactic

`Tame c` (`ZigLean/Sep/Full/Triple.lean`): `c` keeps the atomic layout and every block's address,
so a legacy triple of `c` lifts to a full-state one (`FTriple.ofTriple`, `FTotalTriple.ofTotal`).
This file adds the control flow of normalized generated code (`throw`, `if`, `match`,
`Option.elim`, `<$>`), `@ptrFromInt`, and the OS page mappings of premise OSM-01 (`Os.mmap`,
`Os.munmap`, `Os.mremap`: they push blocks, or replace a block by one at the same address).

`tame` proves `Tame c` for a `MemM` program built from these, after the generated function is
normalized to its `MemM` program (`gen_norm`-style `simp` with `ZigLean/Sep/AllocSpec/Norm.lean`).
-/

namespace Zig
namespace Full
namespace Tame

open Conc

variable {α β : Type}

theorem throw (e : Error) : Tame (throw e : MemM α) := fun _ _ _ h =>
  (Proto.MemM.throw_ok h).elim

theorem ite {c : Prop} [Decidable c] {x y : MemM α} (hx : Tame x) (hy : Tame y) :
    Tame (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem elim {o : Option β} {x : MemM α} {f : β → MemM α} (hx : Tame x) (hf : ∀ b, Tame (f b)) :
    Tame (o.elim x f) := by
  cases o
  · exact hx
  · exact hf _

theorem map {f : α → β} {x : MemM α} (hx : Tame x) : Tame (f <$> x) := by
  rw [map_eq_pure_bind]; exact bind hx fun _ => pure' _

theorem get : Tame (get : MemM Mem) := fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Proto.MemM.get_ok h; exact ⟨rfl, KMono.refl _⟩

theorem ptrFromAddr (n : Nat) : Tame (Zig.ptrFromAddr n) := fun m v m' h => by
  rcases ptrFromAddr_run n m with ⟨w, hw⟩ | hw <;> rw [hw] at h
  · obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok (m := m) (x := w) (a := v) (by exact h)
    exact ⟨rfl, KMono.refl _⟩
  · exact (Proto.MemM.throw_ok (m := m) (e := Error.unspecified) (a := v) (by exact h)).elim

theorem recordAccess (b o n : Nat) (k : AccessKind) : Tame (Zig.recordAccess b o n k) :=
  of_eq fun m v m' h => by
    obtain ⟨-, rfl⟩ := Proto.recordAccess_ok h
    exact ⟨rfl, KMono.of_blocks rfl⟩

/-! ## OS page mappings (premise OSM-01) -/

theorem throw_bind_ok {β γ : Type} {e : Error} {f : β → MemM γ} {m₀ m₁ : Mem} {x : γ}
    (h : (((MonadExcept.throw e : MemM β) >>= f).run m₀).run = some (.ok (x, m₁))) : False := by
  obtain ⟨_, _, h3, -⟩ := Proto.MemM.bind_ok h
  exact Proto.MemM.throw_ok h3

theorem mappingAt_ok {p : Ptr} {m m' : Mem} {r : BlockId × Block × Nat}
    (h : ((Os.mappingAt p).run m).run = some (.ok (r, m'))) :
    m' = m ∧ m.blocks[r.1]? = some r.2.1 := by
  unfold Os.mappingAt at h
  split at h
  · exact (Proto.MemM.throw_ok h).elim
  · obtain ⟨a, m₁, hg, h₁⟩ := Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok hg
    split at h₁
    · exact (Proto.MemM.throw_ok h₁).elim
    · rename_i hb
      split at h₁
      · split at h₁
        · obtain ⟨rfl, rfl⟩ := Proto.MemM.pure_ok h₁; exact ⟨rfl, hb⟩
        · exact (Proto.MemM.throw_ok h₁).elim
      · exact (Proto.MemM.throw_ok h₁).elim

theorem munmap (os : Os.Target) (s : Slice) : Tame (Os.munmap os s) := of_eq fun m v m' h => by
  unfold Os.munmap at h
  obtain ⟨⟨b, blk, lo⟩, m₁, h1, h2⟩ := Proto.MemM.bind_ok h
  obtain ⟨rfl, hb⟩ := mappingAt_ok h1
  simp only at hb h2
  have tail : ∀ (u : Option Os.Unmap) (m₀ : Mem) (v' : Unit) (h : ((match u with
      | none => (MonadExcept.throw Error.illegal : MemM Unit)
      | some u => do
        Zig.recordAccess b s.ptr.off.toNat ((s.ptr.off.toNat + alignUp s.len.toNat os.pageSize).min
          blk.bytes.size - s.ptr.off.toNat) AccessKind.write
        let m ← MonadState.get
        set { m with blocks := m.blocks.set! b (Os.Unmap.apply blk u) }).run m₀).run =
        some (Except.ok (v', m'))) (hb0 : m₀.blocks[b]? = some blk),
      m'.atomics = m₀.atomics ∧ KMono m₀ m' := by
    intro u m₀ v' h hb0
    split at h
    · exact (Proto.MemM.throw_ok h).elim
    · rename_i u
      obtain ⟨_, m₂, h3, h4⟩ := Proto.MemM.bind_ok h
      obtain ⟨-, rfl⟩ := Proto.recordAccess_ok h3
      obtain ⟨_, m₃, h5, h6⟩ := Proto.MemM.bind_ok h4
      obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok h5
      have := Proto.MemM.set_ok h6
      subst this
      exact ⟨rfl, KMono.set (blk' := Os.Unmap.apply blk u) hb0 (by cases u <;> rfl) rfl⟩
  split at h2
  · exact (throw_bind_ok h2).elim
  · exact tail _ _ _ h2 hb

theorem _root_.Zig.Full.KMono.set_push {m m' : Mem} {b : BlockId} {blk nb x : Block}
    (hb : m.blocks[b]? = some blk) (ha : nb.addr = blk.addr)
    (h : m'.blocks = (m.blocks.set! b nb).push x) : KMono m m' :=
  KMono.trans (m₂ := { m with blocks := m.blocks.set! b nb }) (KMono.set hb ha rfl) (KMono.push h)

theorem mremapLive_ok {os : Os.Target} {p : Ptr} {b : BlockId} {blk : Block} {lo : Nat}
    {newLen : BitVec 64} {flags : BitVec 32} {m m' : Mem} {v : Except ErrName Slice}
    (hb : m.blocks[b]? = some blk)
    (h : ((Os.mremapLive os p b blk lo newLen flags).run m).run = some (.ok (v, m'))) :
    m'.atomics = m.atomics ∧ KMono m m' := by
  unfold Os.mremapLive at h
  simp only at h
  have hset : ∀ {m₁ : Mem} {nb : Block}, m₁.blocks = m.blocks.set! b nb →
      nb.addr = blk.addr → KMono m m₁ := fun h3 h2 => KMono.set hb h2 h3
  split at h
  · exact (throw_bind_ok h).elim
  split at h
  · obtain ⟨_, m₂, h3, h4⟩ := Proto.MemM.bind_ok h
    obtain ⟨-, rfl⟩ := Proto.recordAccess_ok h3
    obtain ⟨_, m₃, h5, h6⟩ := Proto.MemM.bind_ok h4
    obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h6
    have e := Proto.modify_ok h5
    subst e
    exact ⟨rfl, hset rfl rfl⟩
  · obtain ⟨_, m₂, h3, h4⟩ := Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok h3
    obtain ⟨_, m₃, h5, h6⟩ := Proto.MemM.bind_ok h4
    have e := Proto.MemM.set_ok h5
    subst e
    split at h6
    · obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h6; exact ⟨rfl, KMono.of_blocks rfl⟩
    split at h6
    · obtain ⟨_, m₄, h7, h8⟩ := Proto.MemM.bind_ok h6
      obtain ⟨-, rfl⟩ := Proto.recordAccess_ok h7
      obtain ⟨_, m₅, h9, h10⟩ := Proto.MemM.bind_ok h8
      obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok h9
      obtain ⟨_, m₆, h11, h12⟩ := Proto.MemM.bind_ok h10
      obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h12
      have e := Proto.MemM.set_ok h11
      subst e
      exact ⟨rfl, KMono.set_push hb (nb := { blk with live := false }) rfl rfl⟩
    split at h6
    · obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h6; exact ⟨rfl, KMono.of_blocks rfl⟩
    · obtain ⟨_, m₄, h7, h8⟩ := Proto.MemM.bind_ok h6
      obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h8
      have e := Proto.modify_ok h7
      subst e
      exact ⟨rfl, hset rfl rfl⟩

theorem mremap (os : Os.Target) (o : Option Ptr) (oldLen newLen : BitVec 64) (flags : BitVec 32)
    (n : Option Ptr) : Tame (Os.mremap os o oldLen newLen flags n) := of_eq fun m v m' h => by
  unfold Os.mremap at h
  simp only at h
  split at h
  · exact (throw_bind_ok h).elim
  split at h
  · exact (throw_bind_ok h).elim
  · rename_i p
    obtain ⟨_, m₁, h1, h2⟩ := Proto.MemM.bind_ok h
    obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h1
    obtain ⟨⟨b, blk, lo⟩, m₂, h3, h4⟩ := Proto.MemM.bind_ok h2
    obtain ⟨rfl, hb⟩ := mappingAt_ok h3
    split at h4
    · exact (throw_bind_ok h4).elim
    · exact mremapLive_ok hb h4

theorem mmap (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (prot flags fd : BitVec 32)
    (off : BitVec 64) : Tame (Os.mmap os hint len prot flags fd off) := of_eq fun m v m' h => by
  unfold Os.mmap at h
  simp only at h
  split at h
  · exact (throw_bind_ok h).elim
  split at h
  · exact (throw_bind_ok h).elim
  obtain ⟨_, m₂, h3, h4⟩ := Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok h3
  obtain ⟨_, m₃, h5, h6⟩ := Proto.MemM.bind_ok h4
  have e := Proto.MemM.set_ok h5
  subst e
  split at h6
  · obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h6; exact ⟨rfl, KMono.of_blocks rfl⟩
  · obtain ⟨_, m₄, h7, h8⟩ := Proto.MemM.bind_ok h6
    obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok h7
    obtain ⟨_, m₅, h9, h10⟩ := Proto.MemM.bind_ok h8
    obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok h10
    have e := Proto.MemM.set_ok h9
    subst e
    exact ⟨rfl, KMono.push rfl⟩
end Tame

/-- `Tame` goals of normalized generated code. Callees are taken from the hypotheses
(`have := …` the callee's `Tame` lemma first). -/
macro "tame" : tactic => `(tactic| repeat' (first
  | (guard_target = ∀ _, _; intro)
  | with_reducible exact Tame.pure' _
  | with_reducible exact Tame.throw _
  | with_reducible exact Tame.lift _
  | with_reducible exact Tame.get
  | with_reducible exact Tame.load _ _ _
  | with_reducible exact Tame.store _ _ _
  | with_reducible exact Tame.loadBytes _ _ _ _
  | with_reducible exact Tame.storeBytes _ _ _ _
  | with_reducible exact Tame.alloc _ _ _
  | with_reducible exact Tame.free _
  | with_reducible exact Tame.ptrAddr _
  | with_reducible exact Tame.ptrFromAddr _
  | with_reducible exact Tame.recordAccess _ _ _ _
  | with_reducible exact Tame.munmap _ _
  | with_reducible exact Tame.mremap _ _ _ _ _ _
  | with_reducible exact Tame.mmap _ _ _ _ _ _ _
  | with_reducible apply_assumption
  | with_reducible apply Tame.map
  | with_reducible apply Tame.ite
  | with_reducible apply Tame.elim
  | with_reducible apply Tame.bind
  | split))

end Full
end Zig
