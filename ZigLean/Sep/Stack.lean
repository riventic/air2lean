import ZigLean.Sep.Cost
import ZigLean.Sep.Step

/-!
# Total correctness under the stack budget (MM-5, STK-01)

A recursive function that uses memory charges a frame on entry (`Zig.enterFrame`) and releases
it on return (`Zig.leaveFrame`). Under a stack budget (`Mem.stackLimit = some L`) a call chain
whose frames do not fit throws `.stackOverflow`. So no `TotalTriple` of such a function holds:
`TotalTriple` quantifies over every memory, including one with no room at all
(`not_total_of_overflow`). Its total correctness needs a stack premise.

`TotalTripleStk P c Q need held` is that premise made explicit. From every framed memory with
room for `need` more bytes of frames (`Mem.StackRoom`: no budget, or `stackUsed + need ≤ L`), `c`
returns, with the postcondition owned and the frame preserved, and releases exactly `held` bytes
of frames that it did not charge itself (`held = 0` for a whole function; inside a function body
after `enterFrame b`, the body must release `frameBase + b`). The budget is untouched.

* `of_total`: a command that never touches the stack (`StackFree`) and has a `TotalTriple` needs
  no room. `StackFree` holds for loads, stores, pointer projection, lifted pure results
  (arithmetic) and their binds (`StackFree.bind`).
* `enterFrame_bind` / `leaveFrame_bind`: the frame bracket of a generated recursive function:
  entering takes `frameBase + b` bytes of the room and opens them; leaving releases them.
* `spec_bind`: a call whose own triple needs `n ≤ need` bytes (an induction hypothesis of
  `rec_template`).
* `unbudgeted`: on a memory without a budget (`stackLimit = none`, every generated `mem0`) the
  conclusion is the `TotalTriple` conclusion; the statement then rests on premise STK-01 for the
  native stack, and `need` states the model's estimate of the depth it assumes.
* `overflow_of_tight`-style refutations live with the clients: a memory with less room than the
  chain charges overflows, so `need` is not vacuous.

The statement is independent of how a partial `Triple` reads `.stackOverflow` (as a failure or as
non-termination): it is a total statement with its own premise, and its conclusion is an equation
`c.run m = pure (v, m')`.

`sep_step`/`sep_steps` (`ZigLean/Sep/Step.lean`) walk `TotalTripleStk` goals with these rules:
loads and stores as for `TotalTriple`, `Zig.enterFrame`/`Zig.leaveFrame` by the bracket rules,
and `using r` for a callee's `TotalTripleStk` (its need must fit) or `TotalTriple` (its command must
be `StackFree`).
-/

/-- The side condition of a frame rule: room or held bytes, by `omega` over `frameBase`. -/
macro "stk_side" : tactic => `(tactic| first | rfl | omega | (simp only [Zig.frameBase] at *; omega))

namespace Zig

open Assn

/-! ## Room on the stack -/

/-- `m` has room for `need` more bytes of frames: no budget, or the budget holds them. -/
def Mem.StackRoom (m : Mem) (need : Nat) : Prop :=
  ∀ l, m.stackLimit = some l → m.stackUsed + need ≤ l

theorem Mem.StackRoom.mono {m : Mem} {n n' : Nat} (h : m.StackRoom n) (hle : n' ≤ n) :
    m.StackRoom n' := fun l hl => by have := h l hl; omega

theorem Mem.StackRoom.of_none {m : Mem} (h : m.stackLimit = none) (need : Nat) :
    m.StackRoom need := fun _ hl => by rw [h] at hl; cases hl

/-! ## Commands that leave the stack alone -/

/-- Every successful run of `c` keeps the charged bytes and the budget. -/
def StackFree {α : Type} (c : MemM α) : Prop :=
  ∀ m v m', c.run m = pure (v, m') → m'.stackUsed = m.stackUsed ∧ m'.stackLimit = m.stackLimit

namespace StackFree

variable {α β : Type}

theorem pure (v : α) : StackFree (Pure.pure v : MemM α) := by
  intro m w m' h
  simp only [StateT.run, Pure.pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
  cases h; exact ⟨rfl, rfl⟩

theorem lift (r : Result α) : StackFree (StateT.lift r : MemM α) := by
  intro m v m' h
  change ((StateT.lift r : MemM α).run m).run = some (.ok (v, m')) at h
  simp only [StateT.run, StateT.lift, ExceptT.run_bind] at h
  match hr : r.run, h with
  | none, h => simp at h
  | some (.error _), h => simp [Pure.pure] at h
  | some (.ok a'), h =>
    simp [Pure.pure, ExceptT.pure, ExceptT.mk] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem bind {c : MemM α} {f : α → MemM β} (hc : StackFree c) (hf : ∀ v, StackFree (f v)) :
    StackFree (c >>= f) := by
  intro m w m'' h
  change ((c >>= f).run m).run = some (.ok (w, m'')) at h
  rw [StateT.run_bind, ExceptT.run_bind] at h
  match hx : (c.run m).run, h with
  | none, h => simp at h
  | some (.error _), h => simp [Pure.pure] at h
  | some (.ok (v, m')), h =>
    obtain ⟨u₁, l₁⟩ := hc m v m' hx
    obtain ⟨u₂, l₂⟩ := hf v m' w m'' (by simp [hx] at h; exact h)
    exact ⟨u₂.trans u₁, l₂.trans l₁⟩

theorem load {T : Type} [Enc T] (a : Nat) (p : Ptr) : StackFree (Zig.load T a p) := by
  intro m v m' h
  obtain ⟨_, _, _, -, -, rfl⟩ := load_inv h
  exact ⟨rfl, rfl⟩

theorem storeBytes (p : Ptr) (a : Nat) (bs : Array Byte) (kind : AccessKind) :
    StackFree (Zig.storeBytes p a bs kind) := by
  intro m u m' h
  cases hw : m.accessW p bs.size a with
  | none => simp [Zig.storeBytes, zig_unfold, hw] at h
  | some r =>
    cases r with
    | error e => simp [Zig.storeBytes, zig_unfold, hw] at h; cases h
    | ok r =>
      obtain ⟨b, blk, o⟩ := r
      have hacc : m.access p bs.size a = Pure.pure (b, blk, o) ∧ blk.kind ≠ .constGlobal := by
        unfold Mem.accessW at hw
        cases ha : m.access p bs.size a with
        | none => simp [ha, zig_unfold] at hw
        | some r => cases r with
          | error e => simp [ha, zig_unfold] at hw; cases hw
          | ok r =>
            simp [ha, zig_unfold] at hw
            split at hw
            · cases hw
            · rename_i hk; cases hw; exact ⟨rfl, hk⟩
      by_cases hnr : NoRace m b o bs.size kind
      · rw [storeBytes_run hacc.1 hacc.2 hnr] at h
        simp only [Pure.pure, ExceptT.pure, ExceptT.mk] at h
        cases h; exact ⟨rfl, rfl⟩
      · unfold NoRace at hnr
        obtain ⟨err, herr⟩ := Option.ne_none_iff_exists'.mp hnr
        simp [Zig.storeBytes, recordAccess, zig_unfold, hw, herr] at h; cases h

theorem store {T : Type} [Enc T] (a : Nat) (p : Ptr) (v : T) : StackFree (Zig.store a p v) :=
  storeBytes _ _ _ _

theorem ptrProject (p : Ptr) (f : Ptr → Ptr) : StackFree (Zig.ptrProject p f) := by
  intro m q m' h
  simp only [Zig.ptrProject, StateT.run] at h
  split at h
  · simp only [Pure.pure, ExceptT.pure, ExceptT.mk] at h; cases h; exact ⟨rfl, rfl⟩
  · simp [Pure.pure, ExceptT.pure, ExceptT.mk] at h
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk] at h
    cases h

end StackFree

/-! ## The triple -/

/-- Total correctness from every framed memory with room for `need` more bytes of frames; the
run releases `held` bytes of frames charged before it (`0` for a whole call) and keeps the
budget. -/
def TotalTripleStk {α : Type} (P : Assn) (c : MemM α) (Q : α → Assn) (need held : Nat) : Prop :=
  ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq → m.StackRoom need →
    held ≤ m.stackUsed →
    ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧
      m'.Seq ∧ m'.stackUsed + held = m.stackUsed ∧ m'.stackLimit = m.stackLimit

namespace TotalTripleStk

variable {α β : Type} {P P' R : Assn} {Q Q' : β → Assn} {need held : Nat}

/-- On a memory without a budget (every generated `mem0`) the triple gives the `TotalTriple`
conclusion. The statement then assumes STK-01 for the native stack. -/
theorem unbudgeted {c : MemM β} (t : TotalTripleStk P c Q need 0) {m : Mem} {hP hF : Heap}
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    (hl : m.stackLimit = none) :
    ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧
      m'.Seq := by
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs', -⟩ :=
    t m hP hF hd hm hp hs (Mem.StackRoom.of_none hl need) (Nat.zero_le _)
  exact ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩

theorem returns {c : MemM β} (t : TotalTripleStk P c Q need 0) {m : Mem} {hP hF : Heap}
    (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    (hroom : m.StackRoom need) : ∃ v m', c.run m = pure (v, m') := by
  obtain ⟨v, m', -, hr, -⟩ := t m hP hF hd hm hp hs hroom (Nat.zero_le _)
  exact ⟨v, m', hr⟩

/-- More room is a weaker premise. -/
theorem mono {c : MemM β} {n : Nat} (t : TotalTripleStk P c Q n held) (hn : n ≤ need) :
    TotalTripleStk P c Q need held :=
  fun m hP hF hd hm hp hs hroom ho => t m hP hF hd hm hp hs (hroom.mono hn) ho

theorem conseq {c : MemM β} (t : TotalTripleStk P c Q need held) (hp : ∀ h, P' h → P h)
    (hq : ∀ v h, Q v h → Q' v h) : TotalTripleStk P' c Q' need held := by
  intro m hP hF hd hm hp' hs hroom ho
  obtain ⟨v, m', hQ, hr, hd', hm', hq', rest⟩ := t m hP hF hd hm (hp _ hp') hs hroom ho
  exact ⟨v, m', hQ, hr, hd', hm', hq _ _ hq', rest⟩

theorem pre {c : MemM β} (hp : ∀ h, P h → P' h) (t : TotalTripleStk P' c Q need held) :
    TotalTripleStk P c Q need held :=
  conseq t hp fun _ _ hq => hq

theorem frame {c : MemM β} (t : TotalTripleStk P c Q need held) :
    TotalTripleStk (P ∗ R) c (fun v => Q v ∗ R) need held := by
  intro m hPR hF hd hm ⟨hP, hR, hPd, hPR', hp, hr⟩ hs hroom ho
  subst hPR'
  obtain ⟨hPF, hRF⟩ := Heap.disjoint_union_left.mp hd
  have hd' := Heap.disjoint_union_right.mpr ⟨hPd, hPF⟩
  have hm' : m.heap = hP ∪ (hR ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨v, m', hQ, hrun, hQd, hmQ, hq, rest⟩ := t m hP (hR ∪ hF) hd' hm' hp hs hroom ho
  obtain ⟨hQR, hQF⟩ := Heap.disjoint_union_right.mp hQd
  exact ⟨v, m', hQ ∪ hR, hrun, Heap.disjoint_union_left.mpr ⟨hQF, hRF⟩,
    by rw [hmQ, Heap.union_assoc], ⟨hQ, hR, hQR, rfl, hq, hr⟩, rest⟩

/-- A stack-free command with a total triple needs no room and opens nothing. -/
theorem of_total {c : MemM β} (t : TotalTriple P c Q) (hc : StackFree c) :
    TotalTripleStk P c Q need 0 := by
  intro m hP hF hd hm hp hs _ _
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs'⟩ := t m hP hF hd hm hp hs
  obtain ⟨u, l⟩ := hc m v m' hr
  exact ⟨v, m', hQ, hr, hd', hm', hq, hs', by omega, l⟩

theorem ret (v : β) : TotalTripleStk (Q v) (pure v) Q need 0 := by
  intro m hP _ hd hm hq hs _ _
  exact ⟨v, m, hP, rfl, hd, hm, hq, hs, rfl, rfl⟩

theorem ret_of {v : β} (h : ∀ h, P h → Q v h)
    (ho : held = 0 := by stk_side) :
    TotalTripleStk P (pure v) Q need held := by
  subst ho; exact conseq (ret (Q := Q) v) h fun _ _ hq => hq

theorem bind {S : α → Assn} {c : MemM α} {f : α → MemM β} (hc : TotalTripleStk P c S need 0)
    (hf : ∀ v, TotalTripleStk (S v) (f v) Q need held) :
    TotalTripleStk P (c >>= f) Q need held := by
  intro m hP hF hd hm hp hs hroom ho
  obtain ⟨v, m', hS, hr, hd', hm', hs', hst', hu, hl⟩ := hc m hP hF hd hm hp hs hroom (Nat.zero_le _)
  have hroom' : m'.StackRoom need := fun l h => by rw [hl] at h; have := hroom l h; omega
  obtain ⟨w, m'', hQ, hr', hd'', hm'', hq, hst'', hu', hl'⟩ :=
    hf v m' hS hF hd' hm' hs' hst' hroom' (by omega)
  refine ⟨w, m'', hQ, ?_, hd'', hm'', hq, hst'', by omega, hl'.trans hl⟩
  simpa only [StateT.run_bind, hr, pure_bind] using hr'

theorem of_bind_pure {c : MemM β} (t : TotalTripleStk P (c >>= pure) Q need held) :
    TotalTripleStk P c Q need held := by
  simpa only [bind_pure] using t

theorem ex {γ : Type} {F : γ → Assn} {c : MemM β} (t : ∀ x, TotalTripleStk (F x) c Q need held) :
    TotalTripleStk (Assn.ex F) c Q need held := by
  intro m hP hF hd hm ⟨x, hp⟩ hs
  exact t x m hP hF hd hm hp hs

theorem lift {φ : Prop} {c : MemM β} (t : φ → TotalTripleStk P c Q need held) :
    TotalTripleStk (⌜φ⌝ ∗ P) c Q need held := by
  intro m hP hF hd hm hp hs
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact t hφ m hP hF hd hm hp hs

theorem ex_sep {γ : Type} {F : γ → Assn} {c : MemM β}
    (t : ∀ x, TotalTripleStk (F x ∗ R) c Q need held) :
    TotalTripleStk (Assn.ex F ∗ R) c Q need held :=
  pre (P' := Assn.ex fun x => F x ∗ R)
    (fun _ ⟨h₁, h₂, d, e, ⟨x, hx⟩, hr⟩ => ⟨x, h₁, h₂, d, e, hx, hr⟩) (ex t)

/-- A command proved by a `TotalTripleStk` rule that needs `n ≤ need` bytes (a call), framed by
`R`; the continuation gets the rule's result. -/
theorem spec_bind {P₀ : Assn} {Q₀ : α → Assn} {c : MemM α} {f : α → MemM β} {n : Nat}
    (rule : TotalTripleStk P₀ c Q₀ n 0) (k : ∀ r, TotalTripleStk (Q₀ r ∗ R) (f r) Q need held)
    (hn : n ≤ need := by stk_side) :
    TotalTripleStk (P₀ ∗ R) (c >>= f) Q need held :=
  bind (frame (mono rule hn)) k

theorem spec_bind_eq {P₀ P₁ : Assn} {c : MemM α} {v : α} {f : α → MemM β} {n : Nat}
    (rule : TotalTripleStk P₀ c (fun r => ⌜r = v⌝ ∗ P₁) n 0)
    (k : TotalTripleStk (P₁ ∗ R) (f v) Q need held)
    (hn : n ≤ need := by stk_side) :
    TotalTripleStk (P₀ ∗ R) (c >>= f) Q need held :=
  spec_bind rule (fun _ => conseq (lift (P := P₁ ∗ R) fun hr => hr ▸ k)
    (fun _ hp => sep_assoc hp) fun _ _ hq => hq) hn

/-! ### The frame bracket -/

/-- `enterFrame b` takes `frameBase + b` bytes of the room and leaves them held for the rest of
the body. -/
theorem enterFrame_bind {b : Nat} {f : Unit → MemM β}
    (k : TotalTripleStk P (f ()) Q (need - (frameBase + b)) (held + (frameBase + b)))
    (hle : frameBase + b ≤ need := by stk_side) :
    TotalTripleStk P (enterFrame b >>= f) Q need held := by
  intro m hP hF hd hm hp hs hroom ho
  have hrun : (enterFrame b).run m =
      pure ((), { m with stackUsed := m.stackUsed + (frameBase + b) }) := by
    cases hl : m.stackLimit with
    | none => rw [enterFrame_run_none hl b]; simp [hl]
    | some l => rw [enterFrame_run_fits hl (by have := hroom l hl; omega)]; simp [hl]
  let m₁ : Mem := { m with stackUsed := m.stackUsed + (frameBase + b) }
  have hroom₁ : m₁.StackRoom (need - (frameBase + b)) := fun l hl => by
    have := hroom l hl; simp only [m₁]; omega
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs', hu, hl'⟩ :=
    k m₁ hP hF hd hm hp ⟨hs.single⟩ hroom₁ (by simp only [m₁]; omega)
  refine ⟨v, m', hQ, ?_, hd', hm', hq, hs', by simp only [m₁] at hu; omega, hl'⟩
  simpa only [StateT.run_bind, hrun, pure_bind] using hr

/-- `leaveFrame b` releases `frameBase + b` of the held bytes and gives them back to the room. -/
theorem leaveFrame_bind {b : Nat} {f : Unit → MemM β}
    (k : TotalTripleStk P (f ()) Q (need + (frameBase + b)) (held - (frameBase + b)))
    (hle : frameBase + b ≤ held := by stk_side) :
    TotalTripleStk P (leaveFrame b >>= f) Q need held := by
  intro m hP hF hd hm hp hs hroom ho
  let m₁ : Mem := { m with stackUsed := m.stackUsed - (frameBase + b) }
  have hrun : (leaveFrame b).run m = pure ((), m₁) := leaveFrame_run m b
  have hroom₁ : m₁.StackRoom (need + (frameBase + b)) := fun l hl => by
    have := hroom l hl; simp only [m₁]; omega
  obtain ⟨v, m', hQ, hr, hd', hm', hq, hs', hu, hl'⟩ :=
    k m₁ hP hF hd hm hp ⟨hs.single⟩ hroom₁ (by simp only [m₁]; omega)
  refine ⟨v, m', hQ, ?_, hd', hm', hq, hs', by simp only [m₁] at hu; omega, hl'⟩
  simpa only [StateT.run_bind, hrun, pure_bind] using hr

/-! ### Loads, stores and pointers: as for `TotalTriple`, stack-free -/

section Rules

variable {T : Type} [Enc T] {p : Ptr} {a : Nat}

theorem load_bind {v : T} {f : T → MemM β} (hn : 0 < Enc.size T)
    (k : TotalTripleStk (pts p a v ∗ R) (f v) Q need held) :
    TotalTripleStk (pts p a v ∗ R) (Zig.load T a p >>= f) Q need held :=
  spec_bind_eq (of_total (TotalTriple.load hn) (StackFree.load a p)) k (Nat.zero_le _)

theorem store_bind [LawfulEnc T] {v w : T} {f : Unit → MemM β} (hn : 0 < Enc.size T)
    (k : TotalTripleStk (pts p a w ∗ R) (f ()) Q need held) :
    TotalTripleStk (pts p a v ∗ R) (Zig.store a p w >>= f) Q need held :=
  spec_bind (of_total (TotalTriple.store hn w) (StackFree.store a p w)) (fun () => k)
    (Nat.zero_le _)

theorem arr_load_bind {xs : List T} {i : BitVec 64} {f : T → MemM β}
    (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (hi : i.toNat < xs.length) (k : TotalTripleStk (arr p xs ∗ R) (f xs[i.toNat]) Q need held) :
    TotalTripleStk (arr p xs ∗ R) (Zig.load T a (p.elem (Enc.size T) i) >>= f) Q need held :=
  spec_bind_eq (of_total (TotalTriple.arr_load hn ha hs hi) (StackFree.load _ _)) k
    (Nat.zero_le _)

theorem arr_store_bind [LawfulEnc T] {xs : List T} {i : BitVec 64} {w : T}
    {f : Unit → MemM β} (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length)
    (k : TotalTripleStk (arr p (xs.set i.toNat w) ∗ R) (f ()) Q need held) :
    TotalTripleStk (arr p xs ∗ R) (Zig.store a (p.elem (Enc.size T) i) w >>= f) Q need held :=
  spec_bind (of_total (TotalTriple.arr_store hn ha hs hi w) (StackFree.store _ _ _))
    (fun () => k) (Nat.zero_le _)

theorem arr_ptrProject_bind {xs : List T} {i : BitVec 64} {f : Ptr → MemM β}
    (hi : i.toNat ≤ xs.length)
    (k : TotalTripleStk (arr p xs ∗ R) (f (p.elem (Enc.size T) i)) Q need held) :
    TotalTripleStk (arr p xs ∗ R) (ptrProject p (·.elem (Enc.size T) i) >>= f) Q need held :=
  spec_bind_eq (of_total (TotalTriple.arr_ptrProject hi) (StackFree.ptrProject _ _)) k
    (Nat.zero_le _)

theorem arr_split_pre {xs : List T} {k : Nat} {c : MemM β} (hs : Enc.align T ∣ Enc.size T)
    (hk : k ≤ xs.length)
    (t : TotalTripleStk ((arr p (xs.take k) ∗ arr (p.add (Enc.size T * k)) (xs.drop k)) ∗ R) c Q
      need held) : TotalTripleStk (arr p xs ∗ R) c Q need held :=
  pre (fun _ => sep_mono (fun _ ha => arr_split ha hk hs) fun _ hr => hr) t

end Rules

end TotalTripleStk

/-- A body that starts with a frame that does not fit throws `.stackOverflow`: every generated
recursive function that uses memory, on a memory without room for its first frame. -/
theorem enterFrame_bind_overflow {β : Type} {b : Nat} {f : Unit → MemM β} {m : Mem} {l : Nat}
    (hl : m.stackLimit = some l) (hover : l < m.stackUsed + (frameBase + b)) :
    ((enterFrame b >>= f).run m).run = some (.error .stackOverflow) := by
  rw [StateT.run_bind, ExceptT.run_bind, enterFrame_overflow hl hover]
  rfl

/-- A command that throws `.stackOverflow` from an admissible memory has no `TotalTriple`. A
generated recursive function that uses memory overflows on a memory with no room, so its total
correctness needs `TotalTripleStk`. -/
theorem not_total_of_overflow {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {m : Mem}
    {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq)
    (hov : (c.run m).run = some (.error .stackOverflow)) : ¬ TotalTriple P c Q := by
  intro t
  obtain ⟨v, m', -, hr, -⟩ := t m hP hF hd hm hp hs
  rw [hr] at hov
  cases hov

end Zig
