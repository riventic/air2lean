import DeviceEffects.Gen
import ZigLean.Sep.Full.AutoAll
import ZigLean.Sep.Full.Cost

/-!
# Device-effect proofs on the generated UART driver (L13)

`DeviceEffects/Gen.lean` is the unchanged translation of the real 0.16.0 export of
`device_effects.zig` with `--device-contract uart.json`. The statements are total triples of the
full-state logic over the device state `devOwn D` (`docs/sep-full-state.md` §Device state), for
every device state `D`: its oracle, and its trace so far. The device contract (premise DEV-01)
is only that the device answers the reads that a theorem names. `fsym` walks the generated code
with the library's device rules (`ZigLean/Sep/Full/Device.lean`), of which the `uart` contract
is an instance. Nothing about ordinary memory changes: a triple frames every other resource.
-/

namespace DeviceEffectsProofs
open Zig Zig.Full Zig.Full.FAssn DeviceEffects

/-- The register block's address (`uart.json`). -/
abbrev base : Nat := 268435456
abbrev uart : Ptr := ⟨none, (base : Int)⟩
abbrev STATUS : Nat := base
abbrev DATA : Nat := base + 4

/-- A status read event. A data write of the byte `c` is the event `.write DATA 32 c.toNat`,
written out: the walk matches it up to the arithmetic of the byte's zero extension. -/
abbrev rd (v : BitVec 32) : DevEvent := .read STATUS 32 v.toNat

/-- The registers' addresses: the facts of the contract that the device rules ask for. -/
theorem status_addr : devAddr? uart = some STATUS := by decide
theorem data_addr : devAddr? (uart.add 4) = some DATA := by decide

/-! ## Two reads are two events, never one merged read -/

/-- `statusTwice` reads the status register twice: two `read` events, in order, and the second
answer is the oracle's answer *after* the first read. -/
theorem statusTwice_trace (D : DevState) (a b : BitVec 32)
    (ha : D.oracle D.trace STATUS 32 = some a)
    (hb : D.oracle (D.trace ++ [rd a]) STATUS 32 = some b) :
    FTotalTriple (devOwn D) (statusTwice uart)
      (fun r => ⟪r = a ^^^ b⟫ ⋆ devOwn { D with trace := D.trace ++ [rd a, rd b] }) := by
  have hs := status_addr
  fsym

/-- A device that counts the reads so far: the `k`-th read answers `k`. -/
def counter : DevOracle := fun h _ n => some (BitVec.ofNat n h.length)

/-- Under the counting device, `statusTwice` returns `0 ^^^ 1 = 1`. A translation that merged
the two volatile reads into one would return `a ^^^ a = 0` under every device. -/
theorem statusTwice_not_merged :
    FTotalTriple (devOwn { oracle := counter }) (statusTwice uart)
      (fun r => ⟪r = 1⟫ ⋆ devOwn { oracle := counter, trace := [rd 0, rd 1] }) :=
  statusTwice_trace { oracle := counter } 0 1 rfl rfl

theorem statusTwice_ne_merged : ∀ a : BitVec 32, (0 : BitVec 32) ^^^ 1 ≠ a ^^^ a := by
  intro a; simp

/-- An unused read is still one event (a read-to-clear register is cleared). -/
theorem clearStatus_trace (D : DevState) (v : BitVec 32)
    (ho : D.oracle D.trace STATUS 32 = some v) :
    FTotalTriple (devOwn D) (clearStatus uart)
      (fun _ => devOwn { D with trace := D.trace ++ [rd v] }) := by
  have hs := status_addr
  fsym

/-- Program order: the write happens before the read, and the device answers the read after
seeing the write. -/
theorem sendThenStatus_trace (D : DevState) (c : BitVec 8) (v : BitVec 32)
    (ho : D.oracle (D.trace ++ [.write DATA 32 c.toNat]) STATUS 32 = some v) :
    FTotalTriple (devOwn D) (sendThenStatus uart c)
      (fun r => ⟪r = v⟫ ⋆ devOwn { D with trace := D.trace ++ [.write DATA 32 c.toNat] ++ [rd v] }) := by
  have hs := status_addr
  have hd := data_addr
  fsym

/-! ## The polling contract

`Answers o h vs r`: from the trace `h` on, the device answers the status reads with the busy
values `vs` (bit 0 clear), then with the ready value `r` (bit 0 set). Every oracle under which
`putc` returns has exactly one such `vs` and `r`, so this covers every terminating device. -/
def Answers (o : DevOracle) : List DevEvent → List (BitVec 32) → BitVec 32 → Prop
  | h, [], r => o h STATUS 32 = some r ∧ r &&& 1#32 ≠ 0#32
  | h, v :: vs, r => o h STATUS 32 = some v ∧ v &&& 1#32 = 0#32 ∧ Answers o (h ++ [rd v]) vs r

/-- The answer to the next poll at the trace `tr`, which is `h` and the polls so far. -/
def nxt (h : List DevEvent) (vs : List (BitVec 32)) (r : BitVec 32) (tr : List DevEvent) :
    BitVec 32 :=
  (vs.drop (tr.length - h.length)).headD r

/-- `tr` is the trace of a device that answers by the contract from `h` on, after some of its
busy polls. -/
structure Polled (o : DevOracle) (h : List DevEvent) (vs : List (BitVec 32)) (r : BitVec 32)
    (tr : List DevEvent) : Prop where
  answers : Answers o h vs r
  polls : ∃ i, i ≤ vs.length ∧ tr = h ++ (vs.take i).map rd

/-- The contract at each poll: the answer after the first `i` busy polls, busy before the last. -/
theorem Answers.at {o : DevOracle} {vs : List (BitVec 32)} {r : BitVec 32} :
    ∀ {h : List DevEvent}, Answers o h vs r → ∀ i, i ≤ vs.length →
      o (h ++ (vs.take i).map rd) STATUS 32 = some ((vs.drop i).headD r) ∧
      (i < vs.length → (vs.drop i).headD r &&& 1#32 = 0#32) ∧
      (i = vs.length → (vs.drop i).headD r &&& 1#32 ≠ 0#32) := by
  induction vs with
  | nil =>
    intro h ⟨ho, hr⟩ i hi
    obtain rfl : i = 0 := by simpa using hi
    simpa using ⟨ho, hr⟩
  | cons v vs ih =>
    intro h ⟨ho, hv, hrest⟩ i hi
    cases i with
    | zero => simpa using ⟨ho, hv⟩
    | succ i =>
      have := ih hrest i (by simpa using hi)
      simpa [List.append_assoc] using this

theorem Polled.start {o : DevOracle} {h : List DevEvent} {vs : List (BitVec 32)} {r : BitVec 32}
    (hc : Answers o h vs r) : Polled o h vs r h :=
  ⟨hc, 0, Nat.zero_le _, by simp⟩

section
variable {o : DevOracle} {h tr : List DevEvent} {vs : List (BitVec 32)} {r : BitVec 32}

/-- The facts of a polled trace at its position `i`. -/
theorem Polled.pos (hP : Polled o h vs r tr) :
    ∃ i, i ≤ vs.length ∧ tr = h ++ (vs.take i).map rd ∧ tr.length - h.length = i ∧
      tr.length = h.length + i := by
  obtain ⟨i, hi, rfl⟩ := hP.polls
  exact ⟨i, hi, rfl, by simp [Nat.min_eq_left hi], by simp [Nat.min_eq_left hi]⟩

theorem Polled.oracle (hP : Polled o h vs r tr) : o tr STATUS 32 = some (nxt h vs r tr) := by
  obtain ⟨i, hi, rfl, hd, -⟩ := hP.pos
  rw [nxt, hd]
  exact (hP.answers.at i hi).1

theorem Polled.busy (hP : Polled o h vs r tr) (hk : vs.length + h.length - tr.length ≠ 0) :
    nxt h vs r tr &&& 1#32 = 0#32 := by
  obtain ⟨i, hi, rfl, hd, hl⟩ := hP.pos
  rw [nxt, hd]
  exact (hP.answers.at i hi).2.1 (by omega)

theorem Polled.ready (hP : Polled o h vs r tr) (hk : vs.length + h.length - tr.length = 0) :
    nxt h vs r tr &&& 1#32 ≠ 0#32 := by
  obtain ⟨i, hi, rfl, hd, hl⟩ := hP.pos
  rw [nxt, hd]
  exact (hP.answers.at i hi).2.2 (by omega)

/-- After a busy answer the trace is a polled trace again. -/
theorem Polled.next (hP : Polled o h vs r tr) (hb : nxt h vs r tr &&& 1#32 = 0#32) :
    Polled o h vs r (tr ++ [rd (nxt h vs r tr)]) := by
  obtain ⟨i, hi, rfl, hd, hl⟩ := hP.pos
  have hlt : i < vs.length := by
    rcases Nat.lt_or_ge i vs.length with h' | h'
    · exact h'
    · exact absurd hb (hP.ready (by omega))
  refine ⟨hP.answers, i + 1, hlt, ?_⟩
  have hn : nxt h vs r (h ++ (vs.take i).map rd) = vs[i] := by
    rw [nxt, hd, List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hlt]; rfl
  rw [hn, List.take_succ, List.getElem?_eq_getElem hlt, List.map_append, List.append_assoc]; rfl

/-- After the ready answer the trace is the contract's whole trace. -/
theorem Polled.last (hP : Polled o h vs r tr) (hr : ¬nxt h vs r tr &&& 1#32 = 0#32) :
    tr ++ [rd (nxt h vs r tr)] = h ++ (vs ++ [r]).map rd := by
  obtain ⟨i, hi, rfl, hd, hl⟩ := hP.pos
  have he : i = vs.length := by
    rcases Nat.lt_or_ge i vs.length with h' | h'
    · exact absurd (hP.busy (by omega)) hr
    · omega
  subst he
  simp [nxt]

end

set_option linter.unusedVariables false in
/-- The polling loop's invariant, at the exact count `k` of the busy answers still to come: the
device state is the entry's `D0` with a polled trace `tr`, and the device answers the next poll
with `nxt … tr`, busy unless `k = 0` (the facts of `Polled` that the walk reads). -/
@[fsym_inv] def _root_.DeviceEffects.putc.loop3.credits.inv (p0 : Ptr) (D0 : DevState)
    (vs : List (BitVec 32)) (r : BitVec 32) (s : putcLocals) (k : Nat) : FAssn :=
  FAssn.ex fun tr : List DevEvent =>
    ⟪Polled D0.oracle D0.trace vs r tr ∧
      k = vs.length + D0.trace.length - tr.length ∧
      D0.oracle tr STATUS 32 = some (nxt D0.trace vs r tr) ∧
      (k = 0 → nxt D0.trace vs r tr &&& 1#32 ≠ 0#32) ∧
      (k ≠ 0 → nxt D0.trace vs r tr &&& 1#32 = 0#32)⟫ ⋆ devOwn { D0 with trace := tr }

set_option linter.unusedVariables false in
/-- At the loop's exit the trace is the contract's: every poll, in order. -/
@[fsym_inv] def _root_.DeviceEffects.putc.loop3.credits.post (p0 : Ptr) (D0 : DevState)
    (vs : List (BitVec 32)) (r : BitVec 32) (e : putcExit × putcLocals) : FAssn :=
  FAssn.ex fun tr : List DevEvent =>
    ⟪e.1 = .br2 ∧ tr = D0.trace ++ (vs ++ [r]).map rd⟫ ⋆ devOwn { D0 with trace := tr }

/-- **`putc` meets its trace spec for every device oracle satisfying the polling contract**:
the emitted trace is exactly the polls in order, then one data write of `c`, and the run makes
exactly one step per poll: it pays `vs.length + 1` credits (`fsym` takes the loop's credit-mode
invariant and the counted loop rule). Ordinary memory is unchanged (the triple frames it). The
goals `fsym` leaves are the invariant's pure facts, which are the contract's (`Polled`). -/
theorem putc_trace (D : DevState) (c : BitVec 8) (vs : List (BitVec 32)) (r : BitVec 32)
    (hc : Answers D.oracle D.trace vs r) :
    FTotalTriple (devOwn D ⋆ credits (vs.length + 1)) (putc uart c)
      (fun _ => devOwn { D with trace := D.trace ++ (vs ++ [r]).map rd ++ [.write DATA 32 c.toNat] } ⋆
        spent (vs.length + 1)) := by
  have hs := status_addr
  have hd := data_addr
  have hP := Polled.start hc
  fsym
  -- the invariant's facts: at the entry, after a busy answer, and the trace at the exit
  all_goals first
    | exact Polled.last (by assumption) (by assumption)
    | exact hP.oracle
    | exact fun h0 => hP.ready (by omega)
    | exact fun h0 => hP.busy (by omega)
    | exact Polled.next (by assumption) (by assumption)
    | exact (Polled.next (by assumption) (by assumption)).oracle
    | exact fun h0 => (Polled.next (by assumption) (by assumption)).ready (by simpa using h0)
    | exact fun h0 => (Polled.next (by assumption) (by assumption)).busy (by simpa using h0)

/-- **The run from program start**, with the environment's device state `D` in the start memory
(adequacy: `initRes_holds_dev`, and the meter's `FTotalTriple.ticks_eq`): `putc` returns after
exactly one step per poll. -/
theorem putc_steps (σ : Placement) (D : DevState) (c : BitVec 8) (vs : List (BitVec 32))
    (r : BitVec 32) (hc : Answers D.oracle D.trace vs r) :
    ∃ m', (putc uart c).run { mem0 σ with dev := D } = pure ((), m') ∧
      m'.ticks = vs.length + 1 := by
  have hi := initRes_holds_dev σ [] (by simp) D
  have hp : (devOwn D ⋆ emp) _ := hi.2
  obtain ⟨⟨⟩, m', hr, hticks⟩ := (putc_trace D c vs r hc).ticks_eq hi.1 (sep_emp.mp hp)
    (Mem.init_fseq_dev σ [] (by decide) D) ⟨⟨by simp, fun L => by simp, by simp⟩, by simp⟩
  exact ⟨m', hr, by simpa [Mem.ofGlobals] using hticks⟩

/-! ## Every device that eventually reports ready

`EventuallyReady o h k`: from the trace `h` on, the status register reports ready within `k + 1`
reads (each read sees the reads before it). Every such device satisfies `Answers` for exactly the
busy values it gives, so `putc` returns with the specified trace. -/
def EventuallyReady (o : DevOracle) : List DevEvent → Nat → Prop
  | h, 0 => ∃ r, o h STATUS 32 = some r ∧ r &&& 1#32 ≠ 0#32
  | h, k + 1 => ∃ v, o h STATUS 32 = some v ∧
      (v &&& 1#32 ≠ 0#32 ∨ (v &&& 1#32 = 0#32 ∧ EventuallyReady o (h ++ [rd v]) k))

theorem answers_of_ready (o : DevOracle) :
    ∀ k h, EventuallyReady o h k → ∃ vs r, Answers o h vs r := by
  intro k
  induction k with
  | zero => intro h ⟨r, ho, hr⟩; exact ⟨[], r, ho, hr⟩
  | succ k ih =>
    intro h ⟨v, ho, hv⟩
    rcases hv with hr | ⟨hb, hrest⟩
    · exact ⟨[], v, ho, hr⟩
    · obtain ⟨vs, r, ha⟩ := ih _ hrest
      exact ⟨v :: vs, r, ho, hb, ha⟩

/-- **`putc` returns for every device that eventually reports ready**, with the trace of its
polls followed by exactly one data write of `c`, and one step per poll. -/
theorem putc_eventually (D : DevState) (c : BitVec 8) (k : Nat)
    (hr : EventuallyReady D.oracle D.trace k) :
    ∃ vs r, FTotalTriple (devOwn D ⋆ credits (vs.length + 1)) (putc uart c)
      (fun _ => devOwn { D with trace := D.trace ++ (vs ++ [r]).map rd ++ [.write DATA 32 c.toNat] } ⋆
        spent (vs.length + 1)) := by
  obtain ⟨vs, r, ha⟩ := answers_of_ready _ k _ hr
  exact ⟨vs, r, putc_trace D c vs r ha⟩

end DeviceEffectsProofs
