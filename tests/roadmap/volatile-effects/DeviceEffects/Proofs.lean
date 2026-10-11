import DeviceEffects.Gen
import ZigLean.Mem.Lemmas

/-!
# Device-effect proofs on the generated UART driver (L13)

`DeviceEffects/Gen.lean` is the unchanged translation of the real 0.16.0 export of
`device_effects.zig` with `--device-contract uart.json`. Every theorem quantifies over the
device oracle (`Mem.dev.oracle`) and the memory: the device contract (premise DEV-01) is only
that the device answers the reads that the theorem names. Nothing about ordinary memory changes:
each final memory is the initial one with the device events appended to its trace.
-/

namespace DeviceEffectsProofs
open Zig DeviceEffects

/-- The register block's address (`uart.json`). -/
def base : Nat := 268435456
def uart : Ptr := ⟨none, (base : Int)⟩
def STATUS : Nat := base
def DATA : Nat := base + 4

/-- A status read event and a data write event. -/
def rd (v : BitVec 32) : DevEvent := .read STATUS 32 v.toNat
def wr (c : BitVec 8) : DevEvent := .write DATA 32 c.toNat

/-- The byte's zero extension keeps its value. -/
theorem widen_toNat (c : BitVec 8) : (c.setWidth 32).toNat = c.toNat := by
  have := c.isLt
  simp [BitVec.toNat_setWidth]
  omega

/-- The memory `m` after the device events `es`, nothing else changed. -/
def after (m : Mem) (es : List DevEvent) : Mem :=
  { m with dev := { m.dev with trace := m.dev.trace ++ es } }

theorem after_nil (m : Mem) : after m [] = m := by simp [after]

theorem after_append (m : Mem) (es fs : List DevEvent) :
    after (after m es) fs = after m (es ++ fs) := by simp [after]

theorem withEvent_after (m : Mem) (e : DevEvent) : m.withEvent e = after m [e] := rfl

theorem status_addr : devAddr? uart = some STATUS := by decide
theorem data_addr : devAddr? (uart.add 4) = some DATA := by decide

/-- `&uart.data`: an offset inside the declared register window (`ptrProjectDevice`, DEV-01). -/
theorem data_ptr (m : Mem) :
    (ptrProjectDevice air2lean_device uart (·.add 4)).run m = pure (uart.add 4, m) :=
  ptrProjectDevice_run (a := STATUS) (b := DATA) (by decide) (by decide) (by decide) (by decide)

theorem status_read {m : Mem} {v : BitVec 32}
    (ho : m.dev.oracle m.dev.trace STATUS 32 = some v) :
    (vload air2lean_device 32 4 uart).run m = pure (v, after m [rd v]) :=
  vload_run status_addr (by decide) (by decide) ho

theorem data_write (m : Mem) (v : BitVec 32) :
    (vstore air2lean_device 32 4 (uart.add 4) v).run m =
      pure ((), after m [.write DATA 32 v.toNat]) :=
  vstore_run data_addr (by decide) (by decide)

/-! ## The polling contract

`Answers o h vs r`: from the trace `h` on, the device answers the status reads with the busy
values `vs` (bit 0 clear), then with the ready value `r` (bit 0 set). Every oracle under which
`putc` returns has exactly one such `vs` and `r`, so this covers every terminating device. -/
def Answers (o : DevOracle) : List DevEvent → List (BitVec 32) → BitVec 32 → Prop
  | h, [], r => o h STATUS 32 = some r ∧ r &&& 1#32 ≠ 0#32
  | h, v :: vs, r => o h STATUS 32 = some v ∧ v &&& 1#32 = 0#32 ∧ Answers o (h ++ [rd v]) vs r

/-- The specified trace of one `putc c`: every poll, in order, then the data write. -/
def putcSpec (vs : List (BitVec 32)) (r : BitVec 32) (c : BitVec 8) : List DevEvent :=
  (vs ++ [r]).map rd ++ [wr c]

theorem loop_busy (s : putcLocals) {m : Mem} {v : BitVec 32}
    (ho : m.dev.oracle m.dev.trace STATUS 32 = some v) (hv : v &&& 1#32 = 0#32) :
    ((putc.loop3 uart).run s).run m = pure ((.rep3, s), after m [rd v]) := by
  have h := status_read ho
  simp only [StateT.run] at h
  simp [putc.loop3, zig_unfold, h, hv]

theorem loop_ready (s : putcLocals) {m : Mem} {v : BitVec 32}
    (ho : m.dev.oracle m.dev.trace STATUS 32 = some v) (hv : v &&& 1#32 ≠ 0#32) :
    ((putc.loop3 uart).run s).run m = pure ((.br2, s), after m [rd v]) := by
  have h := status_read ho
  simp only [StateT.run] at h
  simp [putc.loop3, zig_unfold, h, hv]

/-- The polling loop reads the status register once per iteration, in order, and exits on the
first ready value. -/
theorem poll_run (s : putcLocals) (vs : List (BitVec 32)) (r : BitVec 32) :
    ∀ m : Mem, Answers m.dev.oracle m.dev.trace vs r →
      ((loop (putc.loop3 uart) putc.again3).run s).run m =
        pure ((.br2, s), after m ((vs ++ [r]).map rd)) := by
  induction vs with
  | nil =>
    intro m ⟨ho, hr⟩
    rw [loop_run_mm, loop_ready s ho hr]
    simp [putc.again3, zig_unfold]
  | cons v vs ih =>
    intro m ⟨ho, hv, hrest⟩
    rw [loop_run_mm, loop_busy s ho hv]
    have := ih (after m [rd v]) hrest
    simp only [StateT.run] at this
    simp [putc.again3, zig_unfold, this, after_append]

/-- **`putc` meets its trace spec for every device oracle satisfying the polling contract**:
the emitted trace is exactly the polls in order, then one data write of `c`; ordinary memory is
unchanged. -/
theorem putc_trace (m : Mem) (c : BitVec 8) (vs : List (BitVec 32)) (r : BitVec 32)
    (hc : Answers m.dev.oracle m.dev.trace vs r) :
    (putc uart c).run m = pure ((), after m (putcSpec vs r c)) := by
  have hp := poll_run default vs r m hc
  have hw := data_write (after m ((vs ++ [r]).map rd)) (c.setWidth 32)
  have hd := data_ptr (after m ((vs ++ [r]).map rd))
  have hi : Zig.intCast false false 32 c = pure (c.setWidth 32) := intCast_unsigned_widen c 32 (by decide)
  simp only [StateT.run, List.map_append, List.map_cons, List.map_nil, widen_toNat] at hp hw hd
  simp [putc, zig_unfold, hp, hw, hd, hi, after_append, putcSpec, wr]

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
polls followed by exactly one data write of `c`, and nothing else changed. -/
theorem putc_eventually (m : Mem) (c : BitVec 8) (k : Nat)
    (hr : EventuallyReady m.dev.oracle m.dev.trace k) :
    ∃ vs r, (putc uart c).run m = pure ((), after m (putcSpec vs r c)) := by
  obtain ⟨vs, r, ha⟩ := answers_of_ready _ k _ hr
  exact ⟨vs, r, putc_trace m c vs r ha⟩

/-! ## Two reads are two events, never one merged read -/

/-- `statusTwice` reads the status register twice: two `read` events, in order, and the second
answer is the oracle's answer *after* the first read. -/
theorem statusTwice_trace (m : Mem) (a b : BitVec 32)
    (ha : m.dev.oracle m.dev.trace STATUS 32 = some a)
    (hb : m.dev.oracle (m.dev.trace ++ [rd a]) STATUS 32 = some b) :
    (statusTwice uart).run m = pure (a ^^^ b, after m [rd a, rd b]) := by
  have h1 := status_read ha
  have h2 := status_read (m := after m [rd a]) (v := b) (by simpa [after] using hb)
  simp only [StateT.run] at h1 h2
  simp [statusTwice, zig_unfold, h1, h2, after_append]

/-- A device that counts the reads so far: the `k`-th read answers `k`. -/
def counter : DevOracle := fun h _ n => some (BitVec.ofNat n h.length)

/-- Under the counting device, `statusTwice` returns `0 ^^^ 1 = 1`. A translation that merged
the two volatile reads into one would return `a ^^^ a = 0` under every device. -/
theorem statusTwice_not_merged :
    (statusTwice uart).run { dev := { oracle := counter } } =
      pure (1, after { dev := { oracle := counter } } [rd 0, rd 1]) :=
  statusTwice_trace _ 0 1 rfl rfl

theorem statusTwice_ne_merged : ∀ a : BitVec 32, (0 : BitVec 32) ^^^ 1 ≠ a ^^^ a := by
  intro a; simp

/-- An unused read is still one event (a read-to-clear register is cleared). -/
theorem clearStatus_trace (m : Mem) (v : BitVec 32)
    (ho : m.dev.oracle m.dev.trace STATUS 32 = some v) :
    (clearStatus uart).run m = pure ((), after m [rd v]) := by
  have h := status_read ho
  simp only [StateT.run] at h
  simp [clearStatus, zig_unfold, h]

/-- Program order: the write happens before the read, and the device answers the read after
seeing the write. -/
theorem sendThenStatus_trace (m : Mem) (c : BitVec 8) (v : BitVec 32)
    (ho : m.dev.oracle (m.dev.trace ++ [wr c]) STATUS 32 = some v) :
    (sendThenStatus uart c).run m = pure (v, after m [wr c, rd v]) := by
  have hi : Zig.intCast false false 32 c = pure (c.setWidth 32) := intCast_unsigned_widen c 32 (by decide)
  have hw := data_write m (c.setWidth 32)
  have hd := data_ptr m
  have hr := status_read (m := after m [wr c]) (v := v) (by simpa [after] using ho)
  simp only [StateT.run, widen_toNat] at hw hr hd
  simp only [wr] at hr
  simp [sendThenStatus, zig_unfold, hi, hw, hd, hr, after_append, wr]

end DeviceEffectsProofs
