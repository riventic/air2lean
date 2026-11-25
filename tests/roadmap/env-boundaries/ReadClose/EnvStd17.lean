import ZigLean.Env.Linux
import EnvStdIo
import EnvStd17.Gen

/-!
# E03: `posix.read` and `Io.Threaded.closeFd`, translated from AIR

`EnvStd17.Gen` is `std_io16.zig`'s `readClose` with std's `posix.read` and
`Io.Threaded.closeFd`, translated by `translate.sh` with only `os.linux.{read,close}` bound
(`registry/std<NN>.json`, ZigLean/Env/Linux.lean). No std function is modelled by hand. The file
of the Zig 0.17.1 translation is written; the file of the 0.16.0 translation is the same text
with that version's names (`scripts/fixtures.py instance`, `check.sh`): the statements and
proofs are the same for both versions.
-/

namespace EnvStd17.Proofs
open Zig Zig.Env Zig.Env.Linux EnvStdIo

theorem errno_err (e : IoError) :
    os_linux_errno__anon_e364564323c2 (errReturn e) = pure ⟨BitVec.ofNat 16 (errno e)⟩ := by
  cases e <;> rfl

theorem errno_ok (n : Nat) (h1 : n ≤ 2147479552) :
    os_linux_errno__anon_e364564323c2 (BitVec.ofNat 64 n) = pure os_linux_E__enum_1.SUCCESS := by
  have hti : (BitVec.ofNat 64 n).toInt = n := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  have hgt : Zig.gt true (BitVec.ofNat 64 n) 18446744073709547520#64 = true := by
    have hm : (18446744073709547520#64).toInt = -4096 := by decide
    simp only [Zig.gt, Zig.lt, ite_true, BitVec.slt, hm, hti, decide_eq_true_eq]
    omega
  have hlt : Zig.lt true (BitVec.ofNat 64 n) 0#64 = false := by
    simp [Zig.lt, BitVec.slt, hti]
  simp [os_linux_errno__anon_e364564323c2, zig_unfold, hgt, hlt, Zig.enumOf, os_linux_E__enum_1.ofInt?,
    Zig.val]
  rfl

theorem closeErrno : os_linux_errno__anon_e364564323c2 0#64 = pure os_linux_E__enum_1.SUCCESS := rfl

/-- The error name of each modelled error in `posix.read`'s switch (errors it does not list are
`error.Unexpected`). -/
def readErrName : IoError → ErrName
  | .wouldBlock => "WouldBlock"
  | .brokenPipe => "Unexpected"
  | .noSpaceLeft => "Unexpected"
  | .accessDenied => "Unexpected"
  | .inputOutput => "InputOutput"
  | .connectionReset => "ConnectionResetByPeer"

/-- What `posix.read` returns for an `Ops.read` result. -/
def readResult : Except IoError (List UInt8) → Except ErrName (BitVec 64)
  | .ok bytes => .ok (BitVec.ofNat 64 bytes.length)
  | .error e => .error (readErrName e)

/-- One iteration of `posix.read`'s retry loop: one `read` of at most `2147479552` bytes. -/
theorem read_loop_body {m : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {errs : List IoError}
    (hc : Contract m.host.ops errs) (ho : OpenAt fd m h)
    (hw : WritableAt m s.ptr (min 2147479552 s.len.toNat)) (hl0 : s.len.toNat ≠ 0)
    (hst : m.SingleThread) (st : posix_readLocals) (hloc : st.local2 = s) :
    ∃ m' : Mem, ((posix_read.loop13 fd).run st).run m =
        pure ((.ret (readResult (m.host.afterRead h (min 2147479552 s.len.toNat)).1), st), m') ∧
      m'.host = (m.host.afterRead h (min 2147479552 s.len.toNat)).2 ∧ m'.SingleThread ∧
      (∀ bytes, (m.host.afterRead h (min 2147479552 s.len.toNat)).1 = .ok bytes →
        BytesAt m' s.ptr bytes) := by
  obtain ⟨k, hkdef⟩ : ∃ k, k = min 2147479552 s.len.toNat := ⟨_, rfl⟩
  rw [← hkdef] at hw ⊢
  have hk31 : k < 2 ^ 31 := by omega
  -- The body's step tick changes only `ticks`: the read runs on the ticked memory.
  obtain ⟨m', hrd, hh', hs', hbytes⟩ :=
    read_run (m := { m with ticks := m.ticks + 1 }) hc ho hw (by omega) (by omega) hst
  refine ⟨m', ?_, hh', hs', hbytes⟩
  have hmin : Zig.min false 2147479552#64 s.len = BitVec.ofNat 64 k := by rw [min_cap, hkdef]
  have hc31 := @intCast31 k hk31
  have hsw := setWidth31 k hk31
  have hc64 := @intCast64of31 k hk31
  have hrm : air2lean_model_1 fd s.ptr (BitVec.ofNat 64 k) { m with ticks := m.ticks + 1 } =
      pure (readRet (m.host.afterRead h k).1, m') := hrd
  unfold Host.afterRead at hrm ⊢
  cases hr : m.host.ops.read m.host.env h k with
  | mk r s' =>
    cases r with
    | ok bytes =>
      have hb := hc.readBound m.host.env h k bytes s' ho.2 (by rw [hr])
      have he := errno_ok bytes.length (by omega)
      simp only [hr, readRet] at hrm
      simp [posix_read.loop13, zig_unfold, tick_apply, Zig.callM, Zig.callR, hloc, hmin, hc31, hsw, hc64, hrm,
        he, intCast64, readResult]
    | error e =>
      simp only [hr, readRet] at hrm
      have he := errno_err e
      cases e <;>
        simp [posix_read.loop13, zig_unfold, tick_apply, Zig.callM, Zig.callR, hloc, hmin, hc31, hsw, hc64, hrm,
          he, readResult, readErrName, errno, posix_unexpectedErrno, os_linux_E__enum_1.SUCCESS,
          os_linux_E__enum_1.INTR, os_linux_E__enum_1.INVAL, os_linux_E__enum_1.FAULT,
          os_linux_E__enum_1.AGAIN, os_linux_E__enum_1.CANCELED, os_linux_E__enum_1.BADF,
          os_linux_E__enum_1.IO, os_linux_E__enum_1.ISDIR, os_linux_E__enum_1.NOBUFS,
          os_linux_E__enum_1.NOMEM, os_linux_E__enum_1.NOTCONN, os_linux_E__enum_1.CONNRESET,
          os_linux_E__enum_1.TIMEDOUT]

/-- `posix.read`: one `read` (no `EINTR` in the model, so no retry). -/
theorem posix_read_run {m : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {errs : List IoError}
    (hc : Contract m.host.ops errs) (ho : OpenAt fd m h)
    (hw : WritableAt m s.ptr (min 2147479552 s.len.toNat)) (hl0 : s.len.toNat ≠ 0)
    (hst : m.SingleThread) :
    ∃ m' : Mem, (posix_read fd s).run m =
        pure (readResult (m.host.afterRead h (min 2147479552 s.len.toNat)).1, m') ∧
      m'.host = (m.host.afterRead h (min 2147479552 s.len.toNat)).2 ∧ m'.SingleThread ∧
      (∀ bytes, (m.host.afterRead h (min 2147479552 s.len.toNat)).1 = .ok bytes →
        BytesAt m' s.ptr bytes) := by
  obtain ⟨m', hbody, hh', hs', hbytes⟩ := read_loop_body hc ho hw hl0 hst { local2 := s } rfl
  refine ⟨m', ?_, hh', hs', hbytes⟩
  have hloop : ((Zig.loop (posix_read.loop13 fd) posix_read.again13).run { local2 := s }).run m =
      pure ((.ret (readResult (m.host.afterRead h (min 2147479552 s.len.toNat)).1),
        { local2 := s }), m') := by
    rw [loop_run_mm, hbody]
    simp [posix_read.again13, zig_unfold]
  have hlen0 : s.len ≠ 0#64 := by
    intro e; apply hl0; rw [e]; rfl
  simp only [StateT.run] at hloop
  simp [posix_read, zig_unfold, hlen0, hloop]

/-- `Io.Threaded.closeFd` of an open descriptor releases it: one `close`, no other effect. -/
theorem closeFd_run {m : Mem} {fd : BitVec 32} {h : Handle} (ho : OpenAt fd m h) :
    (Io_Threaded_closeFd fd).run m = pure ((), { m with host := m.host.afterClose h }) := by
  have hcl : air2lean_model_0 fd m = pure (0, { m with host := m.host.afterClose h }) := close_ok ho
  simp [Io_Threaded_closeFd, zig_unfold, Zig.callM, Zig.callR, hcl, closeErrno,
    os_linux_E__enum_1.SUCCESS, os_linux_E__enum_1.BADF, os_linux_E__enum_1.INTR]

/-- **`readClose` (std `posix.read` + `Io.Threaded.closeFd`, translated from AIR).**
On an open descriptor and a nonempty writable buffer, under the ENV-01 contract: the generated
code never faults; it returns the number of received bytes, which are then in the buffer, or the
read error's Zig name; on both paths the handle is closed exactly once, last, and is then no
longer open, while other handles are unchanged. -/
theorem readClose_spec {m0 : Mem} {fd : BitVec 32} {h : Handle} {s : Slice}
    {errs : List IoError} (hc : Contract m0.host.ops errs) (ho : OpenAt fd m0 h)
    (hw : WritableAt m0 s.ptr (min 2147479552 s.len.toNat)) (hl0 : s.len.toNat ≠ 0)
    (hst : m0.SingleThread) :
    ∃ r m', (readClose fd s).run m0 = pure (r, m') ∧
      m'.host.ops.isOpen m'.host.env h = false ∧
      (∀ h', h' ≠ h → m'.host.ops.isOpen m'.host.env h' = m0.host.ops.isOpen m0.host.env h') ∧
      ((∃ bytes, r = .ok (BitVec.ofNat 64 bytes.length) ∧ bytes.length ≤ s.len.toNat ∧
          BytesAt m' s.ptr bytes ∧
          m'.host.log = m0.host.log ++ [.received h bytes, .closed h]) ∨
       (∃ e, r = .error (readErrName e) ∧ e ∈ errs ∧
          m'.host.log = m0.host.log ++ [.failed h e, .closed h])) := by
  obtain ⟨m1, hrd, hh1, _, hbytes⟩ := posix_read_run hc ho hw hl0 hst
  simp only [StateT.run] at hrd
  have hopen := ho.2
  have hframe := hc.readFrame m0.host.env h (min 2147479552 s.len.toNat)
  unfold Host.afterRead at hrd hh1 hbytes
  cases hr : m0.host.ops.read m0.host.env h (min 2147479552 s.len.toNat) with
  | mk r s' =>
    rw [hr] at hframe
    have hfr : ∀ h', m0.host.ops.isOpen s' h' = m0.host.ops.isOpen m0.host.env h' :=
      fun h' => hframe h' hopen
    cases r with
    | ok bytes =>
      simp only [hr] at hrd hh1 hbytes
      have hops : m1.host.ops = m0.host.ops := by rw [hh1]
      have henv : m1.host.env = s' := by rw [hh1]
      have hlog1 : m1.host.log = m0.host.log ++ [.received h bytes] := by rw [hh1]
      have ho1 : OpenAt fd m1 h := ⟨ho.1, by rw [hops, henv, hfr]; exact hopen⟩
      have hc1 : Contract m1.host.ops errs := hops ▸ hc
      have hcl := closeFd_run ho1
      simp only [StateT.run] at hcl
      have hb := hc.readBound m0.host.env h _ bytes s' hopen (by rw [hr])
      refine ⟨.ok (BitVec.ofNat 64 bytes.length), { m1 with host := m1.host.afterClose h }, ?_, hc1.closeReleases _ h ho1.2,
        fun h' hne => ?_, .inl ⟨bytes, rfl, by omega, (hbytes bytes rfl).blocks rfl, ?_⟩⟩
      · simp [readClose, zig_unfold, Zig.callM, hrd, hcl, readResult]
      · show m1.host.ops.isOpen (m1.host.ops.close m1.host.env h) h' = _
        rw [hc1.closeFrame _ h h' hne, hops, henv, hfr]
      · show m1.host.log ++ [.closed h] = _
        rw [hlog1]; simp
    | error e =>
      simp only [hr] at hrd hh1
      have hops : m1.host.ops = m0.host.ops := by rw [hh1]
      have henv : m1.host.env = s' := by rw [hh1]
      have hlog1 : m1.host.log = m0.host.log ++ [.failed h e] := by rw [hh1]
      have ho1 : OpenAt fd m1 h := ⟨ho.1, by rw [hops, henv, hfr]; exact hopen⟩
      have hc1 : Contract m1.host.ops errs := hops ▸ hc
      have hcl := closeFd_run ho1
      simp only [StateT.run] at hcl
      have he := hc.readError m0.host.env h _ e s' hopen (by rw [hr])
      refine ⟨.error (readErrName e), { m1 with host := m1.host.afterClose h }, ?_, hc1.closeReleases _ h ho1.2, fun h' hne => ?_,
        .inr ⟨e, rfl, he, ?_⟩⟩
      · simp [readClose, zig_unfold, Zig.callM, hrd, hcl, readResult]
      · show m1.host.ops.isOpen (m1.host.ops.close m1.host.env h) h' = _
        rw [hc1.closeFrame _ h h' hne, hops, henv, hfr]
      · show m1.host.log ++ [.closed h] = _
        rw [hlog1]; simp

end EnvStd17.Proofs
