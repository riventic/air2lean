import ZigLean.Env.Linux
import EnvStd15.Gen
import EnvStd16.Gen

/-!
# E03: proofs about translated std I/O over the ENV-03 primitives

`EnvStd15.Gen` is Zig 0.15.2's `fs.File.writeAll`/`write`/`close`/`readAll`/`read` and
`posix.write`/`read`/`close`/`errno`, translated from AIR by `translate.sh` with only
`os.linux.{read,write,close}` bound (`registry/std15.json`, ZigLean/Env/Linux.lean).
`EnvStd16.Gen` is Zig 0.16.0's `posix.read` and `Io.Threaded.closeFd`. No std function is
modelled by hand: every theorem below is about generated code, under the ENV-01 contract of the
installed operations and the ENV-03 binding of the three primitives.
-/

namespace EnvStdIo
open Zig Zig.Env

theorem intCast31 (k : Nat) (hk : k < 2 ^ 31) :
    Zig.intCast false false 31 (BitVec.ofNat 64 k) = pure (BitVec.ofNat 31 k) := by
  have h64 : (BitVec.ofNat 64 k).toNat = k := by simp; omega
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ite_false, h64]
  rw [if_pos (by omega)]
  congr 1
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp [BitVec.toNat_ofInt]
  all_goals omega

theorem setWidth31 (k : Nat) (hk : k < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.ofNat 31 k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp <;> omega

theorem intCast64of31 (k : Nat) (hk : k < 2 ^ 31) :
    Zig.intCast false false 64 (BitVec.ofNat 31 k) = pure (BitVec.ofNat 64 k) := by
  have h31 : (BitVec.ofNat 31 k).toNat = k := by simp; omega
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ite_false, h31]
  rw [if_pos (by omega)]
  congr 1
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp [BitVec.toNat_ofInt]
  all_goals omega

theorem intCast64 (a : BitVec 64) : Zig.intCast false false 64 a = pure a := by
  simp only [Zig.intCast, Zig.val, Bool.false_eq_true, ite_false]
  rw [if_pos (by have := a.isLt; omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]

theorem min_cap (len : BitVec 64) :
    Zig.min false 2147479552#64 len = BitVec.ofNat 64 (min 2147479552 len.toNat) := by
  unfold Zig.min
  simp only [Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_toNat_eq
  by_cases h : 2147479552 ≤ len.toNat
  · rw [if_pos (by simp [BitVec.ule]; omega)]; simp; omega
  · rw [if_neg (by simp [BitVec.ule]; omega)]; simp; omega

theorem add_ofNat (i n : Nat) (h : i + n < 2 ^ 64) :
    Zig.add false (BitVec.ofNat 64 i) (BitVec.ofNat 64 n) = pure (BitVec.ofNat 64 (i + n)) := by
  have : ¬ (BitVec.ofNat 64 i).uaddOverflow (BitVec.ofNat 64 n) := by
    simp [BitVec.uaddOverflow]; omega
  simp only [Zig.add, Bool.false_eq_true, ite_false, this]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- Every event is a write to `h`. -/
def OnlyWrites (h : Handle) (evs : List Event) : Prop := ∀ ev ∈ evs, ∃ c, ev = .wrote h c

theorem OnlyWrites.append {h : Handle} {a b : List Event} (ha : OnlyWrites h a)
    (hb : OnlyWrites h b) : OnlyWrites h (a ++ b) := by
  intro ev hev
  rcases List.mem_append.mp hev with hev | hev
  · exact ha ev hev
  · exact hb ev hev

theorem written_append (a b : List Event) : written (a ++ b) = written a ++ written b := by
  induction a with
  | nil => rfl
  | cons ev rest ih => cases ev <;> simp [written, ih]

theorem OnlyWrites.not_closed {h : Handle} {evs : List Event} (hw : OnlyWrites h evs) :
    Event.closed h ∉ evs := by
  intro hm
  obtain ⟨_, hc⟩ := hw _ hm
  cases hc

end EnvStdIo

namespace EnvStd15.Proofs
open Zig Zig.Env Zig.Env.Linux EnvStdIo

theorem errno_err (e : IoError) :
    posix_errno__anon_c57b4435c781 (errReturn e) = pure ⟨BitVec.ofNat 16 (errno e)⟩ := by
  cases e <;> rfl

theorem errno_ok (n : Nat) (h1 : n ≤ 2147479552) :
    posix_errno__anon_c57b4435c781 (BitVec.ofNat 64 n) = pure os_linux_E__enum_1.SUCCESS := by
  have hti : (BitVec.ofNat 64 n).toInt = n := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  have hgt : Zig.gt true (BitVec.ofNat 64 n) 18446744073709547520#64 = true := by
    have hm : (18446744073709547520#64).toInt = -4096 := by decide
    simp only [Zig.gt, Zig.lt, ite_true, BitVec.slt, hm, hti, decide_eq_true_eq]
    omega
  have hlt : Zig.lt true (BitVec.ofNat 64 n) 0#64 = false := by
    simp [Zig.lt, BitVec.slt, hti]
  simp [posix_errno__anon_c57b4435c781, zig_unfold, hgt, hlt, Zig.enumOf, os_linux_E__enum_1.ofInt?, Zig.val]
  rfl

/-- The error name of each modelled error in `posix.write`'s switch. -/
def writeErrName : IoError → ErrName
  | .wouldBlock => "WouldBlock"
  | .brokenPipe => "BrokenPipe"
  | .noSpaceLeft => "NoSpaceLeft"
  | .accessDenied => "AccessDenied"
  | .inputOutput => "InputOutput"
  | .connectionReset => "ConnectionResetByPeer"

theorem closeErrno : posix_errno__anon_c57b4435c781 0#64 = pure os_linux_E__enum_1.SUCCESS := rfl

/-- What `posix.write` returns for an `Ops.write` result. -/
def writeResult : Except IoError Nat → Except ErrName (BitVec 64)
  | .ok n => .ok (BitVec.ofNat 64 n)
  | .error e => .error (writeErrName e)

/-- One iteration of `posix.write`'s retry loop: one `write` of at most `2147479552` bytes. -/
theorem write_loop_body {m : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {buf : List UInt8}
    {errs : List IoError} (hc : Contract m.host.ops errs)
    (ho : OpenAt fd m h) (hb : BytesAt m s.ptr buf) (hl : s.len.toNat = buf.length)
    (hne : buf ≠ []) (hst : m.SingleThread) (st : posix_writeLocals) :
    ∃ m1 : Mem, m1.blocks = m.blocks ∧ m1.host = m.host ∧ m1.SingleThread ∧
      ((posix_write.loop9 fd s).run st).run m = pure ((.ret (writeResult
        (m.host.ops.write m.host.env h (buf.take 2147479552)).1), st),
        { m1 with host := (m.host.afterWrite h (buf.take 2147479552)).2 }) := by
  have hlen64 : buf.length < 2 ^ 64 := hl ▸ s.len.isLt
  obtain ⟨k, hkdef⟩ : ∃ k, k = min 2147479552 buf.length := ⟨_, rfl⟩
  have hk : (buf.take 2147479552).length = k := by simp [hkdef, Nat.min_comm]
  have hk31 : k < 2 ^ 31 := by omega
  have hne' : buf.take 2147479552 ≠ [] := by
    intro e; have := congrArg List.length e; rw [hk] at this; simp at this
    cases buf with
    | nil => exact hne rfl
    | cons _ _ => simp at hkdef; omega
  obtain ⟨m1, hw, hb1, hh1, hs1⟩ := write_run ho (hb.take 2147479552) hne' (by omega) hst
  refine ⟨m1, hb1, hh1, hs1, ?_⟩
  have hmin : Zig.min false 2147479552#64 s.len = BitVec.ofNat 64 k := by rw [min_cap, hl, hkdef]
  have hc31 := intCast31 k hk31
  have hsw := setWidth31 k hk31
  have hc64 := intCast64of31 k hk31
  rw [hk] at hw
  have hwm : air2lean_model_2 fd s.ptr (BitVec.ofNat 64 k) m = _ := hw
  have hopen := ho.2
  unfold Host.afterWrite at hwm ⊢
  cases hwr : m.host.ops.write m.host.env h (buf.take 2147479552) with
  | mk r s' =>
    cases r with
    | ok n =>
      have hn := hc.writeProgress m.host.env h (buf.take 2147479552) n s' hopen hne' (by rw [hwr])
      rw [hk] at hn
      have he := errno_ok n (by omega)
      simp only [hwr] at hwm
      simp [posix_write.loop9, zig_unfold, Zig.callM, Zig.callR, hmin, hc31, hsw, hc64, hwm, he,
        intCast64, writeResult]
    | error e =>
      simp only [hwr] at hwm
      have he := errno_err e
      cases e <;>
        simp [posix_write.loop9, zig_unfold, Zig.callM, Zig.callR, hmin, hc31, hsw, hc64, hwm, he,
          writeResult, writeErrName, errno, os_linux_E__enum_1.SUCCESS, os_linux_E__enum_1.INTR,
          os_linux_E__enum_1.INVAL, os_linux_E__enum_1.FAULT, os_linux_E__enum_1.SRCH,
          os_linux_E__enum_1.AGAIN, os_linux_E__enum_1.BADF, os_linux_E__enum_1.DESTADDRREQ,
          os_linux_E__enum_1.DQUOT, os_linux_E__enum_1.FBIG, os_linux_E__enum_1.IO,
          os_linux_E__enum_1.NOSPC, os_linux_E__enum_1.ACCES, os_linux_E__enum_1.PERM,
          os_linux_E__enum_1.PIPE, os_linux_E__enum_1.CONNRESET]

/-- `posix.write`: one `write` (no `EINTR` in the model, so no retry). -/
theorem posix_write_run {m : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {buf : List UInt8}
    {errs : List IoError} (hc : Contract m.host.ops errs)
    (ho : OpenAt fd m h) (hb : BytesAt m s.ptr buf) (hl : s.len.toNat = buf.length)
    (hne : buf ≠ []) (hst : m.SingleThread) :
    ∃ m1 : Mem, m1.blocks = m.blocks ∧ m1.host = m.host ∧ m1.SingleThread ∧
      (posix_write fd s).run m = pure (writeResult
        (m.host.ops.write m.host.env h (buf.take 2147479552)).1,
        { m1 with host := (m.host.afterWrite h (buf.take 2147479552)).2 }) := by
  obtain ⟨m1, hb1, hh1, hs1, hbody⟩ := write_loop_body hc ho hb hl hne hst default
  refine ⟨m1, hb1, hh1, hs1, ?_⟩
  have hloop : ((Zig.loop (posix_write.loop9 fd s) posix_write.again9).run default).run m =
      pure ((.ret (writeResult (m.host.ops.write m.host.env h (buf.take 2147479552)).1), default),
        { m1 with host := (m.host.afterWrite h (buf.take 2147479552)).2 }) := by
    rw [loop_run_mm, hbody]
    simp [posix_write.again9, zig_unfold]
  have hlen0 : s.len ≠ 0#64 := by
    intro e
    have : buf.length = 0 := by rw [← hl, e]; rfl
    exact hne (List.eq_nil_of_length_eq_zero this)
  simp only [StateT.run] at hloop
  simp [posix_write, zig_unfold, hlen0, hloop]

theorem fs_File_write_run {m : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {buf : List UInt8}
    {errs : List IoError} (hc : Contract m.host.ops errs)
    (ho : OpenAt fd m h) (hb : BytesAt m s.ptr buf) (hl : s.len.toNat = buf.length)
    (hne : buf ≠ []) (hst : m.SingleThread) :
    ∃ m1 : Mem, m1.blocks = m.blocks ∧ m1.host = m.host ∧ m1.SingleThread ∧
      (fs_File_write ⟨fd⟩ s).run m = pure (writeResult
        (m.host.ops.write m.host.env h (buf.take 2147479552)).1,
        { m1 with host := (m.host.afterWrite h (buf.take 2147479552)).2 }) := by
  obtain ⟨m1, hb1, hh1, hs1, hw⟩ := posix_write_run hc ho hb hl hne hst
  refine ⟨m1, hb1, hh1, hs1, ?_⟩
  simp only [StateT.run] at hw
  simp [fs_File_write, zig_unfold, Zig.callM, hw]

/-! ## `fs.File.writeAll`'s loop -/

theorem writeAll_body_done {fd : BitVec 32} {s : Slice} {st : fs_File_writeAllLocals} {m : Mem}
    (hidx : st.index = s.len) :
    ((fs_File_writeAll.loop5 ⟨fd⟩ s).run st).run m = pure ((.br4, st), m) := by
  have hlt : Zig.lt false st.index s.len = false := by
    simp only [Zig.lt, hidx, Bool.false_eq_true, ite_false, BitVec.ult]; simp
  simp only [StateT.run, fs_File_writeAll.loop5, zig_unfold, hlt, Bool.false_eq_true, ↓reduceIte]

/-- The facts the loop body checks before its call, at index `i < len`. -/
structure BodyFacts (s : Slice) (i : Nat) : Prop where
  lt : Zig.lt false (BitVec.ofNat 64 i) s.len = true
  le1 : Zig.le false (BitVec.ofNat 64 i) s.len = true
  le2 : Zig.le false s.len s.len = true
  sub : Zig.sub false s.len (BitVec.ofNat 64 i) = pure (BitVec.ofNat 64 (s.len.toNat - i))
  /-- The slicing `s[i..]` stays within `s` (the unchecked-illegal slice-end check). -/
  sliceEnd : Zig.checkSliceEnd s.len (BitVec.ofNat 64 i) (BitVec.ofNat 64 (s.len.toNat - i)) 0 = pure ()

theorem bodyFacts {s : Slice} {i : Nat} (hi : i < s.len.toNat) : BodyFacts s i := by
  have hlen := s.len.isLt
  have hi64 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Zig.lt, BitVec.ult, hi64]; omega
  · simp [Zig.le, BitVec.ule, hi64]; omega
  · simp [Zig.le, BitVec.ule]
  · have : ¬ s.len.usubOverflow (BitVec.ofNat 64 i) := by
      simp [BitVec.usubOverflow, hi64]; omega
    simp only [Zig.sub, Bool.false_eq_true, ite_false, this]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, hi64]
    omega
  · have hsub : (BitVec.ofNat 64 (s.len.toNat - i)).toNat = s.len.toNat - i := by simp; omega
    simp only [Zig.checkSliceEnd, hi64, hsub]
    rw [if_pos (by omega)]

theorem writeAll_body_err {fd : BitVec 32} {s : Slice} {st : fs_File_writeAllLocals} {m m' : Mem}
    {n : ErrName} {i : Nat} (hidx : st.index = BitVec.ofNat 64 i) (hb : BodyFacts s i)
    (hpp : (ptrProject s.ptr (·.elem 1 (BitVec.ofNat 64 i))).run m = pure (s.ptr.elem 1 (BitVec.ofNat 64 i), m))
    (hfw : (fs_File_write ⟨fd⟩ ⟨s.ptr.elem 1 (BitVec.ofNat 64 i),
      BitVec.ofNat 64 (s.len.toNat - i)⟩).run m = pure (.error n, m')) :
    ((fs_File_writeAll.loop5 ⟨fd⟩ s).run st).run m = pure ((.ret (.error n), st), m') := by
  simp only [StateT.run] at hfw hpp
  simp only [StateT.run, fs_File_writeAll.loop5, zig_unfold, Zig.callM, Zig.callR, hidx, hb.lt,
    hb.le1, hb.le2, hb.sub, hb.sliceEnd, hpp, hfw, ↓reduceIte, Zig.unwrapErr]

theorem writeAll_body_ok {fd : BitVec 32} {s : Slice} {st : fs_File_writeAllLocals} {m m' : Mem}
    {v w : BitVec 64} {i : Nat} (hidx : st.index = BitVec.ofNat 64 i) (hb : BodyFacts s i)
    (hpp : (ptrProject s.ptr (·.elem 1 (BitVec.ofNat 64 i))).run m = pure (s.ptr.elem 1 (BitVec.ofNat 64 i), m))
    (hfw : (fs_File_write ⟨fd⟩ ⟨s.ptr.elem 1 (BitVec.ofNat 64 i),
      BitVec.ofNat 64 (s.len.toNat - i)⟩).run m = pure (.ok v, m'))
    (ha : Zig.add false (BitVec.ofNat 64 i) v = pure w) :
    ((fs_File_writeAll.loop5 ⟨fd⟩ s).run st).run m = pure ((.rep5, { st with index := w }), m') := by
  simp only [StateT.run] at hfw hpp
  simp only [StateT.run, fs_File_writeAll.loop5, zig_unfold, Zig.callM, Zig.callR, hidx, hb.lt,
    hb.le1, hb.le2, hb.sub, hb.sliceEnd, hpp, hfw, ha, ↓reduceIte]

/-- What a loop iteration keeps: memory blocks, single-threadedness, the operations and the
open handles. -/
def Base (m0 m : Mem) : Prop :=
  m.blocks = m0.blocks ∧ m.SingleThread ∧ m.host.ops = m0.host.ops ∧
    ∀ h', m.host.ops.isOpen m.host.env h' = m0.host.ops.isOpen m0.host.env h'

/-- The state of `fs.File.writeAll`'s loop after the first `i` bytes were accepted. -/
def LoopInv (m0 : Mem) (h : Handle) (buf : List UInt8) (st : fs_File_writeAllLocals) (m : Mem) :
    Prop :=
  ∃ i evs, st.index = BitVec.ofNat 64 i ∧ i ≤ buf.length ∧ Base m0 m ∧
    m.host.log = m0.host.log ++ evs ∧ OnlyWrites h evs ∧ written evs = buf.take i

/-- How the loop ends: every byte accepted, or the first error after a proper prefix. -/
def LoopPost (m0 : Mem) (h : Handle) (buf : List UInt8) (errs : List IoError)
    (e : fs_File_writeAllExit) (m : Mem) : Prop :=
  (e = .br4 ∧ ∃ evs, Base m0 m ∧ m.host.log = m0.host.log ++ evs ∧ OnlyWrites h evs ∧
      written evs = buf) ∨
  (∃ er i pre, e = .ret (.error (writeErrName er)) ∧ er ∈ errs ∧ i < buf.length ∧ Base m0 m ∧
      m.host.log = m0.host.log ++ (pre ++ [.failed h er]) ∧ OnlyWrites h pre ∧
      written pre = buf.take i)

theorem writeAll_step {m0 : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {buf : List UInt8}
    {errs : List IoError} (hc : Contract m0.host.ops errs) (ho : OpenAt fd m0 h)
    (hb : BytesAt m0 s.ptr buf) (hl : s.len.toNat = buf.length)
    (st : fs_File_writeAllLocals) (m : Mem) (hinv : LoopInv m0 h buf st m) :
    ∃ e st' m', ((fs_File_writeAll.loop5 ⟨fd⟩ s).run st).run m = pure ((e, st'), m') ∧
      (if fs_File_writeAll.again5 e then LoopInv m0 h buf st' m' ∧
          buf.length - st'.index.toNat < buf.length - st.index.toNat
        else LoopPost m0 h buf errs e m') := by
  obtain ⟨i, evs, hidx, hile, ⟨hbl, hst, hops, hopen⟩, hlog, honly, hwr⟩ := hinv
  have hlen64 : buf.length < 2 ^ 64 := hl ▸ s.len.isLt
  by_cases hi : i = buf.length
  · subst hi
    have hidx' : st.index = s.len := by
      rw [hidx]; apply BitVec.eq_of_toNat_eq; simp; omega
    refine ⟨.br4, st, m, writeAll_body_done hidx', ?_⟩
    simp only [fs_File_writeAll.again5, Bool.false_eq_true, ite_false]
    refine .inl ⟨rfl, evs, ⟨hbl, hst, hops, hopen⟩, hlog, honly, ?_⟩
    rw [hwr, List.take_length]
  · have hi' : i < buf.length := by omega
    have hc' : Contract m.host.ops errs := hops ▸ hc
    have ho' : OpenAt fd m h := ⟨ho.1, by rw [hopen]; exact ho.2⟩
    have hb' : BytesAt m (s.ptr.elem 1 (BitVec.ofNat 64 i)) (buf.drop i) :=
      (hb.blocks hbl).drop i hile (by omega)
    have hl' : (BitVec.ofNat 64 (s.len.toNat - i)).toNat = (buf.drop i).length := by
      simp; omega
    have hne : buf.drop i ≠ [] := by simp; omega
    obtain ⟨m1, hb1, hh1, hs1, hfw⟩ :=
      fs_File_write_run (s := ⟨s.ptr.elem 1 (BitVec.ofNat 64 i), BitVec.ofNat 64 (s.len.toNat - i)⟩)
        hc' ho' hb' hl' hne hst
    have hbody := bodyFacts (s := s) (i := i) (by omega)
    have hpp := (hb.blocks hbl).ptrProject_run i hile (by omega)
    have hopen_h := ho'.2
    have hframe : ∀ s', (m.host.ops.write m.host.env h ((buf.drop i).take 2147479552)).2 = s' →
        ∀ h', m.host.ops.isOpen s' h' = m0.host.ops.isOpen m0.host.env h' := by
      intro s' hs' h'
      rw [← hs', hc'.writeFrame _ h _ h' hopen_h, hopen]
    unfold Host.afterWrite at hfw
    cases hw : m.host.ops.write m.host.env h ((buf.drop i).take 2147479552) with
    | mk r s' =>
      have hfr := hframe s' (by rw [hw])
      cases r with
      | ok n =>
        have hne2 : (buf.drop i).take 2147479552 ≠ [] := by
          intro e; have := congrArg List.length e; simp at this; omega
        have hn := hc'.writeProgress m.host.env h ((buf.drop i).take 2147479552) n s' hopen_h hne2
          (by rw [hw])
        have hnc : n ≤ 2147479552 := by simp at hn; omega
        have hnl : i + n ≤ buf.length := by simp at hn; omega
        simp only [hw, writeResult] at hfw
        have hadd := add_ofNat i n (by omega)
        refine ⟨.rep5, { st with index := BitVec.ofNat 64 (i + n) }, _,
          writeAll_body_ok hidx hbody hpp hfw hadd, ?_⟩
        simp only [fs_File_writeAll.again5, ite_true]
        refine ⟨⟨i + n, evs ++ [.wrote h (((buf.drop i).take 2147479552).take n)], rfl, hnl,
          ⟨hb1.trans hbl, hs1, hops, hfr⟩, ?_, honly.append ?_, ?_⟩, ?_⟩
        · show m.host.log ++ _ = _
          rw [hlog, List.append_assoc]
        · intro ev hev
          simp only [List.mem_singleton] at hev
          exact ⟨_, hev⟩
        · rw [written_append, hwr, List.take_add]
          simp [written, List.take_take, Nat.min_eq_left hnc]
        · rw [hidx]
          simp
          omega
      | error e =>
        simp only [hw, writeResult] at hfw
        have he := hc'.writeError m.host.env h _ e s' hopen_h (by rw [hw])
        refine ⟨.ret (.error (writeErrName e)), st, _, writeAll_body_err hidx hbody hpp hfw, ?_⟩
        simp only [fs_File_writeAll.again5, Bool.false_eq_true, ite_false]
        refine .inr ⟨e, i, evs, rfl, he, hi', ⟨hb1.trans hbl, hs1, hops, hfr⟩, ?_, honly, hwr⟩
        show m.host.log ++ _ = _
        rw [hlog, List.append_assoc]

theorem writeAll_run {m0 : Mem} {fd : BitVec 32} {h : Handle} {s : Slice} {buf : List UInt8}
    {errs : List IoError} (hc : Contract m0.host.ops errs) (ho : OpenAt fd m0 h)
    (hb : BytesAt m0 s.ptr buf) (hl : s.len.toNat = buf.length) (hst : m0.SingleThread) :
    ∃ r m', (fs_File_writeAll ⟨fd⟩ s).run m0 = pure (r, m') ∧
      ((r = .ok () ∧ ∃ evs, Base m0 m' ∧ m'.host.log = m0.host.log ++ evs ∧ OnlyWrites h evs ∧
          written evs = buf) ∨
       (∃ er i pre, r = .error (writeErrName er) ∧ er ∈ errs ∧ i < buf.length ∧ Base m0 m' ∧
          m'.host.log = m0.host.log ++ (pre ++ [.failed h er]) ∧ OnlyWrites h pre ∧
          written pre = buf.take i)) := by
  have hinv0 : LoopInv m0 h buf { index := 0#64 } m0 :=
    ⟨0, [], rfl, Nat.zero_le _, ⟨rfl, hst, rfl, fun _ => rfl⟩, by simp,
      fun _ hev => by simp at hev, by simp [written]⟩
  obtain ⟨e, st', m', hrun, hpost⟩ := loop_spec_mm (fs_File_writeAll.loop5 ⟨fd⟩ s)
    fs_File_writeAll.again5 (LoopInv m0 h buf) (fun st _ => buf.length - st.index.toNat)
    (fun e _ m => LoopPost m0 h buf errs e m) (writeAll_step hc ho hb hl) { index := 0#64 } m0 hinv0
  simp only [StateT.run] at hrun
  rcases hpost with ⟨rfl, evs, hbase, hlog, honly, hw⟩ |
    ⟨er, i, pre, rfl, her, hi, hbase, hlog, honly, hw⟩
  · refine ⟨.ok (), m', ?_, .inl ⟨rfl, evs, hbase, hlog, honly, hw⟩⟩
    simp [fs_File_writeAll, zig_unfold, hrun]
  · refine ⟨.error (writeErrName er), m', ?_, .inr ⟨er, i, pre, rfl, her, hi, hbase, hlog, honly, hw⟩⟩
    simp [fs_File_writeAll, zig_unfold, hrun]

/-! ## `close` -/

theorem fs_File_close_run {m : Mem} {fd : BitVec 32} {h : Handle} (ho : OpenAt fd m h) :
    (fs_File_close ⟨fd⟩).run m = pure ((), { m with host := m.host.afterClose h }) := by
  have hcl : air2lean_model_0 fd m = pure (0, { m with host := m.host.afterClose h }) := close_ok ho
  simp [fs_File_close, posix_close, zig_unfold, Zig.callM, Zig.callR, hcl, closeErrno,
    os_linux_E__enum_1.SUCCESS, os_linux_E__enum_1.BADF, os_linux_E__enum_1.INTR]

/-! ## The translated client `writeAllClose` -/

/-- **`writeAllClose` (std `fs.File.writeAll` + `fs.File.close`, translated from Zig 0.15.2 AIR).**
On an open descriptor whose buffer bytes are in memory, under the ENV-01 contract of the installed
operations: the generated code never faults; it either writes the whole buffer (the `wrote` events
concatenate to it) or returns the first error, mapped to its Zig error name, after a proper
prefix; on both paths the handle is closed exactly once, last, and is then no longer open, other
handles are unchanged, and memory blocks are unchanged. -/
theorem writeAllClose_spec {m0 : Mem} {fd : BitVec 32} {h : Handle} {s : Slice}
    {buf : List UInt8} {errs : List IoError} (hc : Contract m0.host.ops errs)
    (ho : OpenAt fd m0 h) (hb : BytesAt m0 s.ptr buf) (hl : s.len.toNat = buf.length)
    (hst : m0.SingleThread) :
    ∃ r m', (writeAllClose ⟨fd⟩ s).run m0 = pure (r, m') ∧ m'.blocks = m0.blocks ∧
      m'.host.ops.isOpen m'.host.env h = false ∧
      (∀ h', h' ≠ h → m'.host.ops.isOpen m'.host.env h' = m0.host.ops.isOpen m0.host.env h') ∧
      ∃ evs, m'.host.log = m0.host.log ++ evs ++ [.closed h] ∧ Event.closed h ∉ evs ∧
        ((r = .ok () ∧ OnlyWrites h evs ∧ written evs = buf) ∨
         (∃ e pre rest, r = .error (writeErrName e) ∧ e ∈ errs ∧ evs = pre ++ [.failed h e] ∧
            OnlyWrites h pre ∧ written pre ++ rest = buf ∧ rest ≠ [])) := by
  obtain ⟨r, m1, hwa, hpost⟩ := writeAll_run hc ho hb hl hst
  simp only [StateT.run] at hwa
  have closing : ∀ evs, Base m0 m1 → m1.host.log = m0.host.log ++ evs →
      ∃ m', (fs_File_close ⟨fd⟩).run m1 = pure ((), m') ∧ m'.blocks = m0.blocks ∧
        m'.host.ops.isOpen m'.host.env h = false ∧
        (∀ h', h' ≠ h → m'.host.ops.isOpen m'.host.env h' = m0.host.ops.isOpen m0.host.env h') ∧
        m'.host.log = m0.host.log ++ evs ++ [.closed h] := by
    intro evs ⟨hbl, _, hops, hopen⟩ hlog
    have ho1 : OpenAt fd m1 h := ⟨ho.1, by rw [hopen]; exact ho.2⟩
    have hc1 : Contract m1.host.ops errs := hops ▸ hc
    refine ⟨_, fs_File_close_run ho1, hbl, hc1.closeReleases _ h ho1.2, fun h' hne => ?_, ?_⟩
    · show m1.host.ops.isOpen (m1.host.ops.close m1.host.env h) h' = _
      rw [hc1.closeFrame _ h h' hne, hopen]
    · show m1.host.log ++ [.closed h] = _
      rw [hlog]
  rcases hpost with ⟨rfl, evs, hbase, hlog, honly, hw⟩ |
    ⟨er, i, pre, rfl, her, hi, hbase, hlog, honly, hw⟩
  · obtain ⟨m', hcl, hbl', hclosed, hothers, hlog'⟩ := closing evs hbase hlog
    simp only [StateT.run] at hcl
    refine ⟨.ok (), m', ?_, hbl', hclosed, hothers, evs, hlog', honly.not_closed,
      .inl ⟨rfl, honly, hw⟩⟩
    simp [writeAllClose, zig_unfold, Zig.callM, Zig.callR, hwa, hcl]
  · obtain ⟨m', hcl, hbl', hclosed, hothers, hlog'⟩ := closing (pre ++ [.failed h er]) hbase hlog
    simp only [StateT.run] at hcl
    refine ⟨.error (writeErrName er), m', ?_, hbl', hclosed, hothers, pre ++ [.failed h er], hlog',
      ?_, .inr ⟨er, pre, buf.drop i, rfl, her, rfl, honly, ?_, ?_⟩⟩
    · simp [writeAllClose, zig_unfold, Zig.callM, Zig.callR, hwa, hcl, Zig.unwrapErr]
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact honly.not_closed hm
      · simp at hm
    · rw [hw, List.take_append_drop]
    · simp; omega

end EnvStd15.Proofs

/-! ## Zig 0.16.0: `posix.read` and `Io.Threaded.closeFd` -/

namespace EnvStd16.Proofs
open Zig Zig.Env Zig.Env.Linux EnvStdIo

theorem errno_err (e : IoError) :
    os_linux_errno (errReturn e) = pure ⟨BitVec.ofNat 16 (errno e)⟩ := by
  cases e <;> rfl

theorem errno_ok (n : Nat) (h1 : n ≤ 2147479552) :
    os_linux_errno (BitVec.ofNat 64 n) = pure os_linux_E__enum_1.SUCCESS := by
  have hti : (BitVec.ofNat 64 n).toInt = n := by
    rw [BitVec.toInt_eq_toNat_of_lt] <;> simp <;> omega
  have hgt : Zig.gt true (BitVec.ofNat 64 n) 18446744073709547520#64 = true := by
    have hm : (18446744073709547520#64).toInt = -4096 := by decide
    simp only [Zig.gt, Zig.lt, ite_true, BitVec.slt, hm, hti, decide_eq_true_eq]
    omega
  have hlt : Zig.lt true (BitVec.ofNat 64 n) 0#64 = false := by
    simp [Zig.lt, BitVec.slt, hti]
  simp [os_linux_errno, zig_unfold, hgt, hlt, Zig.enumOf, os_linux_E__enum_1.ofInt?, Zig.val]
  rfl

theorem closeErrno : os_linux_errno 0#64 = pure os_linux_E__enum_1.SUCCESS := rfl

/-- The error name of each modelled error in 0.16.0 `posix.read`'s switch (errors it does not
list are `error.Unexpected`). -/
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
  obtain ⟨m', hrd, hh', hs', hbytes⟩ := read_run hc ho hw (by omega) (by omega) hst
  refine ⟨m', ?_, hh', hs', hbytes⟩
  have hmin : Zig.min false 2147479552#64 s.len = BitVec.ofNat 64 k := by rw [min_cap, hkdef]
  have hc31 := intCast31 k hk31
  have hsw := setWidth31 k hk31
  have hc64 := intCast64of31 k hk31
  have hrm : air2lean_model_1 fd s.ptr (BitVec.ofNat 64 k) m = _ := hrd
  unfold Host.afterRead at hrm ⊢
  cases hr : m.host.ops.read m.host.env h k with
  | mk r s' =>
    cases r with
    | ok bytes =>
      have hb := hc.readBound m.host.env h k bytes s' ho.2 (by rw [hr])
      have he := errno_ok bytes.length (by omega)
      simp only [hr, readRet] at hrm
      simp [posix_read.loop13, zig_unfold, Zig.callM, Zig.callR, hloc, hmin, hc31, hsw, hc64, hrm,
        he, intCast64, readResult]
    | error e =>
      simp only [hr, readRet] at hrm
      have he := errno_err e
      cases e <;>
        simp [posix_read.loop13, zig_unfold, Zig.callM, Zig.callR, hloc, hmin, hc31, hsw, hc64, hrm,
          he, readResult, readErrName, errno, posix_unexpectedErrno, os_linux_E__enum_1.SUCCESS,
          os_linux_E__enum_1.INTR, os_linux_E__enum_1.INVAL, os_linux_E__enum_1.FAULT,
          os_linux_E__enum_1.AGAIN, os_linux_E__enum_1.CANCELED, os_linux_E__enum_1.BADF,
          os_linux_E__enum_1.IO, os_linux_E__enum_1.ISDIR, os_linux_E__enum_1.NOBUFS,
          os_linux_E__enum_1.NOMEM, os_linux_E__enum_1.NOTCONN, os_linux_E__enum_1.CONNRESET,
          os_linux_E__enum_1.TIMEDOUT]

/-- `posix.read` (0.16.0): one `read` (no `EINTR` in the model, so no retry). -/
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

/-- **`readClose` (std `posix.read` + `Io.Threaded.closeFd`, translated from Zig 0.16.0 AIR).**
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

end EnvStd16.Proofs

/-! ## Any contracted environment, and a scripted run -/

namespace EnvStd15.Proofs
open Zig Zig.Env Zig.Env.Linux EnvStdIo

/-- `writeAllClose_spec` for operations over any state type, installed through `Ops.replay`. -/
theorem writeAllClose_spec_replay {σ : Type} {ops : Ops σ} {s0 : σ} {m0 : Mem} {fd : BitVec 32}
    {h : Handle} {s : Slice} {buf : List UInt8} {errs : List IoError} (hc : Contract ops errs)
    (hm : m0.host.ops = ops.replay s0) (ho : OpenAt fd m0 h) (hb : BytesAt m0 s.ptr buf)
    (hl : s.len.toNat = buf.length) (hst : m0.SingleThread) :
    ∃ r m', (writeAllClose ⟨fd⟩ s).run m0 = pure (r, m') ∧ m'.blocks = m0.blocks ∧
      m'.host.ops.isOpen m'.host.env h = false ∧
      (∀ h', h' ≠ h → m'.host.ops.isOpen m'.host.env h' = m0.host.ops.isOpen m0.host.env h') ∧
      ∃ evs, m'.host.log = m0.host.log ++ evs ++ [.closed h] ∧ Event.closed h ∉ evs ∧
        ((r = .ok () ∧ OnlyWrites h evs ∧ written evs = buf) ∨
         (∃ e pre rest, r = .error (writeErrName e) ∧ e ∈ errs ∧ evs = pre ++ [.failed h e] ∧
            OnlyWrites h pre ∧ written pre ++ rest = buf ∧ rest ≠ [])) :=
  writeAllClose_spec (hm ▸ hc.replay s0) ho hb hl hst

/-- A scripted host: descriptor 3 is open until closed; each write accepts at most two bytes,
or fails with `brokenPipe` once `failAfter` writes were accepted. -/
def scripted (failAfter : Nat) : Ops Hist where
  monotonicNow hist := hist.length
  wallNow _ := 0
  isOpen hist h := h == 3 && !(hist.contains (.close 3))
  read hist h max := (.ok [], hist ++ [.read h max])
  write hist h bytes :=
    if (hist.filter fun r => r matches .write ..).length < failAfter then
      (.ok (min 2 bytes.length), hist ++ [.write h bytes])
    else (.error .brokenPipe, hist ++ [.write h bytes])
  close hist h := hist ++ [.close h]

/-- Five bytes at the start of a global block, and the scripted host. -/
def demoMem (failAfter : Nat) : Mem :=
  { Mem.ofGlobals .fresh [((#[1, 2, 3, 4, 5] : Array UInt8).map enc, 1, .global)] with
    host := { ops := scripted failAfter } }

def demoSlice : Slice := ⟨⟨some 0, 0⟩, 5⟩

def demoRun (failAfter : Nat) : Option (Except ErrName Unit × List Event) :=
  match (writeAllClose ⟨3⟩ demoSlice).run (demoMem failAfter) with
  | some (.ok (r, m)) => some (r, m.host.log)
  | _ => none

-- Partial writes are retried until every byte is accepted; the handle is closed once.
#guard demoRun 10 ==
  some (.ok (), [.wrote 3 [1, 2], .wrote 3 [3, 4], .wrote 3 [5], .closed 3])
-- The first error stops the loop after a proper prefix; the handle is still closed once.
#guard demoRun 1 ==
  some (.error "BrokenPipe", [.wrote 3 [1, 2], .failed 3 .brokenPipe, .closed 3])

end EnvStd15.Proofs
