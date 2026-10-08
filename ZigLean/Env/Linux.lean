import ZigLean.Mem.Lemmas
import ZigLean.External

/-!
# Linux raw-syscall primitives bound to the environment boundary (E03, ENV-03)

The only trusted part of translated std I/O. On `x86_64-linux` without libc, Zig's
`std.posix.system` is `std.os.linux`, whose `read`, `write` and `close` are one `syscall`
instruction each (rejected by the translator: an asm `memory` clobber, M21). Everything above them
in std (`posix.read`/`posix.write`/`posix.close`, `fs.File.write`/`writeAll`/`read`/`readAll`/
`close` on 0.15.2, `posix.read` and `Io.Threaded.closeFd` on 0.16.0) is translated from AIR.

These models give each primitive the Linux return convention (a `usize`; `-errno` for an error)
over the `Zig.Env.Host` installed in `Zig.Mem`. A project binds them through the external model
registry (`docs/external-models.md`, E01); each binding's evidence is proved below. That the
kernel behaves as these models over some contracted `Ops` is premise ENV-03
(`docs/premises.md#env-03`); ENV-01 is the contract itself.

Choices that are stricter than the kernel: a negative descriptor or one that is not open is
`.illegal` (the kernel returns `EBADF`, or acts on a reused descriptor); a source byte that is
undefined is `.unspecified`.
-/
namespace Zig.Env.Linux
open Zig

/-- The Linux `errno` of each modelled error. -/
def errno : IoError → Nat
  | .wouldBlock => 11       -- EAGAIN
  | .brokenPipe => 32       -- EPIPE
  | .noSpaceLeft => 28      -- ENOSPC
  | .accessDenied => 13     -- EACCES
  | .inputOutput => 5       -- EIO
  | .connectionReset => 104 -- ECONNRESET

/-- The raw return of a failed syscall: `-errno` as a `usize`. -/
def errReturn (e : IoError) : BitVec 64 := 0 - BitVec.ofNat 64 (errno e)

/-- The handle a descriptor names; a negative descriptor names none. -/
def handle? (fd : BitVec 32) : Option Handle :=
  if fd.toInt < 0 then none else some fd.toNat

/-- The open handle `fd` names, or `.illegal`. -/
def openHandle (fd : BitVec 32) (m : Mem) : Result Handle :=
  match handle? fd with
  | some h => if m.host.ops.isOpen m.host.env h then pure h else throw .illegal
  | none => throw .illegal

/-- The byte values of defined bytes; `none` if one is undefined. -/
def byteValues? : List Byte → Option (List UInt8)
  | [] => some []
  | .int b :: rest => (byteValues? rest).map (UInt8.ofNat b.toNat :: ·)
  | _ :: _ => none

/-- The host after a write request on `h` with the result `r` and state `s'`. -/
def _root_.Zig.Env.Host.afterWrite (host : Host) (h : Handle) (buf : List UInt8) : BitVec 64 × Host :=
  match host.ops.write host.env h buf with
  | (.ok n, s') => (BitVec.ofNat 64 n, { host with env := s', log := host.log ++ [.wrote h (buf.take n)] })
  | (.error e, s') => (errReturn e, { host with env := s', log := host.log ++ [.failed h e] })

def _root_.Zig.Env.Host.afterRead (host : Host) (h : Handle) (max : Nat) : Except IoError (List UInt8) × Host :=
  match host.ops.read host.env h max with
  | (.ok bytes, s') => (.ok bytes, { host with env := s', log := host.log ++ [.received h bytes] })
  | (.error e, s') => (.error e, { host with env := s', log := host.log ++ [.failed h e] })

def _root_.Zig.Env.Host.afterClose (host : Host) (h : Handle) : Host :=
  { host with env := host.ops.close host.env h, log := host.log ++ [.closed h] }

/-- `os.linux.write(fd, buf, count) usize`. A zero count returns 0 without a request; otherwise
the `count` bytes at `buf` are read (a checked, recorded access) and offered to `Ops.write`. -/
def write (args : BitVec 32 × Ptr × BitVec 64) : MemM (BitVec 64) := fun m =>
  match (openHandle args.1 m).run with
  | some (.ok h) =>
    if args.2.2.toNat = 0 then pure (0, m) else
    match ((loadBytes args.2.1 args.2.2.toNat 1).run m).run with
    | some (.ok (bytes, m1)) =>
      match byteValues? bytes.toList with
      | some buf => pure ((m1.host.afterWrite h buf).1, { m1 with host := (m1.host.afterWrite h buf).2 })
      | none => throw .unspecified
    | some (.error e) => throw e
    | none => ExceptT.mk none
  | _ => throw .illegal

/-- The bytes of a received buffer. -/
def received (bytes : List UInt8) : Array Byte := bytes.toArray.map fun b => .int (BitVec.ofNat 8 b.toNat)

/-- `os.linux.read(fd, buf, count) usize`. A zero count returns 0 without a request; otherwise
`Ops.read` is asked for at most `count` bytes, which are stored at `buf` (a checked, recorded
access). -/
def read (args : BitVec 32 × Ptr × BitVec 64) : MemM (BitVec 64) := fun m =>
  match (openHandle args.1 m).run with
  | some (.ok h) =>
    if args.2.2.toNat = 0 then pure (0, m) else
    let m1 := { m with host := (m.host.afterRead h args.2.2.toNat).2 }
    match (m.host.afterRead h args.2.2.toNat).1 with
    | .error e => pure (errReturn e, m1)
    | .ok bytes =>
      if bytes.isEmpty then pure (0, m1) else
      match ((storeBytes args.2.1 1 (received bytes)).run m1).run with
      | some (.ok ((), m2)) => pure (BitVec.ofNat 64 bytes.length, m2)
      | some (.error e) => throw e
      | none => ExceptT.mk none
  | _ => throw .illegal

/-- `os.linux.close(fd) usize`. -/
def close (fd : BitVec 32) : MemM (BitVec 64) := fun m =>
  match (openHandle fd m).run with
  | some (.ok h) => pure (0, { m with host := m.host.afterClose h })
  | _ => throw .illegal

/-! ## Run lemmas -/

theorem access_cases' (m : Mem) (p : Ptr) (n al : Nat) :
    m.access p n al = throw .illegal ∨ ∃ b blk o, m.access p n al = pure (b, blk, o) := by
  unfold Mem.access
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inr ⟨_, _, _, rfl⟩
      · exact .inl rfl

theorem raceAt_illegal' {fp : Array FootprintEntry} {c : VClock} {b o len : Nat} {k : AccessKind}
    {err : Error} (h : raceAt fp c b o len k = some err) : err = .illegal := by
  obtain ⟨e, -, he⟩ := Array.exists_of_findSome?_eq_some h
  split at he
  · unfold racePair at he
    split at he
    · cases he; rfl
    · cases he
  · cases he

/-- A load either fails with `.illegal` (access or race) or performs the checked read. -/
theorem loadBytes_cases (p : Ptr) (n a : Nat) (m : Mem) :
    ((loadBytes p n a).run m).run = some (.error .illegal) ∨
    ∃ b blk o, m.access p n a = pure (b, blk, o) ∧
      ((loadBytes p n a).run m).run = some (.ok (blk.bytes.extract o (o + n), m.recordAt b o n .read)) := by
  rcases access_cases' m p n a with h | ⟨b, blk, o, h⟩
  · left
    simp [loadBytes, h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, throw, throwThe,
      MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure, ExceptT.run]
  · cases hr : raceAt m.footprint (VClock.bump (m.clocks[m.current]!) m.current) b o n .read with
    | none =>
      right
      exact ⟨b, blk, o, h, by rw [loadBytes_run h hr]; rfl⟩
    | some e =>
      left
      have he := raceAt_illegal' hr
      subst he
      simp [loadBytes, recordAccess, h, hr, StateT.run, bind, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, throw,
        throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure,
        ExceptT.pure, ExceptT.run]

/-- A store either fails with `.illegal` (access, constant block or race) or performs the
checked write. -/
theorem storeBytes_cases (p : Ptr) (a : Nat) (bs : Array Byte) (m : Mem) :
    ((storeBytes p a bs).run m).run = some (.error .illegal) ∨
    ∃ b blk o, m.access p bs.size a = pure (b, blk, o) ∧
      ((storeBytes p a bs).run m).run =
        some (.ok ((), (m.recordAt b o bs.size .write).write b blk o bs)) := by
  rcases access_cases' m p bs.size a with h | ⟨b, blk, o, h⟩
  · left
    simp [storeBytes, Mem.accessW, h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, throw, throwThe,
      MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure, ExceptT.run]
  · by_cases hK : blk.kind = .constGlobal
    · left
      simp [storeBytes, Mem.accessW, h, hK, StateT.run, bind, StateT.bind, get, getThe,
        MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift, throw,
        throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure,
        ExceptT.pure, ExceptT.run]
    · cases hr : raceAt m.footprint (VClock.bump (m.clocks[m.current]!) m.current) b o bs.size .write with
      | none => exact .inr ⟨b, blk, o, h, by rw [storeBytes_run h hK hr]; rfl⟩
      | some e =>
        left
        have he := raceAt_illegal' hr
        subst he
        simp [storeBytes, recordAccess, Mem.accessW, h, hK, hr, StateT.run, bind, StateT.bind, get,
          getThe, MonadStateOf.get, StateT.get, liftM, monadLift, MonadLift.monadLift, StateT.lift,
          throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, pure,
          ExceptT.pure, ExceptT.run]

/-- An open handle named by `fd`. -/
def OpenAt (fd : BitVec 32) (m : Mem) (h : Handle) : Prop :=
  handle? fd = some h ∧ m.host.ops.isOpen m.host.env h = true

/-- `fd` names no open handle. -/
def NotOpen (fd : BitVec 32) (m : Mem) : Prop :=
  ∀ h, handle? fd = some h → m.host.ops.isOpen m.host.env h = false

theorem openHandle_cases (fd : BitVec 32) (m : Mem) :
    (openHandle fd m).run = some (.error .illegal) ∧ NotOpen fd m ∨
    ∃ h, (openHandle fd m).run = some (.ok h) ∧ OpenAt fd m h := by
  unfold openHandle NotOpen OpenAt
  split
  · rename_i h hh
    cases ho : m.host.ops.isOpen m.host.env h
    · left
      refine ⟨by simp, fun h' hh' => ?_⟩
      rw [hh] at hh'
      cases hh'
      exact ho
    · exact .inr ⟨h, by simp, hh, ho⟩
  · rename_i hh
    left
    refine ⟨rfl, fun h' hh' => ?_⟩
    rw [hh'] at hh
    cases hh

/-! ## Registry evidence (E01 bindings)

Each primitive is bound with `termination: total` and `effects: tracked`. `close` declares no
footprint; `write` reads its buffer (`footprint.reads = [1]`); `read` writes it
(`footprint.writes = [1]`). -/

def closeContract : External.Contract (BitVec 32) (BitVec 64) where
  pre := fun _ _ => True
  post := fun fd before r after => ∃ h, OpenAt fd before h ∧ r = 0 ∧
    after = { before with host := before.host.afterClose h }
  frame := fun _ before after => after.blocks = before.blocks ∧ after.footprint = before.footprint
  access := fun _ _ _ => False
  failure := fun fd before error => error = .illegal ∧ NotOpen fd before
  divergence := fun _ _ => False

theorem closeEvidence : closeContract.Holds .total [.illegal] .tracked close := by
  intro fd before _
  show match close fd before with | _ => _
  rcases openHandle_cases fd before with ⟨e, hf⟩ | ⟨h, e, hopen⟩
  · simp only [close, e]
    exact ⟨by simp, rfl, hf⟩
  · simp only [close, e]
    exact ⟨⟨h, hopen, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨#[], by simp, by simp⟩, fun h => nomatch h⟩

def writeContract : External.Contract (BitVec 32 × Ptr × BitVec 64) (BitVec 64) where
  pre := fun _ _ => True
  post := fun args before r after => ∃ h, OpenAt args.1 before h ∧ after.blocks = before.blocks ∧
    ((args.2.2.toNat = 0 ∧ r = 0 ∧ after = before) ∨
     (∃ buf, (r, after.host) = before.host.afterWrite h buf))
  frame := fun _ before after => after.blocks = before.blocks
  access := fun args _ entry => some entry.block = args.2.1.block ∧ entry.kind = .read
  failure := fun args before error =>
    (error = .illegal ∧ (NotOpen args.1 before ∨ args.2.2.toNat ≠ 0)) ∨
    (error = .unspecified ∧ args.2.2.toNat ≠ 0)
  divergence := fun _ _ => False

def writeFootprint : External.Footprint (BitVec 32 × Ptr × BitVec 64) where
  reads := fun args => [External.Region.block args.2.1]
  writes := fun _ => []

theorem writeEvidence :
    writeContract.Holds .total [.illegal, .unspecified] .tracked write ∧
    writeContract.Respects writeFootprint := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨fd, p, n⟩ before _
    show match write (fd, p, n) before with | _ => _
    rcases openHandle_cases fd before with ⟨e, hf⟩ | ⟨h, e, hopen⟩
    · simp only [write, e]
      exact ⟨by simp, .inl ⟨rfl, .inl hf⟩⟩
    · simp only [write, e]
      by_cases hn : n.toNat = 0
      · simp only [hn, if_true]
        exact ⟨⟨h, hopen, rfl, .inl ⟨hn, rfl, rfl⟩⟩, rfl, ⟨#[], by simp, by simp⟩,
          fun h => nomatch h⟩
      · simp only [hn, if_false]
        rcases loadBytes_cases p n.toNat 1 before with hl | ⟨b, blk, o, hacc, hl⟩
        · simp only [hl]
          exact ⟨by simp, .inl ⟨rfl, .inr hn⟩⟩
        · simp only [hl]
          obtain ⟨hb, -⟩ := access_eq hacc
          cases hv : byteValues? (blk.bytes.extract o (o + n.toNat)).toList with
          | none => exact ⟨by simp, .inr ⟨rfl, hn⟩⟩
          | some buf =>
            refine ⟨⟨h, hopen, rfl, .inr ⟨buf, rfl⟩⟩, rfl, ⟨#[_], rfl, fun entry mem => ?_⟩,
              fun h => nomatch h⟩
            simp only [List.mem_singleton] at mem
            subst mem
            exact ⟨hb.symm, rfl⟩
  · intro args _ entry ⟨hblock, hkind⟩
    exact .inr ⟨by simp [writeFootprint, External.Region.block, hblock],
      by simp [hkind, AccessKind.isWrite]⟩
  · intro args before after _ frame b _
    rw [frame]

def readContract : External.Contract (BitVec 32 × Ptr × BitVec 64) (BitVec 64) where
  pre := fun _ _ => True
  post := fun args before r after => ∃ h, OpenAt args.1 before h ∧
    ((args.2.2.toNat = 0 ∧ r = 0 ∧ after = before) ∨
     (args.2.2.toNat ≠ 0 ∧ after.host = (before.host.afterRead h args.2.2.toNat).2 ∧
      match (before.host.afterRead h args.2.2.toNat).1 with
      | .error e => r = errReturn e
      | .ok bytes => r = BitVec.ofNat 64 bytes.length))
  frame := fun args before after =>
    ∀ b, some b ≠ args.2.1.block → after.blocks[b]? = before.blocks[b]?
  access := fun args _ entry => some entry.block = args.2.1.block ∧ entry.kind = .write
  failure := fun args before error => error = .illegal ∧ (NotOpen args.1 before ∨ args.2.2.toNat ≠ 0)
  divergence := fun _ _ => False

def readFootprint : External.Footprint (BitVec 32 × Ptr × BitVec 64) where
  reads := fun _ => []
  writes := fun args => [External.Region.block args.2.1]

theorem readEvidence :
    readContract.Holds .total [.illegal] .tracked read ∧ readContract.Respects readFootprint := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨fd, p, n⟩ before _
    show match read (fd, p, n) before with | _ => _
    rcases openHandle_cases fd before with ⟨e, hf⟩ | ⟨h, e, hopen⟩
    · simp only [read, e]
      exact ⟨by simp, rfl, .inl hf⟩
    · simp only [read, e]
      by_cases hn : n.toNat = 0
      · simp only [hn, if_true]
        exact ⟨⟨h, hopen, .inl ⟨hn, rfl, rfl⟩⟩, fun _ _ => rfl, ⟨#[], by simp, by simp⟩,
          fun h => nomatch h⟩
      · simp only [hn, if_false]
        cases hr : (before.host.afterRead h n.toNat).1 with
        | error e =>
          refine ⟨⟨h, hopen, .inr ⟨hn, rfl, ?_⟩⟩, fun _ _ => rfl, ⟨#[], by simp, by simp⟩,
            fun h => nomatch h⟩
          simp [hr]
        | ok bytes =>
          by_cases he : bytes.isEmpty = true
          · simp only [he, if_true]
            refine ⟨⟨h, hopen, .inr ⟨hn, rfl, ?_⟩⟩, fun _ _ => rfl, ⟨#[], by simp, by simp⟩,
              fun h => nomatch h⟩
            simp [hr, List.isEmpty_iff.mp he]
          · simp only [he, if_false]
            rcases storeBytes_cases p 1 (received bytes)
                { before with host := (before.host.afterRead h n.toNat).2 }
              with hs | ⟨b, blk, o, hacc, hs⟩
            · simp only [hs]
              exact ⟨by simp, rfl, .inr hn⟩
            · simp only [hs]
              obtain ⟨hb, -⟩ := access_eq hacc
              refine ⟨⟨h, hopen, .inr ⟨hn, rfl, by simp [hr]⟩⟩, ?_,
                ⟨#[_], rfl, fun entry mem => ?_⟩, fun h => nomatch h⟩
              · intro b' hne
                have : b ≠ b' := fun e => hne (e ▸ hb.symm)
                simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds,
                  Array.getElem?_setIfInBounds_ne this]
              · simp only [List.mem_singleton] at mem
                subst mem
                exact ⟨hb.symm, rfl⟩
  · intro args _ entry ⟨hblock, _⟩
    exact .inl (by simp [readFootprint, External.Region.block, hblock])
  · intro args before after _ frame b outside
    exact frame b fun h => outside (by simp [readFootprint, External.Region.block, h])

end Zig.Env.Linux
