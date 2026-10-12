-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...7.2-musl","zig_version":"0.17.0"}}
import ZigLean


namespace TryLifetimes

structure Thread_SpawnConfig where
  stack_size : BitVec 64
  allocator : Option (Zig.Allocator)
  deriving Repr, Inhabited, DecidableEq

/-- The memory at program start under the placement `σ`: block `k` is global `k`. -/
def mem0 (σ : Zig.Placement) : Zig.Mem := Zig.Mem.ofGlobals σ []

/-- The spawn targets of the program; fields are captured by value. -/
inductive Tgt where
  | reader (a : (Zig.Ptr) × (Zig.Ptr))
  | writer (a : (Zig.Ptr) × (BitVec 8))

/-- The child protocol obligation for the complete captured tuple. Pointer
identities are copied; a proof must explicitly justify ownership transfer or sharing. -/
abbrev Tgt.spawnInit {γ : Type} (P : Zig.Conc.Proto Tgt γ) (target : Tgt) (ghost : γ) : Prop :=
  P.init target ghost

/-- Each captured field in source order. A value is copied and carries no ownership;
a pointer or slice copies only its identity, so a spawn proof must hand over or share its
region (`Zig.Conc.Capture.grant`). An `other` field's obligation cannot be discharged. -/
def Tgt.captures : Tgt → List Zig.Conc.Capture
  | .reader (capture0, capture1) => [.ptr capture0, .ptr capture1]
  | .writer (capture0, _) => [.ptr capture0, .value]

structure readPayloadLocals where
  deriving Inhabited

inductive readPayloadExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def readPayload (p0 : Zig.Ptr) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0 with
    | .error _ => (do
      let i3 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
      let i4 ← pure ((.error i3) : Except Zig.ErrName (BitVec 8))
      pure (.ret i4))
    | .ok v2 => (do
      let i6 ← Zig.load (BitVec 8) 1 v2
      let i7 ← pure ((.ok i6) : Except Zig.ErrName (BitVec 8))
      pure (.ret i7))) : Zig.MM readPayloadLocals readPayloadExit).run' (default : readPayloadLocals)
  match e with
  | .ret v => pure v

structure readerLocals where
  deriving Inhabited

inductive readerExit where
  | ret
  | br2 (v : BitVec 8)

def reader (p0 : Zig.Ptr) (p1 : Zig.Ptr) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callM (readPayload p0)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        let i6 ← Zig.callR (Zig.unwrapPayload i3)
        pure (.br2 i6))
      else (do
        let _i8 ← Zig.callR (Zig.unwrapErr i3)
        pure (.br2 (0 : BitVec 8)))) : Zig.MM readerLocals readerExit) with
    | .br2 v2 => (do
      Zig.store (α := BitVec 8) 1 p1 v2
      pure .ret)
    | e => pure e) : Zig.MM readerLocals readerExit).run' (default : readerLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure concurrentReadsLocals where
  cell : Zig.Ptr
  x : Zig.Ptr
  y : Zig.Ptr
  deriving Inhabited

inductive concurrentReadsExit where
  | ret (v : Except Zig.ErrName (BitVec 16))
  | br3 (v : Except Zig.ErrName (BitVec 8))

def concurrentReads (p0 : BitVec 8) (p1 : Bool) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 16)) := do
  let s2 ← Zig.allocStack 4 2
  let s9 ← Zig.allocStack 1 1
  let s11 ← Zig.allocStack 1 1
  let e ← ((do
    let i2 ← pure (← get).cell
    match ← ((do
      if p1 then (do
        pure (.br3 (.error "Other" : Except Zig.ErrName (BitVec 8))))
      else (do
        let i6 ← pure ((.ok p0) : Except Zig.ErrName (BitVec 8))
        pure (.br3 i6))) : Zig.CM Tgt concurrentReadsLocals concurrentReadsExit) with
    | .br3 v3 => (do
      (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 i2 v3)
      let i9 ← pure (← get).x
      Zig.store (α := BitVec 8) 1 i9 (1 : BitVec 8)
      let i11 ← pure (← get).y
      Zig.store (α := BitVec 8) 1 i11 (1 : BitVec 8)
      let i13 ← pure (i2, i9)
      let i14 ← Zig.spawnC (Tgt.reader i13)
      match i14 with
      | .error _ => (do
        let i16 ← Zig.callRC (Zig.unwrapErr i14)
        let i17 ← pure (i16)
        let i18 ← pure ((.error i17) : Except Zig.ErrName (BitVec 16))
        pure (.ret i18))
      | .ok v15 => (do
        let i20 ← pure (i2, i11)
        let i21 ← Zig.spawnC (Tgt.reader i20)
        match i21 with
        | .error _ => (do
          let i23 ← Zig.callRC (Zig.unwrapErr i21)
          let i24 ← pure (i23)
          let i25 ← pure ((.error i24) : Except Zig.ErrName (BitVec 16))
          pure (.ret i25))
        | .ok v22 => (do
          let _i27 ← Zig.joinC v15
          let _i28 ← Zig.joinC v22
          let i29 ← Zig.load (BitVec 8) 1 i9
          let i30 ← Zig.intCast false false 16 i29
          let i31 ← Zig.load (BitVec 8) 1 i11
          let i32 ← Zig.intCast false false 16 i31
          let i33 ← Zig.add false i30 i32
          let i34 ← pure ((.ok i33) : Except Zig.ErrName (BitVec 16))
          pure (.ret i34))))
    | e => pure e) : Zig.CM Tgt concurrentReadsLocals concurrentReadsExit).run' { (default : concurrentReadsLocals) with cell := s2, x := s9, y := s11 }
  Zig.free s2
  Zig.free s9
  Zig.free s11
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure writePayloadLocals where
  deriving Inhabited

inductive writePayloadExit where
  | ret (v : Except Zig.ErrName (Unit))

def writePayload (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Except Zig.ErrName (Unit)) := do
  let e ← ((do
    Zig.loadDiscardBytes 4 2 p0
    match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0 with
    | .error _ => (do
      let i4 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 p0
      let i5 ← pure ((.error i4) : Except Zig.ErrName (Unit))
      pure (.ret i5))
    | .ok v3 => (do
      Zig.store (α := BitVec 8) 1 v3 p1
      pure (.ret (.ok () : Except Zig.ErrName (Unit))))) : Zig.MM writePayloadLocals writePayloadExit).run' (default : writePayloadLocals)
  match e with
  | .ret v => pure v

structure writerLocals where
  deriving Inhabited

inductive writerExit where
  | ret
  | br2

def writer (p0 : Zig.Ptr) (p1 : BitVec 8) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      let i3 ← Zig.callM (writePayload p0 p1)
      let i4 ← pure (Zig.isNonErr i3)
      if i4 then (do
        pure .br2)
      else (do
        let _i7 ← Zig.callR (Zig.unwrapErr i3)
        pure .br2)) : Zig.MM writerLocals writerExit) with
    | .br2 => (do
      pure .ret)
    | e => pure e) : Zig.MM writerLocals writerExit).run' (default : writerLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure concurrentWritesLocals where
  c1 : Zig.Ptr
  c2 : Zig.Ptr
  deriving Inhabited

inductive concurrentWritesExit where
  | ret (v : Except Zig.ErrName (BitVec 16))

def concurrentWrites (p0 : BitVec 8) (p1 : BitVec 8) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 16)) := do
  let s2 ← Zig.allocStack 4 2
  let s4 ← Zig.allocStack 4 2
  let e ← ((do
    let i2 ← pure (← get).c1
    (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 i2 (.ok (0 : BitVec 8) : Except Zig.ErrName (BitVec 8)))
    let i4 ← pure (← get).c2
    (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 i4 (.ok (0 : BitVec 8) : Except Zig.ErrName (BitVec 8)))
    let i6 ← pure (i2, p0)
    let i7 ← Zig.spawnC (Tgt.writer i6)
    match i7 with
    | .error _ => (do
      let i9 ← Zig.callRC (Zig.unwrapErr i7)
      let i10 ← pure (i9)
      let i11 ← pure ((.error i10) : Except Zig.ErrName (BitVec 16))
      pure (.ret i11))
    | .ok v8 => (do
      let i13 ← pure (i4, p1)
      let i14 ← Zig.spawnC (Tgt.writer i13)
      match i14 with
      | .error _ => (do
        let i16 ← Zig.callRC (Zig.unwrapErr i14)
        let i17 ← pure (i16)
        let i18 ← pure ((.error i17) : Except Zig.ErrName (BitVec 16))
        pure (.ret i18))
      | .ok v15 => (do
        let _i20 ← Zig.joinC v8
        let _i21 ← Zig.joinC v15
        let i22 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.load (Except Zig.ErrName (BitVec 8)) 2 i2)
        match i22 with
        | .error _ => (do
          let i24 ← Zig.callRC (Zig.unwrapErr i22)
          let i25 ← pure (i24)
          let i26 ← pure ((.error i25) : Except Zig.ErrName (BitVec 16))
          pure (.ret i26))
        | .ok v23 => (do
          let i28 ← Zig.intCast false false 16 v23
          let i29 ← Zig.mul false i28 (256 : BitVec 16)
          let i30 ← (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.load (Except Zig.ErrName (BitVec 8)) 2 i4)
          match i30 with
          | .error _ => (do
            let i32 ← Zig.callRC (Zig.unwrapErr i30)
            let i33 ← pure (i32)
            let i34 ← pure ((.error i33) : Except Zig.ErrName (BitVec 16))
            pure (.ret i34))
          | .ok v31 => (do
            let i36 ← Zig.intCast false false 16 v31
            let i37 ← Zig.add false i29 i36
            let i38 ← pure ((.ok i37) : Except Zig.ErrName (BitVec 16))
            pure (.ret i38)))))) : Zig.CM Tgt concurrentWritesLocals concurrentWritesExit).run' { (default : concurrentWritesLocals) with c1 := s2, c2 := s4 }
  Zig.free s2
  Zig.free s4
  match e with
  | .ret v => pure v

structure danglingPayloadLocals where
  deriving Inhabited

inductive danglingPayloadExit where
  | ret (v : Except Zig.ErrName (Zig.Ptr))

-- air2lean-premises: {"ALC-09":[0]}
def danglingPayload (p0 : Zig.Allocator) (p1 : BitVec 8) : Zig.MemM (Except Zig.ErrName (Zig.Ptr)) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.Allocator.create p0 4 2)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let i5 ← pure (i4)
      let i6 ← pure ((.error i5) : Except Zig.ErrName (Zig.Ptr))
      pure (.ret i6))
    | .ok v3 => (do
      let i8 ← pure ((.ok p1) : Except Zig.ErrName (BitVec 8))
      (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 v3 i8)
      Zig.loadDiscardBytes 4 2 v3
      match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 v3 with
      | .error _ => (do
        let i12 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 v3
        let _i13 ← Zig.callM (Zig.Allocator.destroy p0 4 v3)
        let i14 ← pure (i12)
        let i15 ← pure ((.error i14) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i15))
      | .ok v11 => (do
        let _i17 ← Zig.callM (Zig.Allocator.destroy p0 4 v3)
        let i18 ← pure ((.ok v11) : Except Zig.ErrName (Zig.Ptr))
        pure (.ret i18)))) : Zig.MM danglingPayloadLocals danglingPayloadExit).run' (default : danglingPayloadLocals)
  match e with
  | .ret v => pure v

structure freeOnErrorLocals where
  deriving Inhabited

inductive freeOnErrorExit where
  | ret (v : Except Zig.ErrName (BitVec 8))
  | br9 (v : Except Zig.ErrName (BitVec 8))

-- air2lean-premises: {"ALC-09":[0]}
def freeOnError (p0 : Zig.Allocator) (p1 : BitVec 8) (p2 : Bool) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    let i3 ← Zig.callM (Zig.Allocator.create p0 4 2)
    match i3 with
    | .error _ => (do
      let i5 ← Zig.callR (Zig.unwrapErr i3)
      let i6 ← pure (i5)
      let i7 ← pure ((.error i6) : Except Zig.ErrName (BitVec 8))
      pure (.ret i7))
    | .ok v4 => (do
      match ← ((do
        if p2 then (do
          pure (.br9 (.error "Bad" : Except Zig.ErrName (BitVec 8))))
        else (do
          let i12 ← pure ((.ok p1) : Except Zig.ErrName (BitVec 8))
          pure (.br9 i12))) : Zig.MM freeOnErrorLocals freeOnErrorExit) with
      | .br9 v9 => (do
        (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 v4 v9)
        Zig.loadDiscardBytes 4 2 v4
        match ← Zig.finiteTryPayloadPtr (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 v4 with
        | .error _ => (do
          let i17 ← Zig.finiteErrCodeAt (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) (BitVec 8) 2 v4
          let _i18 ← Zig.callM (Zig.Allocator.destroy p0 4 v4)
          let i19 ← pure (i17)
          let i20 ← pure ((.error i19) : Except Zig.ErrName (BitVec 8))
          pure (.ret i20))
        | .ok v16 => (do
          let i22 ← Zig.load (BitVec 8) 1 v16
          let _i23 ← Zig.callM (Zig.Allocator.destroy p0 4 v4)
          let i24 ← pure ((.ok i22) : Except Zig.ErrName (BitVec 8))
          pure (.ret i24)))
      | e => pure e)) : Zig.MM freeOnErrorLocals freeOnErrorExit).run' (default : freeOnErrorLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure racingAliasesLocals where
  cell : Zig.Ptr
  out : Zig.Ptr
  deriving Inhabited

inductive racingAliasesExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

def racingAliases (p0 : BitVec 8) : Zig.ConcM Tgt (Except Zig.ErrName (BitVec 8)) := do
  let s1 ← Zig.allocStack 4 2
  let s3 ← Zig.allocStack 1 1
  let e ← ((do
    let i1 ← pure (← get).cell
    (letI : Zig.Enc (Except Zig.ErrName (BitVec 8)) := Zig.errorUnionEnc (⟨#["Bad", "Other"], by decide, by decide⟩ : Zig.ErrorDomain) ((inferInstance : Zig.Enc (BitVec 8))); Zig.store (α := Except Zig.ErrName (BitVec 8)) 2 i1 (.ok (0 : BitVec 8) : Except Zig.ErrName (BitVec 8)))
    let i3 ← pure (← get).out
    Zig.store (α := BitVec 8) 1 i3 (0 : BitVec 8)
    let i5 ← pure (i1, p0)
    let i6 ← Zig.spawnC (Tgt.writer i5)
    match i6 with
    | .error _ => (do
      let i8 ← Zig.callRC (Zig.unwrapErr i6)
      let i9 ← pure (i8)
      let i10 ← pure ((.error i9) : Except Zig.ErrName (BitVec 8))
      pure (.ret i10))
    | .ok v7 => (do
      let i12 ← pure (i1, i3)
      let i13 ← Zig.spawnC (Tgt.reader i12)
      match i13 with
      | .error _ => (do
        let i15 ← Zig.callRC (Zig.unwrapErr i13)
        let i16 ← pure (i15)
        let i17 ← pure ((.error i16) : Except Zig.ErrName (BitVec 8))
        pure (.ret i17))
      | .ok v14 => (do
        let _i19 ← Zig.joinC v7
        let _i20 ← Zig.joinC v14
        let i21 ← Zig.load (BitVec 8) 1 i3
        let i22 ← pure ((.ok i21) : Except Zig.ErrName (BitVec 8))
        pure (.ret i22)))) : Zig.CM Tgt racingAliasesLocals racingAliasesExit).run' { (default : racingAliasesLocals) with cell := s1, out := s3 }
  Zig.free s1
  Zig.free s3
  match e with
  | .ret v => pure v

structure readDanglingLocals where
  deriving Inhabited

inductive readDanglingExit where
  | ret (v : Except Zig.ErrName (BitVec 8))

-- air2lean-premises: {"ALC-09":[0]}
def readDangling (p0 : Zig.Allocator) (p1 : BitVec 8) : Zig.MemM (Except Zig.ErrName (BitVec 8)) := do
  let e ← ((do
    let i2 ← Zig.callM (danglingPayload p0 p1)
    match i2 with
    | .error _ => (do
      let i4 ← Zig.callR (Zig.unwrapErr i2)
      let i5 ← pure ((.error i4) : Except Zig.ErrName (BitVec 8))
      pure (.ret i5))
    | .ok v3 => (do
      let i7 ← Zig.load (BitVec 8) 1 v3
      let i8 ← pure ((.ok i7) : Except Zig.ErrName (BitVec 8))
      pure (.ret i8))) : Zig.MM readDanglingLocals readDanglingExit).run' (default : readDanglingLocals)
  match e with
  | .ret v => pure v

/-- Runs a spawn target (`Zig.Sched.run`). -/
def dispatch : Tgt → Zig.ConcM Tgt Unit
  | .reader a =>
    let (capture0, capture1) := a
    discard (Zig.ConcM.liftMem (reader capture0 capture1))
  | .writer a =>
    let (capture0, capture1) := a
    discard (Zig.ConcM.liftMem (writer capture0 capture1))

end TryLifetimes