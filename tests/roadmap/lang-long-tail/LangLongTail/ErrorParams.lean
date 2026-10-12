-- air2lean-profile: {"correspondence":"model","float_semantics":"ieee","profile":{"abi":"musl","backend":"stage2_llvm","build_mode":"ReleaseSafe","cpu":"x86_64","endian":"little","error_layout":"type-table","error_set_bits":16,"error_tracing":false,"export_stage":"analyzed-air","features":["64bit","cmov","cx8","fxsr","idivq_to_divl","macrofusion","mmx","nopl","slow_3ops_lea","slow_incdec","sse","sse2","vzeroupper","x87"],"float_mode":"per-instruction","name":"abi64-le-v1","pointer_bits":64,"schema":12,"target_triple":"x86_64-linux.5.10...6.19-musl","zig_version":"0.16.0"}}
import ZigLean


namespace ErrorParams

structure fail__anon_60b8866c0f76Locals where
  deriving Inhabited

inductive fail__anon_60b8866c0f76Exit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br2

def fail__anon_60b8866c0f76 (p0 : BitVec 32) (p1 : Zig.ErrName) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 32))
      if i3 then (do
        let i5 ← pure ((.error p1) : Except Zig.ErrName (BitVec 32))
        pure (.ret i5))
      else (do
        pure .br2)) : Zig.M fail__anon_60b8866c0f76Locals fail__anon_60b8866c0f76Exit) with
    | .br2 => (do
      let i8 ← Zig.add false p0 (1 : BitVec 32)
      let i9 ← pure ((.ok i8) : Except Zig.ErrName (BitVec 32))
      pure (.ret i9))
    | e => pure e) : Zig.M fail__anon_60b8866c0f76Locals fail__anon_60b8866c0f76Exit).run' (default : fail__anon_60b8866c0f76Locals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fail__anon_6e006e1a96cdLocals where
  deriving Inhabited

inductive fail__anon_6e006e1a96cdExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br2

def fail__anon_6e006e1a96cd (p0 : BitVec 32) (p1 : Zig.ErrName) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 32))
      if i3 then (do
        let i5 ← pure ((.error p1) : Except Zig.ErrName (BitVec 32))
        pure (.ret i5))
      else (do
        pure .br2)) : Zig.M fail__anon_6e006e1a96cdLocals fail__anon_6e006e1a96cdExit) with
    | .br2 => (do
      let i8 ← Zig.add false p0 (1 : BitVec 32)
      let i9 ← pure ((.ok i8) : Except Zig.ErrName (BitVec 32))
      pure (.ret i9))
    | e => pure e) : Zig.M fail__anon_6e006e1a96cdLocals fail__anon_6e006e1a96cdExit).run' (default : fail__anon_6e006e1a96cdLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure orBoomLocals where
  deriving Inhabited

inductive orBoomExit where
  | ret (v : Except Zig.ErrName (BitVec 32))
  | br2

def orBoom (p0 : BitVec 32) (p1 : Zig.ErrName) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    match ← ((do
      let i3 ← pure (p0 == (0 : BitVec 32))
      if i3 then (do
        let i5 ← pure ((.error p1) : Except Zig.ErrName (BitVec 32))
        pure (.ret i5))
      else (do
        pure .br2)) : Zig.M orBoomLocals orBoomExit) with
    | .br2 => (do
      let i8 ← pure ((.ok p0) : Except Zig.ErrName (BitVec 32))
      pure (.ret i8))
    | e => pure e) : Zig.M orBoomLocals orBoomExit).run' (default : orBoomLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure forwardLocals where
  deriving Inhabited

inductive forwardExit where
  | ret (v : Except Zig.ErrName (BitVec 32))

def forward (p0 : BitVec 32) : Zig.Result (Except Zig.ErrName (BitVec 32)) := do
  let e ← ((do
    let i1 ← Zig.call (orBoom p0 "Boom")
    pure (.ret i1)) : Zig.M forwardLocals forwardExit).run' (default : forwardLocals)
  match e with
  | .ret v => pure v

structure skipFirstLocals where
  deriving Inhabited

inductive skipFirstExit where
  | ret (v : BitVec 32)

def skipFirst (p0 : Zig.ErrName) (p1 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i2 ← pure (Zig.mulWrap p1 (3 : BitVec 32))
    pure (.ret i2)) : Zig.M skipFirstLocals skipFirstExit).run' (default : skipFirstLocals)
  match e with
  | .ret v => pure v

structure unwrapEmptyLocals where
  deriving Inhabited

inductive unwrapEmptyExit where
  | ret (v : BitVec 32)

def unwrapEmpty (p0 : Except Zig.ErrName (BitVec 32)) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← Zig.call (Zig.unwrapPayload p0)
    pure (.ret i1)) : Zig.M unwrapEmptyLocals unwrapEmptyExit).run' (default : unwrapEmptyLocals)
  match e with
  | .ret v => pure v

structure viaFailLocals where
  deriving Inhabited

inductive viaFailExit where
  | ret (v : BitVec 32)
  | br1 (v : BitVec 32)
  | br9 (v : BitVec 32)
  | br18 (v : BitVec 32)

def viaFail (p0 : BitVec 32) : Zig.Result (BitVec 32) := do
  let e ← ((do
    match ← ((do
      let i2 ← Zig.call (fail__anon_60b8866c0f76 p0 "Boom")
      let i3 ← pure (Zig.isNonErr i2)
      if i3 then (do
        let i5 ← Zig.call (Zig.unwrapPayload i2)
        pure (.br1 i5))
      else (do
        let _i7 ← Zig.call (Zig.unwrapErr i2)
        pure (.ret (100 : BitVec 32)))) : Zig.M viaFailLocals viaFailExit) with
    | .br1 v1 => (do
      match ← ((do
        let i10 ← pure (Zig.subWrap p0 (1 : BitVec 32))
        let i11 ← Zig.call (fail__anon_6e006e1a96cd i10 "Right")
        let i12 ← pure (Zig.isNonErr i11)
        if i12 then (do
          let i14 ← Zig.call (Zig.unwrapPayload i11)
          pure (.br9 i14))
        else (do
          let _i16 ← Zig.call (Zig.unwrapErr i11)
          let i17 ← Zig.call (Zig.unwrapErr i11)
          match ← ((do
            if i17 == "Left" then (do
              pure (.br18 (200 : BitVec 32)))
            else (do
              if i17 == "Right" then (do
                pure (.br18 (201 : BitVec 32)))
              else (do
                throw .panic))) : Zig.M viaFailLocals viaFailExit) with
          | .br18 v18 => (do
            pure (.ret v18))
          | e => pure e)) : Zig.M viaFailLocals viaFailExit) with
      | .br9 v9 => (do
        let i25 ← Zig.add false v1 v9
        pure (.ret i25))
      | e => pure e)
    | e => pure e) : Zig.M viaFailLocals viaFailExit).run' (default : viaFailLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end ErrorParams