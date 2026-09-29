import ZigLean


namespace Slices

structure Tag where
  name : Vector (BitVec 8) 4
  n : BitVec 8
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Tag where
  size := 5
  align := 1
  encode v := Zig.Enc.fields 5 [(0, Zig.Enc.encode v.name), (4, Zig.Enc.encode v.n)]
  decode bs := do pure { name := ← Zig.Enc.decodeAt bs 0, n := ← Zig.Enc.decodeAt bs 4 }

inductive Color where
  | red
  | green
  | blue
  deriving Repr, Inhabited, DecidableEq

def Color.toBits : Color → BitVec 2
  | .red => (0 : BitVec 2)
  | .green => (1 : BitVec 2)
  | .blue => (2 : BitVec 2)

def Color.ofInt? (v : Int) : Option Color :=
  if v = 0 then Option.some .red else if v = 1 then Option.some .green else if v = 2 then Option.some .blue else Option.none

def Color.isNamed (_ : Color) : Bool := true

/-- The memory at program start: block `k` is global `k`. -/
def mem0 : Zig.Mem := Zig.Mem.ofGlobals [
  -- 0: slices.counter
  (Zig.Enc.encode ((0 : BitVec 32) : BitVec 32), 4, .global),
  -- 1: a constant
  (Zig.Enc.encode ((#v[(104 : BitVec 8), (101 : BitVec 8), (108 : BitVec 8), (108 : BitVec 8), (111 : BitVec 8), (44 : BitVec 8), (32 : BitVec 8), (119 : BitVec 8), (111 : BitVec 8), (114 : BitVec 8), (108 : BitVec 8), (100 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 13) : Vector (BitVec 8) 13), 1, .constGlobal),
  -- 2: the name of Color.red
  (Zig.Enc.encode (#v[114, 101, 100, 0] : Vector (BitVec 8) 4), 1, .constGlobal),
  -- 3: the name of Color.green
  (Zig.Enc.encode (#v[103, 114, 101, 101, 110, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 4: the name of Color.blue
  (Zig.Enc.encode (#v[98, 108, 117, 101, 0] : Vector (BitVec 8) 5), 1, .constGlobal),
  -- 5: the name of error.Empty
  (Zig.Enc.encode (#v[69, 109, 112, 116, 121, 0] : Vector (BitVec 8) 6), 1, .constGlobal),
  -- 6: the name of error.TooLong
  (Zig.Enc.encode (#v[84, 111, 111, 76, 111, 110, 103, 0] : Vector (BitVec 8) 8), 1, .constGlobal)]

def Color.tagName (e : Color) : Zig.Result Zig.Slice :=
  match e with
  | .red => pure ⟨⟨some 2, 0⟩, 3⟩
  | .green => pure ⟨⟨some 3, 0⟩, 5⟩
  | .blue => pure ⟨⟨some 4, 0⟩, 4⟩

def errorNameOf (e : Zig.ErrName) : Zig.Result Zig.Slice :=
  if e = "Empty" then pure ⟨⟨some 5, 0⟩, 5⟩ else
  if e = "TooLong" then pure ⟨⟨some 6, 0⟩, 7⟩ else
  throw .unspecified

structure atLocals where
  deriving Inhabited

inductive atExit where
  | ret (v : BitVec 32)

def «at» (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i2 ← Zig.callM (Zig.load (BitVec 32) 4 (p0.elem 4 p1))
    pure (.ret i2)) : Zig.MM atLocals atExit).run' (default : atLocals)
  match e with
  | .ret v => pure v

structure bumpLocals where
  deriving Inhabited

inductive bumpExit where
  | ret (v : BitVec 32)

def bump  : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i0 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    let i1 ← Zig.add false i0 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr) i1
    let i3 ← Zig.load (BitVec 32) 4 (⟨some 0, 0⟩ : Zig.Ptr)
    pure (.ret i3)) : Zig.MM bumpLocals bumpExit).run' (default : bumpLocals)
  match e with
  | .ret v => pure v

structure bumpAtLocals where
  deriving Inhabited

inductive bumpAtExit where
  | ret (v : BitVec 8)
  | br3

def bumpAt (p0 : Zig.Ptr) (p1 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let e ← ((do
    let i2 ← pure (Zig.lt false p1 (4 : BitVec 64))
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .outOfBounds)) : Zig.MM bumpAtLocals bumpAtExit) with
    | .br3 => (do
      let i8 ← pure (p0.elem 1 p1)
      let i9 ← Zig.load (BitVec 8) 1 i8
      let i10 ← pure (Zig.addWrap i9 (1 : BitVec 8))
      Zig.store (α := BitVec 8) 1 i8 i10
      let i12 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 (3 : BitVec 64)))
      pure (.ret i12))
    | e => pure e) : Zig.MM bumpAtLocals bumpAtExit).run' (default : bumpAtLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure clearLocals where
  deriving Inhabited

inductive clearExit where
  | ret

def clear (p0 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let _i1 ← pure p0.len
    Zig.callM (Zig.memset (α := BitVec 16) 2 p0.ptr p0.len none)
    pure .ret) : Zig.MM clearLocals clearExit).run' (default : clearLocals)
  match e with
  | .ret => pure ()

structure colorNameLocals where
  deriving Inhabited

inductive colorNameExit where
  | ret (v : Zig.Slice)
  | br2

def colorName (p0 : Color) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i1 ← pure (Color.isNamed p0)
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .panic)) : Zig.MM colorNameLocals colorNameExit) with
    | .br2 => (do
      let i7 ← Zig.callR (Color.tagName p0)
      let i8 ← pure (i7)
      pure (.ret i8))
    | e => pure e) : Zig.MM colorNameLocals colorNameExit).run' (default : colorNameLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure copyLocals where
  deriving Inhabited

inductive copyExit where
  | ret
  | br5
  | br17

def copy (p0 : Zig.Slice) (p1 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    let i2 ← pure p0.len
    let i3 ← pure p1.len
    let i4 ← pure (i2 == i3)
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .panic)) : Zig.MM copyLocals copyExit) with
    | .br5 => (do
      let i10 ← pure p1.ptr
      let i11 ← pure p0.ptr
      let i12 ← pure (i10.elem 1 i2)
      let i13 ← pure (i11.elem 1 i2)
      let i14 ← Zig.callM (Zig.ptrLe i12 i11)
      let i15 ← Zig.callM (Zig.ptrLe i13 i10)
      let i16 ← pure (i14 || i15)
      match ← ((do
        if i16 then (do
          pure .br17)
        else (do
          throw .panic)) : Zig.MM copyLocals copyExit) with
      | .br17 => (do
        Zig.callM (Zig.memmove 1 1 1 p0.ptr i10 p0.len)
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM copyLocals copyExit).run' (default : copyLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure copyWithinLocals where
  deriving Inhabited

inductive copyWithinExit where
  | ret
  | br9
  | br20
  | br29

def copyWithin (p0 : Zig.Slice) (p1 : BitVec 64) (p2 : BitVec 64) (p3 : BitVec 64) : Zig.MemM (Unit) := do
  let e ← ((do
    let i4 ← pure p0.ptr
    let i5 ← pure (i4.elem 4 p1)
    let i6 ← Zig.add false p1 p3
    let i7 ← pure p0.len
    let i8 ← pure (Zig.le false i6 i7)
    match ← ((do
      if i8 then (do
        pure .br9)
      else (do
        throw .outOfBounds)) : Zig.MM copyWithinLocals copyWithinExit) with
    | .br9 => (do
      let i14 ← pure (⟨i5, p3⟩ : Zig.Slice)
      let i15 ← pure p0.ptr
      let i16 ← pure (i15.elem 4 p2)
      let i17 ← Zig.add false p2 p3
      let i18 ← pure p0.len
      let i19 ← pure (Zig.le false i17 i18)
      match ← ((do
        if i19 then (do
          pure .br20)
        else (do
          throw .outOfBounds)) : Zig.MM copyWithinLocals copyWithinExit) with
      | .br20 => (do
        let i25 ← pure (⟨i16, p3⟩ : Zig.Slice)
        let i26 ← pure i14.len
        let i27 ← pure i25.len
        let i28 ← pure (i26 == i27)
        match ← ((do
          if i28 then (do
            pure .br29)
          else (do
            throw .panic)) : Zig.MM copyWithinLocals copyWithinExit) with
        | .br29 => (do
          let i34 ← pure i25.ptr
          Zig.callM (Zig.memmove 4 4 4 i14.ptr i34 i14.len)
          pure .ret)
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM copyWithinLocals copyWithinExit).run' (default : copyWithinLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure factorialLocals where
  deriving Inhabited

inductive factorialExit where
  | ret (v : BitVec 16)
  | br2

def factorial (p0 : BitVec 64) : Zig.Result (BitVec 16) := do
  let e ← ((do
    let i1 ← pure (Zig.lt false p0 (8 : BitVec 64))
    match ← ((do
      if i1 then (do
        pure .br2)
      else (do
        throw .outOfBounds)) : Zig.M factorialLocals factorialExit) with
    | .br2 => (do
      let i7 ← Zig.call (Zig.vindex (#v[(1 : BitVec 16), (1 : BitVec 16), (2 : BitVec 16), (6 : BitVec 16), (24 : BitVec 16), (120 : BitVec 16), (720 : BitVec 16), (5040 : BitVec 16)] : Vector (BitVec 16) 8) p0)
      pure (.ret i7))
    | e => pure e) : Zig.M factorialLocals factorialExit).run' (default : factorialLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure failNameLocals where
  deriving Inhabited

inductive failNameExit where
  | ret (v : Zig.Slice)
  | br1 (v : Zig.ErrName)

def failName (p0 : BitVec 8) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure (p0 == (0 : BitVec 8))
      if i2 then (do
        pure (.br1 "Empty"))
      else (do
        pure (.br1 "TooLong"))) : Zig.MM failNameLocals failNameExit) with
    | .br1 v1 => (do
      let i6 ← pure (v1)
      let i7 ← Zig.callR (errorNameOf i6)
      let i8 ← pure (i7)
      pure (.ret i8))
    | e => pure e) : Zig.MM failNameLocals failNameExit).run' (default : failNameLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure fillLocals where
  deriving Inhabited

inductive fillExit where
  | ret

def fill (p0 : Zig.Slice) (p1 : BitVec 8) : Zig.MemM (Unit) := do
  let e ← ((do
    let _i2 ← pure p0.len
    Zig.callM (Zig.memset (α := BitVec 8) 1 p0.ptr p0.len (some p1))
    pure .ret) : Zig.MM fillLocals fillExit).run' (default : fillLocals)
  match e with
  | .ret => pure ()

structure indexOfScalarLocals where
  local1 : BitVec 64
  deriving Inhabited

inductive indexOfScalarExit where
  | ret (v : Option (BitVec 64))
  | br11
  | br6
  | br3
  | rep4

def indexOfScalar.again4 : indexOfScalarExit → Bool
  | .rep4 => true
  | _ => false

def indexOfScalar.loop4 (p0 : BitVec 8) : Zig.MM indexOfScalarLocals indexOfScalarExit := do
  let i5 ← pure ((← get).local1)
  match ← ((do
    let i7 ← pure (i5)
    let i8 ← pure (Zig.lt false i7 (12 : BitVec 64))
    if i8 then (do
      let i10 ← Zig.callM (Zig.load (BitVec 8) 1 ((⟨some 1, 0⟩ : Zig.Ptr).elem 1 i5))
      match ← ((do
        let i12 ← pure (i10 == p0)
        if i12 then (do
          let i14 ← pure (some i5)
          pure (.ret i14))
        else (do
          pure .br11)) : Zig.MM indexOfScalarLocals indexOfScalarExit) with
      | .br11 => (do
        pure .br6)
      | e => pure e)
    else (do
      pure .br3)) : Zig.MM indexOfScalarLocals indexOfScalarExit) with
  | .br6 => (do
    let i19 ← Zig.add false i5 (1 : BitVec 64)
    modify (fun s => { s with local1 := i19 })
    pure .rep4)
  | e => pure e

def indexOfScalar (p0 : BitVec 8) : Zig.MemM (Option (BitVec 64)) := do
  let e ← ((do
    modify (fun s => { s with local1 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (indexOfScalar.loop4 p0) indexOfScalar.again4) : Zig.MM indexOfScalarLocals indexOfScalarExit) with
    | .br3 => (do
      pure (.ret none))
    | e => pure e) : Zig.MM indexOfScalarLocals indexOfScalarExit).run' (default : indexOfScalarLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure lenOrLocals where
  deriving Inhabited

inductive lenOrExit where
  | ret (v : BitVec 64)
  | br1 (v : BitVec 64)

def lenOr (p0 : Option (Zig.Slice)) : Zig.MemM (BitVec 64) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure ((p0).isSome)
      if i2 then (do
        let i4 ← Zig.optPayload p0
        let i5 ← pure i4.len
        pure (.br1 i5))
      else (do
        pure (.br1 (0 : BitVec 64)))) : Zig.MM lenOrLocals lenOrExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.MM lenOrLocals lenOrExit).run' (default : lenOrLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure localArrLocals where
  a : Zig.Ptr
  deriving Inhabited

inductive localArrExit where
  | ret (v : BitVec 8)
  | br5

def localArr (p0 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 4 1
  let e ← ((do
    let i1 ← pure (← get).a
    Zig.store (α := Vector (BitVec 8) 4) 1 i1 (#v[(1 : BitVec 8), (2 : BitVec 8), (3 : BitVec 8), (4 : BitVec 8)] : Vector (BitVec 8) 4)
    let i3 ← Zig.rem false p0 (4 : BitVec 64)
    let i4 ← pure (Zig.lt false i3 (4 : BitVec 64))
    match ← ((do
      if i4 then (do
        pure .br5)
      else (do
        throw .outOfBounds)) : Zig.MM localArrLocals localArrExit) with
    | .br5 => (do
      let i10 ← pure (i1.elem 1 i3)
      let i11 ← Zig.load (BitVec 8) 1 i10
      let i12 ← Zig.add false i11 (1 : BitVec 8)
      Zig.store (α := BitVec 8) 1 i10 i12
      let i14 ← Zig.callM (Zig.load (BitVec 8) 1 (i1.elem 1 (0 : BitVec 64)))
      let i15 ← Zig.callM (Zig.load (BitVec 8) 1 (i1.elem 1 (3 : BitVec 64)))
      let i16 ← Zig.add false i14 i15
      pure (.ret i16))
    | e => pure e) : Zig.MM localArrLocals localArrExit).run' { (default : localArrLocals) with a := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure prevItemLocals where
  deriving Inhabited

inductive prevItemExit where
  | ret (v : BitVec 32)

def prevItem (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0.elem 4 (2 : BitVec 64))
    let i2 ← pure (i1.elemSub 4 (1 : BitVec 64))
    let i3 ← Zig.callM (Zig.load (BitVec 32) 4 (i2.elem 4 (0 : BitVec 64)))
    pure (.ret i3)) : Zig.MM prevItemLocals prevItemExit).run' (default : prevItemLocals)
  match e with
  | .ret v => pure v

structure reverseLocals where
  i : BitVec 64
  j : BitVec 64
  deriving Inhabited

inductive reverseExit where
  | ret
  | br1
  | br27
  | br36
  | br45
  | br55
  | br23
  | br16
  | br14
  | rep15

def reverse.again15 : reverseExit → Bool
  | .rep15 => true
  | _ => false

def reverse.loop15 (p0 : Zig.Slice) : Zig.MM reverseLocals reverseExit := do
  match ← ((do
    let i17 ← pure ((← get).i)
    let i18 ← pure ((← get).j)
    let i19 ← pure (i17)
    let i20 ← pure (i18)
    let i21 ← pure (Zig.lt false i19 i20)
    if i21 then (do
      match ← ((do
        let i24 ← pure ((← get).i)
        let i25 ← pure p0.len
        let i26 ← pure (Zig.lt false i24 i25)
        match ← ((do
          if i26 then (do
            pure .br27)
          else (do
            throw .outOfBounds)) : Zig.MM reverseLocals reverseExit) with
        | .br27 => (do
          let i32 ← Zig.callM (Zig.load (BitVec 32) 4 (p0.ptr.elem 4 i24))
          let i33 ← pure ((← get).i)
          let i34 ← pure p0.len
          let i35 ← pure (Zig.lt false i33 i34)
          match ← ((do
            if i35 then (do
              pure .br36)
            else (do
              throw .outOfBounds)) : Zig.MM reverseLocals reverseExit) with
          | .br36 => (do
            let i41 ← pure (p0.ptr.elem 4 i33)
            let i42 ← pure ((← get).j)
            let i43 ← pure p0.len
            let i44 ← pure (Zig.lt false i42 i43)
            match ← ((do
              if i44 then (do
                pure .br45)
              else (do
                throw .outOfBounds)) : Zig.MM reverseLocals reverseExit) with
            | .br45 => (do
              let i50 ← Zig.callM (Zig.load (BitVec 32) 4 (p0.ptr.elem 4 i42))
              Zig.store (α := BitVec 32) 4 i41 i50
              let i52 ← pure ((← get).j)
              let i53 ← pure p0.len
              let i54 ← pure (Zig.lt false i52 i53)
              match ← ((do
                if i54 then (do
                  pure .br55)
                else (do
                  throw .outOfBounds)) : Zig.MM reverseLocals reverseExit) with
              | .br55 => (do
                let i60 ← pure (p0.ptr.elem 4 i52)
                Zig.store (α := BitVec 32) 4 i60 i32
                pure .br23)
              | e => pure e)
            | e => pure e)
          | e => pure e)
        | e => pure e) : Zig.MM reverseLocals reverseExit) with
      | .br23 => (do
        let i63 ← pure ((← get).i)
        let i64 ← Zig.add false i63 (1 : BitVec 64)
        modify (fun s => { s with i := i64 })
        let i66 ← pure ((← get).j)
        let i67 ← Zig.sub false i66 (1 : BitVec 64)
        modify (fun s => { s with j := i67 })
        pure .br16)
      | e => pure e)
    else (do
      pure .br14)) : Zig.MM reverseLocals reverseExit) with
  | .br16 => (do
    pure .rep15)
  | e => pure e

def reverse (p0 : Zig.Slice) : Zig.MemM (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0.len
      let i3 ← pure (i2)
      let i4 ← pure (i3 == (0 : BitVec 64))
      if i4 then (do
        pure .ret)
      else (do
        pure .br1)) : Zig.MM reverseLocals reverseExit) with
    | .br1 => (do
      modify (fun s => { s with i := (0 : BitVec 64) })
      let i11 ← pure p0.len
      let i12 ← Zig.sub false i11 (1 : BitVec 64)
      modify (fun s => { s with j := i12 })
      match ← ((do
        Zig.loop (reverse.loop15 p0) reverse.again15) : Zig.MM reverseLocals reverseExit) with
      | .br14 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.MM reverseLocals reverseExit).run' (default : reverseLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

structure secondLocals where
  deriving Inhabited

inductive secondExit where
  | ret (v : BitVec 32)

def second (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (p0.elem 4 (1 : BitVec 64))
    let i2 ← Zig.callM (Zig.load (BitVec 32) 4 (i1.elem 4 (0 : BitVec 64)))
    pure (.ret i2)) : Zig.MM secondLocals secondExit).run' (default : secondLocals)
  match e with
  | .ret v => pure v

structure sentinelArrLocals where
  x : Zig.Ptr
  deriving Inhabited

inductive sentinelArrExit where
  | ret (v : BitVec 8)
  | br17

def sentinelArr (p0 : BitVec 64) : Zig.MemM (BitVec 8) := do
  let s1 ← Zig.allocStack 5 1
  let e ← ((do
    let i1 ← pure (← get).x
    let i2 ← pure (i1.add 0)
    let i3 ← pure (i2.elem 1 (0 : BitVec 64))
    let i4 ← pure (Zig.trunc 8 p0)
    Zig.store (α := BitVec 8) 1 i3 i4
    let i6 ← pure (i2.elem 1 (1 : BitVec 64))
    Zig.store (α := BitVec 8) 1 i6 (2 : BitVec 8)
    let i8 ← pure (i2.elem 1 (2 : BitVec 64))
    Zig.store (α := BitVec 8) 1 i8 (3 : BitVec 8)
    let i10 ← pure (i2.elem 1 (3 : BitVec 64))
    Zig.store (α := BitVec 8) 1 i10 (0 : BitVec 8)
    let i12 ← pure (i1.add 4)
    Zig.store (α := BitVec 8) 1 i12 (7 : BitVec 8)
    let i14 ← Zig.load (Tag) 1 i1
    let i15 ← pure ((i14).name)
    let i16 ← pure (Zig.le false p0 (3 : BitVec 64))
    match ← ((do
      if i16 then (do
        pure .br17)
      else (do
        throw .outOfBounds)) : Zig.MM sentinelArrLocals sentinelArrExit) with
    | .br17 => (do
      let i22 ← Zig.callR (Zig.vindex i15 p0)
      let i23 ← Zig.callR (Zig.vindex (#v[(120 : BitVec 8), (121 : BitVec 8), (122 : BitVec 8), (0 : BitVec 8)] : Vector (BitVec 8) 4) p0)
      let i24 ← pure (Zig.addWrap i22 i23)
      let i25 ← pure ((i14).n)
      let i26 ← pure (Zig.addWrap i24 i25)
      pure (.ret i26))
    | e => pure e) : Zig.MM sentinelArrLocals sentinelArrExit).run' { (default : sentinelArrLocals) with x := s1 }
  Zig.free s1
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure subZLocals where
  deriving Inhabited

inductive subZExit where
  | ret (v : Zig.Slice)
  | br6
  | br15
  | br23

def subZ (p0 : Zig.Slice) (p1 : BitVec 64) (p2 : BitVec 64) : Zig.MemM (Zig.Slice) := do
  let e ← ((do
    let i3 ← pure p0.ptr
    let i4 ← pure (i3.elem 1 p1)
    let i5 ← pure (Zig.le false p1 p2)
    match ← ((do
      if i5 then (do
        pure .br6)
      else (do
        throw .outOfBounds)) : Zig.MM subZLocals subZExit) with
    | .br6 => (do
      let i11 ← Zig.sub false p2 p1
      let i12 ← pure p0.len
      let i13 ← Zig.add false p2 (1 : BitVec 64)
      let i14 ← pure (Zig.le false i13 i12)
      match ← ((do
        if i14 then (do
          pure .br15)
        else (do
          throw .outOfBounds)) : Zig.MM subZLocals subZExit) with
      | .br15 => (do
        let i20 ← pure (⟨i4, i11⟩ : Zig.Slice)
        let i21 ← Zig.callM (Zig.load (BitVec 8) 1 (i20.ptr.elem 1 i11))
        let i22 ← pure ((0 : BitVec 8) == i21)
        match ← ((do
          if i22 then (do
            pure .br23)
          else (do
            throw .panic)) : Zig.MM subZLocals subZExit) with
        | .br23 => (do
          pure (.ret i20))
        | e => pure e)
      | e => pure e)
    | e => pure e) : Zig.MM subZLocals subZExit).run' (default : subZLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumSliceLocals where
  t : BitVec 32
  local3 : BitVec 64
  deriving Inhabited

inductive sumSliceExit where
  | ret (v : BitVec 32)
  | br9
  | br6
  | rep7

def sumSlice.again7 : sumSliceExit → Bool
  | .rep7 => true
  | _ => false

def sumSlice.loop7 (p0 : Array (BitVec 32)) (i5 : BitVec 64) : Zig.M sumSliceLocals sumSliceExit := do
  let i8 ← pure ((← get).local3)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (i5)
    let i12 ← pure (Zig.lt false i10 i11)
    if i12 then (do
      let i14 ← Zig.call (Zig.index p0 i8)
      let i15 ← pure ((← get).t)
      let i16 ← Zig.add false i15 i14
      modify (fun s => { s with t := i16 })
      pure .br9)
    else (do
      pure .br6)) : Zig.M sumSliceLocals sumSliceExit) with
  | .br9 => (do
    let i20 ← Zig.add false i8 (1 : BitVec 64)
    modify (fun s => { s with local3 := i20 })
    pure .rep7)
  | e => pure e

def sumSlice (p0 : Array (BitVec 32)) : Zig.Result (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with t := (0 : BitVec 32) })
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    let i5 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (sumSlice.loop7 p0 i5) sumSlice.again7) : Zig.M sumSliceLocals sumSliceExit) with
    | .br6 => (do
      let i23 ← pure ((← get).t)
      pure (.ret i23))
    | e => pure e) : Zig.M sumSliceLocals sumSliceExit).run' (default : sumSliceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumMidLocals where
  deriving Inhabited

inductive sumMidExit where
  | ret (v : BitVec 32)
  | br6
  | br14

def sumMid (p0 : Zig.Slice) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← pure p0.len
    let i2 ← Zig.sub false i1 (1 : BitVec 64)
    let i3 ← pure p0.ptr
    let i4 ← pure (i3.elem 4 (1 : BitVec 64))
    let i5 ← pure (Zig.le false (1 : BitVec 64) i2)
    match ← ((do
      if i5 then (do
        pure .br6)
      else (do
        throw .outOfBounds)) : Zig.MM sumMidLocals sumMidExit) with
    | .br6 => (do
      let i11 ← Zig.sub false i2 (1 : BitVec 64)
      let i12 ← pure p0.len
      let i13 ← pure (Zig.le false i2 i12)
      match ← ((do
        if i13 then (do
          pure .br14)
        else (do
          throw .outOfBounds)) : Zig.MM sumMidLocals sumMidExit) with
      | .br14 => (do
        let i19 ← pure (⟨i4, i11⟩ : Zig.Slice)
        let i20 ← pure (i19)
        let i21 ← Zig.callR (sumSlice (← Zig.callM (Zig.readSlice (BitVec 32) 4 i20)))
        pure (.ret i21))
      | e => pure e)
    | e => pure e) : Zig.MM sumMidLocals sumMidExit).run' (default : sumMidLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure sumZLocals where
  sum : BitVec 32
  i : BitVec 64
  deriving Inhabited

inductive sumZExit where
  | ret (v : BitVec 32)
  | br7
  | br5
  | rep6

def sumZ.again6 : sumZExit → Bool
  | .rep6 => true
  | _ => false

def sumZ.loop6 (p0 : Zig.Ptr) : Zig.MM sumZLocals sumZExit := do
  match ← ((do
    let i8 ← pure ((← get).i)
    let i9 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i8))
    let i10 ← pure (i9 != (0 : BitVec 8))
    if i10 then (do
      let i12 ← pure ((← get).sum)
      let i13 ← pure ((← get).i)
      let i14 ← Zig.callM (Zig.load (BitVec 8) 1 (p0.elem 1 i13))
      let i15 ← Zig.intCast false false 32 i14
      let i16 ← Zig.add false i12 i15
      modify (fun s => { s with sum := i16 })
      let i18 ← pure ((← get).i)
      let i19 ← Zig.add false i18 (1 : BitVec 64)
      modify (fun s => { s with i := i19 })
      pure .br7)
    else (do
      pure .br5)) : Zig.MM sumZLocals sumZExit) with
  | .br7 => (do
    pure .rep6)
  | e => pure e

def sumZ (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    modify (fun s => { s with sum := (0 : BitVec 32) })
    modify (fun s => { s with i := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (sumZ.loop6 p0) sumZ.again6) : Zig.MM sumZLocals sumZExit) with
    | .br5 => (do
      let i24 ← pure ((← get).sum)
      pure (.ret i24))
    | e => pure e) : Zig.MM sumZLocals sumZExit).run' (default : sumZLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure totalLocals where
  deriving Inhabited

inductive totalExit where
  | ret (v : BitVec 32)

def total (p0 : Zig.Ptr) : Zig.MemM (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (⟨p0, (3 : BitVec 64)⟩ : Zig.Slice)
    let i2 ← Zig.callR (sumSlice (← Zig.callM (Zig.readSlice (BitVec 32) 4 i1)))
    pure (.ret i2)) : Zig.MM totalLocals totalExit).run' (default : totalLocals)
  match e with
  | .ret v => pure v

end Slices