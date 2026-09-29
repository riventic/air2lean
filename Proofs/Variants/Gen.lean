import ZigLean


namespace Variants

inductive ShapeTag where
  | circle
  | rect
  | square
  | empty
  deriving Repr, Inhabited, DecidableEq

def ShapeTag.toBits : ShapeTag → BitVec 2
  | .circle => (0 : BitVec 2)
  | .rect => (1 : BitVec 2)
  | .square => (2 : BitVec 2)
  | .empty => (3 : BitVec 2)

def ShapeTag.ofInt? (v : Int) : Option ShapeTag :=
  if v = 0 then Option.some .circle else if v = 1 then Option.some .rect else if v = 2 then Option.some .square else if v = 3 then Option.some .empty else Option.none

def ShapeTag.isNamed (_ : ShapeTag) : Bool := true

structure Rect where
  w : BitVec 32
  h : BitVec 32
  deriving Repr, Inhabited, DecidableEq

inductive Shape where
  | circle (v : BitVec 32)
  | rect (v : Rect)
  | square (v : BitVec 32)
  | empty
  deriving Repr, Inhabited, DecidableEq

def Shape.tag : Shape → ShapeTag
  | .circle _ => .circle
  | .rect _ => .rect
  | .square _ => .square
  | .empty => .empty

def Shape.get_circle : Shape → Zig.Result (BitVec 32)
  | .circle v => pure v
  | _ => throw .panic

def Shape.modify_circle (g : BitVec 32 → BitVec 32) : Shape → Shape
  | .circle v => .circle (g v)
  | _ => .circle (g default)

def Shape.setTag_circle : Shape → Shape
  | .circle v => .circle v
  | _ => .circle default

def Shape.get_rect : Shape → Zig.Result (Rect)
  | .rect v => pure v
  | _ => throw .panic

def Shape.modify_rect (g : Rect → Rect) : Shape → Shape
  | .rect v => .rect (g v)
  | _ => .rect (g default)

def Shape.setTag_rect : Shape → Shape
  | .rect v => .rect v
  | _ => .rect default

def Shape.get_square : Shape → Zig.Result (BitVec 32)
  | .square v => pure v
  | _ => throw .panic

def Shape.modify_square (g : BitVec 32 → BitVec 32) : Shape → Shape
  | .square v => .square (g v)
  | _ => .square (g default)

def Shape.setTag_square : Shape → Shape
  | .square v => .square v
  | _ => .square default

def Shape.get_empty : Shape → Zig.Result (Unit)
  | .empty => pure ()
  | _ => throw .panic

def Shape.modify_empty (_g : Unit → Unit) : Shape → Shape
  | .empty => .empty
  | _ => .empty

def Shape.setTag_empty : Shape → Shape
  | .empty => .empty
  | _ => .empty

inductive Prio where
  | low
  | mid
  | high
  deriving Repr, Inhabited, DecidableEq

def Prio.toBits : Prio → BitVec 8
  | .low => (-(1 : BitVec 8))
  | .mid => (0 : BitVec 8)
  | .high => (5 : BitVec 8)

def Prio.ofInt? (v : Int) : Option Prio :=
  if v = -1 then Option.some .low else if v = 0 then Option.some .mid else if v = 5 then Option.some .high else Option.none

def Prio.isNamed (_ : Prio) : Bool := true

inductive Light where
  | red
  | yellow
  | green
  deriving Repr, Inhabited, DecidableEq

def Light.toBits : Light → BitVec 8
  | .red => (0 : BitVec 8)
  | .yellow => (1 : BitVec 8)
  | .green => (2 : BitVec 8)

def Light.ofInt? (v : Int) : Option Light :=
  if v = 0 then Option.some .red else if v = 1 then Option.some .yellow else if v = 2 then Option.some .green else Option.none

def Light.isNamed (_ : Light) : Bool := true

structure Code where
  bits : BitVec 8
  deriving Repr, Inhabited, DecidableEq

def Code.ok : Code := ⟨(0 : BitVec 8)⟩
def Code.warn : Code := ⟨(1 : BitVec 8)⟩

def Code.toBits (e : Code) : BitVec 8 := e.bits

def Code.ofInt? (v : Int) : Option Code :=
  if 0 ≤ v ∧ v ≤ 255 then Option.some ⟨BitVec.ofInt 8 v⟩ else Option.none

def Code.isNamed (e : Code) : Bool := e.bits == (0 : BitVec 8) || e.bits == (1 : BitVec 8)

structure nextLocals where
  deriving Inhabited

inductive nextExit where
  | ret (v : Light)
  | br1 (v : Light)

def next (p0 : Light) : Zig.Result (Light) := do
  let e ← ((do
    match ← ((do
      match p0 with
      | .red => (do
        pure (.br1 Light.green))
      | .green => (do
        pure (.br1 Light.yellow))
      | .yellow => (do
        pure (.br1 Light.red))) : Zig.M nextLocals nextExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.M nextLocals nextExit).run' (default : nextLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure advanceLocals where
  cur : Light
  i : BitVec 32
  deriving Inhabited

inductive advanceExit where
  | ret (v : Light)
  | br8
  | br6
  | rep7

def advance.again7 : advanceExit → Bool
  | .rep7 => true
  | _ => false

def advance.loop7 (p1 : BitVec 32) : Zig.M advanceLocals advanceExit := do
  match ← ((do
    let i9 ← pure ((← get).i)
    let i10 ← pure (Zig.lt false i9 p1)
    if i10 then (do
      let i12 ← pure ((← get).cur)
      let i13 ← Zig.call (next i12)
      modify (fun s => { s with cur := i13 })
      let i15 ← pure ((← get).i)
      let i16 ← Zig.add false i15 (1 : BitVec 32)
      modify (fun s => { s with i := i16 })
      pure .br8)
    else (do
      pure .br6)) : Zig.M advanceLocals advanceExit) with
  | .br8 => (do
    pure .rep7)
  | e => pure e

def advance (p0 : Light) (p1 : BitVec 32) : Zig.Result (Light) := do
  let e ← ((do
    modify (fun s => { s with cur := p0 })
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (advance.loop7 p1) advance.again7) : Zig.M advanceLocals advanceExit) with
    | .br6 => (do
      let i21 ← pure ((← get).cur)
      pure (.ret i21))
    | e => pure e) : Zig.M advanceLocals advanceExit).run' (default : advanceLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure areaLocals where
  deriving Inhabited

inductive areaExit where
  | ret (v : BitVec 64)
  | br2 (v : BitVec 64)

def area (p0 : Shape) : Zig.Result (BitVec 64) := do
  let e ← ((do
    let i1 ← pure (Shape.tag p0)
    match ← ((do
      match i1 with
      | .circle => (do
        let i6 ← Zig.call (Shape.get_circle p0)
        let i7 ← Zig.intCast false false 64 i6
        let i8 ← Zig.mul false (3 : BitVec 64) i7
        let i9 ← Zig.intCast false false 64 i6
        let i10 ← Zig.mul false i8 i9
        pure (.br2 i10))
      | .rect => (do
        let i12 ← Zig.call (Shape.get_rect p0)
        let i13 ← pure ((i12).w)
        let i14 ← Zig.intCast false false 64 i13
        let i15 ← pure ((i12).h)
        let i16 ← Zig.intCast false false 64 i15
        let i17 ← Zig.mul false i14 i16
        pure (.br2 i17))
      | .square => (do
        let i19 ← Zig.call (Shape.get_square p0)
        let i20 ← Zig.intCast false false 64 i19
        let i21 ← Zig.intCast false false 64 i19
        let i22 ← Zig.mul false i20 i21
        pure (.br2 i22))
      | .empty => (do
        pure (.br2 (0 : BitVec 64)))) : Zig.M areaLocals areaExit) with
    | .br2 v2 => (do
      pure (.ret v2))
    | e => pure e) : Zig.M areaLocals areaExit).run' (default : areaLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure codeOfLocals where
  deriving Inhabited

inductive codeOfExit where
  | ret (v : Code)

def codeOf (p0 : BitVec 8) : Zig.Result (Code) := do
  let e ← ((do
    let i1 ← Zig.enumOf (Code.ofInt? (Zig.val false p0))
    pure (.ret i1)) : Zig.M codeOfLocals codeOfExit).run' (default : codeOfLocals)
  match e with
  | .ret v => pure v

structure isRoundLocals where
  deriving Inhabited

inductive isRoundExit where
  | ret (v : Bool)

def isRound (p0 : Shape) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (Shape.tag p0)
    let i2 ← pure (i1 == ShapeTag.circle)
    pure (.ret i2)) : Zig.M isRoundLocals isRoundExit).run' (default : isRoundLocals)
  match e with
  | .ret v => pure v

structure isUrgentLocals where
  deriving Inhabited

inductive isUrgentExit where
  | ret (v : Bool)

def isUrgent (p0 : Prio) : Zig.Result (Bool) := do
  let e ← ((do
    let i1 ← pure (p0 == Prio.high)
    pure (.ret i1)) : Zig.M isUrgentLocals isUrgentExit).run' (default : isUrgentLocals)
  match e with
  | .ret v => pure v

structure lightOfLocals where
  deriving Inhabited

inductive lightOfExit where
  | ret (v : Light)

def lightOf (p0 : BitVec 8) : Zig.Result (Light) := do
  let e ← ((do
    let i1 ← Zig.enumOf (Light.ofInt? (Zig.val false p0))
    pure (.ret i1)) : Zig.M lightOfLocals lightOfExit).run' (default : lightOfLocals)
  match e with
  | .ret v => pure v

structure prioValueLocals where
  deriving Inhabited

inductive prioValueExit where
  | ret (v : BitVec 8)

def prioValue (p0 : Prio) : Zig.Result (BitVec 8) := do
  let e ← ((do
    let i1 ← pure (Prio.toBits p0)
    pure (.ret i1)) : Zig.M prioValueLocals prioValueExit).run' (default : prioValueLocals)
  match e with
  | .ret v => pure v

structure radiusLocals where
  deriving Inhabited

inductive radiusExit where
  | ret (v : BitVec 32)
  | br3

def radius (p0 : Shape) : Zig.Result (BitVec 32) := do
  let e ← ((do
    let i1 ← pure (Shape.tag p0)
    let i2 ← pure (i1 == ShapeTag.circle)
    match ← ((do
      if i2 then (do
        pure .br3)
      else (do
        throw .panic)) : Zig.M radiusLocals radiusExit) with
    | .br3 => (do
      let i8 ← Zig.call (Shape.get_circle p0)
      pure (.ret i8))
    | e => pure e) : Zig.M radiusLocals radiusExit).run' (default : radiusLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure scaleLocals where
  local2 : Shape
  deriving Inhabited

inductive scaleExit where
  | ret (v : Shape)
  | br4

def scale (p0 : Shape) (p1 : BitVec 32) : Zig.Result (Shape) := do
  let e ← ((do
    let i3 ← pure (Shape.tag p0)
    match ← ((do
      match i3 with
      | .circle => (do
        let i8 ← Zig.call (Shape.get_circle p0)
        modify (fun s => { s with local2 := (Shape.setTag_circle s.local2) })
        let i11 ← Zig.mul false i8 p1
        modify (fun s => { s with local2 := (Shape.modify_circle (fun _ => i11) s.local2) })
        pure .br4)
      | .rect => (do
        let i14 ← Zig.call (Shape.get_rect p0)
        modify (fun s => { s with local2 := (Shape.setTag_rect s.local2) })
        let i18 ← pure ((i14).w)
        let i19 ← Zig.mul false i18 p1
        modify (fun s => { s with local2 := (Shape.modify_rect (fun x => { x with w := i19 }) s.local2) })
        let i22 ← pure ((i14).h)
        let i23 ← Zig.mul false i22 p1
        modify (fun s => { s with local2 := (Shape.modify_rect (fun x => { x with h := i23 }) s.local2) })
        pure .br4)
      | .square => (do
        let i26 ← Zig.call (Shape.get_square p0)
        modify (fun s => { s with local2 := (Shape.setTag_square s.local2) })
        let i29 ← Zig.mul false i26 p1
        modify (fun s => { s with local2 := (Shape.modify_square (fun _ => i29) s.local2) })
        pure .br4)
      | .empty => (do
        modify (fun s => { s with local2 := Shape.empty })
        pure .br4)) : Zig.M scaleLocals scaleExit) with
    | .br4 => (do
      let _i34 ← pure ((← get).local2)
      pure (.ret (← get).local2))
    | e => pure e) : Zig.M scaleLocals scaleExit).run' (default : scaleLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure severityLocals where
  deriving Inhabited

inductive severityExit where
  | ret (v : BitVec 8)
  | br1 (v : BitVec 8)

def severity (p0 : Code) : Zig.Result (BitVec 8) := do
  let e ← ((do
    match ← ((do
      if p0 == Code.ok then (do
        pure (.br1 (0 : BitVec 8)))
      else (do
        if p0 == Code.warn then (do
          pure (.br1 (1 : BitVec 8)))
        else (do
          pure (.br1 (2 : BitVec 8))))) : Zig.M severityLocals severityExit) with
    | .br1 v1 => (do
      pure (.ret v1))
    | e => pure e) : Zig.M severityLocals severityExit).run' (default : severityLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

structure totalAreaLocals where
  total : BitVec 64
  local3 : BitVec 64
  deriving Inhabited

inductive totalAreaExit where
  | ret (v : BitVec 64)
  | br9
  | br6
  | rep7

def totalArea.again7 : totalAreaExit → Bool
  | .rep7 => true
  | _ => false

def totalArea.loop7 (p0 : Array (Shape)) (i5 : BitVec 64) : Zig.M totalAreaLocals totalAreaExit := do
  let i8 ← pure ((← get).local3)
  match ← ((do
    let i10 ← pure (i8)
    let i11 ← pure (i5)
    let i12 ← pure (Zig.lt false i10 i11)
    if i12 then (do
      let i14 ← Zig.call (Zig.index p0 i8)
      let i15 ← pure ((← get).total)
      let i16 ← Zig.call (area i14)
      let i17 ← Zig.add false i15 i16
      modify (fun s => { s with total := i17 })
      pure .br9)
    else (do
      pure .br6)) : Zig.M totalAreaLocals totalAreaExit) with
  | .br9 => (do
    let i21 ← Zig.add false i8 (1 : BitVec 64)
    modify (fun s => { s with local3 := i21 })
    pure .rep7)
  | e => pure e

def totalArea (p0 : Array (Shape)) : Zig.Result (BitVec 64) := do
  let e ← ((do
    modify (fun s => { s with total := (0 : BitVec 64) })
    modify (fun s => { s with local3 := (0 : BitVec 64) })
    let i5 ← pure (Zig.len p0)
    match ← ((do
      Zig.loop (totalArea.loop7 p0 i5) totalArea.again7) : Zig.M totalAreaLocals totalAreaExit) with
    | .br6 => (do
      let i24 ← pure ((← get).total)
      pure (.ret i24))
    | e => pure e) : Zig.M totalAreaLocals totalAreaExit).run' (default : totalAreaLocals)
  match e with
  | .ret v => pure v
  | _ => throw .panic

end Variants