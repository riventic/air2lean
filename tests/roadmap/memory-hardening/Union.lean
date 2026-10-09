import Proofs.Variants.Gen
import Proofs.Layout.Gen

/-! MM-13 regression: a retag of a tagged union held as a Lean value leaves the new payload
undefined (`undef_f`), as Zig does, instead of `default` (0). A read before the payload is
defined is `.unspecified`; a whole-payload write (`set_f`) or a write of every field of a
struct payload (`setField_f`) defines it. -/

open Zig Variants

-- Retag circle → rect: the rect payload is undefined, not `{ w := 0, h := 0 }`.
example : Shape.get_rect (Shape.setTag_rect (.circle 1)) = throw .unspecified := rfl
-- The tag is the new one.
example : (Shape.setTag_rect (.circle 1)).tag = .rect := rfl
-- Writing one field of the struct payload leaves the other undefined.
example : Shape.get_rect (Shape.setField_rect "w" (fun x => { x with w := 5 })
    (Shape.setTag_rect (.circle 1))) = throw .unspecified := by
  simp [Shape.setField_rect, Shape.setTag_rect, Shape.get_rect]
-- Writing every field defines the payload.
example : Shape.get_rect (Shape.setField_rect "h" (fun x => { x with h := 7 })
    (Shape.setField_rect "w" (fun x => { x with w := 5 }) (Shape.setTag_rect (.circle 1)))) =
    pure { w := 5, h := 7 } := by
  simp [Shape.setField_rect, Shape.setTag_rect, Shape.get_rect]
-- A whole-payload write defines a scalar payload.
example : Shape.get_square (Shape.set_square 3 (Shape.setTag_square (.circle 1))) = pure 3 := rfl
-- A retag to the active field keeps its payload; reading an inactive field still panics.
example : Shape.get_circle (Shape.setTag_circle (.circle 1)) = pure 1 := rfl
example : Shape.get_circle (Shape.setTag_rect (.circle 1)) = throw .panic := rfl

-- In memory, an undefined payload is undefined bytes: decoding it is `.unspecified`.
#guard ((Enc.decode (Enc.encode (Layout.Num.setTag_small (.int 1))) : Result Layout.Num).run ==
  some (.error .unspecified))
#guard ((Enc.decode (Enc.encode (Layout.Num.small 3)) : Result Layout.Num).run ==
  some (.ok (.small 3)))
