import Lean.Elab.Deriving.ToExpr
import Air2Lean.Program

/-!
# Complete source-program terms

Certificates retain the complete original program, including instructions outside their
proof fragment. Constructor quotation follows the source datatypes automatically: adding
a field or an operation cannot silently substitute a default body or omit a graph edge.
The native printer is part of the existing translation correspondence trust boundary;
the resulting term and the canonically derived policy are checked by Lean.
-/

namespace Air2Lean.Reify

open Lean

deriving instance ToExpr for ZigVersion
deriving instance ToExpr for Endian
deriving instance ToExpr for Dialect
deriving instance ToExpr for AllocatorModel
deriving instance ToExpr for Ty
deriving instance ToExpr for Val
deriving instance ToExpr for ReduceOp
deriving instance ToExpr for ShuffleLane
deriving instance ToExpr for AsmOperand
deriving instance ToExpr for Mode
deriving instance ToExpr for ArithOp
deriving instance ToExpr for DivOp
deriving instance ToExpr for BitOp
deriving instance ToExpr for BitCountOp
deriving instance ToExpr for BitPermuteOp
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for CmpOp
deriving instance ToExpr for FloatRoundOp
deriving instance ToExpr for LibmOp
deriving instance ToExpr for AtomicOrder
deriving instance ToExpr for RmwOp

deriving instance ToExpr for Op, SwitchCase, Inst
deriving instance ToExpr for Layout
deriving instance ToExpr for Global
deriving instance ToExpr for Identity.Record
deriving instance ToExpr for ExternDecl
deriving instance ToExpr for ExportDecl
deriving instance ToExpr for Func
deriving instance ToExpr for BuildProfile
deriving instance ToExpr for ModelFootprint
deriving instance ToExpr for ExternBinding
deriving instance ToExpr for JsonNumber

/-- JSON objects are quoted through their complete key/value contents, independently of
the parser's balanced-tree representation. No key or value is discarded. -/
private partial def jsonExpr (j : Json) : Expr :=
  let _ : ToExpr Json := { toExpr := jsonExpr, toTypeExpr := mkConst ``Json }
  match j with
  | .null => mkConst ``Json.null
  | .bool b => mkApp (mkConst ``Json.bool) (toExpr b)
  | .num n => mkApp (mkConst ``Json.num) (toExpr n)
  | .str s => mkApp (mkConst ``Json.str) (toExpr s)
  | .arr xs => mkApp (mkConst ``Json.arr) (toExpr xs)
  | .obj xs => mkApp (mkConst ``Json.mkObj) (toExpr xs.toList)

private instance : ToExpr Json where
  toExpr := jsonExpr
  toTypeExpr := mkConst ``Json

deriving instance ToExpr for ModelBinding

/-- Render constructor quotations with all term arguments explicit. The quotation API
supplies constructors, applications and literals; any unexpected expression is rejected,
not replaced by an inhabited value. Universe arguments are inferred from the explicit
types and values supplied by `ToExpr`. -/
private def term : Expr → Except String String
  | .const n _ => pure ("@_root_." ++ n.toString)
  | .app f a => return "(" ++ (← term f) ++ " " ++ (← term a) ++ ")"
  | .lit (.natVal n) => pure (toString n)
  | .lit (.strVal s) => pure s.quote
  | .mdata _ e => term e
  | _ => throw "source-program quotation produced a non-constructor expression"

/-- Every field and instruction of an original function, including outside the semantic
certificate fragment. -/
def func (f : Func) : Except String String := term (toExpr f)

/-- Complete validated model bindings from the same translation invocation. Their symbol
projection participates in the canonical memory analysis, rather than a separate list of
policy flags supplied by a certificate. -/
def models (ms : Array ModelBinding) : Except String String := term (toExpr ms)

end Air2Lean.Reify
