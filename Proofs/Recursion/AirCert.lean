-- air2lean AIR semantics certificate (docs/air-semantics.md). Generated; do not edit.
import Air2Lean.Sem
import Proofs.Recursion.Gen

set_option linter.unusedSimpArgs false

namespace Recursion.AirCert

open Air2Lean Air2Lean.Sem

/-! Certified: `recursion.fact`, `recursion.gcd`, `recursion.isEven`, `recursion.isOdd`

Outside the certificate fragment:

(none)
-/

def source_0 : _root_.Air2Lean.Func :=
(@_root_.Air2Lean.Func.mk (@_root_.Air2Lean.Dialect.mk @_root_.Air2Lean.ZigVersion.v0_15_2 "" "" (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) @_root_.Air2Lean.Endian.little (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 16) (@_root_.instOfNatNat (nat_lit 16))) "unverified" "unverified" @_root_.Bool.false) "recursion.fact" (@_root_.List.toArray @_root_.Nat (@_root_.List.cons @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.nil @_root_.Nat))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arg (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 10) (@_root_.instOfNatNat (nat_lit 10))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.block (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.cmp @_root_.Air2Lean.CmpOp.eq (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 0) (@_root_.instOfNat (nat_lit 0)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.condBr (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 11) (@_root_.instOfNatNat (nat_lit 11))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 1) (@_root_.instOfNat (nat_lit 1)))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 5) (@_root_.instOfNatNat (nat_lit 5))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.br (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) @_root_.Air2Lean.Val.void)) (@_root_.List.nil @_root_.Air2Lean.Inst))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 12) (@_root_.instOfNatNat (nat_lit 12))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arith @_root_.Air2Lean.ArithOp.sub @_root_.Air2Lean.Mode.checked (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 1) (@_root_.instOfNat (nat_lit 1)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 13) (@_root_.instOfNatNat (nat_lit 13))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.call (@_root_.Air2Lean.Val.func "recursion.fact" @_root_.Bool.false (@_root_.Option.none @_root_.String)) (@_root_.List.toArray @_root_.Air2Lean.Val (@_root_.List.cons @_root_.Air2Lean.Val (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6)))) (@_root_.List.nil @_root_.Air2Lean.Val))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 14) (@_root_.instOfNatNat (nat_lit 14))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arith @_root_.Air2Lean.ArithOp.mul @_root_.Air2Lean.Mode.checked (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 15) (@_root_.instOfNatNat (nat_lit 15))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 9) (@_root_.instOfNatNat (nat_lit 9))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8)))))) (@_root_.List.nil @_root_.Air2Lean.Inst))))))))))))) (@_root_.List.toArray @_root_.Air2Lean.Ty (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.int @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 32) (@_root_.instOfNatNat (nat_lit 32)))) (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.void (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.bool (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.noreturn (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.other "fn (u32) callconv(.c) u32") (@_root_.List.nil @_root_.Air2Lean.Ty))))))) (@_root_.List.toArray @_root_.Air2Lean.Layout (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.nil @_root_.Air2Lean.Layout))))))) (@_root_.List.toArray @_root_.Air2Lean.Global (@_root_.List.nil @_root_.Air2Lean.Global)) (@_root_.List.toArray @_root_.Air2Lean.Identity.Record (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.fact" (@_root_.Option.none @_root_.String) "recursion.fact" (@_root_.Option.none @_root_.String)) (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.fact" (@_root_.Option.none @_root_.String) "recursion.fact" (@_root_.Option.none @_root_.String)) (@_root_.List.nil @_root_.Air2Lean.Identity.Record)))) (@_root_.List.toArray @_root_.Air2Lean.ExternDecl (@_root_.List.nil @_root_.Air2Lean.ExternDecl)) (@_root_.Option.none @_root_.Air2Lean.ExportDecl) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.List.toArray @_root_.String (@_root_.List.cons @_root_.String "for_len" (@_root_.List.nil @_root_.String))) @_root_.Air2Lean.AllocatorModel.std "" (@_root_.Option.none (@_root_.Array @_root_.String)) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String)))

def source_1 : _root_.Air2Lean.Func :=
(@_root_.Air2Lean.Func.mk (@_root_.Air2Lean.Dialect.mk @_root_.Air2Lean.ZigVersion.v0_15_2 "" "" (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) @_root_.Air2Lean.Endian.little (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 16) (@_root_.instOfNatNat (nat_lit 16))) "unverified" "unverified" @_root_.Bool.false) "recursion.gcd" (@_root_.List.toArray @_root_.Nat (@_root_.List.cons @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.cons @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.nil @_root_.Nat)))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arg (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arg (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 16) (@_root_.instOfNatNat (nat_lit 16))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.block (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.cmp @_root_.Air2Lean.CmpOp.eq (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 0) (@_root_.instOfNat (nat_lit 0)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.condBr (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 17) (@_root_.instOfNatNat (nat_lit 17))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 5) (@_root_.instOfNatNat (nat_lit 5))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.br (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) @_root_.Air2Lean.Val.void)) (@_root_.List.nil @_root_.Air2Lean.Inst))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 18) (@_root_.instOfNatNat (nat_lit 18))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.cmp @_root_.Air2Lean.CmpOp.ne (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 0) (@_root_.instOfNat (nat_lit 0)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.block (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 9) (@_root_.instOfNatNat (nat_lit 9))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.condBr (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 10) (@_root_.instOfNatNat (nat_lit 10))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.br (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) @_root_.Air2Lean.Val.void)) (@_root_.List.nil @_root_.Air2Lean.Inst))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 11) (@_root_.instOfNatNat (nat_lit 11))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.call (@_root_.Air2Lean.Val.func "debug.FullPanic((function 'defaultPanic')).divideByZero" @_root_.Bool.true (@_root_.Option.none @_root_.String)) (@_root_.List.toArray @_root_.Air2Lean.Val (@_root_.List.nil @_root_.Air2Lean.Val)))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 12) (@_root_.instOfNatNat (nat_lit 12))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) @_root_.Air2Lean.Op.unreach) (@_root_.List.nil @_root_.Air2Lean.Inst)))))) (@_root_.List.nil @_root_.Air2Lean.Inst))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 13) (@_root_.instOfNatNat (nat_lit 13))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.div @_root_.Air2Lean.DivOp.rem (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 19) (@_root_.instOfNatNat (nat_lit 19))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 14) (@_root_.instOfNatNat (nat_lit 14))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.call (@_root_.Air2Lean.Val.func "recursion.gcd" @_root_.Bool.false (@_root_.Option.none @_root_.String)) (@_root_.List.toArray @_root_.Air2Lean.Val (@_root_.List.cons @_root_.Air2Lean.Val (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.cons @_root_.Air2Lean.Val (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 13) (@_root_.instOfNatNat (nat_lit 13)))) (@_root_.List.nil @_root_.Air2Lean.Val)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 20) (@_root_.instOfNatNat (nat_lit 20))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 15) (@_root_.instOfNatNat (nat_lit 15))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 14) (@_root_.instOfNatNat (nat_lit 14)))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))))))))))))) (@_root_.List.toArray @_root_.Air2Lean.Ty (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.int @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 32) (@_root_.instOfNatNat (nat_lit 32)))) (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.void (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.bool (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.noreturn (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.other "fn () noreturn") (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.other "fn (u32, u32) callconv(.c) u32") (@_root_.List.nil @_root_.Air2Lean.Ty)))))))) (@_root_.List.toArray @_root_.Air2Lean.Layout (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.nil @_root_.Air2Lean.Layout)))))))) (@_root_.List.toArray @_root_.Air2Lean.Global (@_root_.List.nil @_root_.Air2Lean.Global)) (@_root_.List.toArray @_root_.Air2Lean.Identity.Record (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.gcd" (@_root_.Option.none @_root_.String) "recursion.gcd" (@_root_.Option.none @_root_.String)) (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "debug.FullPanic((function 'defaultPanic')).divideByZero" (@_root_.Option.none @_root_.String) "debug.FullPanic((function 'defaultPanic')).divideByZero" (@_root_.Option.none @_root_.String)) (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.gcd" (@_root_.Option.none @_root_.String) "recursion.gcd" (@_root_.Option.none @_root_.String)) (@_root_.List.nil @_root_.Air2Lean.Identity.Record))))) (@_root_.List.toArray @_root_.Air2Lean.ExternDecl (@_root_.List.nil @_root_.Air2Lean.ExternDecl)) (@_root_.Option.none @_root_.Air2Lean.ExportDecl) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.List.toArray @_root_.String (@_root_.List.cons @_root_.String "for_len" (@_root_.List.nil @_root_.String))) @_root_.Air2Lean.AllocatorModel.std "" (@_root_.Option.none (@_root_.Array @_root_.String)) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String)))

def source_2 : _root_.Air2Lean.Func :=
(@_root_.Air2Lean.Func.mk (@_root_.Air2Lean.Dialect.mk @_root_.Air2Lean.ZigVersion.v0_15_2 "" "" (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) @_root_.Air2Lean.Endian.little (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 16) (@_root_.instOfNatNat (nat_lit 16))) "unverified" "unverified" @_root_.Bool.false) "recursion.isEven" (@_root_.List.toArray @_root_.Nat (@_root_.List.cons @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.nil @_root_.Nat))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arg (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 9) (@_root_.instOfNatNat (nat_lit 9))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.block (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.cmp @_root_.Air2Lean.CmpOp.eq (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 0) (@_root_.instOfNat (nat_lit 0)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.condBr (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 10) (@_root_.instOfNatNat (nat_lit 10))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.bool @_root_.Bool.true))) (@_root_.List.nil @_root_.Air2Lean.Inst)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 5) (@_root_.instOfNatNat (nat_lit 5))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.br (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) @_root_.Air2Lean.Val.void)) (@_root_.List.nil @_root_.Air2Lean.Inst))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 11) (@_root_.instOfNatNat (nat_lit 11))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arith @_root_.Air2Lean.ArithOp.sub @_root_.Air2Lean.Mode.checked (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 1) (@_root_.instOfNat (nat_lit 1)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 12) (@_root_.instOfNatNat (nat_lit 12))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.call (@_root_.Air2Lean.Val.func "recursion.isOdd" @_root_.Bool.false (@_root_.Option.none @_root_.String)) (@_root_.List.toArray @_root_.Air2Lean.Val (@_root_.List.cons @_root_.Air2Lean.Val (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6)))) (@_root_.List.nil @_root_.Air2Lean.Val))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 13) (@_root_.instOfNatNat (nat_lit 13))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7)))))) (@_root_.List.nil @_root_.Air2Lean.Inst))))))))))) (@_root_.List.toArray @_root_.Air2Lean.Ty (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.int @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 32) (@_root_.instOfNatNat (nat_lit 32)))) (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.bool (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.void (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.noreturn (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.other "fn (u32) callconv(.c) bool") (@_root_.List.nil @_root_.Air2Lean.Ty))))))) (@_root_.List.toArray @_root_.Air2Lean.Layout (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.nil @_root_.Air2Lean.Layout))))))) (@_root_.List.toArray @_root_.Air2Lean.Global (@_root_.List.nil @_root_.Air2Lean.Global)) (@_root_.List.toArray @_root_.Air2Lean.Identity.Record (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.isEven" (@_root_.Option.none @_root_.String) "recursion.isEven" (@_root_.Option.none @_root_.String)) (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.isOdd" (@_root_.Option.none @_root_.String) "recursion.isOdd" (@_root_.Option.none @_root_.String)) (@_root_.List.nil @_root_.Air2Lean.Identity.Record)))) (@_root_.List.toArray @_root_.Air2Lean.ExternDecl (@_root_.List.nil @_root_.Air2Lean.ExternDecl)) (@_root_.Option.none @_root_.Air2Lean.ExportDecl) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.List.toArray @_root_.String (@_root_.List.cons @_root_.String "for_len" (@_root_.List.nil @_root_.String))) @_root_.Air2Lean.AllocatorModel.std "" (@_root_.Option.none (@_root_.Array @_root_.String)) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String)))

def source_3 : _root_.Air2Lean.Func :=
(@_root_.Air2Lean.Func.mk (@_root_.Air2Lean.Dialect.mk @_root_.Air2Lean.ZigVersion.v0_15_2 "" "" (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) @_root_.Air2Lean.Endian.little (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 16) (@_root_.instOfNatNat (nat_lit 16))) "unverified" "unverified" @_root_.Bool.false) "recursion.isOdd" (@_root_.List.toArray @_root_.Nat (@_root_.List.cons @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.List.nil @_root_.Nat))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arg (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 9) (@_root_.instOfNatNat (nat_lit 9))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.block (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.cmp @_root_.Air2Lean.CmpOp.eq (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 0) (@_root_.instOfNat (nat_lit 0)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.condBr (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 10) (@_root_.instOfNatNat (nat_lit 10))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.bool @_root_.Bool.false))) (@_root_.List.nil @_root_.Air2Lean.Inst)))) (@_root_.List.toArray @_root_.Air2Lean.Inst (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 5) (@_root_.instOfNatNat (nat_lit 5))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.br (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) @_root_.Air2Lean.Val.void)) (@_root_.List.nil @_root_.Air2Lean.Inst))))) (@_root_.List.nil @_root_.Air2Lean.Inst)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 11) (@_root_.instOfNatNat (nat_lit 11))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Air2Lean.Op.arith @_root_.Air2Lean.ArithOp.sub @_root_.Air2Lean.Mode.checked (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Air2Lean.Val.int (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Int (nat_lit 1) (@_root_.instOfNat (nat_lit 1)))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 12) (@_root_.instOfNatNat (nat_lit 12))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1))) (@_root_.Air2Lean.Op.call (@_root_.Air2Lean.Val.func "recursion.isEven" @_root_.Bool.false (@_root_.Option.none @_root_.String)) (@_root_.List.toArray @_root_.Air2Lean.Val (@_root_.List.cons @_root_.Air2Lean.Val (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 6) (@_root_.instOfNatNat (nat_lit 6)))) (@_root_.List.nil @_root_.Air2Lean.Val))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 13) (@_root_.instOfNatNat (nat_lit 13))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 2) (@_root_.instOfNatNat (nat_lit 2))) (@_root_.Air2Lean.Op.line (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))))) (@_root_.List.cons @_root_.Air2Lean.Inst (@_root_.Air2Lean.Inst.mk (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 3) (@_root_.instOfNatNat (nat_lit 3))) (@_root_.Air2Lean.Op.ret (@_root_.Air2Lean.Val.inst (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 7) (@_root_.instOfNatNat (nat_lit 7)))))) (@_root_.List.nil @_root_.Air2Lean.Inst))))))))))) (@_root_.List.toArray @_root_.Air2Lean.Ty (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.int @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 32) (@_root_.instOfNatNat (nat_lit 32)))) (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.bool (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.void (@_root_.List.cons @_root_.Air2Lean.Ty @_root_.Air2Lean.Ty.noreturn (@_root_.List.cons @_root_.Air2Lean.Ty (@_root_.Air2Lean.Ty.other "fn (u32) callconv(.c) bool") (@_root_.List.nil @_root_.Air2Lean.Ty))))))) (@_root_.List.toArray @_root_.Air2Lean.Layout (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 4) (@_root_.instOfNatNat (nat_lit 4)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0)))) (@_root_.Option.some @_root_.Nat (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 1) (@_root_.instOfNatNat (nat_lit 1)))) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.cons @_root_.Air2Lean.Layout (@_root_.Air2Lean.Layout.mk (@_root_.Option.none @_root_.Nat) (@_root_.Option.none @_root_.Nat) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 0) (@_root_.instOfNatNat (nat_lit 0))) (@_root_.Option.none @_root_.Nat) @_root_.Bool.false @_root_.Bool.false @_root_.Bool.false (@_root_.OfNat.ofNat @_root_.Nat (nat_lit 8) (@_root_.instOfNatNat (nat_lit 8))) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String))) (@_root_.List.nil @_root_.Air2Lean.Layout))))))) (@_root_.List.toArray @_root_.Air2Lean.Global (@_root_.List.nil @_root_.Air2Lean.Global)) (@_root_.List.toArray @_root_.Air2Lean.Identity.Record (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.isOdd" (@_root_.Option.none @_root_.String) "recursion.isOdd" (@_root_.Option.none @_root_.String)) (@_root_.List.cons @_root_.Air2Lean.Identity.Record (@_root_.Air2Lean.Identity.Record.mk "recursion.isEven" (@_root_.Option.none @_root_.String) "recursion.isEven" (@_root_.Option.none @_root_.String)) (@_root_.List.nil @_root_.Air2Lean.Identity.Record)))) (@_root_.List.toArray @_root_.Air2Lean.ExternDecl (@_root_.List.nil @_root_.Air2Lean.ExternDecl)) (@_root_.Option.none @_root_.Air2Lean.ExportDecl) (@_root_.List.toArray @_root_.Nat (@_root_.List.nil @_root_.Nat)) (@_root_.List.toArray @_root_.String (@_root_.List.cons @_root_.String "for_len" (@_root_.List.nil @_root_.String))) @_root_.Air2Lean.AllocatorModel.std "" (@_root_.Option.none (@_root_.Array @_root_.String)) (@_root_.List.toArray @_root_.String (@_root_.List.nil @_root_.String)))

/-- The complete original translation input, before certificate selection. -/
def program : _root_.Air2Lean.Program := ⟨#[source_0, source_1, source_2, source_3], (@_root_.List.toArray @_root_.Air2Lean.ModelBinding (@_root_.List.nil @_root_.Air2Lean.ModelBinding))⟩

/-- The decoded canonical AIR of `recursion.fact` in the original program. -/
def air_fact : _root_.Air2Lean.Func := source_0

theorem lookup_fact : program.lookup "recursion.fact" = some air_fact := rfl
theorem policy_fact : program.ticked "recursion.fact" = false := by decide +kernel
theorem entry_fact : program.entryTicked "recursion.fact" = false := by decide +kernel

/-- The decoded canonical AIR of `recursion.gcd` in the original program. -/
def air_gcd : _root_.Air2Lean.Func := source_1

theorem lookup_gcd : program.lookup "recursion.gcd" = some air_gcd := rfl
theorem policy_gcd : program.ticked "recursion.gcd" = false := by decide +kernel
theorem entry_gcd : program.entryTicked "recursion.gcd" = false := by decide +kernel

/-- The decoded canonical AIR of `recursion.isEven` in the original program. -/
def air_isEven : _root_.Air2Lean.Func := source_2

theorem lookup_isEven : program.lookup "recursion.isEven" = some air_isEven := rfl
theorem policy_isEven : program.ticked "recursion.isEven" = false := by decide +kernel
theorem entry_isEven : program.entryTicked "recursion.isEven" = false := by decide +kernel

/-- The decoded canonical AIR of `recursion.isOdd` in the original program. -/
def air_isOdd : _root_.Air2Lean.Func := source_3

theorem lookup_isOdd : program.lookup "recursion.isOdd" = some air_isOdd := rfl
theorem policy_isOdd : program.ticked "recursion.isOdd" = false := by decide +kernel
theorem entry_isOdd : program.entryTicked "recursion.isOdd" = false := by decide +kernel

theorem callee_0 : panicOf? "recursion.fact" = none := rfl
theorem callee_1 : panicOf? "debug.FullPanic((function 'defaultPanic')).divideByZero" = some .divByZero := rfl
theorem callee_2 : panicOf? "recursion.gcd" = none := rfl
theorem callee_3 : panicOf? "recursion.isOdd" = none := rfl
theorem callee_4 : panicOf? "recursion.isEven" = none := rfl

/-- The certified functions, by fully qualified name. -/
def table : Table := [
  "recursion.fact",
  "recursion.gcd",
  "recursion.isEven",
  "recursion.isOdd"]

/-- The generated definitions as a call oracle (arguments decoded by type). -/
def gen : Oracle
  | "recursion.fact", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Recursion.fact ((args.getD 0 .void).toBV 32))
  | "recursion.gcd", args =>
    StateT.lift ((fun v => (Value.int false 32 v)) <$> Recursion.gcd ((args.getD 0 .void).toBV 32) ((args.getD 1 .void).toBV 32))
  | "recursion.isEven", args =>
    StateT.lift ((fun v => (Value.bool v)) <$> Recursion.isEven ((args.getD 0 .void).toBV 32))
  | "recursion.isOdd", args =>
    StateT.lift ((fun v => (Value.bool v)) <$> Recursion.isOdd ((args.getD 0 .void).toBV 32))
  | _, _ => StateT.lift stuck

/-- `recursion.fact`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem fact_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc program gen air_fact [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Recursion.fact p0 := by
  conv => rhs; rw [Recursion.fact]
  simp only [air_fact, air_sem, policy_fact, entry_fact, source_0, callee_0, gen]

theorem fact_fix (args : List Value)
    (h : argsOk air_fact air_fact.params.toList args = true) :
    execFunc program gen air_fact args = gen "recursion.fact" args := by
  replace h : argsOk air_fact [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc program gen air_fact _).run m = (gen _ _).run m
  rw [fact_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- `recursion.gcd`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem gcd_step (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (execFunc program gen air_gcd [(Value.int false 32 p0), (Value.int false 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1 := by
  conv => rhs; rw [Recursion.gcd]
  simp only [air_gcd, air_sem, policy_gcd, entry_gcd, source_1, callee_1, callee_2, gen]

theorem gcd_fix (args : List Value)
    (h : argsOk air_gcd air_gcd.params.toList args = true) :
    execFunc program gen air_gcd args = gen "recursion.gcd" args := by
  replace h : argsOk air_gcd [0, 0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain ⟨v1, args, rfl, h1, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  replace h1 : valOk (.int false 32) v1 = true := h1
  rw [valOk_int h1]
  funext m
  show (execFunc program gen air_gcd _).run m = (gen _ _).run m
  rw [gcd_step (v0.toBV 32) (v1.toBV 32)]
  simp only [gen, air_sem]

/-- `recursion.isEven`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem isEven_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc program gen air_isEven [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.bool v), m)) <$> Recursion.isEven p0 := by
  conv => rhs; rw [Recursion.isEven]
  simp only [air_isEven, air_sem, policy_isEven, entry_isEven, source_2, callee_3, gen]

theorem isEven_fix (args : List Value)
    (h : argsOk air_isEven air_isEven.params.toList args = true) :
    execFunc program gen air_isEven args = gen "recursion.isEven" args := by
  replace h : argsOk air_isEven [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc program gen air_isEven _).run m = (gen _ _).run m
  rw [isEven_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- `recursion.isOdd`: the AIR semantics of the decoded function, with the generated program answering its calls, equals the generated definition. -/
theorem isOdd_step (p0 : BitVec 32) (m : Zig.Mem) :
    (execFunc program gen air_isOdd [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.bool v), m)) <$> Recursion.isOdd p0 := by
  conv => rhs; rw [Recursion.isOdd]
  simp only [air_isOdd, air_sem, policy_isOdd, entry_isOdd, source_3, callee_4, gen]

theorem isOdd_fix (args : List Value)
    (h : argsOk air_isOdd air_isOdd.params.toList args = true) :
    execFunc program gen air_isOdd args = gen "recursion.isOdd" args := by
  replace h : argsOk air_isOdd [0] args = true := h
  obtain ⟨v0, args, rfl, h0, h⟩ := argsOk_cons h
  obtain rfl := argsOk_nil h
  replace h0 : valOk (.int false 32) v0 = true := h0
  rw [valOk_int h0]
  funext m
  show (execFunc program gen air_isOdd _).run m = (gen _ _).run m
  rw [isOdd_step (v0.toBV 32)]
  simp only [gen, air_sem]

/-- The generated program satisfies every certified function's AIR equation. -/
theorem gen_fixpoint : Fixpoint program gen table :=
  ⟨(by intro f args hp ha; rw [lookup_fact] at hp; cases hp; exact fact_fix args ha), (by intro f args hp ha; rw [lookup_gcd] at hp; cases hp; exact gcd_fix args ha), (by intro f args hp ha; rw [lookup_isEven] at hp; cases hp; exact isEven_fix args ha), (by intro f args hp ha; rw [lookup_isOdd] at hp; cases hp; exact isOdd_fix args ha), trivial⟩

/-- The AIR semantics restricted to the certified names, using the complete original
program's lookup and cost policy, is below the
generated program: every terminating AIR behaviour is the generated definition's. -/
theorem run_le_gen : Lean.Order.PartialOrder.rel (runOn program table) gen :=
  run_le_of_table gen_fixpoint

/-- `recursion.fact`: every terminating AIR run is the generated definition's. -/
theorem fact_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((runOn program table "recursion.fact" [(Value.int false 32 p0)]).run m)
      ((fun v => ((Value.int false 32 v), m)) <$> Recursion.fact p0) := by
  have h : Lean.Order.PartialOrder.rel ((runOn program table "recursion.fact" [(Value.int false 32 p0)]).run m)
      ((gen "recursion.fact" [(Value.int false 32 p0)]).run m) := run_le_gen "recursion.fact" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.gcd`: every terminating AIR run is the generated definition's. -/
theorem gcd_sound (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((runOn program table "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m)
      ((fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1) := by
  have h : Lean.Order.PartialOrder.rel ((runOn program table "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m)
      ((gen "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m) := run_le_gen "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.isEven`: every terminating AIR run is the generated definition's. -/
theorem isEven_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((runOn program table "recursion.isEven" [(Value.int false 32 p0)]).run m)
      ((fun v => ((Value.bool v), m)) <$> Recursion.isEven p0) := by
  have h : Lean.Order.PartialOrder.rel ((runOn program table "recursion.isEven" [(Value.int false 32 p0)]).run m)
      ((gen "recursion.isEven" [(Value.int false 32 p0)]).run m) := run_le_gen "recursion.isEven" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.isOdd`: every terminating AIR run is the generated definition's. -/
theorem isOdd_sound (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((runOn program table "recursion.isOdd" [(Value.int false 32 p0)]).run m)
      ((fun v => ((Value.bool v), m)) <$> Recursion.isOdd p0) := by
  have h : Lean.Order.PartialOrder.rel ((runOn program table "recursion.isOdd" [(Value.int false 32 p0)]).run m)
      ((gen "recursion.isOdd" [(Value.int false 32 p0)]).run m) := run_le_gen "recursion.isOdd" [(Value.int false 32 p0)] m
  simp only [gen, air_sem] at h
  exact h

/-- `recursion.fact`: the generated definition terminates only as the AIR does: it is below `run`. -/
theorem fact_complete (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> Recursion.fact p0)
      ((runOn program table "recursion.fact" [(Value.int false 32 p0)]).run m) := by
  have h_complete : (fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> g a0) ((runOn program table "recursion.fact" [(Value.int false 32 a0)]).run m)) ((fun (v0 : BitVec 32) => Recursion.fact v0)) := by
    apply Recursion.fact.fixpoint_induct (motive := fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> g a0) ((runOn program table "recursion.fact" [(Value.int false 32 a0)]).run m))
    ·
      apply Lean.Order.admissible_pi; intro a0
      apply Lean.Order.admissible_pi; intro m
      apply Lean.Order.admissible_pi; intro hfixed
      apply Lean.Order.admissible_apply (fun _ (r : Zig.Result (BitVec 32)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> r) ((runOn program table "recursion.fact" [(Value.int false 32 a0)]).run m)) (x := a0)
      exact adm_app0 _ _
    ·
      intro g_0 hg_0
      let b_fn_fact : BitVec 32 → Zig.Result (BitVec 32) := fun (a0 : BitVec 32) => if True then g_0 a0 else stuck
      have hb_fn_fact : ∀ (a0 : BitVec 32) (m : Zig.Mem), Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> b_fn_fact a0) ((runOn program table "recursion.fact" [(Value.int false 32 a0)]).run m) := by
        intro a0 m
        by_cases hfixed : True
        · simpa only [b_fn_fact, hfixed, if_pos] using hg_0 a0 m hfixed
        · simp only [b_fn_fact, hfixed, if_neg]
          exact Lean.Order.FlatOrder.rel.bot
      intro a0 m hfixed
      rw [runOn_of_lookup (by decide) lookup_fact]
      simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_fact, policy_fact, entry_fact, source_0, callee_0, b_fn_fact, Env.val, Frame.cell]
      all_goals repeat (first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact hb_fn_fact _ _
        | (refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.MonoBind.bind_mono_left (hb_fn_fact _ _))
           simp only [bind_map_left]
           first
           | refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_
           | (conv => lhs; rw [← bind_pure_comp]
              refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_)
           intro r _
           simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_fact, policy_fact, entry_fact, source_0, callee_0, b_fn_fact, Env.val, Frame.cell])
        | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (fun _ _ => True.intro) ?_
           intro r _; simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_fact, policy_fact, entry_fact, source_0, callee_0, b_fn_fact, Env.val, Frame.cell])
        | (split <;> simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_fact, policy_fact, entry_fact, source_0, callee_0, b_fn_fact, Env.val, Frame.cell, *])
        | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)
        | (apply Lean.Order.MonoBind.bind_mono_right; intro))
  exact h_complete p0 m (by simp)

/-- `recursion.fact`: its AIR semantics equals the generated definition. -/
theorem fact_eq (p0 : BitVec 32) (m : Zig.Mem) :
    (runOn program table "recursion.fact" [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Recursion.fact p0 :=
  Lean.Order.PartialOrder.rel_antisymm (fact_sound p0 m) (fact_complete p0 m)

/-- `recursion.gcd`: the generated definition terminates only as the AIR does: it is below `run`. -/
theorem gcd_complete (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1)
      ((runOn program table "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m) := by
  have h_complete : (fun g => ∀ (a0 : BitVec 32) (a1 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> g a0 a1) ((runOn program table "recursion.gcd" [(Value.int false 32 a0), (Value.int false 32 a1)]).run m)) ((fun (v0 : BitVec 32) (v1 : BitVec 32) => Recursion.gcd v0 v1)) := by
    apply Recursion.gcd.fixpoint_induct (motive := fun g => ∀ (a0 : BitVec 32) (a1 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> g a0 a1) ((runOn program table "recursion.gcd" [(Value.int false 32 a0), (Value.int false 32 a1)]).run m))
    ·
      apply Lean.Order.admissible_pi; intro a0
      apply Lean.Order.admissible_pi; intro a1
      apply Lean.Order.admissible_pi; intro m
      apply Lean.Order.admissible_pi; intro hfixed
      apply Lean.Order.admissible_apply (fun _ (r : (BitVec 32) → Zig.Result (BitVec 32)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> r a1) ((runOn program table "recursion.gcd" [(Value.int false 32 a0), (Value.int false 32 a1)]).run m)) (x := a0)
      apply Lean.Order.admissible_apply (fun _ (r : Zig.Result (BitVec 32)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> r) ((runOn program table "recursion.gcd" [(Value.int false 32 a0), (Value.int false 32 a1)]).run m)) (x := a1)
      exact adm_app0 _ _
    ·
      intro g_0 hg_0
      let b_fn_gcd : BitVec 32 → BitVec 32 → Zig.Result (BitVec 32) := fun (a0 : BitVec 32) (a1 : BitVec 32) => if True then g_0 a0 a1 else stuck
      have hb_fn_gcd : ∀ (a0 : BitVec 32) (a1 : BitVec 32) (m : Zig.Mem), Lean.Order.PartialOrder.rel ((fun v => ((Value.int false 32 v), m)) <$> b_fn_gcd a0 a1) ((runOn program table "recursion.gcd" [(Value.int false 32 a0), (Value.int false 32 a1)]).run m) := by
        intro a0 a1 m
        by_cases hfixed : True
        · simpa only [b_fn_gcd, hfixed, if_pos] using hg_0 a0 a1 m hfixed
        · simp only [b_fn_gcd, hfixed, if_neg]
          exact Lean.Order.FlatOrder.rel.bot
      intro a0 a1 m hfixed
      rw [runOn_of_lookup (by decide) lookup_gcd]
      simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_gcd, policy_gcd, entry_gcd, source_1, callee_1, callee_2, b_fn_gcd, Env.val, Frame.cell]
      all_goals repeat (first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact hb_fn_gcd _ _ _
        | (refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.MonoBind.bind_mono_left (hb_fn_gcd _ _ _))
           simp only [bind_map_left]
           first
           | refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_
           | (conv => lhs; rw [← bind_pure_comp]
              refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_)
           intro r _
           simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_gcd, policy_gcd, entry_gcd, source_1, callee_1, callee_2, b_fn_gcd, Env.val, Frame.cell])
        | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (fun _ _ => True.intro) ?_
           intro r _; simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_gcd, policy_gcd, entry_gcd, source_1, callee_1, callee_2, b_fn_gcd, Env.val, Frame.cell])
        | (split <;> simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_gcd, policy_gcd, entry_gcd, source_1, callee_1, callee_2, b_fn_gcd, Env.val, Frame.cell, *])
        | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)
        | (apply Lean.Order.MonoBind.bind_mono_right; intro))
  exact h_complete p0 p1 m (by simp)

/-- `recursion.gcd`: its AIR semantics equals the generated definition. -/
theorem gcd_eq (p0 : BitVec 32) (p1 : BitVec 32) (m : Zig.Mem) :
    (runOn program table "recursion.gcd" [(Value.int false 32 p0), (Value.int false 32 p1)]).run m =
      (fun v => ((Value.int false 32 v), m)) <$> Recursion.gcd p0 p1 :=
  Lean.Order.PartialOrder.rel_antisymm (gcd_sound p0 p1 m) (gcd_complete p0 p1 m)

/-- `recursion.isEven`: the generated definition terminates only as the AIR does: it is below `run`. -/
theorem isEven_complete (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> Recursion.isEven p0)
      ((runOn program table "recursion.isEven" [(Value.int false 32 p0)]).run m) := by
  have h_complete : (fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> g a0) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m)) ((fun (v0 : BitVec 32) => Recursion.isEven v0)) := by
    apply Recursion.isEven.fixpoint_induct (motive_1 := fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> g a0) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m)) (motive_2 := fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> g a0) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m))
    ·
      apply Lean.Order.admissible_pi; intro a0
      apply Lean.Order.admissible_pi; intro m
      apply Lean.Order.admissible_pi; intro hfixed
      apply Lean.Order.admissible_apply (fun _ (r : Zig.Result (Bool)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> r) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m)) (x := a0)
      exact adm_app0 _ _
    ·
      apply Lean.Order.admissible_pi; intro a0
      apply Lean.Order.admissible_pi; intro m
      apply Lean.Order.admissible_pi; intro hfixed
      apply Lean.Order.admissible_apply (fun _ (r : Zig.Result (Bool)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> r) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m)) (x := a0)
      exact adm_app0 _ _
    ·
      intro g_0 hg_0
      let b_fn_isOdd : BitVec 32 → Zig.Result (Bool) := fun (a0 : BitVec 32) => if True then g_0 a0 else stuck
      have hb_fn_isOdd : ∀ (a0 : BitVec 32) (m : Zig.Mem), Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> b_fn_isOdd a0) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m) := by
        intro a0 m
        by_cases hfixed : True
        · simpa only [b_fn_isOdd, hfixed, if_pos] using hg_0 a0 m hfixed
        · simp only [b_fn_isOdd, hfixed, if_neg]
          exact Lean.Order.FlatOrder.rel.bot
      intro a0 m hfixed
      rw [runOn_of_lookup (by decide) lookup_isEven]
      simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell]
      all_goals repeat (first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact hb_fn_isOdd _ _
        | (refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.MonoBind.bind_mono_left (hb_fn_isOdd _ _))
           simp only [bind_map_left]
           first
           | refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_
           | (conv => lhs; rw [← bind_pure_comp]
              refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_)
           intro r _
           simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell])
        | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (fun _ _ => True.intro) ?_
           intro r _; simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell])
        | (split <;> simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell, *])
        | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)
        | (apply Lean.Order.MonoBind.bind_mono_right; intro))
    ·
      intro g_0 hg_0
      let b_fn_isEven : BitVec 32 → Zig.Result (Bool) := fun (a0 : BitVec 32) => if True then g_0 a0 else stuck
      have hb_fn_isEven : ∀ (a0 : BitVec 32) (m : Zig.Mem), Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> b_fn_isEven a0) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m) := by
        intro a0 m
        by_cases hfixed : True
        · simpa only [b_fn_isEven, hfixed, if_pos] using hg_0 a0 m hfixed
        · simp only [b_fn_isEven, hfixed, if_neg]
          exact Lean.Order.FlatOrder.rel.bot
      intro a0 m hfixed
      rw [runOn_of_lookup (by decide) lookup_isOdd]
      simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell]
      all_goals repeat (first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact hb_fn_isEven _ _
        | (refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.MonoBind.bind_mono_left (hb_fn_isEven _ _))
           simp only [bind_map_left]
           first
           | refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_
           | (conv => lhs; rw [← bind_pure_comp]
              refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_)
           intro r _
           simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell])
        | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (fun _ _ => True.intro) ?_
           intro r _; simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell])
        | (split <;> simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell, *])
        | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)
        | (apply Lean.Order.MonoBind.bind_mono_right; intro))
  exact h_complete p0 m (by simp)

/-- `recursion.isOdd`: the generated definition terminates only as the AIR does: it is below `run`. -/
theorem isOdd_complete (p0 : BitVec 32) (m : Zig.Mem) :
    Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> Recursion.isOdd p0)
      ((runOn program table "recursion.isOdd" [(Value.int false 32 p0)]).run m) := by
  have h_complete : (fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> g a0) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m)) ((fun (v0 : BitVec 32) => Recursion.isOdd v0)) := by
    apply Recursion.isOdd.fixpoint_induct (motive_1 := fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> g a0) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m)) (motive_2 := fun g => ∀ (a0 : BitVec 32) (m : Zig.Mem), True → Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> g a0) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m))
    ·
      apply Lean.Order.admissible_pi; intro a0
      apply Lean.Order.admissible_pi; intro m
      apply Lean.Order.admissible_pi; intro hfixed
      apply Lean.Order.admissible_apply (fun _ (r : Zig.Result (Bool)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> r) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m)) (x := a0)
      exact adm_app0 _ _
    ·
      apply Lean.Order.admissible_pi; intro a0
      apply Lean.Order.admissible_pi; intro m
      apply Lean.Order.admissible_pi; intro hfixed
      apply Lean.Order.admissible_apply (fun _ (r : Zig.Result (Bool)) => Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> r) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m)) (x := a0)
      exact adm_app0 _ _
    ·
      intro g_0 hg_0
      let b_fn_isOdd : BitVec 32 → Zig.Result (Bool) := fun (a0 : BitVec 32) => if True then g_0 a0 else stuck
      have hb_fn_isOdd : ∀ (a0 : BitVec 32) (m : Zig.Mem), Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> b_fn_isOdd a0) ((runOn program table "recursion.isOdd" [(Value.int false 32 a0)]).run m) := by
        intro a0 m
        by_cases hfixed : True
        · simpa only [b_fn_isOdd, hfixed, if_pos] using hg_0 a0 m hfixed
        · simp only [b_fn_isOdd, hfixed, if_neg]
          exact Lean.Order.FlatOrder.rel.bot
      intro a0 m hfixed
      rw [runOn_of_lookup (by decide) lookup_isEven]
      simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell]
      all_goals repeat (first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact hb_fn_isOdd _ _
        | (refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.MonoBind.bind_mono_left (hb_fn_isOdd _ _))
           simp only [bind_map_left]
           first
           | refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_
           | (conv => lhs; rw [← bind_pure_comp]
              refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_)
           intro r _
           simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell])
        | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (fun _ _ => True.intro) ?_
           intro r _; simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell])
        | (split <;> simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isEven, policy_isEven, entry_isEven, source_2, callee_3, b_fn_isOdd, Env.val, Frame.cell, *])
        | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)
        | (apply Lean.Order.MonoBind.bind_mono_right; intro))
    ·
      intro g_0 hg_0
      let b_fn_isEven : BitVec 32 → Zig.Result (Bool) := fun (a0 : BitVec 32) => if True then g_0 a0 else stuck
      have hb_fn_isEven : ∀ (a0 : BitVec 32) (m : Zig.Mem), Lean.Order.PartialOrder.rel ((fun v => ((Value.bool v), m)) <$> b_fn_isEven a0) ((runOn program table "recursion.isEven" [(Value.int false 32 a0)]).run m) := by
        intro a0 m
        by_cases hfixed : True
        · simpa only [b_fn_isEven, hfixed, if_pos] using hg_0 a0 m hfixed
        · simp only [b_fn_isEven, hfixed, if_neg]
          exact Lean.Order.FlatOrder.rel.bot
      intro a0 m hfixed
      rw [runOn_of_lookup (by decide) lookup_isOdd]
      simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell]
      all_goals repeat (first
        | exact Lean.Order.PartialOrder.rel_refl
        | exact hb_fn_isEven _ _
        | (refine Lean.Order.PartialOrder.rel_trans ?_ (Lean.Order.MonoBind.bind_mono_left (hb_fn_isEven _ _))
           simp only [bind_map_left]
           first
           | refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_
           | (conv => lhs; rw [← bind_pure_comp]
              refine bind_le_ok _ (fun _ => True) (fun _ _ => True.intro) ?_)
           intro r _
           simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell])
        | (refine map_bind_le_ok _ _ Lean.Order.PartialOrder.rel_refl (fun _ => True) (fun _ _ => True.intro) ?_
           intro r _; simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell])
        | (split <;> simp (config := { failIfUnchanged := false }) only [air_sem, id_map', air_isOdd, policy_isOdd, entry_isOdd, source_3, callee_4, b_fn_isEven, Env.val, Frame.cell, *])
        | (simp only [map_bind]; apply Lean.Order.MonoBind.bind_mono_right; intro)
        | (apply Lean.Order.MonoBind.bind_mono_right; intro))
  exact h_complete p0 m (by simp)

/-- `recursion.isEven`: its AIR semantics equals the generated definition. -/
theorem isEven_eq (p0 : BitVec 32) (m : Zig.Mem) :
    (runOn program table "recursion.isEven" [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.bool v), m)) <$> Recursion.isEven p0 :=
  Lean.Order.PartialOrder.rel_antisymm (isEven_sound p0 m) (isEven_complete p0 m)

/-- `recursion.isOdd`: its AIR semantics equals the generated definition. -/
theorem isOdd_eq (p0 : BitVec 32) (m : Zig.Mem) :
    (runOn program table "recursion.isOdd" [(Value.int false 32 p0)]).run m =
      (fun v => ((Value.bool v), m)) <$> Recursion.isOdd p0 :=
  Lean.Order.PartialOrder.rel_antisymm (isOdd_sound p0 m) (isOdd_complete p0 m)

end Recursion.AirCert
