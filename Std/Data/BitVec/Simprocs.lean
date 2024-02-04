/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Std.Data.BitVec.Basic

namespace Std.BitVec
open Lean Meta Simp

/-- A bit-vector literal -/
structure Literal where
  /-- Size. -/
  n     : Nat
  /-- Actual value. -/
  value : BitVec n

/--
Try to convert an `OfNat.ofNat`-application into a bitvector literal.
-/
private def fromOfNatExpr? (e : Expr) : SimpM (Option Literal) := OptionT.run do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  let type ← whnf e.appFn!.appFn!.appArg!
  guard (type.isAppOfArity ``BitVec 1)
  let n ← Nat.fromExpr? type.appArg!
  let v ← Nat.fromExpr? e.appFn!.appArg!
  return { n, value := BitVec.ofNat n v }

/--
Try to convert an `Std.BitVec.ofNat`-application into a bitvector literal.
-/
private def fromBitVecExpr? (e : Expr) : SimpM (Option Literal) := OptionT.run do
  guard (e.isAppOfArity ``Std.BitVec.ofNat 2)
  let n ← Nat.fromExpr? e.appFn!.appArg!
  let v ← Nat.fromExpr? e.appArg!
  return { n, value := BitVec.ofNat n v }

/--
Try to convert `OfNat.ofNat`/`Std.BitVec.OfNat` application into a
bitvector literal.
-/
def fromExpr? (e : Expr) : SimpM (Option Literal) := OptionT.run do
  fromBitVecExpr? e <|> fromOfNatExpr? e

/--
Convert a bitvector literal into an expression.
-/
-- Using `Std.BitVec.ofNat` because it is being used in `simp` theorems
def Literal.toExpr (lit : Literal) : Expr :=
  mkApp2 (mkConst ``Std.BitVec.ofNat) (mkNatLit lit.n) (mkNatLit lit.value.toNat)

/--
Helper function for reducing homogenous unary bitvector operators.
-/
@[inline] def reduceUnary (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let v := { v with value := op v.value }
  return .done { expr := v.toExpr }

/--
Helper function for reducing homogenous binary bitvector operators.
-/
@[inline] def reduceBin (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    trace[Meta.debug] "reduce [{declName}] {v₁.value}, {v₂.value}"
    let v := { v₁ with value := op v₁.value (h ▸ v₂.value) }
    return .done { expr := v.toExpr }
  else
    return .continue

/--
Helper function for reducing bitvector functions such as `getLsb` and `getMsb`.
-/
@[inline] def reduceGetBit (declName : Name) (op : {n : Nat} → BitVec n → Nat → Bool) (e : Expr)
    : SimpM Step := do
  unless e.isAppOfArity declName 3 do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  let b := op v.value i
  return .done { expr := toExpr b }

/--
Helper function for reducing bitvector functions such as `shiftLeft` and `rotateRight`.
-/
@[inline] def reduceShift (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → Nat → BitVec n) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  let v := { v with value := op v.value i }
  return .done { expr := v.toExpr }

/--
Helper function for reducing bitvector predicates.
-/
@[inline] def reduceBinPred (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → Bool) (e : Expr) (isProp := true) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    let b := op v₁.value (h ▸ v₂.value)
    if isProp then
      evalPropStep e b
    else
      return .done { expr := toExpr b }
  else
    return .continue


simproc [simp, seval] reduceNeg ((- _ : BitVec _)) := reduceUnary ``Neg.neg 3 (- ·)
simproc [simp, seval] reduceNot ((~~~ _ : BitVec _)) :=
  reduceUnary ``Complement.complement 3 (~~~ ·)
simproc [simp, seval] reduceAbs (BitVec.abs _) := reduceUnary ``BitVec.abs 2 BitVec.abs
simproc [simp, seval] reduceAnd ((_ &&& _ : BitVec _)) := reduceBin ``HAnd.hAnd 6 (· &&& ·)
simproc [simp, seval] reduceOr ((_ ||| _ : BitVec _)) := reduceBin ``HOr.hOr 6 (· ||| ·)
simproc [simp, seval] reduceXOr ((_ ^^^ _ : BitVec _)) := reduceBin ``HXor.hXor 6 (· ^^^ ·)
simproc [simp, seval] reduceAdd ((_ + _ : BitVec _)) := reduceBin ``HAdd.hAdd 6 (· + ·)
simproc [simp, seval] reduceMul ((_ * _ : BitVec _)) := reduceBin ``HMul.hMul 6 (· * ·)
simproc [simp, seval] reduceSub ((_ - _ : BitVec _)) := reduceBin ``HSub.hSub 6 (· - ·)
simproc [simp, seval] reduceDiv ((_ / _ : BitVec _)) := reduceBin ``HDiv.hDiv 6 (· / ·)
simproc [simp, seval] reduceMod ((_ % _ : BitVec _)) := reduceBin ``HMod.hMod 6 (· % ·)
simproc [simp, seval] reduceUMod ((umod _ _ : BitVec _)) := reduceBin ``umod 3 umod
simproc [simp, seval] reduceUDiv ((udiv _ _ : BitVec _)) := reduceBin ``udiv 3 udiv
simproc [simp, seval] reduceSMTUDiv ((smtUDiv _ _ : BitVec _)) := reduceBin ``smtUDiv 3 smtUDiv
simproc [simp, seval] reduceSMod ((smod _ _ : BitVec _)) := reduceBin ``smod 3 smod
simproc [simp, seval] reduceSRem ((srem _ _ : BitVec _)) := reduceBin ``srem 3 srem
simproc [simp, seval] reduceSDiv ((sdiv _ _ : BitVec _)) := reduceBin ``sdiv 3 sdiv
simproc [simp, seval] reduceSMTSDiv ((smtSDiv _ _ : BitVec _)) := reduceBin ``smtSDiv 3 smtSDiv
simproc [simp, seval] reduceGetLsb (getLsb _ _) := reduceGetBit ``getLsb getLsb
simproc [simp, seval] reduceGetMsb (getMsb _ _) := reduceGetBit ``getMsb getMsb

simproc [simp, seval] reduceShiftLeft (BitVec.shiftLeft _ _) :=
  reduceShift ``BitVec.shiftLeft 3 BitVec.shiftLeft
simproc [simp, seval] reduceUShiftRight (BitVec.ushiftRight _ _) :=
  reduceShift ``BitVec.ushiftRight 3 BitVec.ushiftRight
simproc [simp, seval] reduceSShiftRight (BitVec.sshiftRight _ _) :=
  reduceShift ``BitVec.sshiftRight 3 BitVec.sshiftRight
simproc [simp, seval] reduceHShiftLeft ((_ <<< _ : BitVec _)) :=
  reduceShift ``HShiftLeft.hShiftLeft 6 (· <<< ·)
simproc [simp, seval] reduceHShiftRight ((_ >>> _ : BitVec _)) :=
  reduceShift ``HShiftRight.hShiftRight 6 (· >>> ·)
simproc [simp, seval] reduceRotateLeft (BitVec.rotateLeft _ _) :=
  reduceShift ``BitVec.rotateLeft 3 BitVec.rotateLeft
simproc [simp, seval] reduceRotateRight (BitVec.rotateRight _ _) :=
  reduceShift ``BitVec.rotateRight 3 BitVec.rotateRight

simproc [simp, seval] reduceAppend ((_ ++ _ : BitVec _)) := fun e => do
  unless e.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  let v : Literal := { n := v₁.n + v₂.n, value := v₁.value ++ v₂.value }
  return .done { expr := v.toExpr }

simproc [simp, seval] reduceCast (cast _ _) := fun e => do
  unless e.isAppOfArity ``cast 4 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some m ← Nat.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let v : Literal := { n := m, value := BitVec.ofNat m v.value.toNat }
  return .done { expr := v.toExpr }

simproc [simp, seval] reduceToNat (BitVec.toNat _) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit v.value.toNat }

simproc [simp, seval] reduceToInt (BitVec.toInt _) := fun e => do
  unless e.isAppOfArity ``BitVec.toInt 2 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done { expr := Int.toExpr v.value.toInt }

simproc [simp, seval] reduceOfInt (BitVec.ofInt _ _) := fun e => do
  unless e.isAppOfArity ``BitVec.ofInt 2 do return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Int.fromExpr? e.appArg! | return .continue
  let lit : Literal := { n, value := BitVec.ofInt n i }
  return .done { expr := lit.toExpr }

simproc [simp, seval] reduceLT (( _ : BitVec _) < _)  := reduceBinPred ``LT.lt 4 (· < ·)
simproc [simp, seval] reduceLE (( _ : BitVec _) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
simproc [simp, seval] reduceGT (( _ : BitVec _) > _)  := reduceBinPred ``GT.gt 4 (. > .)
simproc [simp, seval] reduceGE (( _ : BitVec _) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

simproc [simp, seval] reduceULT (BitVec.ult _ _) :=
  reduceBinPred ``BitVec.ult 3 BitVec.ult (isProp := false)
simproc [simp, seval] reduceULE (BitVec.ule _ _) :=
  reduceBinPred ``BitVec.ule 3 BitVec.ule (isProp := false)
simproc [simp, seval] reduceSLT (BitVec.slt _ _) :=
  reduceBinPred ``BitVec.slt 3 BitVec.slt (isProp := false)
simproc [simp, seval] reduceSLE (BitVec.sle _ _) :=
  reduceBinPred ``BitVec.sle 3 BitVec.sle (isProp := false)

simproc [simp, seval] reduceZeroExtend' (zeroExtend' _ _) := fun e => do
  unless e.isAppOfArity ``zeroExtend' 4 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some w ← Nat.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  if h : v.n ≤ w then
    let lit : Literal := { n := w, value := v.value.zeroExtend' h }
    return .done { expr := lit.toExpr }
  else
    return .continue

simproc [simp, seval] reduceShiftLeftZeroExtend (shiftLeftZeroExtend _ _) := fun e => do
  unless e.isAppOfArity ``shiftLeftZeroExtend 3 do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← Nat.fromExpr? e.appArg! | return .continue
  let lit : Literal := { n := v.n + m, value := v.value.shiftLeftZeroExtend m }
  return .done { expr := lit.toExpr }

simproc [simp, seval] reduceExtracLsb' (extractLsb' _ _ _) := fun e => do
  unless e.isAppOfArity ``extractLsb' 4 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some start ← Nat.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let some len ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let lit : Literal := { n := len, value := v.value.extractLsb' start len }
  return .done { expr := lit.toExpr }

simproc [simp, seval] reduceReplicate (replicate _ _) := fun e => do
  unless e.isAppOfArity ``replicate 3 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some w ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let lit : Literal := { n := v.n * w, value := v.value.replicate w }
  return .done { expr := lit.toExpr }

simproc [simp, seval] reduceZeroExtend (zeroExtend _ _) := fun e => do
  unless e.isAppOfArity ``zeroExtend 3 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let lit : Literal := { n, value := v.value.zeroExtend n }
  return .done { expr := lit.toExpr }

end Std.BitVec
