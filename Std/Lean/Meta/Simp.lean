/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Gabriel Ebner, Floris van Doorn
-/
import Std.Tactic.OpenPrivate
import Std.Lean.Meta.DiscrTree

/-!
# Helper functions for using the simplifier.

[TODO] Reunification of `mkSimpContext'` with core.
-/

namespace Lean

namespace Meta.Simp
open Elab.Tactic

/-- Flip the proof in a `Simp.Result`. -/
def mkEqSymm (e : Expr) (r : Simp.Result) : MetaM Simp.Result :=
  ({ expr := e, proof? := · }) <$>
  match r.proof? with
  | none => pure none
  | some p => some <$> Meta.mkEqSymm p

/-- Construct the `Expr` `cast h e`, from a `Simp.Result` with proof `h`. -/
def mkCast (r : Simp.Result) (e : Expr) : MetaM Expr := do
  mkAppM ``cast #[← r.getProof, e]

export private mkDischargeWrapper from Lean.Elab.Tactic.Simp

/-- Construct a `Simp.DischargeWrapper` from the `Syntax` for a `simp` discharger. -/
add_decl_doc mkDischargeWrapper

open Simp

/-- Make `MkSimpContextResult` giving data instead of Syntax. Doesn't support arguments.
Intended to be very similar to `Lean.Elab.Tactic.mkSimpContext`
Todo: support arguments. -/
def mkSimpContextResult (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM MkSimpContextResult := do
  match dischargeWrapper with
  | .default => pure ()
  | _ =>
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    Meta.getSimpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx : Simp.Context := {
    config       := cfg
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !hasStar then
    return { ctx, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := { ctx with simpTheorems }
    return { ctx, dischargeWrapper }

/-- Make `Simp.Context` giving data instead of Syntax. Doesn't support arguments.
Intended to be very similar to `Lean.Elab.Tactic.mkSimpContext`
Todo: support arguments. -/
def mkSimpContext (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM Simp.Context := do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

-- This has been copied from Lean, where it is unfortunately private.
-- Notice there is considerable duplication with `mkSimpContextResult` above.
-- Ideally this would be resolved in Lean,
-- by cleanly dividing this code into the pieces that handle `Syntax`
-- and the pieces that don't, and making these functions public.
/--
If `ctx == false`, the config argument is assumed to have type `Meta.Simp.Config`,
and `Meta.Simp.ConfigCtx` otherwise.
If `ctx == false`, the `discharge` option must be none
-/
def mkSimpContext' (simpTheorems : SimpTheorems) (stx : Syntax) (eraseLocal : Bool)
    (kind := SimpKind.simp) (ctx := false) (ignoreStarArg : Bool := false) :
    TacticM MkSimpContextResult := do
  if ctx && !stx[2].isNone then
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) {}
  else
    pure simpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) {
    config       := (← elabSimpConfig stx[1] (kind := kind))
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !r.starArg || ignoreStarArg then
    return { r with dischargeWrapper }
  else
    let mut simpTheorems := r.ctx.simpTheorems
    /-
    When using `zeta := false`, we do not expand let-declarations when using `[*]`.
    Users must explicitly include it in the list.
    -/
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    return { ctx := { r.ctx with simpTheorems }, dischargeWrapper }

end Simp

end Lean.Meta
