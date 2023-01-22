/-
Copyright (c) 2023 Parth Shastri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parth Shastri
-/
import Lean.Compiler.CSimpAttr
import Lean.Elab.Predefinition

/-!
# Define the `#compile inductive` command.
-/

namespace Std.Util.CompileInductive

open Lean

private def replaceConst (old new : Name) (e : Expr) : Expr :=
  e.replace λ | .const n us => if n == old then some (.const new us) else none | _ => none

open Meta

private def mkFunExts' (xs : Array Expr) (e : Expr) (βfg : Expr × Expr × Expr) : MetaM Expr :=
  Prod.fst <$> xs.foldrM (init := (e, βfg)) λ x (e, β, f, g) => do
    let α ← inferType x
    let f ← mkLambdaFVars #[x] f
    let g ← mkLambdaFVars #[x] g
    return (
      mkApp5
        (.const ``funext [(← inferType α).sortLevel!, (← inferType β).sortLevel!])
        α
        (← mkLambdaFVars #[x] β)
        f
        g
        (← mkLambdaFVars #[x] e),
      ← mkForallFVars #[x] β,
      f,
      g
    )

private def mkFunExts (e : Expr) : MetaM Expr := do
  forallTelescope (← inferType e) λ xs body => do
    let some βfg := (← whnf body).eq?
      | throwError "expected equality"
    mkFunExts' xs (mkAppN e xs) βfg

private def mkEq (α a b : Expr) : MetaM Expr := do
  return mkApp3 (.const ``Eq [(← inferType α).sortLevel!]) α a b

open Elab

/--
Compile the recursor for `i`.
-/
def compileInductive (i : Name) : TermElabM Unit := do
  _ ← getConstInfoInduct i
  let rv ← getConstInfoRec <| mkRecName i
  if ← isProp rv.type then
    logWarning m!"not compiling {rv.name}"
    return
  unless rv.numMotives == 1 do
    throwError "mutual/nested inductives unsupported"
  let levels := rv.levelParams.map .param
  let name ← MonadQuotation.addMacroScope rv.name
  addPreDefinitions #[{
    ref := ← getRef
    kind := .def
    levelParams := rv.levelParams
    modifiers := {}
    declName := name
    type := rv.type
    value := ← forallTelescope rv.type λ xs body => do
      let val := .const (mkCasesOnName i) levels
      let val := mkAppN val xs[:rv.numParams]
      let val := .app val <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] body
      let val := mkAppN val xs[rv.getFirstIndexIdx:]
      let val := mkAppN val <| rv.rules.toArray.map λ rule =>
        .beta (replaceConst rv.name name rule.rhs) xs[:rv.getFirstIndexIdx]
      mkLambdaFVars xs val
  }] {}
  let some eqn ← getUnfoldEqnFor? name true
    | throwError "no unfold equation found"
  let old := .const rv.name levels
  let new := .const name levels
  let name ← MonadQuotation.addMacroScope <| rv.name.str "eq"
  addDecl <| .thmDecl {
    name
    type := ← mkEq rv.type old new
    levelParams := rv.levelParams
    value := ← forallTelescope rv.type λ xs body => do
      let eqn := mkAppN (.const eqn levels) xs[:rv.getFirstIndexIdx]
      let levels := .zero :: levels.tail!
      let pf := .const rv.name levels
      let pf := mkAppN pf xs[:rv.numParams]
      let old := mkAppN old xs
      let new := mkAppN new xs
      let motive ← mkLambdaFVars xs[rv.getFirstIndexIdx:] <| ← mkEq body old new
      let pf := .app pf motive
      let pf := mkAppN pf <| ← rv.rules.toArray.zip xs[rv.getFirstMinorIdx:] |>.mapM λ (rule, minor) => do
        forallTelescope ((← inferType minor).replaceFVar xs[rv.numParams]! motive) λ ys body' => do
          let pf' ← mkEqRefl <| mkAppN minor ys[:rule.nfields]
          let pf' ← ys[rule.nfields:].foldlM (λ pf' y => do mkCongr pf' (← mkFunExts y)) pf'
          let eqn := mkAppN eqn body'.getAppArgs
          let eqn ← mkEqSymm eqn
          let pf' ← mkEqTrans pf' eqn
          mkLambdaFVars ys pf'
      let pf := mkAppN pf xs[rv.getFirstIndexIdx:]
      mkFunExts' xs pf (body, old, new)
  }
  Compiler.CSimp.add name .global
  compileDecls <| [mkRecOnName i, mkBRecOnName i].filter (← getEnv).contains

/--
`#compile inductive i` compiles the recursor for `i`.
-/
elab "#compile " "inductive " i:ident : command => Command.liftTermElabM do
  compileInductive <| ← resolveGlobalConstNoOverload i
