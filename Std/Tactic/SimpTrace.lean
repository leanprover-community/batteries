/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.ElabRules
import Lean.Elab.Tactic.Simp
import Std.Lean.Parser
import Std.Tactic.TryThis

/-!
# `simp?` tactic

The `simp?` tactic is a simple wrapper around the simp with trace behavior implemented in core.
-/
namespace Std.Tactic
open Lean Elab Parser Tactic Meta Simp

/-- The common arguments of `simp?` and `simp?!`. -/
syntax simpTraceArgsRest := (config)? (discharger)? (&" only")? (simpArgs)? (location)?

/--
`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.
-/
syntax (name := simpTrace) "simp?" "!"? simpTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"simp?!" rest:simpTraceArgsRest : tactic => `(tactic| simp?%$tk ! $rest)

open TSyntax.Compat in
-- adapted from traceSimpCall
/-- Constructs the syntax for a simp call, for use with `simp?`. -/
def mkSimpCallStx (stx : Syntax) (usedSimps : UsedSimps) : MetaM (TSyntax `tactic) := do
  let mut stx := stx.unsetTrailing
  if stx[3].isNone then
    stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
  let mut args := #[]
  let mut localsOrStar := some #[]
  let lctx ← getLCtx
  let env ← getEnv
  for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
    match thm with
    | .decl declName => -- global definitions in the environment
      if env.contains declName && !simpOnlyBuiltins.contains declName then
        args := args.push (← `(Parser.Tactic.simpLemma|
          $(mkIdent (← unresolveNameGlobal declName)):ident))
    | .fvar fvarId => -- local hypotheses in the context
      if let some ldecl := lctx.find? fvarId then
        localsOrStar := localsOrStar.bind fun locals =>
          if !ldecl.userName.isInaccessibleUserName &&
              (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
            some (locals.push ldecl.userName)
          else
            none
      -- Note: the `if let` can fail for `simp (config := {contextual := true})` when
      -- rewriting with a variable that was introduced in a scope. In that case we just ignore.
    | .stx _ thmStx => -- simp theorems provided in the local invocation
      args := args.push thmStx
    | .other _ => -- Ignore "special" simp lemmas such as constructed by `simp_all`.
      pure ()     -- We can't display them anyway.
  if let some locals := localsOrStar then
    args := args ++ (← locals.mapM fun id => `(Parser.Tactic.simpLemma| $(mkIdent id):ident))
  else
    args := args.push (← `(Parser.Tactic.simpStar| *))
  let argsStx := if args.isEmpty then #[] else #[mkAtom "[", (mkAtom ",").mkSep args, mkAtom "]"]
  pure <| stx.setArg 4 (mkNullNode argsStx)

elab_rules : tactic
  | `(tactic|
      simp?%$tk $[!%$bang]? $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    let stx ← if bang.isSome then
      `(tactic| simp!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)
    else
      `(tactic| simp%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]? $(loc)?)
    let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
    let usedSimps ← dischargeWrapper.with fun discharge? =>
      simpLocation ctx discharge? <| (loc.map expandLocation).getD (.targets #[] true)
    let stx ← mkSimpCallStx stx usedSimps
    TryThis.addSuggestion tk stx (origSpan? := ← getRef)

/-- The common arguments of `simp_all?` and `simp_all?!`. -/
syntax simpAllTraceArgsRest := (config)? (discharger)? (&" only")? (dsimpArgs)?

@[inherit_doc simpTrace]
syntax (name := simpAllTrace) "simp_all?" "!"? simpAllTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"simp_all?!" rest:simpAllTraceArgsRest : tactic => `(tactic| simp_all?%$tk ! $rest)

elab_rules : tactic
  | `(tactic| simp_all?%$tk $[!%$bang]? $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?) => do
    let stx ← if bang.isSome then
      `(tactic| simp_all!%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)
    else
      `(tactic| simp_all%$tk $(config)? $(discharger)? $[only%$o]? $[[$args,*]]?)
    let { ctx, .. } ← mkSimpContext stx (eraseLocal := true)
      (kind := .simpAll) (ignoreStarArg := true)
    let (result?, usedSimps) ← simpAll (← getMainGoal) ctx
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    let stx ← mkSimpCallStx stx usedSimps
    TryThis.addSuggestion tk stx (origSpan? := ← getRef)

/-- The common arguments of `dsimp?` and `dsimp?!`. -/
syntax dsimpTraceArgsRest := (config)? (&" only")? (dsimpArgs)? (location)?

-- TODO: move to core
/-- Implementation of `dsimp`. -/
def dsimpLocation' (ctx : Simp.Context) (loc : Location) : TacticM Simp.UsedSimps := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  /-- Implementation of `dsimp`. -/
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Simp.UsedSimps := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ←
      dsimpGoal mvarId ctx (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    pure usedSimps

@[inherit_doc simpTrace]
syntax (name := dsimpTrace) "dsimp?" "!"? dsimpTraceArgsRest : tactic

@[inherit_doc simpTrace]
macro tk:"dsimp?!" rest:dsimpTraceArgsRest : tactic => `(tactic| dsimp?%$tk ! $rest)

elab_rules : tactic
  | `(tactic| dsimp?%$tk $[!%$bang]? $(config)? $[only%$o]? $[[$args,*]]? $(loc)?) => do
    let stx ← if bang.isSome then
      `(tactic| dsimp!%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)
    else
      `(tactic| dsimp%$tk $(config)? $[only%$o]? $[[$args,*]]? $(loc)?)
    let { ctx, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    let usedSimps ← dsimpLocation' ctx <| (loc.map expandLocation).getD (.targets #[] true)
    let stx ← mkSimpCallStx stx usedSimps
    TryThis.addSuggestion tk stx (origSpan? := ← getRef)
