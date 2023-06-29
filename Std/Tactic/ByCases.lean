/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Util
import Lean.Parser.Tactic

/-!
# `by_cases` and `if then else` tactics

This implements the `if` tactic, which is a structured proof version of `by_cases`.
It allows writing `if h : t then tac1 else tac2` for case analysis on `h : t`,
-/
open Lean.Elab.Tactic
open Lean Parser.Tactic

private def expandIfThenElse
    (ifTk thenTk elseTk pos neg : Syntax)
    (mkIf : Term → Term → TacticM Term) : TacticM Unit := do
  let mkCase tk holeOrTacticSeq mkName : TacticM (Term × Array (TSyntax `tactic)) := do
    if holeOrTacticSeq.isOfKind ``Parser.Term.syntheticHole then
      pure (⟨holeOrTacticSeq⟩, #[])
    else if holeOrTacticSeq.isOfKind ``Parser.Term.hole then
      pure (← mkName, #[])
    else
      let hole ← withFreshMacroScope mkName
      let holeId := hole.raw[1]
      let case ← (open TSyntax.Compat in `(tactic|
          case $holeId:ident =>%$tk
            -- annotate `then/else` with state after `case`
            with_annotate_state $tk skip
            $holeOrTacticSeq))
      pure (hole, #[case])
  let tag ← (← getMainGoal).getTag
  let posTag : Name ← MonadQuotation.addMacroScope (Meta.appendTag tag `pos);
  let negTag : Name ← MonadQuotation.addMacroScope (Meta.appendTag tag `neg);
  let (posHole, posCase) ← mkCase thenTk pos `(?$(mkIdent posTag))
  let (negHole, negCase) ← mkCase elseTk neg `(?$(mkIdent negTag))
  evalTactic (← `(tactic| (open Classical in
    refine%$ifTk $(← mkIf posHole negHole); $[$(posCase ++ negCase)]*)))

/--
In tactic mode, `if h : t then tac1 else tac2` can be used as alternative syntax for:
```
by_cases h : t
· tac1
· tac2
```
It performs case distinction on `h : t` or `h : ¬t` and `tac1` and `tac2` are the subproofs.

You can use `?_` or `_` for either subproof to delay the goal to after the tactic, but
if a tactic sequence is provided for `tac1` or `tac2` then it will require the goal to be closed
by the end of the block.
-/
syntax (name := tacDepIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " binderIdent " : " term " then") ppSpace matchRhs)
    ppDedent(ppSpace) ppRealFill("else " matchRhs)) : tactic

/--
In tactic mode, `if t then tac1 else tac2` is alternative syntax for:
```
by_cases t
· tac1
· tac2
```
It performs case distinction on `h† : t` or `h† : ¬t`, where `h†` is an anonymous
hypothesis, and `tac1` and `tac2` are the subproofs. (It doesn't actually use
nondependent `if`, since this wouldn't add anything to the context and hence would be
useless for proving theorems. To actually insert an `ite` application use
`refine if t then ?_ else ?_`.)
-/
syntax (name := tacIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace matchRhs)
    ppDedent(ppSpace) ppRealFill("else " matchRhs)) : tactic

elab_rules : tactic
  | `(tactic| if%$tk $h : $c then%$ttk $pos else%$etk $neg) =>
    expandIfThenElse tk ttk etk pos neg fun pos neg => `(if $h : $c then $pos else $neg)

elab_rules : tactic
  | `(tactic| if%$tk $c then%$ttk $pos else%$etk $neg) =>
    expandIfThenElse tk ttk etk pos neg fun pos neg => `(if h : $c then $pos else $neg)

-- This is an improved version of `by_cases` from core that uses `Decidable` if possible
macro_rules
  | `(tactic| by_cases $h : $e) =>
    `(tactic| open Classical in if $h:ident : $e then _ else _)
macro_rules | `(tactic| by_cases $e) => `(tactic| by_cases h : $e)
