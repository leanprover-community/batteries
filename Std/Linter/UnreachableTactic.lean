/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Linter.Util

namespace Std.Linter
open Lean Elab Command Linter

/--
Enables the 'unreachable tactic' linter. This will warn on any tactics that are never executed.
For example, in `example : True := by trivial <;> done`, the tactic `done` is never executed
because `trivial` produces no subgoals; you could put `sorry` or `apply I_don't_exist`
or anything else there and no error would result.

A common source of such things is `simp <;> tac` in the case that `simp` improves and
closes a subgoal that was previously being closed by `tac`.
-/
register_option linter.unreachableTactic : Bool := {
  defValue := true
  descr := "enable the 'unreachable tactic' linter"
}

namespace UnreachableTactic
/-- Gets the value of the `linter.unreachableTactic` option. -/
def getLinterUnreachableTactic (o : Options) : Bool := getLinterValue linter.unreachableTactic o

/-- The monad for collecting used tactic syntaxes. -/
abbrev M (ω) := StateRefT (HashMap String.Range Syntax) (ST ω)

/--
A list of blacklisted syntax kinds, which are expected to have subterms that contain
unevaluated tactics.
-/
initialize ignoreTacticKinds : NameHashSet ←
  pure <| HashSet.empty
    |>.insert ``Parser.Term.binderTactic
    |>.insert ``Lean.Parser.Term.dynamicQuot
    |>.insert ``Lean.Parser.Tactic.quotSeq

/-- Is this a syntax kind that contains intentionally unevaluated tactic subterms? -/
def isIgnoreTacticKind (k : SyntaxNodeKind) : Bool :=
  match k with
  | .str _ "quot" => true
  | _ => ignoreTacticKinds.contains k

variable (isTacKind : SyntaxNodeKind → Bool) in
/-- Accumulates the set of tactic syntaxes that should be evaluated at least once. -/
@[specialize] partial def getTactics {ω} (stx : Syntax) : M ω Unit := do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind k then
      args.forM getTactics
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx

mutual
variable (isTacKind : SyntaxNodeKind → Bool)
/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def eraseUsedTacticsList (trees : PersistentArray InfoTree) : M ω Unit :=
  trees.forM eraseUsedTactics

/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def eraseUsedTactics : InfoTree → M ω Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
        modify (·.erase r)
    eraseUsedTacticsList c
  | .context _ t => eraseUsedTactics t
  | .hole _ => pure ()

end

/-- The main entry point to the unreachable tactic linter. -/
partial def unreachableTacticLinter : Linter := fun stx => do
  unless getLinterUnreachableTactic (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let tactics := cats.find! `tactic |>.kinds
  let convs := cats.find! `conv |>.kinds
  let trees ← getInfoTrees
  let go {ω} : M ω Unit := do
    getTactics (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTacticsList trees
  let (_, map) := runST fun _ => go.run {}
  let unreachable := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unreachable.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then
      continue
    logLint linter.unreachableTactic stx "this tactic is never executed"
    last := r

initialize addLinter unreachableTacticLinter
