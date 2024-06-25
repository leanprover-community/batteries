/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Tactic.Unreachable

namespace Batteries.Linter
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
abbrev M := StateRefT (HashMap String.Range Syntax) IO

/--
A list of blacklisted syntax kinds, which are expected to have subterms that contain
unevaluated tactics.
-/
initialize ignoreTacticKindsRef : IO.Ref NameHashSet ←
  IO.mkRef <| HashSet.empty
    |>.insert ``Parser.Term.binderTactic
    |>.insert ``Lean.Parser.Term.dynamicQuot
    |>.insert ``Lean.Parser.Tactic.quotSeq
    |>.insert ``Lean.Parser.Tactic.tacticStop_
    |>.insert ``Lean.Parser.Command.notation
    |>.insert ``Lean.Parser.Command.mixfix
    |>.insert ``Lean.Parser.Tactic.discharger

/-- Is this a syntax kind that contains intentionally unevaluated tactic subterms? -/
def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
  match k with
  | .str _ "quot" => true
  | _ => ignoreTacticKinds.contains k

/--
Adds a new syntax kind whose children will be ignored by the `unreachableTactic` linter.
This should be called from an `initialize` block.
-/
def addIgnoreTacticKind (kind : SyntaxNodeKind) : IO Unit :=
  ignoreTacticKindsRef.modify (·.insert kind)

variable (ignoreTacticKinds : NameHashSet) (isTacKind : SyntaxNodeKind → Bool) in
/-- Accumulates the set of tactic syntaxes that should be evaluated at least once. -/
@[specialize] partial def getTactics (stx : Syntax) : M Unit := do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM getTactics
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx

mutual
variable (isTacKind : SyntaxNodeKind → Bool)
/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def eraseUsedTacticsList (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM eraseUsedTactics

/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def eraseUsedTactics : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
        modify (·.erase r)
    eraseUsedTacticsList c
  | .context _ t => eraseUsedTactics t
  | .hole _ => pure ()

end

@[inherit_doc Batteries.Linter.linter.unreachableTactic]
def unreachableTacticLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterUnreachableTactic (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  let trees ← getInfoTrees
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTacticsList trees
  let (_, map) ← go.run {}
  let unreachable := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unreachable.qsort (key ·.1 < key ·.1) do
    if stx.getKind ∈ [``Batteries.Tactic.unreachable, ``Batteries.Tactic.unreachableConv] then
      continue
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    logLint linter.unreachableTactic stx "this tactic is never executed"
    last := r

initialize addLinter unreachableTacticLinter
