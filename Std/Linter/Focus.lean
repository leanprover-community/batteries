/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Lean.Command
import Std.Tactic.Unreachable

import Lean.Elab.Tactic.BuiltinTactic

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
register_option linter.focus : Bool := {
  defValue := true
  descr := "enable the 'focus' linter"
}

namespace Focus
/-- Gets the value of the `linter.focus` option. -/
def getLinterFocus (o : Options) : Bool := getLinterValue linter.focus o

/-- The monad for collecting used tactic syntaxes. -/
abbrev M := StateRefT (HashMap String.Range Syntax) IO

#check Lean.Elab.Tactic.evalTacticCDot

/--
A list of whitelisted syntax kinds, which are allowed to be used with multiple goals present.
-/
initialize ignoreTacticKindsRef : IO.Ref NameHashSet ←
  IO.mkRef <| HashSet.empty
    |>.insert ``cdot
    -- |>.insert ``Parser.Term.binderTactic
    -- |>.insert ``Lean.Parser.Term.dynamicQuot
    -- |>.insert ``Lean.Parser.Tactic.quotSeq
    -- |>.insert ``Lean.Parser.Tactic.tacticStop_
    -- |>.insert ``Lean.Parser.Command.notation
    -- |>.insert ``Lean.Parser.Command.mixfix
    -- |>.insert ``Lean.Parser.Tactic.discharger

variable (ignoreTacticKinds : NameHashSet)

-- /-- Is this a syntax kind that contains intentionally unevaluated tactic subterms? -/
-- def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
--   match k with
--   | .str _ "quot" => true
--   | _ => ignoreTacticKinds.contains k

/--
Adds a new syntax kind whose children will be ignored by the `unreachableTactic` linter.
This should be called from an `initialize` block.
-/
def addIgnoreTacticKind (kind : SyntaxNodeKind) : IO Unit :=
  ignoreTacticKindsRef.modify (·.insert kind)

-- variable (ignoreTacticKinds : NameHashSet) (isTacKind : SyntaxNodeKind → Bool) in
-- /-- Accumulates the set of tactic syntaxes that should be evaluated at least once. -/
-- @[specialize] partial def getTactics (stx : Syntax) : M Unit := do
--   if let .node _ k args := stx then
--     if !isIgnoreTacticKind ignoreTacticKinds k then
--       args.forM getTactics
--     if isTacKind k then
--       if let some r := stx.getRange? true then
--         modify fun m => m.insert r stx

mutual
partial def findUnfocusedTacticsList (ctx : ContextInfo) (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM (findUnfocusedTactics ctx)

partial def findUnfocusedTactics : ContextInfo → InfoTree → M Unit
  | ctx, .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
        if i.goalsBefore == i.goalsAfter then return ()
        match i.goalsBefore, i.goalsAfter with
        | [_], _ => pure ()
        | _ :: bs, a :: as =>
          if as == bs || a :: as == bs then
            dbg_trace s!"Syntax: {i.stx}"
            if let .node _ k _ := i.stx then
              if ignoreTacticKinds.contains k then
                return ()
              dbg_trace s!"Tactic kind: {k}"
            let f ← i.format ctx
            dbg_trace s!"TacticInfo: {f}"
            modify (·.insert r i.stx)
        | _, _ => pure ()
    findUnfocusedTacticsList ctx c
  | _, .context ctx' t => findUnfocusedTactics ctx' t
  | _, .hole _ => pure ()
end

/-- The main entry point to the unreachable tactic linter. -/
def focusLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterFocus (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  -- let cats := (Parser.parserExtension.getState (← getEnv)).categories
  -- -- These lookups may fail when the linter is run in a fresh, empty environment
  -- let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
  --   | return
  -- let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
  --   | return
  let trees ← getInfoTrees
  dbg_trace s!"InfoTrees:\n{← trees.toList.mapM (·.format)}"
  -- Hack:
  let ctx : ContextInfo := { env := ← getEnv, fileMap := default, ngen := default }
  let (_, map) ← (findUnfocusedTacticsList (← ignoreTacticKindsRef.get) ctx trees).run {}
  let unreachable := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unreachable.qsort (key ·.1 < key ·.1) do
    if stx.getKind ∈ [``Std.Tactic.unreachable, ``Std.Tactic.unreachableConv] then continue
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    logLint linter.focus stx "this tactic is unfocused"
    last := r

initialize addLinter focusLinter
