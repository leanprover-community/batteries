/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Batteries.Lean.AttributeExtra
public meta import Lean.Linter.Basic
public meta import Lean.Elab.InfoTree.Types
import Lean.Message
import Lean.Syntax

public meta section

namespace Batteries.Linter
open Lean Elab Command Linter Std

/--
Enables the 'unnecessary `<;>`' linter. This will warn whenever the `<;>` tactic combinator
is used when `;` would work.

```
example : True := by apply id <;> trivial
```
The `<;>` is unnecessary here because `apply id` only makes one subgoal.
Prefer `apply id; trivial` instead.

In some cases, the `<;>` is syntactically necessary because a single tactic is expected:
```
example : True := by
  cases () with apply id <;> apply id
  | unit => trivial
```
In this case, you should use parentheses, as in `(apply id; apply id)`:
```
example : True := by
  cases () with (apply id; apply id)
  | unit => trivial
```
-/
register_option linter.unnecessarySeqFocus : Bool := {
  defValue := true
  descr := "enable the 'unnecessary <;>' linter"
}
example : True := by
  cases () with apply id <;> apply id
  | unit => trivial

namespace UnnecessarySeqFocus

/-- Gets the value of the `linter.unnecessarySeqFocus` option. -/
def getLinterUnnecessarySeqFocus (o : LinterOptions) : Bool :=
  getLinterValue linter.unnecessarySeqFocus o

/--
The `multigoal` attribute keeps track of tactics that operate on multiple goals,
meaning that `tac` acts differently from `focus tac`. This is used by the
'unnecessary `<;>`' linter to prevent false positives where `tac <;> tac'` cannot
be replaced by `(tac; tac')` because the latter would expose `tac` to a different set of goals.
-/
initialize multigoalAttr : TagAttributeExtra ←
  registerTagAttributeExtra `multigoal "this tactic acts on multiple goals" [
    ``Parser.Tactic.«tacticNext_=>_»,
    ``Parser.Tactic.allGoals,
    ``Parser.Tactic.anyGoals,
    ``Parser.Tactic.case,
    ``Parser.Tactic.case',
    ``Parser.Tactic.Conv.«convNext__=>_»,
    ``Parser.Tactic.Conv.allGoals,
    ``Parser.Tactic.Conv.anyGoals,
    ``Parser.Tactic.Conv.case,
    ``Parser.Tactic.Conv.case',
    ``Parser.Tactic.rotateLeft,
    ``Parser.Tactic.rotateRight,
    ``Parser.Tactic.show,
    ``Parser.Tactic.tacticStop_
  ]

/-- The monad for collecting used tactic syntaxes.
- `some stx` means that this `<;>` syntax has only been used unnecessarily.
- `none` means that this `<;>` syntax was necessary at least once, so we won't warn about it. -/
abbrev M := StateRefT (Std.HashMap Lean.Syntax.Range (Option Syntax)) BaseIO

/--
Traverse the info tree down a given path.
Each `(n, i)` means that the array must have length `n` and we will descend into the `i`'th child.
-/
def getPath : Info → PersistentArray InfoTree → List ((n : Nat) × Fin n) → Option Info
  | i, _, [] => some i
  | _, c, ⟨n, i, h⟩::ns =>
    if e : c.size = n then
      if let .node i c' := c[i] then getPath i c' ns else none
    else none

mutual
variable (env : Environment)
/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def markUsedTacticsList (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM markUsedTactics

/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def markUsedTactics : InfoTree → M Unit
  | .node i c => do
    markUsedTacticsList c
    let .ofTacticInfo i := i | pure ()
    if i.stx.getKind == ``Parser.Tactic.«tactic_<;>_» then
      let some r := i.stx.getRange? true | pure ()
      let isBad := do
        unless i.goalsBefore.length == 1 || !multigoalAttr.hasTag env i.stx[0].getKind do
          none
        -- Note: this uses the exact sequence of tactic applications
        -- in the macro expansion of `<;> : tactic`
        let .ofTacticInfo i ← getPath (.ofTacticInfo i) c
          [⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨5, 0⟩] | none
        guard <| i.goalsAfter.length == 1
      modify fun s => if isBad.isSome then s.insertIfNew r i.stx else s.insert r none
    else if i.stx.getKind == ``Parser.Tactic.Conv.«conv_<;>_» then
      let some r := i.stx.getRange? true | pure ()
      let isBad := do
        unless i.goalsBefore.length == 1 || !multigoalAttr.hasTag env i.stx[0].getKind do
          none
        -- Note: this uses the exact sequence of tactic applications
        -- in the macro expansion of `<;> : conv`
        let .ofTacticInfo i ← getPath (.ofTacticInfo i) c
          [⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨5, 0⟩] | none
        guard <| i.goalsAfter.length == 1
      modify fun s => if isBad.isSome then s.insertIfNew r i.stx else s.insert r none
  | .context _ t => markUsedTactics t
  | .hole _ => pure ()

end

@[inherit_doc Batteries.Linter.linter.unnecessarySeqFocus]
def unnecessarySeqFocusLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterUnnecessarySeqFocus (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let env ← getEnv
  let (_, map) ← markUsedTacticsList env trees |>.run {}
  let unused := map.fold (init := #[]) fun acc r stx? =>
    if let some stx := stx? then acc.push (stx[1].getRange?.getD r, stx[1]) else acc
  let key (r : Lean.Syntax.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : Lean.Syntax.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    logLint linter.unnecessarySeqFocus stx
      "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
    last := r

initialize addLinter unnecessarySeqFocusLinter
