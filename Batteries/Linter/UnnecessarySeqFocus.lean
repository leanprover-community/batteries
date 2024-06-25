/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Lean.AttributeExtra

namespace Batteries.Linter
open Lean Elab Command Linter

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
def getLinterUnnecessarySeqFocus (o : Options) : Bool :=
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
    ``Parser.Tactic.tacticShow_,
    ``Parser.Tactic.tacticStop_
  ]

/-- The information we record for each `<;>` node appearing in the syntax. -/
structure Entry where
  /-- The `<;>` node itself. -/
  stx : Syntax
  /--
  * `true`: this `<;>` has been used unnecessarily at least once
  * `false`: it has never been executed
  * If it has been used properly at least once, the entry is removed from the table.
  -/
  used : Bool

/-- The monad for collecting used tactic syntaxes. -/
abbrev M (ω) := StateRefT (HashMap String.Range Entry) (ST ω)

/-- True if this is a `<;>` node in either `tactic` or `conv` classes. -/
@[inline] def isSeqFocus (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Tactic.«tactic_<;>_» || k == ``Parser.Tactic.Conv.«conv_<;>_»

/-- Accumulates the set of tactic syntaxes that should be evaluated at least once. -/
@[specialize] partial def getTactics {ω} (stx : Syntax) : M ω Unit := do
  if let .node _ k args := stx then
    if isSeqFocus k then
      let r := stx.getRange? true
      if let some r := r then
        modify fun m => m.insert r { stx, used := false }
    args.forM getTactics

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
partial def markUsedTacticsList (trees : PersistentArray InfoTree) : M ω Unit :=
  trees.forM markUsedTactics

/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def markUsedTactics : InfoTree → M ω Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
      if let some entry := (← get).find? r then
      if i.stx.getKind == ``Parser.Tactic.«tactic_<;>_» then
        let isBad := do
          unless i.goalsBefore.length == 1 || !multigoalAttr.hasTag env i.stx[0].getKind do
            none
          -- Note: this uses the exact sequence of tactic applications
          -- in the macro expansion of `<;> : tactic`
          let .ofTacticInfo i ← getPath (.ofTacticInfo i) c
            [⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨5, 0⟩] | none
          guard <| i.goalsAfter.length == 1
        modify fun s => if isBad.isSome then s.insert r { entry with used := true } else s.erase r
      else if i.stx.getKind == ``Parser.Tactic.Conv.«conv_<;>_» then
        let isBad := do
          unless i.goalsBefore.length == 1 || !multigoalAttr.hasTag env i.stx[0].getKind do
            none
          -- Note: this uses the exact sequence of tactic applications
          -- in the macro expansion of `<;> : conv`
          let .ofTacticInfo i ← getPath (.ofTacticInfo i) c
            [⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨5, 0⟩] | none
          guard <| i.goalsAfter.length == 1
        modify fun s => if isBad.isSome then s.insert r { entry with used := true } else s.erase r
    markUsedTacticsList c
  | .context _ t => markUsedTactics t
  | .hole _ => pure ()

end

@[inherit_doc Batteries.Linter.linter.unnecessarySeqFocus]
def unnecessarySeqFocusLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterUnnecessarySeqFocus (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let env ← getEnv
  let go {ω} : M ω Unit := do
    getTactics stx
    markUsedTacticsList env trees
  let (_, map) := runST fun _ => go.run {}
  let unused := map.fold (init := #[]) fun acc r { stx, used } =>
    if used then acc.push (stx[1].getRange?.getD r, stx[1]) else acc
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    logLint linter.unnecessarySeqFocus stx
      "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
    last := r

initialize addLinter unnecessarySeqFocusLinter
