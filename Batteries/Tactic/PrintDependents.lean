/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
# `#print dependents` command

This is a variation on `#print axioms` where one instead specifies the axioms to avoid,
and it prints a list of all the theorems in the file that depend on that axiom, and the list
of all theorems directly referenced that are "to blame" for this dependency. Useful for debugging
unexpected dependencies.
-/
namespace Batteries.Tactic
open Lean Elab Command

namespace CollectDependents

/-- Collects the result of a `CollectDependents` query. -/
structure State where
  /-- If true, an axiom not in the initial list will be considered as marked. -/
  otherAxiom : Bool := true
  /-- The cached results on visited constants. -/
  result : NameMap Bool := {}

/-- The monad used by `CollectDependents`. -/
abbrev M := ReaderT Environment $ StateM State

/--
Constructs the initial state, marking the constants in `cs`. The result of `collect` will say
whether a given declaration depends transitively on one of these constants.

If `otherAxiom` is true, any axiom not specified in `cs` will also be tracked.
-/
def mkState (cs : Array (Name × Bool)) (otherAxiom := true) : State :=
  { otherAxiom, result := cs.foldl (fun r (c, b) => r.insert c b) {} }

/-- Collect the results for a given constant. -/
partial def collect (c : Name) : M Bool := do
  let collectExpr (e : Expr) : M Bool := e.getUsedConstants.anyM collect
  let s ← get
  if let some b := s.result.find? c then return b
  modify fun s => { s with result := s.result.insert c false }
  let env ← read
  let r ← match env.find? c with
    | some (ConstantInfo.axiomInfo _)  => pure s.otherAxiom
    | some (ConstantInfo.defnInfo v)   => collectExpr v.type <||> collectExpr v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr v.type <||> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr v.type <||> collectExpr v.value
    | some (ConstantInfo.quotInfo _)   => pure false
    | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
    | some (ConstantInfo.recInfo v)    => collectExpr v.type
    | some (ConstantInfo.inductInfo v) => collectExpr v.type <||> v.ctors.anyM collect
    | none                             => pure false
  modify fun s => { s with result := s.result.insert c r }
  pure r

end CollectDependents

/--
The command `#print dependents X Y` prints a list of all the declarations in the file that
transitively depend on `X` or `Y`. After each declaration, it shows the list of all declarations
referred to directly in the body which also depend on `X` or `Y`.

For example, `#print axioms bar'` below shows that `bar'` depends on `Classical.choice`, but not
why. `#print dependents Classical.choice` says that `bar'` depends on `Classical.choice` because
it uses `foo` and `foo` uses `Classical.em`. `bar` is not listed because it is proved without using
`Classical.choice`.
```
import Batteries.Tactic.PrintDependents

theorem foo : x = y ∨ x ≠ y := Classical.em _
theorem bar : 1 = 1 ∨ 1 ≠ 1 := by simp
theorem bar' : 1 = 1 ∨ 1 ≠ 1 := foo

#print axioms bar'
-- 'bar'' depends on axioms: [Classical.choice, Quot.sound, propext]

#print dependents Classical.choice
-- foo: Classical.em
-- bar': foo
```

-/
elab tk:"#print" &"dependents" ids:(ppSpace colGt ident)* : command => do
  let env ← getEnv
  let ids ← ids.mapM fun c => return (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c, true)
  let init := CollectDependents.mkState ids false
  let mut state := init
  let mut out := #[]
  for (c, _) in env.constants.map₂ do
    let (b, state') := CollectDependents.collect c |>.run env |>.run state
    state := state'
    if b then
      if let some ranges ← findDeclarationRanges? c then
        out := out.push (c, ranges.range.pos.1)
  let msg ← out.qsort (·.2 < ·.2) |>.mapM fun (c, _) => do
    let mut msg := m!"{MessageData.ofConst (← mkConstWithLevelParams c)}: "
    if init.result.contains c then
      msg := msg ++ m!"<specified>"
    else
      let consts := match env.find? c with
      | some (ConstantInfo.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (ConstantInfo.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (ConstantInfo.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
      | some (ConstantInfo.ctorInfo v)   => v.type.getUsedConstants
      | some (ConstantInfo.recInfo v)    => v.type.getUsedConstants
      | some (ConstantInfo.inductInfo v) => v.type.getUsedConstants ++ v.ctors
      | _                                => #[]
      for c in RBTree.fromArray consts Name.cmp do
        if state.result.find? c = some true then
          msg := msg ++ m!"{MessageData.ofConst (← mkConstWithLevelParams c)} "
    return msg
  logInfoAt tk (.joinSep msg.toList "\n")
