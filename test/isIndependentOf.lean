import Batteries.Lean.Meta.Basic
import Batteries.Tactic.PermuteGoals
import Lean.Meta.Tactic.IndependentOf

open Lean Meta Elab.Tactic

elab "check_indep" : tactic => do
  match ← getGoals with
  | [] => throwError "Expected goal"
  | g :: l =>
    let res := if ←g.isIndependentOf l then "" else "not "
    let t ← instantiateMVars (← g.getType)
    logWarning s!"{←ppExpr (.mvar g)} : {←ppExpr t} is {res}independent of:"
    l.forM fun g' => do
      logInfo s!"  {←ppExpr (.mvar g')} : {←ppExpr (← g'.getType)}"
      let ppD (l : LocalDecl) : TacticM PUnit := do
        logInfo s!"    {←ppExpr (.fvar l.fvarId)} : {←ppExpr l.type}"
      let _ ← (←g'.getDecl).lctx.forM ppD
      pure ()

/-- warning: ?w : Nat is not independent of: -/
#guard_msgs(warning, drop info) in
example : ∃ (n : Nat), ∀(x : Fin n), x.val = 0 := by
  apply Exists.intro
  intro x
  swap
  check_indep
  exact 0
  revert x
  intro ⟨x, lt⟩
  contradiction

-- This is a tricker one, where the dependency is via a hypothesis.
/-- warning: ?w : Nat is not independent of: -/
#guard_msgs(warning, drop info) in
example : ∃ (n : Nat), ∀(x : Fin n) (y : Nat), x.val = y → y = 0 := by
  apply Exists.intro
  intro x y p
  swap
  check_indep
  exact 0
  revert x
  intro ⟨x, lt⟩
  contradiction
