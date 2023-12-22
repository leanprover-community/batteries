/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.CoreM
import Std.Lean.SMap

namespace Lean.Name

/-- Returns true if the name has any numeric components. -/
def hasNum : Name → Bool
  | .anonymous => false
  | .str p _ => p.hasNum
  | .num _ _ => true

/-- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternalOrNum : Name → Bool
  | .str p s => s.get 0 == '_' || isInternalOrNum p
  | .num _ _ => true
  | _       => false

/--
Returns true if this a part of name that is internal or dynamically
generated so that it may easily be changed.

Generally, user code should not explicitly use internal names.
-/
def isInternalDetail : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      || s.startsWith "match_"
      || s.startsWith "proof_"
      || p.isInternalOrNum
  | .num _ _     => true
  | p            => p.isInternalOrNum

end Lean.Name

open Lean Meta Elab

/-!
# Additional functions on `Lean.Name`.
-/

/--
Retrieve all names in the environment satisfying a predicate.
-/
def allNames (p : Name → Bool) : CoreM (Array Name) := do
  (← getEnv).constants.foldM (init := #[]) fun names n _ => do
    if p n then
      return names.push n
    else
      return names

/--
Retrieve all names in the environment satisfying a predicate,
gathered together into a `HashMap` according to the module they are defined in.
-/
def allNamesByModule (p : Name → Bool) : CoreM (HashMap Name (Array Name)) := do
  (← getEnv).constants.foldM (init := HashMap.empty) fun names n _ => do
    if p n then
      let some m ← findModuleOf? n | return names
      -- TODO use `Std.HashMap.modify` when we bump Std4 (or `alter` if that is written).
      match names.find? m with
      | some others => return names.insert m (others.push n)
      | none => return names.insert m #[n]
    else
      return names
