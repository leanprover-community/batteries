-- None of these imports are really necessary, except to create namespace mentioned below.
import Lean.Elab.Term
import Lean.Elab.Command
import Batteries.Data.UnionFind.Basic

-- Return to pristine state
set_option linter.missingDocs false
set_option internal.cmdlineSnapshots false

/-- info: -- In root namespace with initial scope -/
#guard_msgs in #where

noncomputable section
/-- info: noncomputable section -/
#guard_msgs in #where
end

namespace WhereTest
variable (x : Nat) (α : Type)
/--
info: namespace WhereTest

variable (x : Nat) (α : Type)
-/
#guard_msgs in #where

universe u v w

/--
info: namespace WhereTest

universe u v w

variable (x : Nat) (α : Type)
-/
#guard_msgs in #where

set_option pp.piBinderTypes false

/--
info: namespace WhereTest

universe u v w

variable (x : Nat) (α : Type)

set_option pp.piBinderTypes false
-/
#guard_msgs in #where
end WhereTest

open Lean Meta

/--
info: open Lean Lean.Meta
-/
#guard_msgs in #where

open Elab hiding TermElabM

/--
info: open Lean Lean.Meta
open Lean.Elab hiding TermElabM
-/
#guard_msgs in #where

open Command Batteries
open Array renaming map -> listMap

/--
info: open Lean Lean.Meta
open Lean.Elab hiding TermElabM
open Lean.Elab.Command Batteries
open Array renaming map → listMap
-/
#guard_msgs in #where
