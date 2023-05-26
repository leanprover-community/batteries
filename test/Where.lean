import Std.Tactic.Where
import Std.Tactic.GuardMsgs

-- Return to pristine state
set_option linter.missingDocs false

/--
info: In root namespace with initial scope
-/
#guard_msgs in #where

noncomputable section
/--
info: (Within namespace/section level 1, noncomputable section)
-/
#guard_msgs in #where
end

namespace WhereTest
variable (x : Nat) (α : Type)
/--
info: (Within namespace/section level 1)

namespace WhereTest

variable (x : Nat) (α : Type)
-/
#guard_msgs in #where

universe u v w

/--
info: (Within namespace/section level 1)

namespace WhereTest

universe u v w

variable (x : Nat) (α : Type)
-/
#guard_msgs in #where

set_option pp.piBinderTypes false

/--
info: (Within namespace/section level 1)

namespace WhereTest

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

open Command Std
open Array renaming map -> listMap

/--
info: open Lean Lean.Meta
open Lean.Elab hiding TermElabM
open Lean.Elab.Command Std
open listMap → Array.map
-/
#guard_msgs in #where
