import Batteries.CodeAction.Attr
import Batteries.CodeAction.Basic
import Batteries.CodeAction.Misc


example (x : Nat) : x = x := by
  induction x with
  | zero => sorry
  | succ n _ => sorry

/-direct pattern completion here will be worked on, when the explicit match is deemed good--/
def myfun : Nat → Nat → Nat
  | .zero => sorry
  | .succ n => sorry

--These will be generated with underscores instead of sorry's
def myfun2 (n:Nat) : Nat :=
  match n with
  | .zero => sorry
  | .succ n => sorry



def myfun3 (e: Lean.Expr) : Bool :=
  match e with
  | .bvar deBruijnIndex => sorry
  | .fvar fvarId => sorry
  | .mvar mvarId => sorry
  | .sort u => sorry
  | .const declName us => sorry
  | .app fn arg => sorry
  | .lam binderName binderType body binderInfo => sorry
  | .forallE binderName binderType body binderInfo => sorry
  | .letE declName type value body nonDep => sorry
  | .lit _ => sorry
  | .mdata data expr => sorry
  | .proj typeName idx struct => sorry
