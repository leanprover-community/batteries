import Batteries.CodeAction.Attr
import Batteries.CodeAction.Basic
import Batteries.CodeAction.Misc


example (x : Nat) : x = x := by
  induction x with
  | zero => sorry
  | succ n _ => sorry


def myfun : Nat → Nat → Nat --direct pattern completion here will be worked on, when the explicit match is deemed good enough.
  | .zero => _
  | .succ n => _


def myfun2 (n:Nat) : Nat :=
  match n with
  | .zero => _
  | .succ n => _



def myfun3 (e: Lean.Expr) : Bool :=
  match e with
  | .bvar deBruijnIndex => _
  | .fvar fvarId => _
  | .mvar mvarId => _
  | .sort u => _
  | .const declName us => _
  | .app fn arg => _
  | .lam binderName binderType body binderInfo => _
  | .forallE binderName binderType body binderInfo => _
  | .letE declName type value body nonDep => _
  | .lit _ => _
  | .mdata data expr => _
  | .proj typeName idx struct => _
