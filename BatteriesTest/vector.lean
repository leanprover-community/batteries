import Batteries.Data.Vector

/-! ### Testing decidable quantifiers for `Vector`. -/

open Batteries

example : ∃ v : Vector Bool 6, v.toList.count true = 3 := by decide

inductive Gate : Nat → Type
| const : Bool → Gate 0
| if : ∀ {n}, Gate n → Gate n → Gate (n + 1)

namespace Gate

def and : Gate 2 := .if (.if (.const true) (.const false)) (.if (.const false) (.const false))

def eval (g : Gate n) (v : Vector Bool n) : Bool :=
  match g, v with
  | .const b, _ => b
  | .if g₁ g₂, v => if v.1.back! then eval g₁ v.pop else eval g₂ v.pop

example : ∀ v, and.eval v = (v[0] && v[1]) := by decide
example : ∃ v, and.eval v = false := by decide

end Gate
