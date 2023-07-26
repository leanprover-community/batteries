import Std.Tactic.Alias
import Std.Tactic.GuardExpr

open Lean Meta
namespace Alias
namespace A

/-- doc string for foo -/
theorem foo : 1 + 1 = 2 := rfl

/-- doc string for `alias foo` -/
alias foo1 := foo
alias foo2 := foo
alias _root_.B.foo3 := foo

example : 1 + 1 = 2 := foo1
example : 1 + 1 = 2 := foo2
example : 1 + 1 = 2 := B.foo3

/-- doc string for bar -/
def bar : Nat := 5
alias bar1 := bar
alias _root_.B.bar2 := bar
example : bar1 = 5 := rfl
example : B.bar2 = 5 := rfl

theorem baz (x : Nat) : x = x := rfl
alias baz1 := baz
example : 3 = 3 := baz1 3

/-- doc string for foobar -/
def foobar : ℕ → ℕ := id
alias foobar1 := foobar
@[simp] alias foobar2 := foobar
/-- doc string for foobar2 -/
def foobar3 (n : ℕ) := foobar1 n

example : foobar1 x = foobar x := by simp; admit
example : foobar2 x = foobar x := by simp

/-- doc string for foobaz -/
noncomputable def foobaz : ℕ → ℕ := id
alias foobaz1 := foobaz
/-- doc string for foobaz2 -/
noncomputable def foobaz2 (n : ℕ) := foobaz1 n

/-- doc string for barbaz -/
unsafe def barbaz : ℕ → ℕ := id
alias barbaz1 := barbaz
/-- doc string for barbaz2 -/
unsafe def barbaz2 (n : ℕ) := barbaz1 n
