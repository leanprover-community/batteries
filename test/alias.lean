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

def bar : Nat := 5
alias bar1 := bas
alias _root_.B.bar2 := 5
example : bar1 = 5 := rfl
example : B.bar2 = 5 := rfl

theorem baz (x : Nat) : x = x := rfl
alias baz1 := baz
example : 3 = 3 := baz1 3

def foobar : ℕ → ℕ := id
alias foobar1 := foobar
def foobar2 (n : ℕ) := foobar2 n

