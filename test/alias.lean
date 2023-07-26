import Std.Tactic.Alias
import Std.Tactic.GuardMsgs

set_option linter.unusedVariables false

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
@[inherit_doc foobar] alias foobar1 := foobar
@[simp] alias foobar2 := foobar
/-- doc string for foobar2 -/
def foobar3 (n : ℕ) := foobar1 n

/-- error: unsolved goals
α✝ : Sort ?u.919
x : α✝
⊢ foobar1 x = foobar x-/
#guard_msgs in
example : foobar1 x = foobar x := by simp
example : foobar2 x = foobar x := by simp

/- Test noncomputable -/

/-- doc string for foobaz -/
noncomputable def foobaz : ℕ → ℕ := id
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Alias.A.foobaz', and it does not have executable code -/
#guard_msgs in alias foobaz1 := foobaz

noncomputable alias foobaz2 := id
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Alias.A.foobaz2', and it does not have executable code -/
#guard_msgs in def foobaz4 (n : ℕ) := foobaz2 n

/- Test unsafe -/

/-- doc string for barbaz -/
unsafe def barbaz : ℕ → ℕ := id
/-- error: (kernel) invalid declaration, it uses unsafe declaration 'Alias.A.barbaz' -/
#guard_msgs in alias barbaz1 := barbaz

unsafe alias barbaz2 := id
/-- error: (kernel) invalid declaration, it uses unsafe declaration 'Alias.A.barbaz2' -/
#guard_msgs in def barbaz4 (n : ℕ) := barbaz2 n

/- iff version -/

alias ⟨mpId, mprId⟩ := Iff.rfl

/-- info: mpId {a : Prop} (a✝ : a) : a -/
#guard_msgs in
#check mpId
/-- info: mprId {a : Prop} (a✝ : a) : a -/
#guard_msgs in
#check mprId
