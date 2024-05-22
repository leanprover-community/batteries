import Batteries.Tactic.Alias

set_option linter.unusedVariables false
set_option linter.missingDocs false

open Lean Meta
namespace A

/-- doc string for foo -/
theorem foo : 1 + 1 = 2 := rfl

/-- doc string for `alias foo` -/
alias foo1 := foo
@[deprecated] alias foo2 := foo
@[deprecated foo2] alias _root_.B.foo3 := foo
@[deprecated foo2 "it was never a good idea anyway" (since := "last thursday")] alias foo4 := foo

example : 1 + 1 = 2 := foo1
/-- warning: `A.foo2` has been deprecated, use `A.foo` instead -/
#guard_msgs in example : 1 + 1 = 2 := foo2
/-- warning: `B.foo3` has been deprecated, use `A.foo2` instead -/
#guard_msgs in example : 1 + 1 = 2 := B.foo3
/-- warning: it was never a good idea anyway -/
#guard_msgs in example : 1 + 1 = 2 := foo4

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
def foobar : Nat → Nat := id
@[inherit_doc foobar] alias foobar1 := foobar
@[simp] alias foobar2 := foobar
/-- doc string for foobar2 -/
def foobar3 (n : Nat) := foobar1 n

/-- error: simp made no progress -/
#guard_msgs in
example : foobar1 x = foobar x := by simp
example : foobar2 x = foobar x := by simp

/- Test protected -/

/-- doc string for Foo.barbaz -/
protected alias Foo.barbaz := trivial
/-- error: unknown identifier 'barbaz' -/
#guard_msgs in example : True := barbaz
example : True := Foo.barbaz

/- Test noncomputable -/

/-- doc string for foobaz -/
noncomputable def foobaz : Nat → Nat := id
alias foobaz1 := foobaz

/--
error: failed to compile definition, consider marking it as 'noncomputable' because
it depends on 'A.foobaz1', and it does not have executable code
-/
#guard_msgs in def foobaz2 (n : Nat) := foobaz1 n

noncomputable alias foobaz3 := id
/--
error: failed to compile definition, consider marking it as 'noncomputable' because
it depends on 'A.foobaz3', and it does not have executable code
-/
#guard_msgs in def foobaz4 (n : Nat) := foobaz3 n

/- Test unsafe -/

/-- doc string for barbaz -/
unsafe def barbaz : Nat → Nat := id
alias barbaz1 := barbaz
/-- error: (kernel) invalid declaration, it uses unsafe declaration 'A.barbaz1' -/
#guard_msgs in def barbaz2 (n : Nat) := barbaz1 n

unsafe alias barbaz3 := id
/-- error: (kernel) invalid declaration, it uses unsafe declaration 'A.barbaz3' -/
#guard_msgs in def barbaz4 (n : Nat) := barbaz3 n

/- iff version -/

@[deprecated] alias ⟨mpId, mprId⟩ := Iff.rfl

/-- info: A.mpId {a : Prop} : a → a -/
#guard_msgs in #check mpId
/-- info: A.mprId {a : Prop} : a → a -/
#guard_msgs in #check mprId

/--
warning: `A.mpId` has been deprecated, use `Iff.rfl` instead
---
warning: `A.mprId` has been deprecated, use `Iff.rfl` instead
-/
#guard_msgs in example := And.intro @mpId @mprId

/- Test environment extension -/

/-- info: **Alias** of `A.foo`. -/
#guard_msgs in
#eval show MetaM _ from do
  match ← Batteries.Tactic.Alias.getAliasInfo `A.foo1 with
  | some i => IO.println i.toString
  | none => IO.println "alias not found"
