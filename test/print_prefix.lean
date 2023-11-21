import Std.Tactic.PrintPrefix
import Std.Tactic.GuardMsgs

/--
info: Empty : Type
Empty.casesOn : (motive : Empty → Sort u) → (t : Empty) → motive t
Empty.rec : (motive : Empty → Sort u) → (t : Empty) → motive t
Empty.recOn : (motive : Empty → Sort u) → (t : Empty) → motive t
-/
#guard_msgs in
#print prefix Empty -- Test type that probably won't change much.

/--
-/
#guard_msgs in
#print prefix (config:={imported:=false}) Empty

namespace EmptyPrefixTest

end EmptyPrefixTest

-- Note.  This error message could be cleaned up, but left during migration from Mathlib
/--
error: unknown constant 'EmptyPrefixTest'
-/
#guard_msgs in
#print prefix EmptyPrefixTest

namespace Prefix.Test

/-- Supress lint -/
def foo (_l:List String) : Int := 0

end Prefix.Test

/--
info: Prefix.Test.foo : List String → Int
-/
#guard_msgs in
#print prefix Prefix.Test

/-- Supress lint -/
structure TestStruct where
  /-- Supress lint -/
  foo : Int
  /-- Supress lint -/
  bar : Int

/-
  /-- Include declarations whose types are propositions. -/
  propositions : Bool := true
  /-- Exclude declarations whose types are not propositions. -/
  propositionsOnly : Bool := false
  /-- Print the type of a declaration. -/
  showTypes : Bool := true
-/
/--
info: TestStruct : Type
TestStruct.bar : TestStruct → Int
TestStruct.casesOn : {motive : TestStruct → Sort u} → (t : TestStruct) → ((foo bar : Int) → motive { foo := foo, bar := bar }) → motive t
TestStruct.foo : TestStruct → Int
TestStruct.mk : Int → Int → TestStruct
TestStruct.mk.inj : ∀ {foo bar foo_1 bar_1 : Int}, { foo := foo, bar := bar } = { foo := foo_1, bar := bar_1 } → foo = foo_1 ∧ bar = bar_1
TestStruct.mk.injEq : ∀ (foo bar foo_1 bar_1 : Int),
  ({ foo := foo, bar := bar } = { foo := foo_1, bar := bar_1 }) = (foo = foo_1 ∧ bar = bar_1)
TestStruct.mk.sizeOf_spec : ∀ (foo bar : Int), sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
TestStruct.noConfusion : {P : Sort u} → {v1 v2 : TestStruct} → v1 = v2 → TestStruct.noConfusionType P v1 v2
TestStruct.noConfusionType : Sort u → TestStruct → TestStruct → Sort u
TestStruct.rec : {motive : TestStruct → Sort u} → ((foo bar : Int) → motive { foo := foo, bar := bar }) → (t : TestStruct) → motive t
TestStruct.recOn : {motive : TestStruct → Sort u} → (t : TestStruct) → ((foo bar : Int) → motive { foo := foo, bar := bar }) → motive t
-/
#guard_msgs in
#print prefix TestStruct

/--
info: TestStruct : Type
TestStruct.bar : TestStruct → Int
TestStruct.casesOn : {motive : TestStruct → Sort u} → (t : TestStruct) → ((foo bar : Int) → motive { foo := foo, bar := bar }) → motive t
TestStruct.foo : TestStruct → Int
TestStruct.mk : Int → Int → TestStruct
TestStruct.noConfusion : {P : Sort u} → {v1 v2 : TestStruct} → v1 = v2 → TestStruct.noConfusionType P v1 v2
TestStruct.noConfusionType : Sort u → TestStruct → TestStruct → Sort u
TestStruct.rec : {motive : TestStruct → Sort u} → ((foo bar : Int) → motive { foo := foo, bar := bar }) → (t : TestStruct) → motive t
TestStruct.recOn : {motive : TestStruct → Sort u} → (t : TestStruct) → ((foo bar : Int) → motive { foo := foo, bar := bar }) → motive t
-/
#guard_msgs in
#print prefix (config:={propositions:=false}) TestStruct

/--
info: TestStruct.mk.inj : ∀ {foo bar foo_1 bar_1 : Int}, { foo := foo, bar := bar } = { foo := foo_1, bar := bar_1 } → foo = foo_1 ∧ bar = bar_1
TestStruct.mk.injEq : ∀ (foo bar foo_1 bar_1 : Int),
  ({ foo := foo, bar := bar } = { foo := foo_1, bar := bar_1 }) = (foo = foo_1 ∧ bar = bar_1)
TestStruct.mk.sizeOf_spec : ∀ (foo bar : Int), sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
-/
#guard_msgs in
#print prefix (config:={propositionsOnly:=true}) TestStruct

/--
info: TestStruct
TestStruct.bar
TestStruct.casesOn
TestStruct.foo
TestStruct.mk
TestStruct.mk.inj
TestStruct.mk.injEq
TestStruct.mk.sizeOf_spec
TestStruct.noConfusion
TestStruct.noConfusionType
TestStruct.rec
TestStruct.recOn
-/
#guard_msgs in
#print prefix (config:={showTypes:=false}) TestStruct

/--
info: TestStruct : Type
TestStruct._sizeOf_1 : TestStruct → Nat
TestStruct._sizeOf_inst : SizeOf TestStruct
TestStruct.bar : TestStruct → Int
TestStruct.casesOn : {motive : TestStruct → Sort u} → (t : TestStruct) → ((foo bar : Int) → motive { foo := foo, bar := bar }) → motive t
TestStruct.foo : TestStruct → Int
TestStruct.mk : Int → Int → TestStruct
TestStruct.mk.inj : ∀ {foo bar foo_1 bar_1 : Int}, { foo := foo, bar := bar } = { foo := foo_1, bar := bar_1 } → foo = foo_1 ∧ bar = bar_1
TestStruct.mk.injEq : ∀ (foo bar foo_1 bar_1 : Int),
  ({ foo := foo, bar := bar } = { foo := foo_1, bar := bar_1 }) = (foo = foo_1 ∧ bar = bar_1)
TestStruct.mk.sizeOf_spec : ∀ (foo bar : Int), sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
TestStruct.noConfusion : {P : Sort u} → {v1 v2 : TestStruct} → v1 = v2 → TestStruct.noConfusionType P v1 v2
TestStruct.noConfusionType : Sort u → TestStruct → TestStruct → Sort u
TestStruct.rec : {motive : TestStruct → Sort u} → ((foo bar : Int) → motive { foo := foo, bar := bar }) → (t : TestStruct) → motive t
TestStruct.recOn : {motive : TestStruct → Sort u} → (t : TestStruct) → ((foo bar : Int) → motive { foo := foo, bar := bar }) → motive t
-/
#guard_msgs in
#print prefix (config:={internals:=true}) TestStruct

private inductive TestInd where
| foo : TestInd
| bar : TestInd

/--
info: _private.test.print_prefix.0.TestInd : Type
_private.test.print_prefix.0.TestInd.bar : TestInd
_private.test.print_prefix.0.TestInd.bar.sizeOf_spec : sizeOf TestInd.bar = 1
_private.test.print_prefix.0.TestInd.casesOn : {motive : TestInd → Sort u} → (t : TestInd) → motive TestInd.foo → motive TestInd.bar → motive t
_private.test.print_prefix.0.TestInd.foo : TestInd
_private.test.print_prefix.0.TestInd.foo.sizeOf_spec : sizeOf TestInd.foo = 1
_private.test.print_prefix.0.TestInd.noConfusion : {P : Sort v✝} → {x y : TestInd} → x = y → TestInd.noConfusionType P x y
_private.test.print_prefix.0.TestInd.noConfusionType : Sort v✝ → TestInd → TestInd → Sort v✝
_private.test.print_prefix.0.TestInd.rec : {motive : TestInd → Sort u} → motive TestInd.foo → motive TestInd.bar → (t : TestInd) → motive t
_private.test.print_prefix.0.TestInd.recOn : {motive : TestInd → Sort u} → (t : TestInd) → motive TestInd.foo → motive TestInd.bar → motive t
_private.test.print_prefix.0.TestInd.toCtorIdx : TestInd → Nat
-/
#guard_msgs in
#print prefix TestInd
