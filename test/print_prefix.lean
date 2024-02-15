import Std.Tactic.PrintPrefix
import Std.Tactic.GuardMsgs

inductive TEmpty : Type
/--
info: TEmpty : Type
TEmpty.casesOn : (motive : TEmpty → Sort u) → (t : TEmpty) → motive t
TEmpty.noConfusion : {P : Sort u} → {v1 v2 : TEmpty} → v1 = v2 → TEmpty.noConfusionType P v1 v2
TEmpty.noConfusionType : Sort u → TEmpty → TEmpty → Sort u
TEmpty.rec : (motive : TEmpty → Sort u) → (t : TEmpty) → motive t
TEmpty.recOn : (motive : TEmpty → Sort u) → (t : TEmpty) → motive t
-/
#guard_msgs in
#print prefix TEmpty -- Test type that probably won't change much.

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
Artificial test function to show #print prefix filters out internals
including match_/proof_.

Note.  Internal names are inherently subject to change.  This test case may
fail regularly when the Lean version is changed.  If so, we should disable
the test case using this function below until a more robust solution is found.
-/
def testMatchProof : (n : Nat) → Fin n → Unit
  | _,  ⟨0, _⟩ => ()
  | Nat.succ as, ⟨Nat.succ i, h⟩ => testMatchProof as ⟨i, Nat.le_of_succ_le_succ h⟩

/--
info: testMatchProof : (n : Nat) → Fin n → Unit
-/
#guard_msgs in
#print prefix testMatchProof

/--
info: testMatchProof : (n : Nat) → Fin n → Unit
testMatchProof._cstage1 : (n : Nat) → Fin n → Unit
testMatchProof._cstage2 : _obj → _obj → _obj
testMatchProof._sunfold : (n : Nat) → Fin n → Unit
testMatchProof._unsafe_rec : (n : Nat) → Fin n → Unit
testMatchProof.match_1 : (motive : (x : Nat) → Fin x → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x) →
      ((n : Nat) → (isLt : 0 < n) → motive n { val := 0, isLt := isLt }) →
        ((as i : Nat) → (h : Nat.succ i < Nat.succ as) → motive (Nat.succ as) { val := Nat.succ i, isLt := h }) →
          motive x x_1
testMatchProof.match_1._cstage1 : (motive : (x : Nat) → Fin x → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x) →
      ((n : Nat) → (isLt : 0 < n) → motive n { val := 0, isLt := isLt }) →
        ((as i : Nat) → (h : Nat.succ i < Nat.succ as) → motive (Nat.succ as) { val := Nat.succ i, isLt := h }) →
          motive x x_1
testMatchProof.proof_1 : ∀ (as i : Nat), Nat.succ i < Nat.succ as → Nat.succ i ≤ as
testMatchProof.proof_2 : ∀ (as i : Nat), Nat.succ i < Nat.succ as → Nat.succ i ≤ as
-/
#guard_msgs in
#print prefix (config:={internals:=true}) testMatchProof

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
