import Std.Tactic.PrintPrefix

inductive TEmpty : Type
/--
info: TEmpty : Type
TEmpty.casesOn.{u} (motive : TEmpty → Sort u) (t : TEmpty) : motive t
TEmpty.noConfusion.{u} {P : Sort u} {v1 v2 : TEmpty} (h12 : v1 = v2) : TEmpty.noConfusionType P v1 v2
TEmpty.noConfusionType.{u} (P : Sort u) (v1 v2 : TEmpty) : Sort u
TEmpty.rec.{u} (motive : TEmpty → Sort u) (t : TEmpty) : motive t
TEmpty.recOn.{u} (motive : TEmpty → Sort u) (t : TEmpty) : motive t
-/
#guard_msgs in
#print prefix TEmpty -- Test type that probably won't change much.

/--
-/
#guard_msgs in
#print prefix (config := {imported := false}) Empty

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

/-- info: Prefix.Test.foo (_l : List String) : Int -/
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
TestStruct.bar (self : TestStruct) : Int
TestStruct.casesOn.{u} {motive : TestStruct → Sort u} (t : TestStruct)
  (mk : (foo bar : Int) → motive { foo := foo, bar := bar }) : motive t
TestStruct.foo (self : TestStruct) : Int
TestStruct.mk (foo bar : Int) : TestStruct
TestStruct.mk.inj {foo bar foo bar : Int} (x✝ : { foo := foo, bar := bar } = { foo := foo, bar := bar }) :
  foo = foo ∧ bar = bar
TestStruct.mk.injEq (foo bar foo bar : Int) :
  ({ foo := foo, bar := bar } = { foo := foo, bar := bar }) = (foo = foo ∧ bar = bar)
TestStruct.mk.sizeOf_spec (foo bar : Int) : sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
TestStruct.noConfusion.{u} {P : Sort u} {v1 v2 : TestStruct} (h12 : v1 = v2) : TestStruct.noConfusionType P v1 v2
TestStruct.noConfusionType.{u} (P : Sort u) (v1 v2 : TestStruct) : Sort u
TestStruct.rec.{u} {motive : TestStruct → Sort u} (mk : (foo bar : Int) → motive { foo := foo, bar := bar })
  (t : TestStruct) : motive t
TestStruct.recOn.{u} {motive : TestStruct → Sort u} (t : TestStruct)
  (mk : (foo bar : Int) → motive { foo := foo, bar := bar }) : motive t
-/
#guard_msgs in
#print prefix TestStruct

/--
info: TestStruct : Type
TestStruct.bar (self : TestStruct) : Int
TestStruct.casesOn.{u} {motive : TestStruct → Sort u} (t : TestStruct)
  (mk : (foo bar : Int) → motive { foo := foo, bar := bar }) : motive t
TestStruct.foo (self : TestStruct) : Int
TestStruct.mk (foo bar : Int) : TestStruct
TestStruct.noConfusion.{u} {P : Sort u} {v1 v2 : TestStruct} (h12 : v1 = v2) : TestStruct.noConfusionType P v1 v2
TestStruct.noConfusionType.{u} (P : Sort u) (v1 v2 : TestStruct) : Sort u
TestStruct.rec.{u} {motive : TestStruct → Sort u} (mk : (foo bar : Int) → motive { foo := foo, bar := bar })
  (t : TestStruct) : motive t
TestStruct.recOn.{u} {motive : TestStruct → Sort u} (t : TestStruct)
  (mk : (foo bar : Int) → motive { foo := foo, bar := bar }) : motive t
-/
#guard_msgs in
#print prefix (config := {propositions := false}) TestStruct

/--
info: TestStruct.mk.inj {foo bar foo bar : Int} (x✝ : { foo := foo, bar := bar } = { foo := foo, bar := bar }) :
  foo = foo ∧ bar = bar
TestStruct.mk.injEq (foo bar foo bar : Int) :
  ({ foo := foo, bar := bar } = { foo := foo, bar := bar }) = (foo = foo ∧ bar = bar)
TestStruct.mk.sizeOf_spec (foo bar : Int) : sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
-/
#guard_msgs in
#print prefix (config := {propositionsOnly := true}) TestStruct

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
#print prefix (config := {showTypes := false}) TestStruct

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

/-- info: testMatchProof (n : Nat) (a✝ : Fin n) : Unit -/
#guard_msgs in
#print prefix testMatchProof

/--
info: testMatchProof (n : Nat) (a✝ : Fin n) : Unit
testMatchProof._cstage1 (n : Nat) (a✝ : Fin n) : Unit
testMatchProof._cstage2 (x✝x✝¹ : _obj) : _obj
testMatchProof._sunfold (n : Nat) (a✝ : Fin n) : Unit
testMatchProof._unsafe_rec (n : Nat) (a✝ : Fin n) : Unit
testMatchProof.match_1.{u_1} (motive : (x : Nat) → Fin x → Sort u_1) (x✝ : Nat) (x✝¹ : Fin x✝)
  (h_1 : (n : Nat) → (isLt : 0 < n) → motive n { val := 0, isLt := isLt })
  (h_2 : (as i : Nat) → (h : Nat.succ i < Nat.succ as) → motive (Nat.succ as) { val := Nat.succ i, isLt := h }) :
  motive x✝ x✝¹
testMatchProof.match_1._cstage1.{u_1} (motive : (x : Nat) → Fin x → Sort u_1) (x✝ : Nat) (x✝¹ : Fin x✝)
  (h_1 : (n : Nat) → (isLt : 0 < n) → motive n { val := 0, isLt := isLt })
  (h_2 : (as i : Nat) → (h : Nat.succ i < Nat.succ as) → motive (Nat.succ as) { val := Nat.succ i, isLt := h }) :
  motive x✝ x✝¹
testMatchProof.proof_1 (as i : Nat) (h : Nat.succ i < Nat.succ as) : Nat.succ i ≤ as
testMatchProof.proof_2 (as i : Nat) (h : Nat.succ i < Nat.succ as) : Nat.succ i ≤ as
-/
#guard_msgs in
#print prefix (config := {internals := true}) testMatchProof

private inductive TestInd where
| foo : TestInd
| bar : TestInd

/--
info: TestInd : Type
TestInd.bar : TestInd
TestInd.bar.sizeOf_spec : sizeOf TestInd.bar = 1
TestInd.casesOn.{u} {motive : TestInd → Sort u} (t : TestInd) (foo : motive TestInd.foo) (bar : motive TestInd.bar) :
  motive t
TestInd.foo : TestInd
TestInd.foo.sizeOf_spec : sizeOf TestInd.foo = 1
TestInd.noConfusion.{v✝} {P : Sort v✝} {x y : TestInd} (h : x = y) : TestInd.noConfusionType P x y
TestInd.noConfusionType.{v✝} (P : Sort v✝) (x y : TestInd) : Sort v✝
TestInd.rec.{u} {motive : TestInd → Sort u} (foo : motive TestInd.foo) (bar : motive TestInd.bar) (t : TestInd) :
  motive t
TestInd.recOn.{u} {motive : TestInd → Sort u} (t : TestInd) (foo : motive TestInd.foo) (bar : motive TestInd.bar) :
  motive t
TestInd.toCtorIdx (x✝ : TestInd) : Nat
-/
#guard_msgs in
#print prefix TestInd
