import Batteries.Tactic.PrintPrefix

inductive TEmpty : Type
/--
info: TEmpty : Type
TEmpty.casesOn.{u} (motive : TEmpty → Sort u) (t : TEmpty) : motive t
TEmpty.noConfusion.{u} {P : Sort u} {x1 x2 : TEmpty} (h12 : x1 = x2) : TEmpty.noConfusionType P x1 x2
TEmpty.noConfusionType.{u} (P : Sort u) (x1 x2 : TEmpty) : Sort u
TEmpty.noConfusionType.withCtor.{u} (P : Type u) (ctorIdx : Nat) (k : TEmpty.noConfusionType.withCtorType P ctorIdx)
  (k' : P) (x : TEmpty) : P
TEmpty.noConfusionType.withCtorType.{u} (P : Type u) (ctorIdx : Nat) : Type (max 1 u)
TEmpty.rec.{u} (motive : TEmpty → Sort u) (t : TEmpty) : motive t
TEmpty.recOn.{u} (motive : TEmpty → Sort u) (t : TEmpty) : motive t
-/
#guard_msgs in
#print prefix TEmpty -- Test type that probably won't change much.

/-- info: -/
#guard_msgs in
#print prefix -imported Empty

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
TestStruct.mk.inj {foo bar foo✝ bar✝ : Int} :
  { foo := foo, bar := bar } = { foo := foo✝, bar := bar✝ } → foo = foo✝ ∧ bar = bar✝
TestStruct.mk.injEq (foo bar foo✝ bar✝ : Int) :
  ({ foo := foo, bar := bar } = { foo := foo✝, bar := bar✝ }) = (foo = foo✝ ∧ bar = bar✝)
TestStruct.mk.sizeOf_spec (foo bar : Int) : sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
TestStruct.noConfusion.{u} {P : Sort u} {x1 x2 : TestStruct} (h12 : x1 = x2) : TestStruct.noConfusionType P x1 x2
TestStruct.noConfusionType.{u} (P : Sort u) (x1 x2 : TestStruct) : Sort u
TestStruct.noConfusionType.withCtor.{u} (P : Type u) (ctorIdx : Nat)
  (k : TestStruct.noConfusionType.withCtorType P ctorIdx) (k' : P) (x : TestStruct) : P
TestStruct.noConfusionType.withCtorType.{u} (P : Type u) (ctorIdx : Nat) : Type (max 1 u)
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
TestStruct.noConfusion.{u} {P : Sort u} {x1 x2 : TestStruct} (h12 : x1 = x2) : TestStruct.noConfusionType P x1 x2
TestStruct.noConfusionType.{u} (P : Sort u) (x1 x2 : TestStruct) : Sort u
TestStruct.noConfusionType.withCtor.{u} (P : Type u) (ctorIdx : Nat)
  (k : TestStruct.noConfusionType.withCtorType P ctorIdx) (k' : P) (x : TestStruct) : P
TestStruct.noConfusionType.withCtorType.{u} (P : Type u) (ctorIdx : Nat) : Type (max 1 u)
TestStruct.rec.{u} {motive : TestStruct → Sort u} (mk : (foo bar : Int) → motive { foo := foo, bar := bar })
  (t : TestStruct) : motive t
TestStruct.recOn.{u} {motive : TestStruct → Sort u} (t : TestStruct)
  (mk : (foo bar : Int) → motive { foo := foo, bar := bar }) : motive t
-/
#guard_msgs in
#print prefix -propositions TestStruct

/--
info: TestStruct.mk.inj {foo bar foo✝ bar✝ : Int} :
  { foo := foo, bar := bar } = { foo := foo✝, bar := bar✝ } → foo = foo✝ ∧ bar = bar✝
TestStruct.mk.injEq (foo bar foo✝ bar✝ : Int) :
  ({ foo := foo, bar := bar } = { foo := foo✝, bar := bar✝ }) = (foo = foo✝ ∧ bar = bar✝)
TestStruct.mk.sizeOf_spec (foo bar : Int) : sizeOf { foo := foo, bar := bar } = 1 + sizeOf foo + sizeOf bar
-/
#guard_msgs in
#print prefix +propositionsOnly TestStruct

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
TestStruct.noConfusionType.withCtor
TestStruct.noConfusionType.withCtorType
TestStruct.rec
TestStruct.recOn
-/
#guard_msgs in
#print prefix -showTypes TestStruct

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

/-- info: testMatchProof (n : Nat) : Fin n → Unit -/
#guard_msgs in
#print prefix testMatchProof

/--
info: testMatchProof (n : Nat) : Fin n → Unit
testMatchProof._proof_1 (as i : Nat) (h : i.succ < as.succ) : i.succ ≤ as
testMatchProof._sunfold (n : Nat) : Fin n → Unit
testMatchProof._unsafe_rec (n : Nat) : Fin n → Unit
testMatchProof.match_1.{u_1} (motive : (x : Nat) → Fin x → Sort u_1) (x✝ : Nat) (x✝¹ : Fin x✝)
  (h_1 : (n : Nat) → (isLt : 0 < n) → motive n ⟨0, isLt⟩)
  (h_2 : (as i : Nat) → (h : i.succ < as.succ) → motive as.succ ⟨i.succ, h⟩) : motive x✝ x✝¹
-/
#guard_msgs in
#print prefix +internals testMatchProof

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
TestInd.toCtorIdx : TestInd → Nat
-/
#guard_msgs in
#print prefix TestInd

-- `#print prefix` does nothing if no identifier is provided
#guard_msgs in
#print prefix
