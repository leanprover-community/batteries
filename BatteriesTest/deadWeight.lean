import Batteries.Util.DeadWeight
import Lean.Elab.Command

/-! Tests for `Batteries.DeadWeight.analyze`. -/

set_option linter.unusedVariables false

namespace DeadWeightTest

/-- Nothing reads the last two fields. -/
structure Bundle where
  value : Nat
  bound : value < 10
  proof : value ≠ 11
  data : Nat

/-- `match` binds both fields at once, so whether `right` is read is inconclusive. -/
structure Destructured where
  left : Nat
  right : Nat

structure Parent where
  a : Nat
  b : Nat

structure Child extends Parent where
  c : Nat
  d : Nat

/-- The type of `h` reads `n`. -/
structure Dependent where
  n : Nat
  h : n = n

/-- No root reaches this structure, so its fields are not reported. -/
structure Unreached where
  x : Nat

inductive UnreachedInductive
  | a
  | b

def bundle : Bundle := ⟨3, by decide, by decide, 0⟩

-- An instance that no root uses.
instance : Inhabited Bundle := ⟨bundle⟩

def destruct : Destructured → Nat
  | ⟨l, _⟩ => l

def child : Child := { a := 1, b := 2, c := 3, d := 4 }

def anyGeometry : Nat → Prop := fun _ => True

def constantData (_ : Nat) : Nat := 7

def usesArgument (n : Nat) : Nat := n + 1

def statement : Prop := ∀ n : Nat, n = n

-- The report covers only reachable constant predicates.
def unreachedPredicate (_ : Nat) : Prop := True

def unreachedDef : Nat := 5

theorem unreachedThm : unreachedDef = 5 := rfl

-- A private theorem that the root reaches.
private theorem bound : bundle.value < 10 := bundle.bound

theorem dependent (s : Dependent) : s.n = s.n := s.h

theorem root : bundle.value < 10 ∧ destruct ⟨1, 2⟩ = 1 ∧ anyGeometry 3 ∧ constantData 2 = 7 ∧
    child.c = 3 ∧ child.toParent.a = 1 ∧ usesArgument 1 = 2 ∧ statement :=
  ⟨bound, rfl, trivial, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- A primitive projection reads a field without its projection function. -/
structure Primitive where
  x : Nat
  y : Nat

-- The elaborator produces projection functions, so build the primitive projection by hand.
open Lean in
run_cmd Elab.Command.liftCoreM do
  let prim := mkConst ``Primitive
  addDecl <| .defnDecl {
    name := `DeadWeightTest.primitive, levelParams := [], type := ← mkArrow prim (mkConst ``Nat)
    value := .lam `p prim (.proj ``Primitive 1 (.bvar 0)) .default
    hints := .abbrev, safety := .safe }

end DeadWeightTest

open Lean Elab Command Batteries.DeadWeight

/-- Prints the report on the declarations of this file. -/
def printReport (roots : Array Name) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let report ← analyze roots fun n =>
    (env.getModuleIdxFor? n).isNone && (privateToUserName n).getRoot == `DeadWeightTest
  let fields (destructured : Bool) := report.unreadFields.filterMap fun f =>
    if f.destructured == destructured then some (f.structName ++ f.fieldName) else none
  logInfo m!"{report.numDead} of {report.numDecls} declarations are dead: {report.deadDecls}\n\
    dead modules: {report.deadModules}\n\
    unread fields: {fields false}\n\
    inconclusive fields: {fields true}\n\
    constant predicates: {report.constantPredicates}\n\
    constant functions: {report.constantFunctions}\n\
    axioms: {report.axioms}"

/--
info: 10 of 23 declarations are dead: [DeadWeightTest.Dependent,
 DeadWeightTest.Primitive,
 DeadWeightTest.Unreached,
 DeadWeightTest.UnreachedInductive,
 DeadWeightTest.dependent,
 DeadWeightTest.instInhabitedBundle,
 DeadWeightTest.primitive,
 DeadWeightTest.unreachedDef,
 DeadWeightTest.unreachedPredicate,
 DeadWeightTest.unreachedThm]
dead modules: []
unread fields: [DeadWeightTest.Bundle.data,
 DeadWeightTest.Bundle.proof,
 DeadWeightTest.Child.d,
 DeadWeightTest.Parent.b]
inconclusive fields: [DeadWeightTest.Destructured.left, DeadWeightTest.Destructured.right]
constant predicates: [(DeadWeightTest.anyGeometry, is always `True`, but it is part of what the roots state)]
constant functions: [DeadWeightTest.constantData]
axioms: []
-/
#guard_msgs in
run_cmd printReport #[``DeadWeightTest.root]

/--
info: 19 of 23 declarations are dead: [DeadWeightTest.Bundle,
 DeadWeightTest.Child,
 DeadWeightTest.Destructured,
 DeadWeightTest.Parent,
 DeadWeightTest.Unreached,
 DeadWeightTest.UnreachedInductive,
 DeadWeightTest.anyGeometry,
 DeadWeightTest.bundle,
 DeadWeightTest.child,
 DeadWeightTest.constantData,
 DeadWeightTest.destruct,
 DeadWeightTest.instInhabitedBundle,
 DeadWeightTest.root,
 DeadWeightTest.statement,
 DeadWeightTest.unreachedDef,
 DeadWeightTest.unreachedPredicate,
 DeadWeightTest.unreachedThm,
 DeadWeightTest.usesArgument,
 _private.BatteriesTest.deadWeight.0.DeadWeightTest.bound]
dead modules: []
unread fields: [DeadWeightTest.Primitive.x]
inconclusive fields: []
constant predicates: []
constant functions: []
axioms: []
-/
#guard_msgs in
run_cmd printReport #[``DeadWeightTest.dependent, `DeadWeightTest.primitive]

/--
error: unknown constant 'DeadWeightTest.misspelled'
-/
#guard_msgs in
run_cmd printReport #[`DeadWeightTest.misspelled]

/-! ## Predicates that are always true -/

/-- For roots whose statements do not mention what the proof `h` is about. -/
theorem aboutTrue {p : Prop} (h : p) : True := trivial

/-- Prints what the report on `root` says about predicates that are always true. -/
def printPredicates (root : Name) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let report ← analyze #[root] fun n => (env.getModuleIdxFor? n).isNone
  for (name, filled) in report.vacuousPredicates do
    logInfo m!"dead weight: {name}, as a parameter of {filled}"
  for (name, msg) in report.constantPredicates do
    logInfo m!"{name} {msg}"

namespace Geometry

/-! A predicate that is a parameter of a structure and the only source of values for its type, also
through an inductive closure and a structure field. -/

abbrev GeoP : Type := ∀ D : Nat, Fin D → Fin D → Prop

def anyGeometry : GeoP := fun _ _ _ => True

def realGeometry (n : Nat) : GeoP := fun _ c X => c.val = X.val + n

inductive GeoCl (Γ : GeoP) : GeoP
  | base {D c X} : Γ D c X → GeoCl Γ D c X
  | step {D c X} : GeoCl Γ D c X → GeoCl Γ D X c

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ

theorem geoCl_of {Γ : GeoP} {D c X} (h : Γ D c X) : geoCl Γ D c X := .base h

structure OAt (Γ : GeoP) (D : Nat) (c X : Fin D) : Type where
  geo : Γ D c X
  lam : c = c

def OX (Γ : GeoP) (D : Nat) (c X : Fin D) : Type := OAt Γ D c X

structure Parameters where
  n : Nat
  Γ : GeoP

def mkParameters (Γ : GeoP) : Parameters := ⟨3, Γ⟩

def parameters : Parameters := mkParameters (geoCl anyGeometry)

def Transfer : Prop := ∀ (Γ : GeoP) (D c X), OAt Γ D c X → Nonempty (OX (geoCl Γ) D c X)

theorem transfer : Transfer := fun _ _ _ _ o => ⟨⟨geoCl_of o.geo, o.lam⟩⟩

theorem ofField (p : Parameters) (D c X) (o : OAt p.Γ D c X) : c = c := o.lam

theorem exists_any (D c X) : Nonempty (OX anyGeometry D c X) := ⟨⟨trivial, rfl⟩⟩

theorem closing (D c X) : c = c ∧ Nonempty (OX (geoCl anyGeometry) D c X) :=
  ⟨ofField parameters D c X ⟨geoCl_of trivial, rfl⟩,
    (exists_any D c X).elim fun o => transfer _ D c X o⟩

theorem dead (D : Nat) (c X : Fin D) : c = c := (closing D c X).1

-- An alternative reaches the same parameters.
theorem alternative (D : Nat) (c X : Fin D) : True :=
  aboutTrue (And.intro (closing D c X) (transfer (realGeometry 0) D c X))

-- An alternative reaches them through a structure field.
theorem alternativeInField (D : Nat) (c X : Fin D) : True :=
  aboutTrue (And.intro (closing D c X) (ofField (mkParameters (realGeometry 0)) D c X))

-- An alternative reaches a parameter that `OX` passes its parameter on to.
theorem alternativeInRoot (Γ : GeoP) (D c X) (o : OAt Γ D c X) : c = c :=
  o.lam.trans (closing D c X).1

-- The root is about the predicate.
theorem stated (D c X) : Nonempty (OX anyGeometry D c X) := exists_any D c X

structure Statement (D c X) : Prop where
  h : Nonempty (OX anyGeometry D c X)

-- The root is about the predicate, indirectly.
theorem statedIndirectly (D c X) : Statement D c X := ⟨exists_any D c X⟩

end Geometry

/--
info: dead weight: Geometry.anyGeometry, as a parameter of [Geometry.OX,
 Geometry.geoCl,
 Geometry.geoCl_of,
 Geometry.mkParameters,
 Geometry.transfer,
 Geometry.OAt.mk]
-/
#guard_msgs in run_cmd printPredicates ``Geometry.dead

/--
info: Geometry.anyGeometry is always `True`, but `Geometry.transfer` also gets `Geometry.realGeometry`
-/
#guard_msgs in run_cmd printPredicates ``Geometry.alternative

/--
info: Geometry.anyGeometry is always `True`, but `Geometry.mkParameters` also gets `Geometry.realGeometry`
-/
#guard_msgs in run_cmd printPredicates ``Geometry.alternativeInField

/--
info: Geometry.anyGeometry is always `True`, but the root `Geometry.alternativeInRoot` has a predicate as a parameter
-/
#guard_msgs in run_cmd printPredicates ``Geometry.alternativeInRoot

/--
info: Geometry.anyGeometry is always `True`, but it is part of what the roots state
-/
#guard_msgs in run_cmd printPredicates ``Geometry.stated

/--
info: Geometry.anyGeometry is always `True`, but it is part of what the roots state
-/
#guard_msgs in run_cmd printPredicates ``Geometry.statedIndirectly

namespace Comparison

/-! Deliberate predicates: the weakest of several conditions, and the base case of a construction. -/

def algCls (m : Nat) : Nat → Nat → Prop := fun a b => a + m = b

def trivialCondition (m a b : Nat) : Prop := True

structure Point (P : Nat → Nat → Prop) where
  a : Nat
  b : Nat
  h : P a b

def Point.widen {P Q : Nat → Nat → Prop} (f : ∀ a b, P a b → Q a b) (y : Point P) : Point Q :=
  ⟨y.a, y.b, f _ _ y.h⟩

def values (P : Nat → Nat → Prop) (n : Nat) : Prop := ∃ y : Point P, y.a = n

theorem values_subset (m n : Nat) : values (algCls m) n → values (trivialCondition m) n :=
  fun ⟨y, h⟩ => ⟨y.widen fun _ _ _ => trivial, h⟩

theorem compared : True := aboutTrue values_subset

def onIdeal (y : Point (trivialCondition 0)) : Nat → Nat → Prop := fun a _ => a = y.a

theorem baseCase (y : Point (trivialCondition 0)) : values (onIdeal y) y.a := ⟨⟨y.a, 0, rfl⟩, rfl⟩

theorem base : True := aboutTrue baseCase

def Represents (P : Nat → Nat → Prop) (r : Nat) : Prop := ∀ a, P a r

structure Universal (P : Nat → Nat → Prop) where
  r : Nat
  rep : Represents P r

def onUniversal (u : Universal (trivialCondition 0)) : Nat → Nat → Prop := fun a _ => a = u.r

-- The predicate reaches `Represents` only through a field of `Universal` that nothing reads.
theorem throughType : True :=
  aboutTrue (p := ∀ u, Represents (onUniversal u) u.r → Represents (onUniversal u) u.r) fun _ h => h

end Comparison

/--
info: Comparison.trivialCondition is always `True`, but `Comparison.values` also gets `Comparison.algCls`
-/
#guard_msgs in run_cmd printPredicates ``Comparison.compared

/--
info: Comparison.trivialCondition is always `True`, but `Comparison.Point.a` also gets `Comparison.onIdeal`
-/
#guard_msgs in run_cmd printPredicates ``Comparison.base

/--
info: Comparison.trivialCondition is always `True`, but `Comparison.Represents` also gets `Comparison.onUniversal`
-/
#guard_msgs in run_cmd printPredicates ``Comparison.throughType

namespace Values

def any : Nat → Prop := fun _ => True

structure S (P : Nat → Prop) where
  n : Nat

def s : S any := ⟨1⟩

def size (P : Nat → Prop) (s : S P) : Nat := s.n

-- Values that are always true are not alternatives.
def other : Nat → Prop := fun _ => True
def conj (P : Nat → Prop) : Nat → Prop := fun n => P n ∧ n = n
theorem deadSame : True := aboutTrue (p := size any s = size (fun n => any n) ⟨1⟩) rfl
theorem deadOther : True := aboutTrue (p := size any s = size other ⟨1⟩) rfl
theorem deadConj : True := aboutTrue (p := size any s = size (conj any) ⟨1⟩) rfl

-- Other values are, even if they mention the predicate.
def strengthen (P : Nat → Prop) : Nat → Prop := fun n => P n ∧ 3 < n
def never : Nat → Prop := fun _ => False
def choose : Option Nat → Nat → Prop
  | none => any
  | some k => fun n => n = k
theorem strengthened : True := aboutTrue (p := size any s = size (strengthen any) ⟨1⟩) rfl
theorem lambda : True := aboutTrue (p := size any s = size (fun n => any n ∧ 3 < n) ⟨1⟩) rfl
theorem opposite : True := aboutTrue (p := size any s = size never ⟨1⟩) rfl
theorem chosen (o : Option Nat) : True := aboutTrue (p := size any s = size (choose o) ⟨1⟩) rfl

-- So are values that the analysis cannot follow.
structure Box where
  P : Nat → Prop
def unbox : Box → Nat
  | ⟨P⟩ => size P ⟨2⟩
theorem destructed (b : Box) : True :=
  aboutTrue (p := size any s = 1 ∧ unbox b = 2) ⟨rfl, rfl⟩
theorem partialApplication (f : ∀ P, S P → Nat) (h : f = size) : True :=
  aboutTrue (p := size any s = 1 ∧ f = size) ⟨rfl, h⟩

-- Recursion passes the predicate on to itself.
def loop (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => loop P n
theorem deadLoop : True := aboutTrue (p := loop any 3 = 0) rfl

-- Without a parameter to fill, there is nothing to say.
theorem neverPassed : True := aboutTrue (p := any 3) trivial
theorem library : True := aboutTrue (p := ∃ n, any n) ⟨0, trivial⟩

end Values

/--
info: dead weight: Values.any, as a parameter of [Values.S, Values.size, Values.S.mk]
-/
#guard_msgs in run_cmd printPredicates ``Values.deadSame

/--
info: dead weight: Values.any, as a parameter of [Values.S, Values.size, Values.S.mk]
---
info: dead weight: Values.other, as a parameter of [Values.size, Values.S.mk]
-/
#guard_msgs in run_cmd printPredicates ``Values.deadOther

/--
info: dead weight: Values.any, as a parameter of [Values.S, Values.conj, Values.size, Values.S.mk]
-/
#guard_msgs in run_cmd printPredicates ``Values.deadConj

/--
info: dead weight: Values.any, as a parameter of [Values.loop]
-/
#guard_msgs in run_cmd printPredicates ``Values.deadLoop

/--
info: Values.any is always `True`, but `Values.size` also gets `Values.strengthen`
-/
#guard_msgs in run_cmd printPredicates ``Values.strengthened

/--
info: Values.any is always `True`, but `Values.size` also gets another value
-/
#guard_msgs in run_cmd printPredicates ``Values.lambda

/--
info: Values.any is always `True`, but `Values.size` also gets `Values.never`
---
info: Values.never is always `False`
-/
#guard_msgs in run_cmd printPredicates ``Values.opposite

/--
info: Values.any is always `True`, but `Values.size` also gets `Values.choose`
-/
#guard_msgs in run_cmd printPredicates ``Values.chosen

/--
info: Values.any is always `True`, but `Values.size` also gets a value that is not known
-/
#guard_msgs in run_cmd printPredicates ``Values.destructed

/--
info: Values.any is always `True`, but `Values.size` also gets a value that is not known
-/
#guard_msgs in run_cmd printPredicates ``Values.partialApplication

/--
info: Values.any is always `True`, but it is never an argument for a predicate parameter in scope
-/
#guard_msgs in run_cmd printPredicates ``Values.neverPassed

/--
info: Values.any is always `True`, but it is never an argument for a predicate parameter in scope
-/
#guard_msgs in run_cmd printPredicates ``Values.library
