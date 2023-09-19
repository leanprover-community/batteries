/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Util.ExtendedBinder

/-- Notation type class for the subset relation `⊆`. -/
class HasSubset (α : Type u) where
  /-- Subset relation: `a ⊆ b`  -/
  Subset : α → α → Prop
export HasSubset (Subset)

/-- Subset relation: `a ⊆ b`  -/
infix:50 " ⊆ " => HasSubset.Subset

/-- Notation type class for the strict subset relation `⊂`. -/
class HasSSubset (α : Type u) where
  /-- Strict subset relation: `a ⊂ b`  -/
  SSubset : α → α → Prop
export HasSSubset (SSubset)

/-- Strict subset relation: `a ⊂ b`  -/
infix:50 " ⊂ " => HasSSubset.SSubset

/-- Superset relation: `a ⊇ b`  -/
abbrev Superset [HasSubset α] (a b : α) := b ⊆ a
/-- Superset relation: `a ⊇ b`  -/
infix:50 " ⊇ " => Superset

/-- Strict superset relation: `a ⊃ b`  -/
abbrev SSuperset [HasSSubset α] (a b : α) := b ⊂ a
/-- Strict superset relation: `a ⊃ b`  -/
infix:50 " ⊃ " => SSuperset

/-- Notation type class for the union operation `∪`. -/
class Union (α : Type u) where
  /-- `a ∪ b` is the union of`a` and `b`. -/
  union : α → α → α
/-- `a ∪ b` is the union of`a` and `b`. -/
infixl:65 " ∪ " => Union.union

/-- Notation type class for the intersection operation `∩`. -/
class Inter (α : Type u) where
  /-- `a ∩ b` is the intersection of`a` and `b`. -/
  inter : α → α → α
/-- `a ∩ b` is the intersection of`a` and `b`. -/
infixl:70 " ∩ " => Inter.inter

/-- Notation type class for the set difference `\`. -/
class SDiff (α : Type u) where
  /--
  `a \ b` is the set difference of `a` and `b`,
  consisting of all elements in `a` that are not in `b`.
  -/
  sdiff : α → α → α
/--
`a \ b` is the set difference of `a` and `b`,
consisting of all elements in `a` that are not in `b`.
-/
infix:70 " \\ " => SDiff.sdiff

/--
Type class for the `insert` operation.
Used to implement the `{ a, b, c }` syntax.
-/
class Insert (α : outParam <| Type u) (γ : Type v) where
  /-- `insert x xs` inserts the element `x` into the collection `xs`. -/
  insert : α → γ → γ
export Insert (insert)

/--
Type class for the `singleton` operation.
Used to implement the `{ a, b, c }` syntax.
-/
class Singleton (α : outParam <| Type u) (β : Type v) where
  /-- `singleton x` is a collection with the single element `x` (notation: `{x}`). -/
  singleton : α → β
export Singleton (singleton)

/-- Type class used to implement the notation `{ a ∈ c | p a }` -/
class Sep (α : outParam <| Type u) (γ : Type v) where
  /-- Computes `{ a ∈ c | p a }`. -/
  sep : (α → Prop) → γ → γ

/-- Declare `∃ x ∈ y, ...` as syntax for `∃ x, x ∈ y ∧ ...` -/
binder_predicate x " ∈ " y:term => `($x ∈ $y)

/--
`{ a, b, c }` is a set with elements `a`, `b`, and `c`.

This notation works for all types that implement `Insert` and `Singleton`.
-/
syntax "{" term,+ "}" : term

macro_rules
  | `({$x:term}) => `(singleton $x)
  | `({$x:term, $xs:term,*}) => `(insert $x {$xs:term,*})

/-- Unexpander for the `{ x }` notation. -/
@[app_unexpander singleton]
def singletonUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `({ $a:term })
  | _ => throw ()

/-- Unexpander for the `{ x, y, ... }` notation. -/
@[app_unexpander insert]
def insertUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a { $ts:term,* }) => `({$a:term, $ts,*})
  | _ => throw ()

/-- `insert x ∅ = {x}` -/
class IsLawfulSingleton (α : Type u) (β : Type v) [EmptyCollection β] [Insert α β] [Singleton α β] :
    Prop where
  /-- `insert x ∅ = {x}` -/
  insert_emptyc_eq (x : α) : (insert x ∅ : β) = {x}
export IsLawfulSingleton (insert_emptyc_eq)
