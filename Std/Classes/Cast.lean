/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Std.Tactic.CoeExt
import Std.Util.LibraryNote

/-- Type class for the canonical homomorphism `Nat → R`. -/
class NatCast (R : Type u) where
  /-- The canonical map `Nat → R`. -/
  protected natCast : Nat → R

instance : NatCast Nat where natCast n := n

/-- Canonical homomorphism from `Nat` to a additive monoid `R` with a `1`.
This is just the bare function in order to aid in creating instances of `AddMonoidWithOne`. -/
@[coe, reducible, match_pattern] protected def Nat.cast {R : Type u} [NatCast R] : Nat → R :=
  NatCast.natCast

-- see note [coercion into rings]
instance [NatCast R] : CoeTail Nat R where coe := Nat.cast

-- see note [coercion into rings]
instance [NatCast R] : CoeHTCT Nat R where coe := Nat.cast

/-- Type class for the canonical homomorphism `Int → R`. -/
class IntCast (R : Type u) where
  /-- The canonical map `Int → R`. -/
  protected intCast : Int → R

instance : IntCast Int where intCast := id

/-- Canonical homomorphism from `Int` to a additive group `R` with a `1`.
This is just the bare function in order to aid in creating instances of `AddGroupWithOne`. -/
@[coe, reducible, match_pattern] protected def Int.cast {R : Type u} [IntCast R] : Int → R :=
  IntCast.intCast

-- see note [coercion into rings]
instance [IntCast R] : CoeTail Int R where coe := Int.cast

-- see note [coercion into rings]
instance [IntCast R] : CoeHTCT Int R where coe := Int.cast

library_note "coercion into rings"
/--
Coercions such as `Nat.castCoe` that go from a concrete structure such as
`Nat` to an arbitrary ring `R` should be set up as follows:
```lean
instance : CoeTail Nat R where coe := ...
instance : CoeHTCT Nat R where coe := ...
```

It needs to be `CoeTail` instead of `Coe` because otherwise type-class
inference would loop when constructing the transitive coercion `Nat → Nat → Nat → ...`.
Sometimes we also need to declare the `CoeHTCT` instance
if we need to shadow another coercion
(e.g. `Nat.cast` should be used over `Int.ofNat`).
-/
