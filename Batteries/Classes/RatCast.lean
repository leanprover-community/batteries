/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Gabriel Ebner
-/
import Batteries.Data.Rat.Basic

/-- Type class for the canonical homomorphism `Rat → K`. -/
class RatCast (K : Type u) where
  /-- The canonical homomorphism `Rat → K`. -/
  protected ratCast : Rat → K

instance : RatCast Rat where ratCast n := n

/-- Canonical homomorphism from `Rat` to a division ring `K`.
This is just the bare function in order to aid in creating instances of `DivisionRing`. -/
@[coe, reducible, match_pattern] protected def Rat.cast {K : Type u} [RatCast K] : Rat → K :=
  RatCast.ratCast

-- see note [coercion into rings]
instance [RatCast K] : CoeTail Rat K where coe := Rat.cast

-- see note [coercion into rings]
instance [RatCast K] : CoeHTCT Rat K where coe := Rat.cast
