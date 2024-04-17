import Std.Data.HashMap
import Std.Data.RBMap

/-!
# Positivity tests

Here we test that it is possible to write inductive types which contain a collection that contains
the type being defined.

-/

open Std

inductive ContainsItselfInAssocListValues where
  | base
  | recursive (l : AssocList Bool ContainsItselfInAssocListValues)

inductive ContainsItselfInHashMapValues where
  | base
  | recursive (l : HashMap.Imp Bool ContainsItselfInHashMapValues)

inductive ContainsItselfInRBMapValues where
  | base
  | recursive (l : RBNode (Nat × ContainsItselfInRBMapValues))
