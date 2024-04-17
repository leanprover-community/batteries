import Std.Data.HashMap
import Std.Data.RBMap

/-!
# Positivity tests

Here we test that it is possible to write inductive types which contain a collection that contains
the type being defined. For this, it is necessary that there is a version of the data structure that
does not bundle the well-formedness constraint. Consequently, the API for each of these collections
needs to be developed twice: once in the normal use case where the well-formedness predicate is
bundled, and once in the unusual case where it is necessary to unbundle the well-formedness
predicate.
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
