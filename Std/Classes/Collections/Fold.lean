/-
Copyright (c) 2022 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

/-! ## Folds -/

/-- `Foldl C τ` for collections `C` which can be folded over elements of type `τ`.

Note `τ` is `outParam`.

TODO: leave β universe polymorphic?
-/
class Foldl (C : Type u) (τ : outParam (Type v)) where
  /-- Left fold function, parametric over accumulator type `β`. -/
  foldl : ∀ (β : Type w), (β → τ → β) → β → C → β

/-- `Foldr C τ` for collections `C` which can be folded over elements of type `τ`.

Note `τ` is `outParam`.

TODO: leave β universe polymorphic?
-/
class Foldr (C : Type u) (τ : outParam (Type v)) where
  /-- Right fold function, parametric over accumulator type `β`. -/
  foldr : ∀ (β : Type w), (τ → β → β) → β → C → β

/-- Undirected fold class. For classes with directed folds, this class
is intended to be the more performant of the two.
-/
class Fold (C : Type u) (τ : outParam (Type v)) where
  /-- Fold function, parametric over accumulator type `β`. -/
  fold : ∀ (β : Type w), (β → τ → β) → β → C → β
