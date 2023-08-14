/-
Copyright (c) 2023 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

import Std.Classes.Collections.Iterable

namespace Std.Collections

/-- Expresses that `ι` has an explicit bijection with `Fin n` for
  some constant `n`.

  TODO: Resolve overlap with Mathlib `Fintype`. -/
class EnumType (ι : Type u) where
  /-- How many elements of type `ι` there are. -/
  card : Nat
  /-- Function into `Fin card`. -/
  toFin : ι → Fin card
  /-- Function from `Fin card`. -/
  ofFin : Fin card → ι
