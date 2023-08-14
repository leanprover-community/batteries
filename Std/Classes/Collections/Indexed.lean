/-
Copyright (c) 2023 James Gallicchio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Gallicchio
-/

import Std.Classes.Collections.Iterable
import Std.Classes.Collections.EnumType

namespace Std.Collections

/-- Collections whose elements are naturally indexed by some type `ι`. -/
class Indexed (C : Type u) (ι : outParam (Type u)) (τ : outParam (Type u)) where
  /-- Get element at index `i : ι` from collection `c : C`. -/
  get : C → ι → τ

namespace Indexed

instance [EnumType ι] [Indexed C ι τ] : Iterable C τ where
  ρ := C × Nat
  toIterator c := (c, 0)
  toStream := {
    next? := fun (c,i) =>
      if h : i < EnumType.card ι then
        some (get c (EnumType.ofFin ⟨i,h⟩), (c,i+1))
      else none
  }
