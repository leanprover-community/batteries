/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.HashMap.Basic

/-!
# Lemmas for `Batteries.HashMap`

Note that Lean core provides an alternative hash map implementation, `Std.HashMap`, which comes with
more lemmas. See the module `Std.Data.HashMap.Lemmas`.
-/

namespace Batteries.HashMap

namespace Imp

@[simp] theorem empty_buckets :
    (empty : Imp α β).buckets = ⟨mkArray 8 AssocList.nil, by simp⟩ := rfl

@[simp] theorem empty_val [BEq α] [Hashable α] : (∅ : HashMap α β).val = Imp.empty := rfl

end Imp

@[simp] theorem empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none := by simp [find?, Imp.find?]
