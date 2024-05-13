/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Batteries.Data.HashMap.Basic
import Batteries.Data.Array.Lemmas
import Batteries.Util.ProofWanted

namespace Batteries.HashMap

namespace Imp

@[simp] theorem empty_buckets :
    (empty : Imp α β).buckets = ⟨mkArray 8 AssocList.nil, by simp⟩ := rfl

@[simp] theorem empty_val [BEq α] [Hashable α] : (∅ : HashMap α β).val = Imp.empty := rfl

end Imp

@[simp] theorem empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none := by simp [find?, Imp.find?]

proof_wanted insert_find? [BEq α] [Hashable α] (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).find? a' = if a' == a then some b else m.find? a'
