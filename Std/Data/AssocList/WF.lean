/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Classes.BEq
import Std.Data.AssocList

namespace Std.AssocList

/-- The well-formedness predicate for associative lists says that the keys are pairwise distinct. -/
structure WF [BEq α] (l : AssocList α β) : Prop where
  /-- The keys of a well-formed associative list are pairwise distinct. -/
  distinct [PartialEquivBEq α] : l.keys.Pairwise fun a b => (a == b) = false

@[simp]
theorem WF.nil [BEq α] : (.nil : AssocList α β).WF :=
  ⟨by simp⟩

theorem WF.cons [BEq α] {l : AssocList α β} {k : α} {v : β} (h : l.contains k = false) :
    (l.cons k v).WF := sorry

theorem WF.replace [BEq α] {l : AssocList α β} {k : α} {v : β} :
    (l.replace k v).WF := sorry

end Std.AssocList
