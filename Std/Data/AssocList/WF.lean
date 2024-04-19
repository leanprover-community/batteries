/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Classes.BEq
import Std.Classes.Hashable
import Std.Data.AssocList

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace Std.AssocList

/-- The well-formedness predicate for associative lists says that the keys are pairwise distinct. -/
structure WF [BEq α] (l : AssocList α β) : Prop where
  /-- The keys of a well-formed associative list are pairwise distinct. -/
  distinct [PartialEquivBEq α] : l.keys.Pairwise fun a b => (a == b) = false

@[simp]
theorem WF.nil [BEq α] : (.nil : AssocList α β).WF :=
  ⟨by simp⟩

theorem WF.cons [BEq α] {l : AssocList α β} {k : α} {v : β} (h : l.contains k = false) :
    l.WF → (l.cons k v).WF := sorry

theorem WF.replace [BEq α] {l : AssocList α β} {k : α} {v : β} :
    l.WF → (l.replace k v).WF := sorry

/-- Well-formedness invariant for a bucket in a hash map. -/
structure WFAtPosition [BEq α] [Hashable α] (l : AssocList α β) (i size : Nat)
    extends l.WF : Prop where
  /-- Every element in a bucket should hash to its location. -/
  hash_self [LawfulHashable α] : ∀ k, l.contains k → ((hash k).toUSize % size).toNat = i

@[simp]
theorem WFAtPosition.nil [BEq α] [Hashable α] {i size} :
    (.nil : AssocList α β).WFAtPosition i size :=
  { WF.nil with
    hash_self := by simp }

theorem WFAtPosition.cons [BEq α] [Hashable α] {l : AssocList α β} {k : α} {v : β}
    (h₁ : l.contains k = false) {i size : Nat} (h₂ : ((hash k).toUSize % size).toNat = i)
    (h : l.WFAtPosition i size) : (l.cons k v).WFAtPosition i size :=
  { h.toWF.cons h₁ with
    hash_self := by
      intros _ k'
      sorry -- Okay, I need all of my normal forms from my own development
    }

theorem WFAtPosition.replace [BEq α] [Hashable α] {l : AssocList α β} {k : α} {v : β} {i size : Nat}
    (h₁ : ((hash k).toUSize % size).toNat = i) (h : l.WFAtPosition i size) :
    (l.replace k v).WFAtPosition i size := sorry

end Std.AssocList
