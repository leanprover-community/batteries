import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF
import Std.Data.List.Lemmas
import Std.Data.List.Perm
import Std.Data.Array.Lemmas

/-- If there is at most one element with the property `p`, erasing one such element
is the same as filtering out all of them. -/
theorem List.eraseP_eq_filter_of_unique (l : List α) (p : α → Bool)
    : l.Pairwise (p · → !p ·) → l.eraseP p = l.filter (!p ·) := by
  intro h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    specialize ih (Pairwise.sublist (sublist_cons x xs) h)
    cases hP : p x with
    | true =>
      rw [Pairwise_cons] at h
      have : ∀ a ∈ xs, !p a := fun a hA => h.left a hA hP
      simp [eraseP, filter, hP, filter_eq_self.mpr this]
    | false => simp [eraseP_cons, filter, hP, ih]

namespace Std.HashMap

variable [BEq α] [Hashable α] [PartialEquivBEq α]

/-- The map does not store duplicate keys. -/
theorem Pairwise_bne_toList (m : HashMap α β) : m.toList.Pairwise (·.1 != ·.1) :=
  sorry

theorem toList_eraseP_eq_toList_filter (m : HashMap α β)
    : m.toList.eraseP (·.1 == a) = m.toList.filter (·.1 != a) := by
  apply List.eraseP_eq_filter_of_unique
  apply List.Pairwise.imp ?_ (Pairwise_bne_toList _)
  intro (a₁, _) (a₂, _) hA₁Bne hA₁Beq
  rw [Bool.not_eq_true_iff_ne_true]
  intro hA₂Beq
  exact Bool.not_bne_of_beq (PartialEquivBEq.trans hA₁Beq (PartialEquivBEq.symm hA₂Beq)) hA₁Bne

theorem toList_insert_perm_cons_eraseP (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toList ~ (a, b) :: m.toList.eraseP (·.1 == a) :=
  sorry

theorem toList_insert (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toList ~ (a, b) :: m.toList.filter (·.1 != a) :=
  toList_eraseP_eq_toList_filter m ▸ toList_insert_perm_cons_eraseP m a b

theorem toList_erase_perm_eraseP (m : HashMap α β) (a : α)
    : (m.erase a).toList ~ m.toList.eraseP (·.1 == a) :=
  sorry

theorem toList_erase (m : HashMap α β) (a : α)
    : (m.erase a).toList ~ m.toList.filter (·.1 != a) :=
  toList_eraseP_eq_toList_filter m ▸ toList_erase_perm_eraseP m a

theorem find?_of_toList_contains (m : HashMap α β) (a : α) (b : β)
    : (∃ a', a == a' ∧ (a', b) ∈ m.toList) ↔ m.find? a = some b :=
  sorry

theorem find?_of_toList_not_contains (m : HashMap α β) (a : α)
    : (∀ a' (b : β), a == a' → (a', b) ∉ m.toList) ↔ m.find? a = none := by
  apply Iff.intro
  . rw [← Option.not_isSome_iff_eq_none]
    intro h hSome
    let ⟨b, hB⟩ := Option.isSome_iff_exists.mp hSome
    let ⟨a', hA, hMem⟩ := find?_of_toList_contains m a b |>.mpr hB
    exact h a' b hA hMem
  . intro h a' b hA hMem
    refine Option.ne_none_iff_exists.mpr ?_ h
    exact ⟨b, find?_of_toList_contains m a b |>.mp ⟨a', hA, hMem⟩ |>.symm⟩

theorem find?_insert (m : HashMap α β) (a a' b)
    : a' == a → (m.insert a b).find? a' = some b := by
  intro hEq
  apply (find?_of_toList_contains _ _ _).mp
  refine ⟨a, hEq, ?_⟩
  rw [List.Perm.mem_iff (toList_insert m a b)]
  apply List.mem_cons_self

theorem find?_insert_of_ne (m : HashMap α β) (a a' : α) (b : β)
    : a != a' → (m.insert a b).find? a' = m.find? a' := by
  intro hNe
  apply Option.ext
  intro b'
  show find? (insert m a b) a' = some b' ↔ find? m a' = some b'
  simp only [← find?_of_toList_contains, List.Perm.mem_iff (toList_insert m a b), List.mem_cons,
    List.mem_filter, Prod.mk.injEq]
  apply Iff.intro
  . intro ⟨a'', hA', h⟩
    cases h with
    | inl hEq =>
      cases hEq.left
      exfalso
      exact Bool.not_bne_of_beq (PartialEquivBEq.symm hA') hNe
    | inr hMem => exact ⟨a'', hA', hMem.left⟩
  . intro ⟨a'', hA', hMem⟩
    refine ⟨a'', hA', .inr ?_⟩
    refine ⟨hMem, Bool.not_eq_true_iff_ne_true.mpr ?_⟩
    intro hA''
    exact Bool.not_bne_of_beq (PartialEquivBEq.symm (PartialEquivBEq.trans hA' hA'')) hNe

theorem find?_erase (m : HashMap α β) (a a')
    : a == a' → (m.erase a).find? a' = none := by
  intro hEq
  apply (find?_of_toList_not_contains _ _).mp
  intro a₂ b hA₂ hMem
  rw [List.Perm.mem_iff (toList_erase m a)] at hMem
  refine Bool.not_bne_of_beq (PartialEquivBEq.symm <| PartialEquivBEq.trans hEq hA₂) ?_
  exact List.mem_filter.mp hMem |>.right

end Std.HashMap
