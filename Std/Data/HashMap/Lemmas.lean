import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF
import Std.Data.List.Lemmas
import Std.Data.List.Perm
import Std.Data.Array.Lemmas

namespace Std.HashMap

variable [BEq α] [Hashable α]

theorem toList_insert (m : HashMap α β) (a b)
    : (m.insert a b).toList ~ (a, b) :: m.toList.eraseP (·.1 == a) :=
  sorry

theorem toList_erase (m : HashMap α β) (a)
    : (m.erase a).toList ~ m.toList.eraseP (·.1 == a) :=
  sorry

theorem find?_of_toList_contains (m : HashMap α β) (a : α) (b : β)
    : (∃ a', a == a' ∧ (a', b) ∈ m.toList) ↔ m.find? a = some b :=
  sorry

theorem find?_of_toList_not_contains (m : HashMap α β) (a : α)
    : (∀ a' (b : β), a == a' → (a', b) ∉ m.toList) ↔ m.find? a = none := by
  apply Iff.intro
  . intro h

  . intro h
    sorry

theorem find?_insert (m : HashMap α β) (a a' b)
    : a' == a → (m.insert a b).find? a' = some b := by
  intro hEq
  apply (find?_of_toList_contains _ _ _).mp
  refine ⟨a, hEq, ?_⟩
  rw [List.Perm.mem_iff (toList_insert m a b)]
  apply List.mem_cons_self

theorem find?_insert_of_ne [PartialEquivBEq α] (m : HashMap α β) (a a' b)
    : a != a' → (m.insert a b).find? a' = m.find? a' := by
  intro hNe
  suffices ∀ b', (m.insert a b).find? a' = some b' ↔ m.find? a' = some b' by
    cases h : (m.insert a b).find? a' with
    | none =>
      apply Eq.symm
      apply Option.not_isSome_iff_eq_none.mp
      intro hSome
      let ⟨b₂, hB₂⟩ := Option.isSome_iff_exists.mp hSome
      rw [← this] at hB₂
      cases h.symm.trans hB₂
    | some b' => exact (this b').mp h |>.symm
  intro b'
  rw [← find?_of_toList_contains, ← find?_of_toList_contains]
  simp only [List.Perm.mem_iff (toList_insert m a b), List.mem_cons]
  apply Iff.intro
  . intro ⟨a₂, hA₂Eq, hA₂⟩
    refine ⟨a₂, hA₂Eq, ?_⟩
    cases hA₂ with
    | inl h =>
      cases h
      have := Bool.not_bne_of_beq (PartialEquivBEq.symm hA₂Eq)
      contradiction
    | inr h => exact List.mem_of_mem_eraseP h
  . intro ⟨a₂, hA₂Eq, hA₂⟩
    refine ⟨a₂, hA₂Eq, ?_⟩
    apply Or.inr
    refine (List.mem_eraseP_of_neg ?_).mpr hA₂
    dsimp
    intro h
    apply Bool.not_bne_of_beq (PartialEquivBEq.trans hA₂Eq h |> PartialEquivBEq.symm) hNe

theorem find?_erase [PartialEquivBEq α] (m : HashMap α β) (a a')
    : a == a' → (m.erase a).find? a' = none := by
  intro hEq
  apply (find?_of_toList_not_contains _ _).mp
  intro a₂ b hA₂ hMem
  rw [List.Perm.mem_iff (toList_erase m a)] at hMem
  sorry
  -- TODO: this is false; do we need to rely on elements in the map never repeating?
  --  theorem not_of_mem_eraseP {l : List α} : a ∈ l.eraseP p → ¬p a := sorry
  -- apply not_of_mem_eraseP hMem
  -- have : a₂ == a := PartialEquivBEq.symm (PartialEquivBEq.trans hEq hA₂)
  -- exact this

end Std.HashMap
