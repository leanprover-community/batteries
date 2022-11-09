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

@[simp]
theorem List.foldl_cons_fn (l₁ l₂ : List α) :
    l₁.foldl (init := l₂) (fun acc x => x :: acc) = l₁.reverse ++ l₂ := by
  induction l₁ generalizing l₂ <;> simp [*]

namespace Std.HashMap
open List

variable [BEq α] [Hashable α] [LawfulHashable α] [PartialEquivBEq α]

/-- It is a bit easier to reason about `foldl (append)` than `foldl (foldl)`, so we use this
(less efficient) variant of `toList` as the mathematical model. -/
def toListModel (m : HashMap α β) : List (α × β) :=
  m.val.buckets.val.foldl (init := []) (fun acc bkt => acc ++ bkt.toList)

theorem toList_eq_reverse_toListModel (m : HashMap α β) : m.toList = m.toListModel.reverse := by
  simp only [toList, toListModel, fold, Imp.fold, Array.foldl_eq_foldl_data, AssocList.foldl_eq,
    List.foldl_cons_fn]
  suffices ∀ (l₁ : List (AssocList α β)) (l₂ : List (α × β)),
      l₁.foldl (init := l₂.reverse) (fun d b => b.toList.reverse ++ d) =
      (l₁.foldl (init := l₂) fun acc bkt => acc ++ bkt.toList).reverse by
    apply this (l₂ := [])
  intro l₁
  induction l₁ with
  | nil => intro; rfl
  | cons a as ih =>
    intro l₂
    simp only [List.foldl, ← List.reverse_append, ih]

/-- The map does not store duplicate (`beq`) keys. -/
theorem Pairwise_bne_toListModel (m : HashMap α β) : m.toListModel.Pairwise (·.1 != ·.1) := by
  unfold toListModel
  refine Array.foldl_induction
    (motive := fun i (acc : List (α × β)) =>
      -- The acc has the desired property
      acc.Pairwise (·.1 != ·.1)
      -- All not-yet-accumulated buckets are pairwise disjoint with the acc
      ∧ ∀ j, i ≤ j → (_ : j < m.val.buckets.val.size) →
        ∀ p ∈ acc, ∀ r ∈ m.val.buckets.val[j].toList, p.1 != r.1)
    ?h0 ?hf |>.left
  case h0 => exact ⟨List.Pairwise.nil, fun.⟩
  case hf =>
    have hWF := Imp.WF_iff.mp m.property |>.right
    intro i acc h
    refine ⟨List.pairwise_append.mpr ⟨h.left, ?bkt, ?accbkt⟩, ?accbkts⟩
    case bkt =>
      -- Main proof 1: the contents of any given bucket are pairwise bne
      have := hWF.distinct m.val.buckets.val[i] (Array.getElem_mem_data _ _)
      exact List.Pairwise.imp Bool.not_eq_true_iff_ne_true.mpr this
    case accbkt =>
      intro a hA b hB
      exact h.right i.val (Nat.le_refl _) i.isLt a hA b hB
    case accbkts =>
      intro j hGe hLt p hP r hR
      cases List.mem_append.mp hP
      case inl hP => exact h.right j (Nat.le_of_succ_le hGe) hLt p hP r hR
      case inr hP =>
        -- Main proof 2: distinct buckets store bne keys
        refine Bool.not_eq_true_iff_ne_true.mpr fun h => ?_
        have hHashEq := LawfulHashable.hash_eq h
        have hGt := Nat.lt_of_succ_le hGe
        have hHashP := hWF.hash_self i (Nat.lt_trans hGt hLt) _ hP
        have hHashR := hWF.hash_self j hLt _ hR
        dsimp at hHashP hHashR
        have : i.val = j := by
          rw [hHashEq] at hHashP
          exact .trans hHashP.symm hHashR
        exact Nat.ne_of_lt hGt this

theorem toListModel_eraseP_eq_toListModel_filter (m : HashMap α β)
    : m.toListModel.eraseP (·.1 == a) = m.toListModel.filter (·.1 != a) := by
  apply List.eraseP_eq_filter_of_unique
  apply List.Pairwise.imp ?_ (Pairwise_bne_toListModel _)
  intro (a₁, _) (a₂, _) hA₁Bne hA₁Beq
  rw [Bool.not_eq_true_iff_ne_true]
  intro hA₂Beq
  exact Bool.not_bne_of_beq (PartialEquivBEq.trans hA₁Beq (PartialEquivBEq.symm hA₂Beq)) hA₁Bne

theorem toListModel_insert_perm_cons_eraseP (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toListModel ~ (a, b) :: m.toListModel.eraseP (·.1 == a) :=
  sorry

theorem toListModel_insert (m : HashMap α β) (a : α) (b : β)
    : (m.insert a b).toListModel ~ (a, b) :: m.toListModel.filter (·.1 != a) :=
  toListModel_eraseP_eq_toListModel_filter m ▸ toListModel_insert_perm_cons_eraseP m a b

theorem toListModel_erase_perm_eraseP (m : HashMap α β) (a : α)
    : (m.erase a).toListModel ~ m.toListModel.eraseP (·.1 == a) :=
  sorry

theorem toListModel_erase (m : HashMap α β) (a : α)
    : (m.erase a).toListModel ~ m.toListModel.filter (·.1 != a) :=
  toListModel_eraseP_eq_toListModel_filter m ▸ toListModel_erase_perm_eraseP m a

theorem findEntry?_eq (m : HashMap α β) (a : α)
    : m.findEntry? a = m.toListModel.find? (·.1 == a) := by
  unfold findEntry? Imp.findEntry?
  conv => simp_match; simp_match
  sorry

theorem find?_of_toListModel_contains (m : HashMap α β) (a : α) (b : β)
    : (∃ a', a == a' ∧ (a', b) ∈ m.toListModel) ↔ m.find? a = some b := by
  unfold HashMap.toListModel HashMap.find? Imp.find?
  -- have H : (∃ a', a == a' ∧ (a', b) ∈ m.toListModel)
  --     ↔ (∃ a', ∃ bkt, (i : Fin m.val.buckets.val.size) → bkt = m.val.buckets.val[i] → (a',b) ∈ bkt) := sorry
  sorry

theorem find?_of_toListModel_not_contains (m : HashMap α β) (a : α)
    : (∀ a' (b : β), a == a' → (a', b) ∉ m.toListModel) ↔ m.find? a = none := by
  apply Iff.intro
  . rw [← Option.not_isSome_iff_eq_none]
    intro h hSome
    let ⟨b, hB⟩ := Option.isSome_iff_exists.mp hSome
    let ⟨a', hA, hMem⟩ := find?_of_toListModel_contains m a b |>.mpr hB
    exact h a' b hA hMem
  . intro h a' b hA hMem
    refine Option.ne_none_iff_exists.mpr ?_ h
    exact ⟨b, find?_of_toListModel_contains m a b |>.mp ⟨a', hA, hMem⟩ |>.symm⟩

theorem find?_insert (m : HashMap α β) (a a' b)
    : a' == a → (m.insert a b).find? a' = some b := by
  intro hEq
  apply (find?_of_toListModel_contains _ _ _).mp
  refine ⟨a, hEq, ?_⟩
  rw [List.Perm.mem_iff (toListModel_insert m a b)]
  apply List.mem_cons_self

theorem find?_insert_of_ne (m : HashMap α β) (a a' : α) (b : β)
    : a != a' → (m.insert a b).find? a' = m.find? a' := by
  intro hNe
  apply Option.ext
  intro b'
  show find? (insert m a b) a' = some b' ↔ find? m a' = some b'
  simp only [← find?_of_toListModel_contains, List.Perm.mem_iff (toListModel_insert m a b), List.mem_cons,
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
  apply (find?_of_toListModel_not_contains _ _).mp
  intro a₂ b hA₂ hMem
  rw [List.Perm.mem_iff (toListModel_erase m a)] at hMem
  refine Bool.not_bne_of_beq (PartialEquivBEq.symm <| PartialEquivBEq.trans hEq hA₂) ?_
  exact List.mem_filter.mp hMem |>.right

end Std.HashMap
