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
theorem Array.foldl_zero {as : Array α} {init : β} {f : β → α → β}
    : as.foldl f init (stop := 0) = init := by
  sorry

@[simp]
theorem Array.foldl_succ {as : Array α} {init : β} {f : β → α → β} (i : Fin as.size)
    : as.foldl f init (stop := i + 1) = f (as.foldl f init (stop := i)) as[i] := by
  sorry

theorem Array.foldlM_zero [Monad m] [LawfulMonad m]
    {as : Array α} {init : β} {f : β → α → m β} {start : Nat}
    : as.foldlM f init start 0 = pure init := by
  unfold foldlM foldlM.loop
  simp [Nat.not_lt_zero]

theorem Array.foldlM_succ [Monad m] [LawfulMonad m]
    {as : Array α} {init : β} {f : β → α → m β} {start : Nat} (i : Fin as.size) : start ≤ i.val
    → (as.foldlM f init start (i.val + 1)) = as.foldlM f init start i >>= (f · as[i]) := by
  intro hStartLe
  have hISuccLe : i.val + 1 ≤ as.size := Nat.succ_le_of_lt i.isLt
  have hILe : i.val ≤ as.size := Nat.le_of_lt i.isLt
  simp only [foldlM, hISuccLe, hILe, dite_true]
  conv => lhs; unfold foldlM.loop
  simp only [Nat.lt_succ_of_le hStartLe, dite_true]
  split
  case h_1 h =>
    exfalso
    exact Nat.le_trans (Nat.sub_eq_zero_iff_le.mp h) hStartLe
      |> Nat.lt_of_succ_le
      |> Nat.not_lt_of_le (Nat.le_refl _)
  case h_2 h =>
    -- This is kinda tricky, since foldlM recurses on start rather than stop. Rethink..
    sorry

namespace Std.HashMap
open List

variable [BEq α] [Hashable α] [LawfulHashable α] [PartialEquivBEq α]

/-- It is a bit easier to reason about `fold (append)` than `fold (fold)`,
so we transfer most proofs about `toList` from this auxiliary function. -/
def toList' (m : HashMap α β) : List (α × β) :=
  m.val.buckets.val.foldl (init := []) (fun acc bkt => acc ++ bkt.toList)

-- TODO: naming
theorem foldl_induction₂ {as : Array α} (motive : Nat → β → β → Prop) {init₁ init₂ : β}
    (h0 : motive 0 init₁ init₂) {f g : β → α → β}
    (hf : ∀ i : Fin as.size, ∀ acc₁ acc₂,
      motive i.1 acc₁ acc₂ → motive (i.1 + 1) (f acc₁ as[i]) (g acc₂ as[i]))
    : motive as.size (as.foldl f init₁) (as.foldl g init₂) := by
  apply Array.foldl_induction
    (motive := fun i (acc : β) => motive i acc (as.foldl g init₂ (stop := i)))
    (h0 := Array.foldl_zero ▸ h0)
    (hf := fun _ _ hPrev => by rw [Array.foldl_succ]; exact hf _ _ _ hPrev)

theorem toList_perm_toList' (m : HashMap α β) : m.toList' ~ m.toList := by
  unfold toList toList' HashMap.fold HashMap.Imp.fold
  apply foldl_induction₂ (fun _ l₁ l₂ => l₁ ~ l₂) (h0 := List.Perm.nil)
  intro acc₁ acc₂ l hAcc
  sorry

/-- The map does not store duplicate (`beq`) keys. -/
theorem Pairwise_bne_toList (m : HashMap α β) : m.toList.Pairwise (·.1 != ·.1) := by
  apply List.Perm.pairwise_iff (bne_symm _ _) (toList_perm_toList' m) |>.mp
  unfold toList'
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
