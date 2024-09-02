/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Mario Carneiro, Gabriel Ebner
-/
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Basic
import Batteries.Tactic.SeqFocus
import Batteries.Util.ProofWanted

namespace Array

theorem forIn_eq_forIn_data [Monad m]
    (as : Array α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn as b f = forIn as.data b f := by
  let rec loop : ∀ {i h b j}, j + i = as.size →
      Array.forIn.loop as f i h b = forIn (as.data.drop j) b f
    | 0, _, _, _, rfl => by rw [List.drop_length]; rfl
    | i+1, _, _, j, ij => by
      simp only [forIn.loop, Nat.add]
      have j_eq : j = size as - 1 - i := by simp [← ij, ← Nat.add_assoc]
      have : as.size - 1 - i < as.size := j_eq ▸ ij ▸ Nat.lt_succ_of_le (Nat.le_add_right ..)
      have : as[size as - 1 - i] :: as.data.drop (j + 1) = as.data.drop j := by
        rw [j_eq]; exact List.getElem_cons_drop _ _ this
      simp only [← this, List.forIn_cons]; congr; funext x; congr; funext b
      rw [loop (i := i)]; rw [← ij, Nat.succ_add]; rfl
  conv => lhs; simp only [forIn, Array.forIn]
  rw [loop (Nat.zero_add _)]; rfl
@[deprecated (since := "2024-08-13")] alias forIn_eq_data_forIn := forIn_eq_forIn_data

/-! ### zipWith / zip -/

theorem data_zipWith (f : α → β → γ) (as : Array α) (bs : Array β) :
    (as.zipWith bs f).data = as.data.zipWith f bs.data := by
  let rec loop : ∀ (i : Nat) cs, i ≤ as.size → i ≤ bs.size →
      (zipWithAux f as bs i cs).data = cs.data ++ (as.data.drop i).zipWith f (bs.data.drop i) := by
    intro i cs hia hib
    unfold zipWithAux
    by_cases h : i = as.size ∨ i = bs.size
    case pos =>
      have : ¬(i < as.size) ∨ ¬(i < bs.size) := by
        cases h <;> simp_all only [Nat.not_lt, Nat.le_refl, true_or, or_true]
      -- Cleaned up aesop output below
      simp_all only [Nat.not_lt]
      cases h <;> [(cases this); (cases this)]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_left, List.append_nil]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
      · simp_all only [Nat.le_refl, Nat.lt_irrefl, dite_false, List.drop_length,
                      List.zipWith_nil_right, List.append_nil]
        split <;> simp_all only [Nat.not_lt]
    case neg =>
      rw [not_or] at h
      have has : i < as.size := Nat.lt_of_le_of_ne hia h.1
      have hbs : i < bs.size := Nat.lt_of_le_of_ne hib h.2
      simp only [has, hbs, dite_true]
      rw [loop (i+1) _ has hbs, Array.push_data]
      have h₁ : [f as[i] bs[i]] = List.zipWith f [as[i]] [bs[i]] := rfl
      let i_as : Fin as.data.length := ⟨i, has⟩
      let i_bs : Fin bs.data.length := ⟨i, hbs⟩
      rw [h₁, List.append_assoc]
      congr
      rw [← List.zipWith_append (h := by simp), getElem_eq_data_getElem, getElem_eq_data_getElem]
      show List.zipWith f (as.data[i_as] :: List.drop (i_as + 1) as.data)
        ((List.get bs.data i_bs) :: List.drop (i_bs + 1) bs.data) =
        List.zipWith f (List.drop i as.data) (List.drop i bs.data)
      simp only [data_length, Fin.getElem_fin, List.getElem_cons_drop, List.get_eq_getElem]
  simp [zipWith, loop 0 #[] (by simp) (by simp)]
@[deprecated (since := "2024-08-13")] alias zipWith_eq_zipWith_data := data_zipWith

theorem size_zipWith (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size := by
  rw [size_eq_length_data, data_zipWith, List.length_zipWith]

theorem data_zip (as : Array α) (bs : Array β) :
    (as.zip bs).data = as.data.zip bs.data :=
  data_zipWith Prod.mk as bs
@[deprecated (since := "2024-08-13")] alias zip_eq_zip_data := data_zip

theorem size_zip (as : Array α) (bs : Array β) :
    (as.zip bs).size = min as.size bs.size :=
  as.size_zipWith bs Prod.mk

/-! ### filter -/

theorem size_filter_le (p : α → Bool) (l : Array α) :
    (l.filter p).size ≤ l.size := by
  simp only [← data_length, filter_data]
  apply List.length_filter_le

/-! ### join -/

@[simp] theorem data_join {l : Array (Array α)} : l.join.data = (l.data.map data).join := by
  dsimp [join]
  simp only [foldl_eq_foldl_data]
  generalize l.data = l
  have : ∀ a : Array α, (List.foldl ?_ a l).data = a.data ++ ?_ := ?_
  exact this #[]
  induction l with
  | nil => simp
  | cons h => induction h.data <;> simp [*]
@[deprecated (since := "2024-08-13")] alias join_data := data_join

theorem mem_join : ∀ {L : Array (Array α)}, a ∈ L.join ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  simp only [mem_def, data_join, List.mem_join, List.mem_map]
  intro l
  constructor
  · rintro ⟨_, ⟨s, m, rfl⟩, h⟩
    exact ⟨s, m, h⟩
  · rintro ⟨s, h₁, h₂⟩
    refine ⟨s.data, ⟨⟨s, h₁, rfl⟩, h₂⟩⟩

/-! ### erase -/

@[simp] proof_wanted data_erase [BEq α] {l : Array α} {a : α} : (l.erase a).data = l.data.erase a

/-! ### shrink -/

theorem size_shrink_loop (a : Array α) (n) : (shrink.loop n a).size = a.size - n := by
  induction n generalizing a with simp[shrink.loop]
  | succ n ih =>
      simp[ih]
      omega

theorem size_shrink (a : Array α) (n) : (a.shrink n).size = min a.size n := by
  simp [shrink, size_shrink_loop]
  omega

/-! ### map -/

theorem mapM_empty [Monad m] (f : α → m β) : mapM f #[] = pure #[] := by
  rw [mapM, mapM.map]; rfl

@[simp] theorem map_empty (f : α → β) : map f #[] = #[] := mapM_empty ..

/-! ### mem -/

alias not_mem_empty := not_mem_nil

theorem mem_singleton : a ∈ #[b] ↔ a = b := by simp

/-! ### append -/

alias append_empty := append_nil

alias empty_append := nil_append
