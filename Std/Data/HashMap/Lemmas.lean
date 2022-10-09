/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Data.HashMap.Basic
import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas
import Std.Tactic.ShowTerm

namespace Std.HashMap.Imp

namespace Bucket

@[ext] protected theorem ext : ∀ {b₁ b₂ : Bucket α β}, b₁.1.data = b₂.1.data → b₁ = b₂
  | ⟨⟨_⟩, _⟩, ⟨⟨_⟩, _⟩, rfl => rfl

theorem update_data (self : Bucket α β) (i d h) :
    (self.update i d h).1.data = self.1.data.set i.toNat d := rfl

theorem exists_of_update (self : Bucket α β) (i d h) :
    ∃ l₁ l₂, self.1.data = l₁ ++ self.1[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.update i d h).1.data = l₁ ++ d :: l₂ := by
  simp [Array.getElem_eq_data_get]; exact List.exists_of_set' h

theorem size_eq (data : Bucket α β) :
  size data = .sum (data.1.data.map (·.toList.length)) := rfl

theorem mk_size (h) : (mk n h : Bucket α β).size = 0 := by
  simp [Bucket.size_eq, Bucket.mk, mkArray]; clear h
  induction n <;> simp [*]

end Bucket

theorem empty'_WF [BEq α] [Hashable α] : (empty' n h : Imp α β).buckets.WF := by
  refine ⟨fun _ h => ?_, fun i h => ?_⟩
  · simp [Bucket.mk, empty', mkArray, List.mem_replicate] at h
    simp [h, List.Pairwise.nil]
  · simp [Bucket.mk, empty', mkArray, Array.getElem_eq_data_get, AssocList.All]

theorem reinsertAux_size (hashFn : α → UInt64) (data : Bucket α β) (a : α) (b : β) :
    (reinsertAux hashFn data a b).size = data.size.succ := by
  simp [Bucket.size_eq, reinsertAux]
  refine have ⟨l₁, l₂, h₁, _, eq⟩ := Bucket.exists_of_update ..; eq ▸ ?_
  simp [h₁, Nat.succ_add]; rfl

theorem expand_size [Hashable α] {buckets : Bucket α β} :
    (expand sz buckets).buckets.size = buckets.size := by
  rw [expand, go]
  · rw [Bucket.mk_size]; simp [Bucket.size]
  · intro.
where
  go (i source) (target : Bucket α β) (hs : ∀ j < i, source.data.getD j .nil = .nil) :
      (expand.go i source target).size =
        .sum (source.data.map (·.toList.length)) + target.size := by
    unfold expand.go; split
    case _ H =>
      refine (go (i+1) _ _ fun j hj => ?a).trans ?b <;> simp
      case a =>
        simp [List.getD_eq_get?, List.get?_set]; split
        case _ => cases List.get? .. <;> rfl
        case _ H => exact hs _ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (Ne.symm H))
      case b =>
        refine have ⟨l₁, l₂, h₁, _, eq⟩ := List.exists_of_set' H; eq ▸ ?_
        simp [h₁, Bucket.size_eq]
        rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]; congr 1
        (conv => rhs; rw [Nat.add_left_comm]); congr 1
        rw [← Array.getElem_eq_data_get]
        have := @reinsertAux_size α β; simp [Bucket.size] at this
        induction source[i].toList generalizing target <;> simp [*, Nat.succ_add]; rfl
    case _ H =>
      rw [(_ : Nat.sum _ = 0), Nat.zero_add]
      rw [← (_ : source.data.map (fun _ => .nil) = source.data)]
      · simp; induction source.data <;> simp [*]
      refine List.ext_get (by simp) fun j h₁ h₂ => ?_
      simp
      have := (hs j (Nat.lt_of_lt_of_le h₂ (Nat.not_lt.1 H))).symm
      rwa [List.getD_eq_get?, List.get?_eq_get, Option.getD_some] at this
termination_by go i source _ _ => source.size - i

theorem insert_size [BEq α] [Hashable α] {m : Imp α β} {k v}
    (h : m.size = m.buckets.size) :
    (insert m k v).size = (insert m k v).buckets.size := by
  unfold insert; dsimp [cond]; split
  · dsimp [Bucket.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Bucket.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Bucket.size_eq]
  split
  · dsimp [Bucket.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Bucket.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Bucket.size_eq, Nat.succ_add]; rfl
  · rw [expand_size]; simp [h, expand, Bucket.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Bucket.exists_of_update ..; eq ▸ ?_
    simp [h₁, Bucket.size_eq, Nat.succ_add]; rfl

theorem erase_size [BEq α] [Hashable α] {m : Imp α β} {k}
    (h : m.size = m.buckets.size) :
    (erase m k).size = (erase m k).buckets.size := by
  unfold erase; dsimp [cond]; split
  case _ H =>
    simp [h, Bucket.size]
    refine have ⟨_, _, h₁, _, eq⟩ := Bucket.exists_of_update ..; eq ▸ ?_
    simp [h, h₁, Bucket.size_eq]
    rw [(_ : List.length _ = _ + 1), Nat.add_right_comm]; {rfl}
    clear h₁ eq
    simp [AssocList.contains_eq] at H
    have ⟨a, h₁, h₂⟩ := H
    refine have ⟨_, _, _, _, _, h, eq⟩ := List.exists_of_eraseP h₁ h₂; eq ▸ ?_
    simp [h]; rfl
  case h_2 => exact h

-- TODO
-- theorem WF_iff [BEq α] [Hashable α] {m : Imp α β} :
--     m.WF ↔ m.size = m.buckets.size ∧ m.buckets.WF := by
--   refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => .mk h₁ h₂⟩
--   induction h with
--   | mk h₁ h₂ => exact ⟨h₁, h₂⟩
--   | @empty' _ h => exact ⟨(Bucket.mk_size h).symm, empty'_WF⟩
--   | insert _ ih => exact ⟨insert_size ih.1, sorry⟩
--   | erase _ ih => exact ⟨erase_size ih.1, sorry⟩
