/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

module
import Batteries.Data.List.Basic

@[expose] public section

namespace Batteries

/-- Nonempty list type. -/
@[ext] structure List1 (α : Type _) where
  /-- Constructor for nonempty list type. -/
  cons ::
  /-- First element of a nonempty list. -/
  head : α
  /-- Additional elements of a nonempty list. -/
  tail : List α
deriving Inhabited, DecidableEq, BEq, Hashable

namespace List1

/-- Alternate constructor for nonempty list type. -/
abbrev mk : (l : List α) → l ≠ [] → List1 α
  | head :: tail, _ => cons head tail

/-- Coercion from nonempty list to list. -/
abbrev toList : List1 α → List α
  | cons head tail => head :: tail

/-- Length of a nonempty list. -/
abbrev length : List1 α → Nat
  | cons _ tail => tail.length + 1

/-- Append a list to a nonempty list. -/
abbrev append : List1 α → List α → List1 α
  | cons head tail, list => cons head (tail ++ list)

@[inline, always_inline]
instance : Coe (List1 α) (List α) := ⟨toList⟩

@[inline, always_inline]
instance : HAppend (List1 α) (List α) (List1 α) := ⟨append⟩

@[inline, always_inline]
instance : Append (List1 α) where
  append a b := HAppend.hAppend a (b : List α)

@[inline, always_inline]
instance : GetElem (List1 α) Nat α fun l i => i < l.length where
  getElem
    | cons head _, 0, _ => head
    | cons _ tail, i+1, h => tail[i]'(Nat.lt_of_succ_lt_succ h)

theorem toList_ne_nil (l : List1 α) : l.toList ≠ [] := by simp

@[grind =]
theorem toList_mk : {l : List α} →  (h : l ≠ []) → (List1.mk l h).toList = l
  | _ :: _, _ => rfl

theorem length_ne_zero (l : List1 α) : l.length ≠ 0 := by simp

instance {l : List1 α} : NeZero l.length := ⟨l.length_ne_zero⟩

@[grind =]
theorem toList_cons (head : α) (tail : List α) : (cons head tail).toList = head :: tail := rfl

@[grind =]
theorem mk_toList : {l : List1 α} → List1.mk l.toList l.toList_ne_nil = l := by simp

@[simp, grind =]
theorem head_mk : {l : List α} → (h : l ≠ []) → (List1.mk l h).head = l.head h
  | _ :: _, _ => rfl

@[simp, grind =]
theorem tail_mk : {l : List α} → (h : l ≠ []) → (List1.mk l h).tail = l.tail
  | _ :: _, _ => rfl

@[grind =]
theorem length_mk : {l : List α} → (h : l ≠ []) → (List1.mk l h).length = l.length
  | _ :: _, _ => rfl

@[grind =]
theorem length_eq_length_toList (l : List1 α) : l.length = l.toList.length := by simp

@[simp, grind =]
theorem getElem_eq_getElem_toList {l : List1 α} {i : Nat} {h : i < l.length} :
    l[i] = l.toList[i] := by cases i <;> rfl
