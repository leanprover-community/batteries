/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Data.DList.Basic

/-!
# Difference list

This file provides a few results about `DList`.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `push` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/

namespace Batteries.DList

open Function

theorem toList_ofList (l : List α) : DList.toList (DList.ofList l) = l := by
  cases l; rfl; simp [ofList]

theorem ofList_toList (l : DList α) : DList.ofList (DList.toList l) = l := by
   obtain ⟨app, inv⟩ := l
   simp only [ofList, toList, mk.injEq]
   funext x
   rw [(inv x)]

theorem toList_empty : toList (@empty α) = [] := by simp [empty]

theorem toList_singleton (x : α) : toList (singleton x) = [x] := by simp [singleton]

theorem toList_append (l₁ l₂ : DList α) : toList (l₁ ++ l₂) = toList l₁ ++ toList l₂ := by
  simp only [toList, append, Function.comp]; rw [invariant]

theorem toList_cons (x : α) (l : DList α) : toList (cons x l) = x :: toList l := by
  cases l; simp [cons]

theorem toList_push (x : α) (l : DList α) : toList (push l x) = toList l ++ [x] := by
  simp only [toList, push]; rw [invariant]

@[simp]
theorem singleton_eq_ofThunk {α : Type _} {a : α} : singleton a = ofThunk [a] :=
  rfl

@[simp]
theorem ofThunk_coe {α : Type _} {l : List α} : ofThunk l = ofList l :=
  rfl

@[deprecated (since := "2024-10-16")] alias DList_singleton := singleton_eq_ofThunk
@[deprecated (since := "2024-10-16")] alias DList_lazy := ofThunk_coe

end Batteries.DList
