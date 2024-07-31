/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Batteries.Data.List.Lemmas

/-!
# Basic properties of `List.eraseIdx`

`List.eraseIdx l k` erases `k`-th element of `l : List α`.
If `k ≥ length l`, then it returns `l`.
-/

namespace List

universe u v
variable {α : Type u} {β : Type v}

@[deprecated mem_eraseIdx_iff_getElem (since := "2024-06-12")]
theorem mem_eraseIdx_iff_get {x : α} {l} {k} :
    x ∈ eraseIdx l k ↔ ∃ i : Fin l.length, ↑i ≠ k ∧ l.get i = x := by
  simp only [mem_eraseIdx_iff_getElem, ne_eq, exists_and_left, get_eq_getElem]
  constructor
  · rintro ⟨i, h, w, rfl⟩
    exact ⟨⟨i, w⟩, h, rfl⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨i.1, h, i.2, rfl⟩

@[deprecated mem_eraseIdx_iff_getElem? (since := "2024-06-12")]
theorem mem_eraseIdx_iff_get? {x : α} {l} {k} : x ∈ eraseIdx l k ↔ ∃ i ≠ k, l.get? i = x := by
  simp [mem_eraseIdx_iff_getElem?]

end List
