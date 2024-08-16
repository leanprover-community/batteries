/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.BinomialHeap.Basic

namespace Batteries.BinomialHeap
namespace Imp

theorem Heap.findMin_val : ((s : Heap α).findMin le k res).val = s.headD le res.val :=
  match s with
  | .nil => rfl
  | .cons r a c s => by rw [findMin, headD]; split <;> apply findMin_val

theorem Heap.deleteMin_fst : ((s : Heap α).deleteMin le).map (·.1) = s.head? le :=
  match s with
  | .nil => rfl
  | .cons r a c s => by simp only [deleteMin, findMin_val, Option.map, head?]

@[simp] theorem HeapNode.WF.realSize_eq :
    ∀ {n} {s : HeapNode α}, s.WF le a n → s.realSize + 1 = 2 ^ n
  | _, .nil, rfl => rfl
  | _, .node .., ⟨_, rfl, _, c, s⟩ => by
    rw [realSize, realSize_eq c, Nat.pow_succ, Nat.mul_succ]
    simp [Nat.add_assoc, realSize_eq s]

@[simp] theorem Heap.WF.size_eq :
    ∀ {s : Heap α}, s.WF le n → s.size = s.realSize
  | .nil, _ => rfl
  | .cons .., ⟨_, h₁, h₂⟩ => by
    simp [size, Nat.shiftLeft, size_eq h₂, Nat.pow_succ, Nat.mul_succ]
    simp [Nat.add_assoc, Nat.one_shiftLeft, h₁.realSize_eq, h₂.size_eq]

end Imp
