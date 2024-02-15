/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap.Basic
import Std.Util.ProofWanted
import Std.Data.Array.Lemmas

namespace Std.HashMap

theorem empty_def [BEq α] [Hashable α] : (∅ : HashMap α β) = HashMap.empty :=
  rfl

@[simp] theorem mkArray_getElem {α : Type u} {v: α} {n i : Nat}
    (h : i < Array.size (mkArray n v)) :
    (mkArray n v)[i]'h = v :=
  List.eq_of_mem_replicate (Array.getElem_mem_data _ h)

@[simp] theorem empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none := by
  simp [empty_def, empty, mkHashMap, find?, Imp.find?, Imp.empty', Imp.empty, Imp.Buckets.mk]

proof_wanted insert_find? [BEq α] [Hashable α] (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).find? a' = if a' == a then some b else m.find? a'
