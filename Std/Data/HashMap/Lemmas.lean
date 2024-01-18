/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap.Basic
import Std.Data.Array.Lemmas
import Std.Util.ProofWanted

namespace Std.HashMap

@[simp] theorem empty_buckets [BEq α] [Hashable α] : (∅ : HashMap α β).1.buckets.1 = mkArray 8 AssocList.nil := rfl

@[simp] theorem empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none := by simp [find?, Imp.find?, Imp.mkIdx, USize.modn_lt]

proof_wanted insert_find? [BEq α] [Hashable α] (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).find? a' = if a' == a then some b else m.find? a'
