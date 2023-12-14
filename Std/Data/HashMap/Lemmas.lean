/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.HashMap.Basic
import Std.Util.ProofWanted

namespace Std.HashMap

@[simp] proof_wanted empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none

proof_wanted insert_find? [BEq α] [Hashable α] (m : HashMap α β) (a a' : α) (b : β) :
    (m.insert a b).find? a' = if a' == a then some b else m.find? a'
