/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
import Batteries.Tactic.Alias

namespace BitVec

@[deprecated (since := "2024-02-07")] alias zero_is_unique := eq_nil

/-! ### sub/neg -/

@[deprecated (since := "2024-02-07")] alias sub_toNat := toNat_sub

@[deprecated (since := "2024-02-07")] alias neg_toNat := toNat_neg
