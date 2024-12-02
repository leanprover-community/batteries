/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
import Batteries.Data.List.OfFn

namespace List

@[deprecated (since := "2024-11-19")]
alias length_list := length_finRange

@[deprecated (since := "2024-11-19")]
alias getElem_list := getElem_finRange

@[deprecated (since := "2024-11-19")]
alias list_zero := finRange_zero

@[deprecated (since := "2024-11-19")]
alias list_succ := finRange_succ

@[deprecated (since := "2024-11-19")]
alias list_succ_last := finRange_succ_last

@[deprecated (since := "2024-11-19")]
alias list_reverse := finRange_reverse
