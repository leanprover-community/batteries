/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.HashMap.Basic
import Batteries.Tactic.Alias

/-!
# Lemmas for `Batteries.HashMap`

Note that Lean core provides an alternative hash map implementation, `Std.HashMap`, which comes with
more lemmas. See the module `Std.Data.HashMap.Lemmas`.
-/

namespace Batteries.HashMap

@[deprecated (since := "2025-03-31")]
alias empty_find? := Std.HashMap.getElem?_empty
