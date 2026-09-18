/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Data.Except
public import Lean.Util.Trace

@[expose] public section

open Lean

namespace Except

/-- Visualize an `Except` using a checkmark or a cross. -/
def emoji : Except ε α → String
  | .error _ => crossEmoji
  | .ok _ => checkEmoji

end Except
