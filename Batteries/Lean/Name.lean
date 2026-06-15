/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Data.Name

/-!
# Additional functions on `Lean.Name`.
-/

public section

open Lean Meta Elab

/-- Decapitalize the last component of a name. -/
def Lean.Name.decapitalize (n : Name) : Name :=
  n.modifyBase fun
    | .str p s => .str p s.decapitalize
    | n       => n
