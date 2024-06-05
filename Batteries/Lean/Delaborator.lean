/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean.PrettyPrinter

open Lean PrettyPrinter Delaborator SubExpr

/-- Pretty print a const expression using `delabConst` and generate terminfo.
This function avoids inserting `@` if the constant is for a function whose first
argument is implicit, which is what the default `toMessageData` for `Expr` does.
Panics if `e` is not a constant. -/
def Lean.ppConst (e : Expr) : MessageData :=
  if e.isConst then
    .ofPPFormat {
      pp := fun
        | some ctx => ctx.runMetaM <| withOptions (pp.tagAppFns.set · true) <|
          -- The pp.tagAppFns option causes the `delabConst` function to annotate
          -- the constant with terminfo, which is necessary for seeing the type on mouse hover.
          PrettyPrinter.ppExprWithInfos (delab := delabConst) e
        | none => return f!"{e}"
    }
  else
    panic! "not a constant"
