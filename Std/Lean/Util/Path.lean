/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Elab.Term

/-!
# `compile_time_search_path%` term elaborator.

Use this as `searchPathRef.set compile_time_search_path%`.
-/

open Lean System

-- Ideally this instance would be constructed simply by `deriving instance ToExpr for FilePath`
-- but for now we have decided not to upstream the `ToExpr` derive handler from `Mathlib`.
-- https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/ToExpr.20derive.20handler/near/386476438
instance : ToExpr FilePath where
  toTypeExpr := mkConst ``FilePath
  toExpr path := mkApp (mkConst ``FilePath.mk) (toExpr path.1)

/--
Term elaborator that retrieves the current `SearchPath`.

Typical usage is `searchPathRef.set compile_time_search_path%`.

This must not be used in files that are potentially compiled on another machine and then
imported.
(That is, if used in an imported file it will embed the search path from whichever machine
compiled the `.olean`.)
-/
elab "compile_time_search_path%" : term =>
  return toExpr (← searchPathRef.get)
