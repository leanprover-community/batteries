/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean.PrettyPrinter

open Lean PrettyPrinter Delaborator SubExpr

/-- Abbreviation for `Lean.MessageData.ofConst`. -/
@[deprecated Lean.MessageData.ofConst (since := "2024-05-18")]
def Lean.ppConst (e : Expr) : MessageData :=
  Lean.MessageData.ofConst e
