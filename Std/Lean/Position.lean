/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Data.Lsp.Utf16

/-- Gets the LSP range from a pair of positions. -/
def Lean.FileMap.utf8PosToLspRange (text : FileMap) (start «end» : String.Pos) : Lsp.Range :=
  { start := text.utf8PosToLspPos start, «end» := text.utf8PosToLspPos «end» }

/-- Gets the LSP range of syntax `stx`. -/
def Lean.FileMap.rangeOfStx? (text : FileMap) (stx : Syntax) : Option Lsp.Range :=
  return text.utf8PosToLspRange (← stx.getPos?) (← stx.getTailPos?)
