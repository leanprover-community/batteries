/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Syntax
import Lean.Data.Lsp.Utf16

/-- Gets the LSP range of syntax `stx`. -/
def Lean.FileMap.rangeOfStx? (text : FileMap) (stx : Syntax) : Option Lsp.Range :=
  text.utf8RangeToLspRange <$> stx.getRange?

/-- Return the beginning of the line contatining character `pos`. -/
def Lean.findLineStart (s : String) (pos : String.Pos) : String.Pos :=
  match s.revFindAux (· = '\n') pos with
  | none => 0
  | some n => ⟨n.byteIdx + 1⟩

/--
Return the indentation (number of leading spaces) of the line containing `pos`,
and whether `pos` is the first non-whitespace character in the line.
-/
def Lean.findIndentAndIsStart (s : String) (pos : String.Pos) : Nat × Bool :=
  let start := findLineStart s pos
  let body := s.findAux (· ≠ ' ') pos start
  ((body - start).1, body == pos)
