/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Lean.Syntax
public import Lean.Data.Lsp.Utf16

public section

namespace Lean

/-- Gets the LSP range of syntax `stx`. -/
@[deprecated Lean.FileMap.lspRangeOfStx? (since := "2025-09-23")]
def FileMap.rangeOfStx? (text : FileMap) (stx : Syntax) : Option Lsp.Range :=
  text.utf8RangeToLspRange <$> stx.getRange?

/-- Return the beginning of the line contatining character `pos`. -/
def findLineStart (s : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
  (s.pos! pos).revFind? '\n' |>.map (·.next!) |>.getD s.startPos |>.offset

/--
Return the indentation (number of leading spaces) of the line containing `pos`,
and whether `pos` is the first non-whitespace character in the line.
-/
def findIndentAndIsStart (s : String) (pos : String.Pos.Raw) : Nat × Bool :=
  let start := findLineStart s pos
  let body := (s.pos! start).find (· ≠ ' ') |>.offset
  (start.byteDistance body, body == pos)

/-- Converts a `DeclarationRange` to a `Syntax.Range`. This assumes that the
`DeclarationRange` is sourced in the given `FileMap`. -/
def DeclarationRange.toSyntaxRange (map : FileMap) (range : DeclarationRange) : Syntax.Range :=
  ⟨map.ofPosition range.pos, map.ofPosition range.endPos⟩

/-- Yields the `Syntax.Range` for the declaration `decl` in the current file. If `decl` is not in
the current file, yields `none`.

By default, this provides the "selection range", which is the part that receives hovers, such as the
declaration's identifier or the `instance` token for an unnamed instance. If `fullRange` is instead
set to `true`, this returns the full declaration range (which excludes modifiers, such as the
docstring). -/
def findDeclarationSyntaxRange? {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    [MonadFileMap m] (decl : Name) (fullRange := false) : m (Option Syntax.Range) := do
  unless (← getEnv).getModuleIdxFor? decl |>.isNone do return none
  let some ranges ← findDeclarationRanges? decl | return none
  return (if fullRange then ranges.range else ranges.selectionRange).toSyntaxRange (← getFileMap)

/-- Runs `x` with a synthetic ref that has position info locating the given `decl` if it is defined
in the current file, or else runs `x` without modifying the ref.

By default, this uses the "selection range" of the declaration, which is the part that receives
hovers, such as the declaration's identifier or the `instance` token for an unnamed instance. If
`fullRange` is instead set to `true`, this uses the full declaration range (which excludes
modifiers, such as the docstring).

`canonical` applies to the synthetic syntax; see `Syntax.ofRange`. -/
@[always_inline, inline]
def withDeclRef? {α} {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    [MonadFileMap m] [MonadRef m] (decl : Name) (x : m α)
    (fullRange := false) (canonical := true) : m α := do
  let some range ← findDeclarationSyntaxRange? decl fullRange | x
  withRef (.ofRange range canonical) x

end Lean
