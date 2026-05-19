/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas R. Murrills
-/
module

public import Lean.Syntax
public import Lean.Data.Lsp.Utf16

public section

namespace Lean

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

/--
If `pos` is a `Lean.Position`, then `pos.getDeclsAfter` returns the array of names of declarations
whose selection range begins in position at least `pos`. By using the `selectionRange`, which is
usually smaller than the `range`, we err on the side of including declarations when possible.

By default, this only inspects the local branch of the environment. This is compatible with being
used to find declarations from the current command in a linter, where we have already waited for
async tasks/parallel branches to complete. Further, since the environment exposed to linters does
not include constants added after the elaboration of the current command, it is safe to use this on
the command's start position without picking up later declarations.
-/
protected def Position.getDeclsAfter (env : Environment) (pos : Position)
    (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  declRangeExt.getState env asyncMode |>.foldl (init := #[])
    fun acc name { selectionRange .. } =>
      if selectionRange.pos.lt pos then acc else acc.push name

/--
If `pos` is a `String.Pos.Raw`, then `pos.getDeclsAfter` returns the array of names of declarations
whose selection range begins in position at least `pos`. By using the `selectionRange`, which is
usually smaller than the `range`, we err on the side of including declarations when possible.

By default, this is intended for use in linters, where only the current environment branch needs to
be checked. See the docstring for `Lean.Position.getDeclsAfter` for details.
-/
@[inline] protected def _root_.String.Pos.Raw.getDeclsAfter (env : Environment) (map : FileMap)
    (pos : String.Pos.Raw) (asyncMode := EnvExtension.AsyncMode.local) : Array Name :=
  map.toPosition pos |>.getDeclsAfter env asyncMode

/-- Converts a `DeclarationRange` to a `Syntax.Range`. This assumes that the
`DeclarationRange` is sourced in the given `FileMap`. -/
def DeclarationRange.toSyntaxRange (map : FileMap) (range : DeclarationRange) : Syntax.Range :=
  ⟨map.ofPosition range.pos, map.ofPosition range.endPos⟩

/-- Yields the `Syntax.Range` for the declaration `decl` in the current file. If `decl` is not in
the current file, yields `none`.

By default, this provides the "selection range", which is usually the declaration's identifier or
e.g. the `instance` token for an unnamed instance. If `fullRange` is instead set to `true`, this
returns the full declaration range (which includes modifiers, such as the docstring). -/
def findDeclarationSyntaxRange? {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    [MonadFileMap m] (decl : Name) (fullRange := false) : m (Option Syntax.Range) := do
  if (← getEnv).isImportedConst decl then return none
  let some ranges ← findDeclarationRanges? decl | return none
  return (if fullRange then ranges.range else ranges.selectionRange).toSyntaxRange (← getFileMap)

/-- Runs `x` with a synthetic ref that has position info locating the given `decl` if it is defined
in the current file, or else runs `x` without modifying the ref. This is useful for logging on a
declaration's name from within linters.

By default, this uses the "selection range" of the declaration, which is usually the declaration's
identifier or e.g. the `instance` token for an unnamed instance. (This is also the place that
receives hovers for the declaration.)

If `fullRange` is instead set to `true`, this uses the full declaration range, which includes the
modifiers (such as the docstring, if there is one) and the body of the declaration.

`canonical` applies to the synthetic syntax generated for the ref; see `Syntax.ofRange`. -/
@[always_inline, inline]
def withDeclRef? {α} {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    [MonadFileMap m] [MonadRef m] (decl : Name) (x : m α)
    (fullRange := false) (canonical := true) : m α := do
  let some range ← findDeclarationSyntaxRange? decl fullRange | x
  withRef (.ofRange range canonical) x

end Lean
