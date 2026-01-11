/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

public meta import Lean.Elab.Command

public meta section

/-!
# Define the `library_note` command.
-/

namespace Batteries.Util

open Lean

/-- A library note is identified by the name of its declaration, and its content should be contained
in its doc-string. -/
@[expose] def LibraryNote := Unit
deriving Inhabited

namespace LibraryNote

/-- Entry for library notes in the environment extension.

We only store the name, and look up the constant's docstring to find its contents.
-/
@[expose] def LibraryNoteEntry := Name
deriving Inhabited

/-- Encode a name to be safe for the Lean export format.

The current export format (used by `lean4export` and consumed by external type checkers like
`nanoda_lib`) does not support whitespace in declaration names. Library notes often have
human-readable names with spaces like `«my library note»`, which would produce declarations
like `LibraryNote.«my library note»` that cannot be exported.

This function replaces spaces with underscores to produce export-safe names like
`LibraryNote.my_library_note`.
-/
def encodeNameForExport (n : Name) : Name :=
  n.componentsRev.foldl (init := .anonymous) fun acc c =>
    match c with
    | .str _ s => .str acc (s.replace " " "_")
    | .num _ k => .num acc k
    | .anonymous => acc

/-- Environment extension supporting `library_note`. -/
initialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id
  }

open Elab Command in
/-- `library_note «my note» /-- documentation -/` creates a library note named `my note`
in the `LibraryNote` namespace, whose content is `/-- documentation -/`.
This can then be cross-referenced using
```
-- See note [some tag]
```
in doc-comments.
You can access the contents using, for example, `#print LibraryNote.my_note`.
(Note: spaces in the name are converted to underscores in the declaration name for
compatibility with the Lean export format.)
Use `#help note "some tag"` to display all notes with the tag `"some tag"` in the infoview.
This command can be imported from Batteries.Tactic.HelpCmd .
-/
elab "library_note " name:ident ppSpace dc:docComment : command => do
  let origName := name.getId
  -- Store original name (with spaces) for lookup via `#help note`
  modifyEnv (libraryNoteExt.addEntry · origName)
  -- Use encoded name (spaces → underscores) for declaration, for export format compatibility
  let safeName := encodeNameForExport origName
  let stx ← `(
    $dc:docComment
    def $(mkIdent (`_root_.LibraryNote ++ safeName)) : LibraryNote :=
      default)
  elabCommandTopLevel stx

open Elab Command in
/-- Support the old `library_note "foo"` syntax, with a deprecation warning. -/
elab "library_note " name:str ppSpace dc:docComment : command => do
  logWarningAt name <|
    "deprecation warning: library_note now takes an identifier instead of a string.\n" ++
    "Hint: replace the double quotes with «french quotes»."
  let name := Name.mkSimple name.getString
  let stx ← `(library_note $(mkIdent name):ident $dc:docComment)
  elabCommandTopLevel stx

open Elab Command in
/-- Support the old `library_note2 «foo»` syntax, with a deprecation warning. -/
elab "library_note2 " name:ident ppSpace dc:docComment : command => do
  logWarningAt name <|
    "deprecation warning: library_note2 has been replaced with library_note."
  let stx ← `(library_note $name:ident $dc:docComment)
  elabCommandTopLevel stx

open Elab Command in
/-- Support the old `library_note2 "foo"` syntax, with a deprecation warning. -/
elab "library_note2 " name:str ppSpace dc:docComment : command => do
  logWarningAt name <|
    "deprecation warning: library_note2 has been replaced with library_note."
  let stx ← `(library_note name $dc:docComment)
  elabCommandTopLevel stx
