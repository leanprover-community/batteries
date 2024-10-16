/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Edward van de Meent
-/
import Lean.Elab.Command

/-!
# Define the `library_note` command.
-/

namespace Batteries.Util.LibraryNote

open Lean

/-- A library note consists of a (short) tag and a (long) note. -/
def LibraryNoteEntry := String × String

/-- Environment extension supporting `library_note`. -/
initialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

open Lean Parser Command in
/--
```
library_note "some tag" /--
... some explanation ...
-/
```
creates a new "library note", which can then be cross-referenced using
```
-- See note [some tag]
```
in doc-comments.
Use `#help note "some tag"` to display all notes with the tag
`"some tag"` in the infoview.
-/
elab "library_note " title:strLit ppSpace text:docComment : command => do
  modifyEnv (libraryNoteExt.addEntry · (title.getString, text.getDocString))


open Lean Parser in
/--
`#help note "some tag"` displays all library notes with tag
`"some tag"` in the infoview.
The command only displays the library notes that are declared in
imported files or in the same file above the line containing the command.
-/
elab "#help note" name:strLit : command => do
  let env ← getEnv

  -- get the library notes from both this and imported files
  let local_entries := (libraryNoteExt.getEntries env).reverse
  let imported_entries := (libraryNoteExt.toEnvExtension.getState env).importedEntries

  -- filter for the appropriate notes while casting to list
  let entry_name := name.getString
  let imported_entries_filtered := imported_entries.flatten.toList.filterMap
    (fun x => if x.fst == entry_name then Option.some x.snd else Option.none)
  let valid_entries := imported_entries_filtered ++ local_entries.filterMap
    (fun x => if x.fst == entry_name then some x.snd else none)

  -- display results in a readable style
  if valid_entries.isEmpty then
    logInfo "Note not found"
  else
    logInfo <| "\n\n".intercalate <|
      valid_entries.map ("/--\n" ++ String.trim · ++ "\n-/")

  -- for when `List.ne_nil_of_mem_groupBy` has landed in batteries or higher in the hierarchy.
  /-
  let imported_entries_filtered := imported_entries.flatten.toList.filterMap
    (fun x => if entry_name.isPrefixOf x.fst then some x else Option.none)
  let valid_entries := imported_entries_filtered ++ local_entries.filterMap
    (fun x => if entry_name.isPrefixOf x.fst then some x else none)

  let grouped_valid_entries := valid_entries.mergeSort (·.fst ≤ ·.fst)
    |>.groupBy (·.fst == ·.fst)

  -- display results in a readable style
  if grouped_valid_entries.isEmpty then
    logInfo "Note not found"
  else
    logInfo <| "\n\n".intercalate <|
      grouped_valid_entries.attach.map (fun ⟨l,h⟩ =>
        "library_note \"" ++ (l.head (by
          unfold grouped_valid_entries at h
          -- `exact List.ne_nil_of_mem_groupBy h`
          -- from mathlib would prove this
          sorry)
          ).fst ++ "\"\n"
        ++ ("\n\n".intercalate <| l.map (fun e => "/--\n" ++ e.snd.trim ++ "\n-/")))
  -/
