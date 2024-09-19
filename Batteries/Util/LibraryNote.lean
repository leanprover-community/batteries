/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
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
Use `#check_note "some tag"` to display all notes with the tag
`"some tag"` in the infoview.
-/
elab "library_note " title:strLit ppSpace text:docComment : command => do
  modifyEnv (libraryNoteExt.addEntry · (title.getString, text.getDocString))

/--
`#check_note "some tag"` displays all library notes with tag
`"some tag"` in the infoview.
The command only displays the library notes that are declared in
imported files or in the same file above the line containing the command.
-/
elab "#check_note" name:strLit : command => do
  let env ← getEnv

  -- get the library notes from both this and imported files
  let local_entries := libraryNoteExt.getEntries env
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
    logInfo <| "\n\n".intercalate <| valid_entries.reverse.map ("/--" ++ · ++ "-/")
