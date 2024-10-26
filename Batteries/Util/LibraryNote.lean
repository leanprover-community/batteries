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
deriving Inhabited

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

/--
format the string to be included in a single markdown bullet
-/
def _root_.String.makeBullet (s:String) := "* " ++ ("\n  ").intercalate (s.splitOn "\n")

open Lean Parser in
/--
`#help note "foo"` searches (case-insensitively) for all library notes whose
label starts with "foo", then displays those library notes sorted alphabetically by label,
grouped by label.
The command only displays the library notes that are declared in
imported files or in the same file above the line containing the command.
-/
elab "#help " colGt &"note" colGt ppSpace name:strLit : command => do
  let env ← getEnv

  -- get the library notes from both this and imported files
  let local_entries := (libraryNoteExt.getEntries env).reverse
  let imported_entries := (libraryNoteExt.toEnvExtension.getState env).importedEntries

  -- filter for the appropriate notes while casting to list
  let label_prefix := name.getString
  let imported_entries_filtered := imported_entries.flatten.toList.filterMap
    fun x => if label_prefix.isPrefixOf x.fst then some x else none
  let valid_entries := imported_entries_filtered ++ local_entries.filterMap
    fun x => if label_prefix.isPrefixOf x.fst then some x else none
  let grouped_valid_entries := valid_entries.mergeSort (·.fst ≤ ·.fst)
    |>.groupBy (·.fst == ·.fst)

  -- display results in a readable style
  if grouped_valid_entries.isEmpty then
    logError "Note not found"
  else
    logInfo <| "\n\n".intercalate <|
      grouped_valid_entries.map
        fun l => "library_note \"" ++ l.head!.fst ++ "\"\n" ++
          "\n\n".intercalate (l.map (·.snd.trim.makeBullet))
    -- this could use List.head when List.ne_nil_of_mem_groupBy gets upstreamed from mathlib
