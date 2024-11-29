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
deriving Inhabited

/-- Environment extension supporting `library_note`. -/
initialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatMap id
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
Use `#help note "some tag"` to display all notes with the tag `"some tag"` in the infoview.
This command can be imported from Batteries.Tactic.HelpCmd .
-/
elab "library_note " title:strLit ppSpace text:docComment : command => do
  modifyEnv (libraryNoteExt.addEntry · (title.getString, text.getDocString))
