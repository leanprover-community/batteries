import Batteries.Util.LibraryNote
import Batteries.Test.Internal.DummyLibraryNote2

/--
info: Note not found
-/
#guard_msgs in
#help note "no note"

library_note "test"/--
4: This note was not imported, and therefore appears below the imported notes.
-/

library_note "test"/--
5: This note was also not imported, and therefore appears below the imported notes,
and the previously added note.
-/


/--
info: /--
1: This is a testnote for testing the library note feature of batteries.
The `#help note` command should be able to find this note when imported.
-/

/--
2: This is a second testnote for testing the library note feature of batteries.
-/

/--
3: this is a note in a different file importing the above testnotes,
but still imported by the actual testfile.
-/

/--
4: This note was not imported, and therefore appears below the imported notes.
-/

/--
5: This note was also not imported, and therefore appears below the imported notes,
and the previously added note.
-/
-/
#guard_msgs in
#help note "test"
