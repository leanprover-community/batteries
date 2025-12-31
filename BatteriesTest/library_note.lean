import Batteries.Tactic.HelpCmd
import BatteriesTest.Internal.DummyLibraryNote2

/--
error: Note not found
-/
#guard_msgs in
#help note "no note"

/--
info: library_note Other
/-- 1: this is a testnote with a label not starting with "te",
so it shouldn't appear when looking for notes with label starting with "te". -/
-/
#guard_msgs in
#help note "Other"

library_note "test4"/--
4: This note was not imported, and therefore appears below the imported notes.
-/

library_note "test5"/--
5: This note was also not imported, and therefore appears below the imported notes,
and the previously added note.
-/


/--
info: library_note «temporary note»
/-- 1: This is a testnote whose label also starts with "te", but gets sorted before "test" -/

library_note test1
/-- 1: This is a testnote for testing the library note feature of batteries.
The `#help note` command should be able to find this note when imported. -/

library_note test2
/-- 2: This is a second testnote for testing the library note feature of batteries. -/

library_note test3
/-- 3: this is a note in a different file importing the above testnotes,
but still imported by the actual testfile. -/

library_note test4
/-- 4: This note was not imported, and therefore appears below the imported notes. -/

library_note test5
/-- 5: This note was also not imported, and therefore appears below the imported notes,
and the previously added note. -/
-/
#guard_msgs in
#help note "te"
