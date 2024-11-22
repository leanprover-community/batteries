import Batteries.Util.LibraryNote

library_note "test" /--
1: This is a testnote for testing the library note feature of batteries.
The `#help note` command should be able to find this note when imported.
-/

library_note "test" /--
2: This is a second testnote for testing the library note feature of batteries.
-/

library_note "temporary note" /--
1: This is a testnote whose label also starts with "te", but gets sorted before "test"
-/
