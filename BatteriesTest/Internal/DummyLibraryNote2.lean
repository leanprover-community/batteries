import BatteriesTest.Internal.DummyLibraryNote

library_note "test" /--
3: this is a note in a different file importing the above testnotes,
but still imported by the actual testfile.
-/

library_note "Test" /--
1: this is a testnote with a label starting with "Te"
-/

library_note "Other" /--
1: this is a testnote with a label not starting with "te",
so it shouldn't appear when looking for notes with label starting with "te".
-/
