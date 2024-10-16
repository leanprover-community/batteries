import Batteries.Util.LibraryNote


/--
info: Note not found
-/
#guard_msgs in
#help note "test"

library_note "test"
/-- Lorem ipsum dolor sit amet, consectetur adipiscing elit.
Sed viverra.
-/

/--
info: /--
Lorem ipsum dolor sit amet, consectetur adipiscing elit.
Sed viverra.
-/
-/
#guard_msgs in
#help note "test"


library_note "test" /--
Cras ut luctus neque.
Mauris ullamcorper turpis in eros vulputate.
-/


/--
info: /--
Lorem ipsum dolor sit amet, consectetur adipiscing elit.
Sed viverra.
-/

/--
Cras ut luctus neque.
Mauris ullamcorper turpis in eros vulputate.
-/
-/
#guard_msgs in
#help note "test"
