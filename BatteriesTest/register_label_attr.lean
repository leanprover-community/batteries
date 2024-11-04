import Batteries.Test.Internal.DummyLabelAttr
import Lean.LabelAttribute

set_option linter.missingDocs false

open Lean

def f := 0

/-- info: #[] -/ #guard_msgs in #eval labelled `dummy_label_attr

attribute [dummy_label_attr] f

/-- info: #[`f] -/ #guard_msgs in #eval labelled `dummy_label_attr

section

attribute [-dummy_label_attr] f

/-- info: #[] -/ #guard_msgs in #eval labelled `dummy_label_attr

end

/-- info: #[`f] -/ #guard_msgs in #eval labelled `dummy_label_attr

-- Adding the label again is a no-op
attribute [dummy_label_attr] f

/-- info: #[`f] -/ #guard_msgs in #eval labelled `dummy_label_attr
