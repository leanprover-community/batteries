import Std.Tactic.LabelAttr

/-- A dummy label attribute, which can be used for testing. -/
-- This can't live in `Std.Tactic.LabelAttr`
-- (because we can't use the extension in the same file it is initialized)
-- and it can't live in `test/`, because files there can not import other files in `test/`.
register_label_attr dummy_label_attr
