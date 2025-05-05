import Batteries.Linter.TrailingWhitespace

set_option linter.trailingWhitespace false

section 
end
/--
warning: using 'exit' to interrupt Lean
---
warning: Lines should not end with a space.
note: this linter can be disabled with `set_option linter.trailingWhitespace false`
---
warning: Files should end with a line-break.
note: this linter can be disabled with `set_option linter.trailingWhitespace false`
-/
#guard_msgs in
set_option linter.trailingWhitespace true in
#exit