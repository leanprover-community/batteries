import Batteries.Tactic.Lint
import Batteries.Linter

-- internal names should be ignored
theorem Foo.Foo._bar : True := trivial

#lint- only dupNamespace
