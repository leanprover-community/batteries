import Batteries.Linter
import Batteries.Linter

-- internal names should be ignored
theorem Foo.Foo._bar : True := trivial

#lint- only dupNamespace
