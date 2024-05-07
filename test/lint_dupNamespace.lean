import Batteries.Tactic.Lint

-- internal names should be ignored
theorem Foo.Foo._bar : True := trivial

#lint- only dupNamespace
