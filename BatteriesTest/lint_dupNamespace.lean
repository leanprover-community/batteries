import Batteries.Tactic.Lint

-- internal names should be ignored
theorem Foo.Foo._bar : True := trivial

-- deprecated names are ignored
@[deprecated Foo.Foo._bar (since := "today")] theorem Foo.Foo.bar : True := trivial

#lint- only dupNamespace
