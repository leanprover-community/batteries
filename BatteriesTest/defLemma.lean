import Batteries.Tactic.Lint

@[implicit_reducible]
def foo : True := trivial

@[reducible, instance]
def bar : Nonempty Bool := ⟨true⟩

instance bar' : Nonempty String := ⟨""⟩

/--
error: /- The `defLemma` linter reports:
INCORRECT DEF/LEMMA: -/
#check foo /- is a def, should be lemma/theorem -/
#check bar /- is a def, should be lemma/theorem -/
-/
#guard_msgs in
#lint- only defLemma
