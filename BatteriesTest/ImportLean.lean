module

public import Batteries

/-!
Lean's metaprogramming API remains available during elaboration, but runtime declarations
must explicitly import the Lean modules they use.
-/

/--
error: Invalid definition `foo`, may not access declaration `Lean.Expr.bvar` imported as `meta`; consider adding `import Lean.Expr`
-/
#guard_msgs in
public def foo : Lean.Expr := .bvar 0
