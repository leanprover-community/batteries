module

public import Batteries

/-!
Lean's metaprogramming API remains available during elaboration, but runtime declarations
must explicitly import the Lean modules they use.

If this test fails in your PR because `foo` no longer produces an error, you have almost certainly
introduced an ordinary import that exposes Lean's metaprogramming API at runtime through `Batteries`.
Check your new or changed imports and their transitive dependencies, and change imports used only
for elaboration to `meta import`. Tactic implementations should be marked `meta` and meta-import
their Lean dependencies.
-/

/--
error: Invalid definition `foo`, may not access declaration `Lean.Expr.bvar` imported as `meta`; consider adding `import Lean.Expr`
-/
#guard_msgs in
public def foo : Lean.Expr := .bvar 0

-- Metaprogramming remains available while elaborating a module.
public meta def elaboratedExpr : Lean.Expr := .bvar 0
