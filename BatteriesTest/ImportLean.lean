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

-- Metaprogramming remains available while elaborating a module.
public meta def elaboratedExpr : Lean.Expr := .bvar 0

-- General data helpers remain usable by runtime declarations.
public def dataEmoji (x : Except String Nat) : String := x.emoji

#guard dataEmoji (.ok 7) = "✅️"
#guard dataEmoji (.error "failed") = "❌️"

/--
error: Invalid definition `rewriteSyntax`, may not access declaration `Lean.TSyntax.replaceM` imported as `meta`; consider adding `import Batteries.Lean.Syntax`
-/
#guard_msgs in
public def rewriteSyntax (s : Lean.TSyntax `term) : Id (Lean.TSyntax `term) :=
  s.replaceM (fun _ => pure none)
