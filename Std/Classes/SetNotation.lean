/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/--
`{ a, b, c }` is a set with elements `a`, `b`, and `c`.

This notation works for all types that implement `Insert` and `Singleton`.
-/
syntax "{" term,+ "}" : term

macro_rules
  | `({$x:term}) => `(singleton $x)
  | `({$x:term, $xs:term,*}) => `(insert $x {$xs:term,*})

/-- Unexpander for the `{ x }` notation. -/
@[app_unexpander singleton]
def singletonUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `({ $a:term })
  | _ => throw ()

/-- Unexpander for the `{ x, y, ... }` notation. -/
@[app_unexpander insert]
def insertUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a { $ts:term,* }) => `({$a:term, $ts,*})
  | _ => throw ()
