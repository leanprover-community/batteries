/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean.PrettyPrinter

open Lean PrettyPrinter Delaborator SubExpr

/--
This is similar to `withAppFnArgs` but it handles construction of an "over-application".
For example, suppose we want to implement a delaborator for applications of `f : Foo A → A`
like `f x` as `F[x]`, but because `A` is a type variable we might encounter a term of the form
`@f (A → B) x y` which has an additional argument `y`.

Most of the built in delaborators will deliberately fail on such an example, resulting in
delaborated syntax `f x y`, but this combinator can be used if we want to display `F[x] y`
instead.

* `arity`: the expected number of arguments to `f`.
  The combinator will fail if fewer than this number of arguments are passed
* `x`: constructs data corresponding to the main application (`f x` in the example)
-/
def Lean.PrettyPrinter.Delaborator.withOverApp (arity : Nat) (x : Delab) : Delab := do
  let n := (← getExpr).getAppNumArgs
  guard (n ≥ arity)
  let kinds ← getParamKinds
  let rec
  /-- Inner loop of `withOverApp`. -/
  loop : Nat → DelabM (Term × Array Term)
  | 0 => return (← x, #[])
  | n+1 => do
    let mut (fnStx, args) ← withAppFn (loop n)
    if kinds.get? (n + arity) |>.all (·.bInfo.isExplicit) then
      args := args.push (← withAppArg delab)
    pure (fnStx, args)
  let (fnStx, argStxs) ← loop (n - arity)
  return Syntax.mkApp fnStx argStxs

/-- Pretty print a const expression using `delabConst` and generate terminfo.
This function avoids inserting `@` if the constant is for a function whose first
argument is implicit, which is what the default `toMessageData` for `Expr` does.
Panics if `e` is not a constant. -/
def Lean.ppConst (e : Expr) : MessageData :=
  if e.isConst then
    .ofPPFormat {
      pp := fun
        | some ctx => ctx.runMetaM <| withOptions (pp.tagAppFns.set · true) <|
          -- The pp.tagAppFns option causes the `delabConst` function to annotate
          -- the constant with terminfo, which is necessary for seeing the type on mouse hover.
          PrettyPrinter.ppExprWithInfos (delab := delabConst) e
        | none => return f!"{e}"
    }
  else
    panic! "not a constant"
