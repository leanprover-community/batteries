module
public import Batteries

/-!
Tests for the `#do` command
-/

/-!
Basic test
-/

#do let x := 3

/-- info: 3 -/
#guard_msgs in #do IO.println x

/-!
`let` declarations actually stay `let` declarations
-/

/-- info: 4 -/
#guard_msgs in #do
  have : x = 3 := rfl
  IO.println #[1, 2, 3, 4][x]

/-!
You can use any do elements, most importantly, monadic computations
-/

open Lean Meta

#do
  let cinfo ← getConstInfo `id
  let value := cinfo.value!

/-- info: fun {α} a => a -/
#guard_msgs in #do logInfo m!"{value}"

/-!
Mutable variables also work
-/

#do let mut x := x
#do x := x + 2

/-- info: 5 -/
#guard_msgs in #do IO.println x

/-- error: mutable variable `x` cannot be shadowed -/
#guard_msgs in #do let x := 5

/-!
`#do_meta` lets you run computation in `MetaM` instead
-/

#do_meta let (vars, bis, body) ← lambdaMetaTelescope value

/-- info: [Sort u, ?m.1], #[Lean.BinderInfo.implicit, Lean.BinderInfo.default], ?m.2 -/
#guard_msgs in #do_meta logInfo m!"{← vars.mapM inferType}, {repr bis}, {body}"

/-!
If you use `return`, variables will not be persisted
-/

set_option linter.unusedVariables false in
#do let uncaptured := 5; return

/-- error: Unknown identifier `uncaptured` -/
#guard_msgs in #do IO.println uncaptured

/-!
... but only if it's in a branch that's also executed
-/

set_option linter.unusedVariables false in
#do
  if false then return
  let y := 5

/-- info: 5 -/
#guard_msgs in #do IO.println y

/-!
`#do` will refuse to evaluate in the presence of `sorry`
-/

/--
error: Aborting evaluation since the expression depends on the 'sorry' axiom,
which can lead to runtime instability and crashes.
-/
#guard_msgs in #do sorry

/-!
After `#clear_do`, all previously existing variables are removed.
-/

#clear_do

/-- error: Unknown identifier `x` -/
#guard_msgs in #do IO.println x
