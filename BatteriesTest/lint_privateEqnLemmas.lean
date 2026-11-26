import Batteries.Linter
import BatteriesTest.Internal.PrivateEqnLemmasDefs
import BatteriesTest.Internal.PrivateEqnLemmasDownstream
import BatteriesTest.Internal.PrivateEqnLemmasPlain
import BatteriesTest.Internal.PrivateEqnLemmasChain

open Lean

/-!
The equation lemmas of a definition whose body is not exposed are private to the module that
generated them. They are automatically generated in downstream modules too, while hand-written
private declarations, even one with the name of an equation lemma, are not.

Two kinds of hand-written private theorems with equation lemma names are possible, and are still
linted: `secretTriple.eq_7`, for the private `secretTriple`, in a module that imports it with
`import all`, and `hiddenDouble.eq_7` in a module that imports `hiddenDouble` without
`import all`. In both, core does not reserve these names. So the equation lemmas of
`secretTriple` generated in another module are linted too. Through a chain of `import all`s the
body of `hiddenQuad` is visible, the names are reserved, and `hiddenQuad.eq_1` generated there is
automatically generated.
-/

/-- Prints whether each declaration about the definitions of the test modules is auto-generated. -/
def showAutoDecls : CoreM Unit := do
  let env ← getEnv
  let names := env.constants.toList.map (·.1) |>.filter fun n =>
    ["hiddenDouble", "shownDouble", "hiddenTriple", "hiddenLater", "secretTriple", "hiddenQuad"].any
      ((privateToUserName n).toString.startsWith ·)
  let names := names.toArray.qsort fun a b =>
    (privateToUserName a).toString < (privateToUserName b).toString
  for n in names do
    logInfo m!"{n}: {env.isAutoDecl n}"

/--
info: hiddenDouble: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.hiddenDouble.eq_1: true
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasPlain.0.hiddenDouble.eq_7: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.hiddenDouble.eq_def: true
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.hiddenDouble.eq_unfold: true
---
info: hiddenDouble_eq: false
---
info: hiddenDouble_eq_fun: false
---
info: hiddenDouble_eq_shownDouble: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.hiddenDouble_zero: false
---
info: hiddenLater: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.hiddenLater.eq_1: false
---
info: hiddenQuad: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasChain.0.hiddenQuad.eq_1: true
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasChain.0.hiddenQuad_eq: false
---
info: hiddenTriple: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDownstream.0.hiddenTriple.eq_1: true
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDownstream.0.hiddenTriple_eq: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.secretTriple: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDownstream.0.secretTriple.eq_1: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDownstream.0.secretTriple.eq_7: false
---
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDownstream.0.secretTriple_eq: false
---
info: shownDouble: false
---
info: shownDouble.eq_1: true
-/
#guard_msgs in
run_meta showAutoDecls

/-- info: `synTaut` on the hand-written `hiddenDouble.eq_7`: LHS equals RHS syntactically -/
#guard_msgs in
run_meta do
  let n := mkPrivateNameCore `BatteriesTest.Internal.PrivateEqnLemmasPlain `hiddenDouble.eq_7
  let some msg ← Batteries.Linter.synTaut.test n | logInfo "no report"
  logInfo m!"`synTaut` on the hand-written `hiddenDouble.eq_7`: {msg}"
