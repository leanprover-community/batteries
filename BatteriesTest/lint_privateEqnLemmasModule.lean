module

meta import Batteries.Linter
import BatteriesTest.Internal.PrivateEqnLemmasDefs

open Lean

/-!
Linting from a `module` file that imports the definitions without `import all`: here the body of
`hiddenDouble` is not visible, so it is not known to be a definition, and its private equation
lemmas are conservatively still linted. Lint drivers such as `runLinter` import every module's
private data, where `BatteriesTest/lint_privateEqnLemmas.lean` shows them recognized.
-/

/--
info: _private.BatteriesTest.Internal.PrivateEqnLemmasDefs.0.hiddenDouble.eq_1: false
-/
#guard_msgs in
run_meta do
  let n := mkPrivateNameCore `BatteriesTest.Internal.PrivateEqnLemmasDefs `hiddenDouble.eq_1
  logInfo m!"{n}: {(← getEnv).isAutoDecl n}"
