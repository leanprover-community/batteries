import Batteries.Tactic.Lint

/-!
This test file runs the environment linters set up in Batteries on the core Lean4 repository.

Everything is commented out as it is too slow to run in regular Batteries CI
(and in any case there are many failures still),
but it is useful to run locally to see what the linters would catch.
-/

-- We can't apply `nolint` attributes to imported declarations,
-- but if we move the environment linters up to Lean,
-- these nolints should be installed there.
-- (And in the meantime you can "manually" ignore them!)
-- attribute [nolint dupNamespace] Lean.Elab.Tactic.Tactic
-- attribute [nolint dupNamespace] Lean.Parser.Parser Lean.Parser.Parser.rec Lean.Parser.Parser.mk
--   Lean.Parser.Parser.info Lean.Parser.Parser.fn

/-! Failing lints that need work. -/

-- #lint only explicitVarsOfIff in all -- Found 109 errors

-- Many fixed in https://github.com/leanprover/lean4/pull/4620
-- and should be checked again.
-- #lint only simpNF in all -- Found 34 errors

/-! Lints that fail, but that we're not intending to do anything about. -/

-- Mostly fixed in https://github.com/leanprover/lean4/pull/4621
-- There are many false positives here.
-- To run this properly we would need to ignore all declarations with `@[extern]`.
-- #lint only unusedArguments in all -- Found 89 errors

-- After https://github.com/leanprover/lean4/pull/4616, these are all intentional and have
-- `nolint` attributes above.
-- #lint only dupNamespace in all -- Found 6 errors

-- After https://github.com/leanprover/lean4/pull/4619 all of these should be caused by `abbrev`.
-- Unless we decide to upstream something like `alias`, we're not planning on fixing these.
-- #lint only defLemma in all -- Found 31 errors

/-! Lints that have succeeded in the past, and hopefully still do! -/

-- #lint only impossibleInstance  in all -- Found 0 errors
-- #lint only simpVarHead in all -- Found 0 error
-- #lint only unusedHavesSuffices in all  -- Found 0 errors
-- #lint only checkUnivs in all -- Found 0 errors
