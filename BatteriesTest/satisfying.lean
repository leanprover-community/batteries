import Batteries.Lean.SatisfiesM
import Batteries.Data.Array.Monadic

open Lean Meta Array Elab Term Tactic Command

-- Note: as of nightly-2025-10-23, after https://github.com/leanprover/lean4/pull/10625
-- the `MonadSatisfying` instances for the core monad stack need to be re-implemented.
-- See `Batteries.Lean.LawfulMonad` first.

-- example (xs : Array Expr) : MetaM { ts : Array Expr // ts.size = xs.size } := do
--   let r ← satisfying (xs.size_mapM inferType)
--   return r
