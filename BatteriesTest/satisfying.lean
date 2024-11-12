import Batteries.Lean.SatisfiesM
import Batteries.Data.Array.Monadic

open Lean Meta Array Elab Term Tactic Command

example (xs : Array Expr) : MetaM { ts : Array Expr // ts.size = xs.size } := do
  let r ← satisfying (xs.size_mapM inferType)
  return r
