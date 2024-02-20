/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace Lean.Parser.Tactic
/-- Extract the arguments from a `simpArgs` syntax as an array of syntaxes -/
def getSimpArgs? : Syntax → Option (Array Syntax)
  | `(simpArgs| [$args,*]) => pure args.getElems
  | _ => none

/-- Extract the arguments from a `dsimpArgs` syntax as an array of syntaxes -/
def getDSimpArgs? : Syntax → Option (Array Syntax)
  | `(dsimpArgs| [$args,*]) => pure args.getElems
  | _                       => none
