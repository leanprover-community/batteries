import Std.Tactic.Lint
open Std.Tactic.Lint
set_option linter.missingDocs false

def f : Nat := 0
def g : Nat := 0
def h : Nat := 0
@[simp] theorem fg : f = g := rfl
@[simp] theorem fh : f = h := rfl
#eval do guard (← [``fg, ``fh].anyM fun n => return (← simpNF.test n).isSome)

@[simp] theorem and_comm : a ∧ b ↔ b ∧ a := And.comm
#eval do guard (← simpComm.test ``and_comm).isSome

@[simp] theorem Prod.mk_fst : (a, b).1 = id a := rfl
#eval do guard (← simpVarHead.test ``Prod.mk_fst).isSome
