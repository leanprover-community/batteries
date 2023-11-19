import Std.Tactic.Lint
import Std.Tactic.GuardMsgs

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

def SemiconjBy [Mul M] (a x y : M) : Prop :=
  a * x = y * a

structure MulOpposite (α : Type u) : Type u where
  op :: unop : α

postfix:max "ᵐᵒᵖ" => MulOpposite

namespace MulOpposite

instance [Mul α] : Mul αᵐᵒᵖ where mul x y := op (unop y * unop x)

@[simp]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y := by
  cases x; cases y; simp

#guard_msgs (drop warning) in
@[simp]
theorem semiconj_by_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := sorry

#eval do guard (← simpComm.test ``unop_inj).isNone

#eval do guard (← simpComm.test ``semiconj_by_unop).isNone

end MulOpposite
