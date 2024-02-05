import Std.Util.CheckTactic
import Std.Data.Array

section
variable {α : Type _}
variable [Inhabited α]
variable (a : Array α)
variable (i : Nat)
variable (v d : α)

variable (g : i < (a.set! i v).size)
variable (h : i < a.size)

set_option pp.notation false

#check_simp (a.set! i v).get ⟨i, g⟩ ~> v
#check_simp (a.set! i v).get! i ~> if i < a.size then v else default
#check_simp (a.set! i v).getD i d ~> if i < a.size then v else d
#check_simp (a.set! i v)[i] ~> v

-- This doesn't work currently.
-- It will be address in the comprehensive overhaul of array lemmas.
-- #check_simp (a.set! i v)[i]? ~> .some v

end
