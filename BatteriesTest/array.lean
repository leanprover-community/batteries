import Batteries.Data.Array

section
variable {α : Type _}
variable [Inhabited α]
variable (a : Array α)
variable (i j : Nat)
variable (v d : α)
variable (g : i < (a.set! i v).size)
variable (j_lt : j < (a.set! i v).size)

#check_simp (a.set! i v)[i] ~> v
#check_simp (a.set! i v)[i]! ~> (a.setIfInBounds i v)[i]!
#check_simp (a.set! i v).getD i d ~> if i < a.size then v else d
#check_simp (a.set! i v)[i] ~> v

-- Checks with different index values.
#check_simp (a.set! i v)[j]'j_lt  ~> (a.setIfInBounds i v)[j]'_
#check_simp (a.setIfInBounds i v)[j]'j_lt !~>

-- This doesn't work currently.
-- It will be address in the comprehensive overhaul of array lemmas.
-- #check_simp (a.set! i v)[i]? ~> .some v

end
