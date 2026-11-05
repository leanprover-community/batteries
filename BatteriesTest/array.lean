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

-- Subarray right scans use the upper bound as the initial index.
#guard (#[1, 2, 3].toSubarray).scanr (· + ·) 0 == #[6, 5, 3, 0]

-- Ignore elements outside the slice and preserve right-to-left accumulation.
#guard (#[100, 1, 2, 3, 200].toSubarray 1 4).scanr (fun x acc => 10 * acc + x) 0 ==
  #[321, 32, 3, 0]

#guard (#[1, 2, 3].toSubarray 2 2).scanr (· + ·) 7 == #[7]

-- Monadic scans must visit each selected element once, in reverse order.
#guard Id.run (((#[100, 1, 2, 3, 200].toSubarray 1 4).scanrM (m := StateM (Array Nat))
  (fun x acc => do
    modify (fun seen => seen.push x)
    pure (10 * acc + x)) 0).run #[]) == (#[321, 32, 3, 0], #[3, 2, 1])

#guard Id.run (((#[1, 2, 3].toSubarray 2 2).scanrM (m := StateM (Array Nat))
  (fun x acc => do
    modify (fun seen => seen.push x)
    pure (x + acc)) 7).run #[]) == (#[7], #[])
