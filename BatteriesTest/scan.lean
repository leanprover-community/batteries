import Batteries.Data.List

example : [1,2,3].scanl (· - ·) 10 = [10,9,7,4] := by rfl
example : [].scanl (· + ·) 0 = [0] := by rfl
example : [(3 : Int), 2, 1].scanr (· - ·) 10 = [-8, 11, -9, 10] := by rfl
example : [].scanr (· + ·) 0 = [0] := by rfl
