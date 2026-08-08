import Batteries.Data.Nat.Digits

open Nat

/-! # Docstring Examples -/

/-! ## `ofDigitsLE` -/
#guard ofDigitsLE (base := 10) [1,2,3] == 321
#guard ofDigitsLE (base := 2) [0,1,0,0] == 2
#guard ofDigitsLE (base := 0) [] == 0
#guard ofDigitsLE (base := 1) [] == 0
#guard ofDigitsLE (base := 12345) [] == 0
#guard ofDigitsLE (base := 1) [0,0,0,0,0] == 0

/-! ## `toDigitsUpToLE` -/
#guard toDigitsUpToLE 123 10 3 == ([3,2,1] : List (Fin 10))
#guard toDigitsUpToLE 2 2 2 == ([0,1] : List (Fin 2))
#guard toDigitsUpToLE 2 2 4 == ([0,1,0,0] : List (Fin 2))
#guard toDigitsUpToLE 12345 1 5 == ([0,0,0,0,0] : List (Fin 1))

/-! ## `toDigitsLE` -/
#guard toDigitsLE 123 10 = ([3,2,1] : List (Fin 10))
#guard toDigitsLE 2 2 = ([0,1] : List (Fin 2))
#guard toDigitsLE 0 12345 = ([] : List (Fin 12345))

/-! ## `ofDigitsBE` -/

#guard ofDigitsBE (base := 10) [2,3,4] == 234
#guard ofDigitsBE (base := 2) [0,1,0,0] = 4
#guard ofDigitsBE (base := 0) [] = 0
#guard ofDigitsBE (base := 1) [] = 0
#guard ofDigitsBE (base := 12345) [] = 0
#guard ofDigitsBE (base := 1) [0,0,0,0,0] = 0

/-! ## `toDigitsUpToBE` -/
#guard toDigitsUpToBE 123 10 3 == ([1,2,3] : List (Fin 10))
#guard toDigitsUpToBE 2 2 2 == ([1,0] : List (Fin 2))
#guard toDigitsUpToBE 4 2 4 == ([0,1,0,0] : List (Fin 2))
#guard toDigitsUpToBE 12345 1 5 == ([0,0,0,0,0] : List (Fin 1))

/-! ## `toDigitsBE` -/

#guard toDigitsBE 123 10 == ([1,2,3] : List (Fin 10))
#guard toDigitsBE 2 2 == ([1,0] : List (Fin 2))
#guard toDigitsBE 0 12345 == ([] : List (Fin 12345))
