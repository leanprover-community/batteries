import Batteries.Data.Nat.Digits

open Nat

/-! ## `ofFinDigits` -/

#guard ofFinDigits (base := 10) [2,3,4] == 234
#guard ofFinDigits (base := 2) [0,1,0,0] == 4
#guard ofFinDigits (base := 0) [] == 0
#guard ofFinDigits (base := 1) [] == 0
#guard ofFinDigits (base := 12345) [] == 0
#guard ofFinDigits (base := 1) [0,0,0,0,0] == 0

/-! ## `ofFinDigitsRev` -/

#guard ofFinDigitsRev (base := 10) [4,3,2] == 234
#guard ofFinDigitsRev (base := 2) [0,0,1,0] == 4
#guard ofFinDigitsRev (base := 0) [] == 0
#guard ofFinDigitsRev (base := 1) [] == 0
#guard ofFinDigitsRev (base := 12345) [] == 0
#guard ofFinDigitsRev (base := 1) [0,0,0,0,0] == 0

/-! ## `toFinDigitsFixed` -/

#guard toFinDigitsFixed 123 10 3 == ([1,2,3] : List (Fin 10))
#guard toFinDigitsFixed 123 10 2 == ([2,3] : List (Fin 10))
#guard toFinDigitsFixed 4 2 4 == ([0,1,0,0] : List (Fin 2))
#guard toFinDigitsFixed 12345 1 5 == ([0,0,0,0,0] : List (Fin 1))

/-! ## `toFinDigitsFixedRev` -/

#guard toFinDigitsFixedRev 123 10 3 == ([3,2,1] : List (Fin 10))
#guard toFinDigitsFixedRev 123 10 2 == ([3,2] : List (Fin 10))
#guard toFinDigitsFixedRev 4 2 4 == ([0,0,1,0] : List (Fin 2))
#guard toFinDigitsFixedRev 12345 1 5 == ([0,0,0,0,0] : List (Fin 1))

/-! ## `toFinDigits` -/

#guard toFinDigits 123 10 == ([1,2,3] : List (Fin 10))
#guard toFinDigits 4 2 == ([1,0,0] : List (Fin 2))
#guard toFinDigits 0 12345 == ([] : List (Fin 12345))
#guard toFinDigits 5 1 == ([] : List (Fin 1))
#guard toFinDigits 0 0 == ([] : List (Fin 0))

/-! ## `toFinDigitsRev` -/

#guard toFinDigitsRev 123 10 == ([3,2,1] : List (Fin 10))
#guard toFinDigitsRev 4 2 == ([0,0,1] : List (Fin 2))
#guard toFinDigitsRev 0 12345 == ([] : List (Fin 12345))
#guard toFinDigitsRev 5 1 == ([] : List (Fin 1))
#guard toFinDigitsRev 0 0 == ([] : List (Fin 0))

/-! ## Large inputs -/

#guard (toFinDigits (10 ^ 5000) 10).length == 5001
#guard ofFinDigits (toFinDigits (3 ^ 20000) 7) == 3 ^ 20000
#guard ofFinDigits (toFinDigitsFixed (3 ^ 20000) 10 3000) == 3 ^ 20000 % 10 ^ 3000
#guard toFinDigits (2 ^ 3000 - 1) 2 == List.replicate 3000 1
#guard (toFinDigits (7 ^ 3000) 10).map Fin.val == (Nat.toDigits 10 (7 ^ 3000)).map (·.toNat - 48)
