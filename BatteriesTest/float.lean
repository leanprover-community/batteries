import Batteries.Lean.Float

#guard 0.0.toRatParts == some (0, -53)
#guard (2^(-1000):Float).toRatParts == some (4503599627370496, -1052)
#guard (2^(-30):Float).toRatParts == some (4503599627370496, -82)
#guard 0.1.toRatParts == some (7205759403792794, -56)
#guard 0.5.toRatParts == some (4503599627370496, -53)
#guard 5.0.toRatParts == some (5629499534213120, -50)
#guard (-5.0).toRatParts == some (-5629499534213120, -50)
#guard 5.5.toRatParts == some (6192449487634432, -50)
#guard 500000000000000.5.toRatParts == some (8000000000000008, -4)
#guard 5000000000000000.5.toRatParts == some (5000000000000000, 0)
#guard 1e1000.toRatParts == none
#guard (-1e1000).toRatParts == none
#guard (-0/0:Float).toRatParts == none

#guard 0.0.toRatParts' == some (0, 0)
#guard (2^(-1000):Float).toRatParts' == some (1, -1000)
#guard (2^(-30):Float).toRatParts' == some (1, -30)
#guard 0.1.toRatParts' == some (3602879701896397, -55)
#guard 0.5.toRatParts' == some (1, -1)
#guard 5.0.toRatParts' == some (5, 0)
#guard (-5.0).toRatParts' == some (-5, 0)
#guard 5.5.toRatParts' == some (11, -1)
#guard 500000000000000.5.toRatParts' == some (1000000000000001, -1)
#guard 5000000000000000.5.toRatParts' == some (152587890625, 15)
#guard 1e1000.toRatParts' == none
#guard (-1e1000).toRatParts' == none
#guard (-0/0:Float).toRatParts' == none

#guard 0.0.toStringFull == "0"
#guard (2^(-1000):Float).toStringFull.length == 1002
#guard (2^(-30):Float).toStringFull == "0.000000000931322574615478515625"
#guard 0.1.toStringFull == "0.1000000000000000055511151231257827021181583404541015625"
#guard 0.5.toStringFull == "0.5"
#guard 5.0.toStringFull == "5"
#guard (-5.0).toStringFull == "-5"
#guard 5.5.toStringFull == "5.5"
#guard 500000000000000.5.toStringFull == "500000000000000.5"
#guard 5000000000000000.5.toStringFull == "5000000000000000"
#guard 1e1000.toStringFull == "inf"
#guard (-1e1000).toStringFull == "-inf"
#guard (-0/0:Float).toStringFull == "NaN"

#guard Nat.divFloat 1 0 == Float.inf
#guard Nat.divFloat 50 0 == Float.inf
#guard (Nat.divFloat 0 0).isNaN
#guard Nat.divFloat 1 3 == (1 / 3 : Float)
#guard Nat.divFloat 1 6 == (1 / 6 : Float)
#guard Nat.divFloat 2 3 == (2 / 3 : Float)
#guard Nat.divFloat 100 17 == (100 / 17 : Float)
#guard Nat.divFloat 5000000000000000 1 == (5000000000000000 : Float)
#guard [0,0,0,1,1,1,2,2,2,2,2,3,3,3,4,4,4].enum.all fun p =>
  Nat.divFloat (5000000000000000*4+p.1) 4 == (5000000000000000+p.2).toFloat
#guard Nat.divFloat ((2^53-1)*(2^(1024-53))) 1 == ((2^53-1)*(2^(1024-53)))
#guard Nat.divFloat (((2^53-1)*4+1)*(2^(1024-53))) 4 == ((2^53-1)*(2^(1024-53)))
#guard Nat.divFloat (((2^53-1)*4+2)*(2^(1024-53))) 4 == Float.inf
#guard Nat.divFloat (((2^53-1)*4+3)*(2^(1024-53))) 4 == Float.inf
#guard Nat.divFloat (((2^53-1)*4+4)*(2^(1024-53))) 4 == Float.inf

#guard Int.divFloat 1 3 == (1 / 3 : Float)
#guard Int.divFloat (-1) 3 == (-1 / 3 : Float)
#guard Int.divFloat 1 (-3) == (1 / -3 : Float)
#guard Int.divFloat (-1) (-3) == (-1 / -3 : Float)
#guard Int.divFloat (-1) 0 == -Float.inf
#guard (Int.divFloat 0 0).isNaN
#guard (Int.divFloat 0 1).toString == "0.000000"
#guard (Int.divFloat 0 (-1)).toString == "-0.000000"
