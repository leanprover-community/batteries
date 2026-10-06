import Batteries.Data.List.Matcher

#guard ([] : List Nat).findInfix? [] == some (0, 0)
#guard [1, 2, 3].findInfix? [] == some (0, 0)
#guard ([] : List Nat).findAllInfix [] == #[(0, 0)]
#guard [1, 2, 3].findAllInfix [] == #[(0, 0), (1, 1), (2, 2), (3, 3)]
#guard ([] : List Nat).containsInfix []
#guard ([] : List Nat).findInfix? [1] == none
#guard [1, 2, 1].findAllInfix [1] == #[(0, 1), (2, 3)]
