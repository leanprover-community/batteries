import Batteries.Data.List.Perm

open List

#guard findIdxNth (· < 3) [5, 1, 3, 2, 4, 0, 1, 4] 2 == 5
#guard idxOfNth 1 [5, 1, 3, 2, 4, 0, 1, 4] 1 == 6
#guard countPBefore (· < 3) [5, 1, 3, 2, 4, 0, 1, 4] 5 == 2
#guard countBefore 1 [5, 1, 3, 2, 4, 0, 1, 4] 6 == 1
#guard (by decide : [1, 0, 1] <+~ [5, 0, 1, 3, 1]).idxInj 1 = 1
#guard (by decide : [0, 1, 1, 3, 5] ~ [5, 0, 1, 3, 1]).idxBij 2 == 4
