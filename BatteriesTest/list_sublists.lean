import Batteries.Data.List.Basic

-- this times out with `sublistsFast`
set_option maxRecDepth 562 in
example : [1, 2, 3].sublists.sublists.length = 256 := rfl
