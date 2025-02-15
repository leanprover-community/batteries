import Batteries.Data.List.Basic

-- this times out with `sublistsFast`
set_option maxRecDepth 562 in
example : [1, 2, 3].sublists.sublists.length = 256 := rfl

-- TODO(batteries#307): until we have the `csimp` lemma in batteries,
-- this is a sanity check that these two are equal.
example : ([] : List Nat).sublists = [].sublistsFast := rfl
example : [1, 2, 3].sublists = [1, 2, 3].sublistsFast := rfl
