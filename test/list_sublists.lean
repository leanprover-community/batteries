import Std.Data.List.Basic

-- this times out with `sublistsFast`
set_option maxRecDepth 561 in
example : [1, 2, 3].sublists.sublists.length = 256 := rfl

-- TODO(std4#307): until we have the `csimp` lemma in std, this is a sanity check that these two
-- are equal.
example : ([] : List Nat).sublists = [].sublistsFast := rfl
example : [1, 2, 3].sublists = [1, 2, 3].sublistsFast := rfl
