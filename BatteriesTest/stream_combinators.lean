import Batteries.Data.Stream.Combinators

/- Examples from docstrings -/

open Stream

-- Constant
#guard next? (const 'a') == ('a', const 'a')

-- TakeUpTo
#guard toList (takeUpTo 3 [1,2,3,4,5,6]) == [1,2,3]
#guard toList (takeUpTo 3 [1,2]) == [1,2]

-- Map
#guard toList (map (· ^ 2) [1,2,3,4,5]) == [1,4,9,16,25]

-- Concat
#guard toList (concat [1,2,3] [4,5]) == [1,2,3,4,5]

-- Join
#guard toList (join [[1,2],[3,4,5],[6]]) == [1,2,3,4,5,6]

-- Zip
#guard toList (zip [1,2,3] ['a','b','c','d','e']) == [(1, 'a'), (2, 'b'), (3, 'c')]
