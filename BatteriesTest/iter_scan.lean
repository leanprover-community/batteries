import Batteries.Data.Iterators

#guard ([1,2,3].iter.scan (· + ·) 0).toList == [0,1,3,6]
#guard ([1,2,3].iter.toIterM.scan (· + ·) 0).toList.run == [0,1,3,6]
