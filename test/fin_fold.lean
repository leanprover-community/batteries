import Std.Data.Fin.Basic
import Std.Tactic.GuardExpr

#guard Fin.foldl 4 (fun x i => List.cons i x) [] == [3,2,1,0]
#guard Fin.foldr 4 (fun i x => List.cons i x) [] == [0,1,2,3]
