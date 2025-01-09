import Batteries.Data.List.ArrayMap

open List

/-- info: #[3, 4, 5, 6] -/
#guard_msgs in
#eval List.toArrayMap [0, 1, 2, 3] (fun n => n + 3)

/-- info: #[7, 9, 15, 25] -/
#guard_msgs in
#eval toArrayMap [0, 1, 2, 3] (fun n => 2 * n ^ 2 + 7)
