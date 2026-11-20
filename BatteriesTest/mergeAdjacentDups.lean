import Batteries.Data.Array.Merge

-- Combining a run can change its equality key. Runs are determined by inputs.
#guard (#[1, 1, 1, 2, 2, 3] : Array Nat).mergeAdjacentDups (· + ·) == #[3, 4, 3]
#guard (#[1, 1, 2] : Array Nat).mergeAdjacentDups (· + ·) == #[2, 2]
#guard (#[1, 1, 1] : Array Nat).mergeAdjacentDups (· + ·) == #[3]
#guard (#[] : Array Nat).mergeAdjacentDups (· + ·) == #[]
#guard (#[7] : Array Nat).mergeAdjacentDups (· + ·) == #[7]
#guard (#[1, 1, 2, 2, 1] : Array Nat).dedupSorted == #[1, 2, 1]
