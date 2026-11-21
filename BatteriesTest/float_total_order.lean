import Batteries.Data.Float.TotalOrder
import Std.Data.TreeMap
import Std.Data.HashMap

/-! Runtime checks. -/

def maxF : Float := .ofBits 0x7FEFFFFFFFFFFFFF

#guard Float.totalCmp (-0) 0 == .lt
#guard Float.totalCmp 0 (-0) == .gt
#guard Float.totalCmp (-0) (-0) == .eq
#guard Float.totalCmp Float.nan Float.nan == .eq
#guard Float.totalCmp Float.inf Float.nan == .lt
#guard Float.totalCmp (-Float.nan) Float.inf == .gt
#guard Float.totalCmp (-Float.inf) (-maxF) == .lt
#guard Float.totalCmp (-2) (-1) == .lt
#guard Float.totalCmp 1 2 == .lt
#guard Float.totalCmp maxF Float.inf == .lt
#guard Float.totalCmp (-1) 1 == .lt

#guard Float32.totalCmp (-0) 0 == .lt
#guard Float32.totalCmp Float32.nan Float32.nan == .eq
#guard Float32.totalCmp Float32.inf Float32.nan == .lt
#guard Float32.totalCmp (-2) (-1) == .lt

#guard (TotalFloat.mk Float.nan == TotalFloat.mk Float.nan)
#guard !(TotalFloat.mk 0 == TotalFloat.mk (-0))
#guard hash (TotalFloat.mk Float.nan) == hash (TotalFloat.mk (0 / 0))

#guard
  let m : Std.TreeMap TotalFloat Nat :=
    .ofList <| [(Float.nan, 0), (1, 1), (-0, 2), (0, 3), (-Float.inf, 4)].map
      fun (x, n) => (TotalFloat.mk x, n)
  m.toList.map (·.2) == [4, 2, 3, 1, 0]

#guard
  let m : Std.HashMap TotalFloat Nat :=
    .ofList [(TotalFloat.mk Float.nan, 0), (TotalFloat.mk (0 / 0), 1)]
  m.size == 1 && m.get? (.mk Float.nan) == some 1

/-! Kernel checks. -/

example : Float.totalCmp (-0) 0 = .lt := by decide +kernel
example : Float.totalCmp Float.inf Float.nan = .lt := by decide +kernel
example : Float32.totalCmp (-1) 1 = .lt := by decide +kernel

/-! The order is lawful. -/

example : Std.TransOrd TotalFloat := inferInstance
example : Std.LawfulEqOrd TotalFloat := inferInstance
example : LawfulBEq TotalFloat32 := inferInstance
example : LawfulHashable TotalFloat32 := inferInstance
