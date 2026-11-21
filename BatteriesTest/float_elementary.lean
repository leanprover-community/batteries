import Batteries.Data.Float.Elementary

/-! Runtime checks of `hypot`, `log1p` and `expm1`. -/

-- Float
def maxF : Float := .ofBits 0x7FEFFFFFFFFFFFFF
def minSubF : Float := .ofBits 1

#guard Float.hypot 3 4 == 5 && Float.hypot (-3) 4 == 5 && Float.hypot 0 (-0) == 0
#guard Float.hypot Float.inf Float.nan == Float.inf
#guard Float.hypot Float.nan (-Float.inf) == Float.inf
#guard (Float.hypot Float.nan 1).isNaN
#guard Float.hypot (3 * Float.twoPow 1000) (4 * Float.twoPow 1000) == 5 * Float.twoPow 1000
#guard Float.hypot (3 * minSubF) (4 * minSubF) == 5 * minSubF
#guard Float.hypot maxF maxF == Float.inf && Float.hypot maxF 1 == maxF
#guard Float.log1p 0 == 0 && (Float.log1p (-0)).toBits == (-0 : Float).toBits
#guard Float.log1p (Float.twoPow (-60)) == Float.twoPow (-60)
#guard (Float.log1p 1e-10 - 9.9999999995e-11).abs ≤ 2e-26
#guard Float.log1p (-1) == -Float.inf && Float.log1p Float.inf == Float.inf
#guard (Float.log1p (-2)).isNaN && (Float.log1p (-Float.inf)).isNaN && (Float.log1p Float.nan).isNaN
#guard Float.expm1 0 == 0 && (Float.expm1 (-0)).toBits == (-0 : Float).toBits
#guard Float.expm1 (Float.twoPow (-60)) == Float.twoPow (-60)
#guard (Float.expm1 1e-10 - 1.00000000005e-10).abs ≤ 2e-26
#guard Float.expm1 (-Float.inf) == -1 && Float.expm1 (-1000) == -1
#guard Float.expm1 Float.inf == Float.inf && Float.expm1 1000 == Float.inf
#guard (Float.expm1 Float.nan).isNaN

-- Float32
def maxF32 : Float32 := .ofBits 0x7F7FFFFF
def minSubF32 : Float32 := .ofBits 1

#guard Float32.hypot 3 4 == 5 && Float32.hypot Float32.inf Float32.nan == Float32.inf
#guard Float32.hypot (3 * Float32.twoPow 100) (4 * Float32.twoPow 100) == 5 * Float32.twoPow 100
#guard Float32.hypot (3 * minSubF32) (4 * minSubF32) == 5 * minSubF32
#guard Float32.hypot maxF32 maxF32 == Float32.inf
#guard Float32.log1p (Float32.twoPow (-30)) == Float32.twoPow (-30)
#guard Float32.log1p (-1) == -Float32.inf && (Float32.log1p (-2)).isNaN
#guard Float32.expm1 (Float32.twoPow (-30)) == Float32.twoPow (-30)
#guard Float32.expm1 (-Float32.inf) == -1 && Float32.expm1 Float32.inf == Float32.inf
