import Batteries.Data.Float

/-! Runtime checks of `twoPow`, `exponent?`, `ldexp`, `mulErr`, `twoSum`, `hypot`, `log1p` and
`expm1`. -/

-- Float
def maxF : Float := .ofBits 0x7FEFFFFFFFFFFFFF
def minSubF : Float := .ofBits 1
def minNormF : Float := .ofBits 0x0010000000000000

#guard Float.twoPow 0 == 1 && Float.twoPow 10 == 1024 && Float.twoPow (-1) == 0.5
#guard Float.twoPow 1023 * 2 == Float.inf && Float.twoPow 1024 == Float.inf
#guard Float.twoPow (-1022) == minNormF && Float.twoPow (-1074) == minSubF
#guard Float.twoPow (-1073) == 2 * minSubF && Float.twoPow (-1075) == 0

#guard Float.exponent? 1 == some 0 && Float.exponent? (-1) == some 0
#guard Float.exponent? 3 == some 1 && Float.exponent? 0.75 == some (-1)
#guard Float.exponent? maxF == some 1023 && Float.exponent? minNormF == some (-1022)
#guard Float.exponent? minSubF == some (-1074) && Float.exponent? (3 * minSubF) == some (-1073)
#guard Float.exponent? (minNormF - minSubF) == some (-1023)
#guard Float.exponent? 0 == none && Float.exponent? (-0) == none
#guard Float.exponent? Float.inf == none && Float.exponent? Float.nan == none
#guard Float.exponent! 1024 == 10

#guard Float.ldexp 1 10 == 1024 && Float.ldexp 3 (-1) == 1.5
#guard Float.ldexp 1 1024 == Float.inf
#guard Float.ldexp minSubF 2097 == Float.twoPow 1023
#guard Float.ldexp maxF (-2098) == minSubF && Float.ldexp 1 (-1074) == minSubF
#guard Float.ldexp 1 (-1075) == 0 && Float.ldexp 1.5 (-1075) == minSubF
-- One rounding, not two: `1 + 2⁻⁵²` scaled into the subnormal range.
#guard Float.ldexp (1 + Float.twoPow (-52)) (-1073) == 2 * minSubF
#guard Float.ldexp (1 + Float.twoPow (-52) * 3) (-1073) == 2 * minSubF
#guard Float.ldexp (-0) 5 == 0 && (Float.ldexp (-0) 5).signBit
#guard (Float.ldexp Float.nan 3).isNaN && Float.ldexp (-Float.inf) (-3000) == -Float.inf
#guard Float.ldexp 1 100000 == Float.inf && Float.ldexp 1 (-100000) == 0

#guard Float.mulErr 3 5 == 0
#guard Float.mulErr (1 + Float.twoPow (-30)) (1 + Float.twoPow (-30)) == Float.twoPow (-60)
#guard (Float.mulErr maxF 2).isFinite == false

#guard Float.twoSum 1 2 == (3, 0)
#guard Float.twoSum 1 (Float.twoPow (-60)) == (1, Float.twoPow (-60))
#guard Float.twoSum (Float.twoPow (-60)) 1 == (1, Float.twoPow (-60))
#guard Float.twoSum 1 (-1 + Float.twoPow (-53)) == (Float.twoPow (-53), 0)

#guard Float.hypot 3 4 == 5 && Float.hypot (-3) 4 == 5 && Float.hypot 0 (-0) == 0
#guard Float.hypot Float.inf Float.nan == Float.inf
#guard Float.hypot Float.nan (-Float.inf) == Float.inf
#guard (Float.hypot Float.nan 1).isNaN
#guard Float.hypot (3 * Float.twoPow 1000) (4 * Float.twoPow 1000) == 5 * Float.twoPow 1000
#guard Float.hypot (3 * minSubF) (4 * minSubF) == 5 * minSubF
#guard Float.hypot maxF maxF == Float.inf && Float.hypot maxF 1 == maxF

#guard Float.log1p 0 == 0 && (Float.log1p (-0)).signBit
#guard Float.log1p (Float.twoPow (-60)) == Float.twoPow (-60)
#guard (Float.ulpDistance? (Float.log1p 1e-10) 9.9999999995e-11).all (· ≤ 1)
#guard Float.log1p (-1) == -Float.inf && Float.log1p Float.inf == Float.inf
#guard (Float.log1p (-2)).isNaN && (Float.log1p (-Float.inf)).isNaN && (Float.log1p Float.nan).isNaN

#guard Float.expm1 0 == 0 && (Float.expm1 (-0)).signBit
#guard Float.expm1 (Float.twoPow (-60)) == Float.twoPow (-60)
#guard (Float.ulpDistance? (Float.expm1 1e-10) 1.00000000005e-10).all (· ≤ 1)
#guard Float.expm1 (-Float.inf) == -1 && Float.expm1 (-1000) == -1
#guard Float.expm1 Float.inf == Float.inf && Float.expm1 1000 == Float.inf
#guard (Float.expm1 Float.nan).isNaN

-- Float32
def maxF32 : Float32 := .ofBits 0x7F7FFFFF
def minSubF32 : Float32 := .ofBits 1
def minNormF32 : Float32 := .ofBits 0x00800000

#guard Float32.twoPow 0 == 1 && Float32.twoPow 10 == 1024 && Float32.twoPow (-1) == 0.5
#guard Float32.twoPow 128 == Float32.inf && Float32.twoPow (-126) == minNormF32
#guard Float32.twoPow (-149) == minSubF32 && Float32.twoPow (-150) == 0

#guard Float32.exponent? 1 == some 0 && Float32.exponent? 3 == some 1
#guard Float32.exponent? maxF32 == some 127 && Float32.exponent? minNormF32 == some (-126)
#guard Float32.exponent? minSubF32 == some (-149)
#guard Float32.exponent? (minNormF32 - minSubF32) == some (-127)
#guard Float32.exponent? 0 == none && Float32.exponent? Float32.inf == none
#guard Float32.exponent! 1024 == 10

#guard Float32.ldexp 1 10 == 1024 && Float32.ldexp 1 128 == Float32.inf
#guard Float32.ldexp minSubF32 276 == Float32.twoPow 127
#guard Float32.ldexp maxF32 (-277) == minSubF32 && Float32.ldexp 1 (-150) == 0
#guard Float32.ldexp (1 + Float32.twoPow (-23)) (-148) == 2 * minSubF32

#guard Float32.mulErr (1 + Float32.twoPow (-12)) (1 + Float32.twoPow (-12)) == Float32.twoPow (-24)
#guard Float32.twoSum 1 (Float32.twoPow (-30)) == (1, Float32.twoPow (-30))

#guard Float32.hypot 3 4 == 5 && Float32.hypot Float32.inf Float32.nan == Float32.inf
#guard Float32.hypot (3 * Float32.twoPow 100) (4 * Float32.twoPow 100) == 5 * Float32.twoPow 100
#guard Float32.hypot (3 * minSubF32) (4 * minSubF32) == 5 * minSubF32
#guard Float32.hypot maxF32 maxF32 == Float32.inf

#guard Float32.log1p (Float32.twoPow (-30)) == Float32.twoPow (-30)
#guard Float32.log1p (-1) == -Float32.inf && (Float32.log1p (-2)).isNaN
#guard Float32.expm1 (Float32.twoPow (-30)) == Float32.twoPow (-30)
#guard Float32.expm1 (-Float32.inf) == -1 && Float32.expm1 Float32.inf == Float32.inf
