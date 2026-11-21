import Batteries.Data.Float.Scale

/-! Runtime checks of `twoPow`, `exponent?` and `ldexp`. -/

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
#guard Float.ldexp (-0) 5 == 0 && (Float.ldexp (-0) 5).toBits == (-0 : Float).toBits
#guard (Float.ldexp Float.nan 3).isNaN && Float.ldexp (-Float.inf) (-3000) == -Float.inf
#guard Float.ldexp 1 100000 == Float.inf && Float.ldexp 1 (-100000) == 0

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
