import Batteries.Data.Float.Bits

/-! Runtime checks (compiled `toBits`/`ofBits`). -/

-- Float
def maxF : Float := .ofBits 0x7FEFFFFFFFFFFFFF
def minSubF : Float := .ofBits 1
def minNormF : Float := .ofBits 0x0010000000000000

#guard Float.nan.classify == .nan
#guard Float.inf.classify == .infinite
#guard (-Float.inf).classify == .infinite
#guard (0 : Float).classify == .zero
#guard (-0 : Float).classify == .zero
#guard minSubF.classify == .subnormal
#guard minNormF.classify == .normal
#guard (1 : Float).isNormal && !(1 : Float).isSubnormal
#guard minSubF.isSubnormal && !minSubF.isNormal

#guard !(0 : Float).signBit && (-0 : Float).signBit && (-1 : Float).signBit
#guard !Float.nan.signBit && !(-Float.nan).signBit
#guard (Float.copySign 2 (-0)).toBits == (-2 : Float).toBits
#guard (Float.copySign (-2) 1).toBits == (2 : Float).toBits
#guard (Float.copySign 0 (-1)).toBits == (-0 : Float).toBits
#guard (Float.copySign Float.inf (-3)) == -Float.inf
#guard (Float.copySign Float.nan 1).isNaN
#guard (Float.copySign (-1) Float.nan) == 1

#guard Float.nextUp 1 == 1 + 2 ^ (-52 : Float)
#guard Float.nextDown 1 == 1 - 2 ^ (-53 : Float)
#guard Float.nextUp 0 == minSubF
#guard Float.nextUp (-0) == minSubF
#guard (Float.nextUp (-minSubF)).toBits == (-0 : Float).toBits
#guard Float.nextDown 0 == -minSubF
#guard Float.nextUp maxF == Float.inf
#guard Float.nextUp Float.inf == Float.inf
#guard Float.nextUp (-Float.inf) == -maxF
#guard Float.nextDown (-Float.inf) == -Float.inf
#guard Float.nextDown Float.inf == maxF
#guard (Float.nextUp Float.nan).isNaN
#guard Float.nextUp (Float.nextDown 3.5) == 3.5

#guard Float.ulp 1 == 2 ^ (-52 : Float)
#guard Float.ulp (-1) == 2 ^ (-52 : Float)
#guard Float.ulp 0 == minSubF
#guard Float.ulp minNormF == minSubF
#guard Float.ulp maxF == 2 ^ (971 : Float)
#guard (Float.ulp Float.inf).isNaN
#guard (Float.ulp Float.nan).isNaN

#guard Float.ulpDistance? 1 (Float.nextUp 1) == some 1
#guard Float.ulpDistance? 0 (-0) == some 0
#guard Float.ulpDistance? (-minSubF) minSubF == some 2
#guard Float.ulpDistance? maxF Float.inf == some 1
#guard Float.ulpDistance? 1 (-1) == some (2 * 0x3FF0000000000000)
#guard Float.ulpDistance? 1 Float.nan == none

-- Float32
def maxF32 : Float32 := .ofBits 0x7F7FFFFF
def minSubF32 : Float32 := .ofBits 1
def minNormF32 : Float32 := .ofBits 0x00800000

#guard Float32.nan.classify == .nan
#guard (-Float32.inf).classify == .infinite
#guard (-0 : Float32).classify == .zero
#guard minSubF32.classify == .subnormal
#guard minNormF32.classify == .normal
#guard (-0 : Float32).signBit && !Float32.nan.signBit
#guard (Float32.copySign 2 (-0)).toBits == (-2 : Float32).toBits
#guard Float32.nextUp 1 == 1 + 2 ^ (-23 : Float32)
#guard Float32.nextDown 1 == 1 - 2 ^ (-24 : Float32)
#guard Float32.nextUp (-0) == minSubF32
#guard Float32.nextUp maxF32 == Float32.inf
#guard Float32.nextUp (-Float32.inf) == -maxF32
#guard Float32.ulp 1 == 2 ^ (-23 : Float32)
#guard Float32.ulp maxF32 == 2 ^ (104 : Float32)
#guard (Float32.ulp Float32.inf).isNaN
#guard Float32.ulpDistance? maxF32 Float32.inf == some 1
#guard Float32.ulpDistance? 0 (-0) == some 0

/-! Kernel checks: the same results hold in the logical model. -/

example : Float.nextUp 0 = .ofBits 1 := by decide +kernel
example : Float.nextUp (.ofBits 0x7FEFFFFFFFFFFFFF) = Float.inf := by decide +kernel
example : Float.nextDown 1 = .ofBits 0x3FEFFFFFFFFFFFFF := by decide +kernel
example : Float.ulp 1 = .ofBits 0x3CB0000000000000 := by decide +kernel
example : Float.copySign 2 (-0) = -2 := by decide +kernel
example : Float.classify (.ofBits 1) = .subnormal := by decide +kernel
example : Float.signBit Float.nan = false := by decide +kernel
example : Float.ulpDistance? 0 (-0) = some 0 := by decide +kernel
example : Float32.nextUp 1 = .ofBits 0x3F800001 := by decide +kernel
example : Float32.ulp (.ofBits 0x7F7FFFFF) = .ofBits 0x73800000 := by decide +kernel
