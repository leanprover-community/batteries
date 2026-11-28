import Batteries.Data.Float.ErrorFree

/-! Runtime checks of `mulErr` and `twoSum`. -/

-- Float
def maxF : Float := .ofBits 0x7FEFFFFFFFFFFFFF
def p30 : Float := .ofBits 0x3E10000000000000 -- `2⁻³⁰`
def p53 : Float := .ofBits 0x3CA0000000000000 -- `2⁻⁵³`
def p60 : Float := .ofBits 0x3C30000000000000 -- `2⁻⁶⁰`

#guard Float.mulErr 3 5 == 0
#guard Float.mulErr (1 + p30) (1 + p30) == p60
#guard (Float.mulErr maxF 2).isFinite == false

#guard Float.twoSum 1 2 == (3, 0)
#guard Float.twoSum 1 p60 == (1, p60)
#guard Float.twoSum p60 1 == (1, p60)
#guard Float.twoSum 1 (-1 + p53) == (p53, 0)

-- Float32
def q12 : Float32 := .ofBits 0x39800000 -- `2⁻¹²`
def q24 : Float32 := .ofBits 0x33800000 -- `2⁻²⁴`
def q30 : Float32 := .ofBits 0x30800000 -- `2⁻³⁰`

#guard Float32.mulErr (1 + q12) (1 + q12) == q24
#guard Float32.twoSum 1 q30 == (1, q30)
#guard Float32.twoSum q30 1 == (1, q30)
