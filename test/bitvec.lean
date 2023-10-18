import Std.Tactic.GuardExpr
import Std.Data.BitVec

open Std.BitVec

-- Basic arithmetic
#guard 1#12 + 2#12 = 3#12
#guard 3#5 * 7#5 = 0x15#5
#guard 3#4 * 7#4 = 0x05#4

-- Division and mod/rem


#guard 3#4 / 0 = 0

#guard 10#4 / 2 = 5

#guard 8#4 % 0 = 8
#guard 4#4 % 1 = 0
#guard 4#4 % 3 = 1
#guard 0xf#4 % (-2) = 1
#guard 0xf#4 % (-8) = 7

#guard sdiv 6#4 2 = 3#4
#guard sdiv 7#4 2 = 3#4
#guard sdiv 6#4 (-2) = -3#4
#guard sdiv 7#4 (-2) = -3#4
#guard sdiv (-6#4) 2 = -3#4
#guard sdiv (-7#4) 2 = -3#4
#guard sdiv (-6#4) (-2) = 3#4
#guard sdiv (-7#4) (-2) = 3#4

#guard srem   3#4    2  =  1
#guard srem (-4#4)   3  = -1
#guard srem ( 4#4) (-3) =  1
#guard srem (-4#4) (-3) = -1

#guard smod   3#4    2  = 1
#guard smod (-4#4)   3  =  2
#guard smod ( 4#4) (-3) = -2
#guard smod (-4#4) (-3) = -1

-- ofInt/toInt

#guard .ofInt 3 (-1) = 0b111#3
#guard .ofInt 3 0 = 0b000#3
#guard .ofInt 3 4 = 0b100#3
#guard .ofInt 3 (-2) = 0b110#3
#guard .ofInt 3 (-4) = 0b100#3

#guard (0x0#4).toInt = 0
#guard (0x7#4).toInt = 7
#guard (0x8#4).toInt = -8
#guard (0xe#4).toInt = -2

-- Bitwise operations

#guard ~~~0b1010#4 = 0b0101#4
#guard 0b1010#4 &&& 0b0110#4 = 0b0010#4
#guard 0b1010#4 ||| 0b0110#4 = 0b1110#4
#guard 0b1010#4 ^^^ 0b0110#4 = 0b1100#4

-- shift operations
#guard 0b0011#4 <<< 3 = 0b1000
#guard 0b1011#4 >>> 1 = 0b0101
#guard sshiftRight 0b1001#4 1 = 0b1100#4
#guard rotateLeft  0b0011#4 3 = 0b1001
#guard rotateRight 0b0010#4 2 = 0b1000
#guard 0xab#8 ++ 0xcd#8 = 0xabcd#16

-- get/extract

#guard !getMsb 0b0101#4 0
#guard getMsb 0b0101#4 1
#guard !getMsb 0b0101#4 2
#guard getMsb 0b0101#4 3
#guard !getMsb 0b1111#4 4

#guard getLsb 0b0101#4 0
#guard !getLsb 0b0101#4 1
#guard getLsb 0b0101#4 2
#guard !getLsb 0b0101#4 3
#guard !getLsb 0b1111#4 4

#guard extractLsb 3 0 0x1234#16 = 4
#guard extractLsb 7 4 0x1234#16 = 3
#guard extractLsb' 0 4 0x1234#16 = 0x4#4

-- Pretty-printing

#guard toString 5#12 = "0x005#12"
#guard toString 5#13 = "0x0005#13"
#guard toString 5#12 = "0x005#12"
#guard toString 5#13 = "0x0005#13"
