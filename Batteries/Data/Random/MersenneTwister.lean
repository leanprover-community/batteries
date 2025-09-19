/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public section

/-! # Mersenne Twister

Generic implementation for the Mersenne Twister pseudorandom number generator.

All choices of parameters from Matsumoto and Nishimura (1998) are supported, along with later
refinements. Parameters for the standard 32-bit MT19937 and 64-bit MT19937-64 algorithms are
provided. Both `RandomGen` and `Stream` interfaces are provided.

Use `mt19937.init seed` to create a MT19937 PRNG with a 32 bit seed value; use
`mt19937_64.init seed` to create a MT19937-64 PRNG with a 64 bit seed value. If omitted, default
seed choices will be used.

Sample usage:
```
import Batteries.Data.Random.MersenneTwister

open Batteries.Random.MersenneTwister

def mtgen := mt19937.init -- default seed 4357

#eval (Stream.take mtgen 5).fst -- [874448474, 2424656266, 2174085406, 1265871120, 3155244894]
```

### References:

- Matsumoto, Makoto and Nishimura, Takuji (1998),
  [**Mersenne twister: A 623-dimensionally equidistributed uniform pseudo-random number generator**](https://doi.org/10.1145/272991.272995),
  ACM Trans. Model. Comput. Simul. 8, No. 1, 3-30.
  [ZBL0917.65005](https://zbmath.org/?q=an:0917.65005).

- Nishimura, Takuji (2000),
  [**Tables of 64-bit Mersenne twisters**](https://doi.org/10.1145/369534.369540),
  ACM Trans. Model. Comput. Simul. 10, No. 4, 348-357.
  [ZBL1390.65014](https://zbmath.org/?q=an:1390.65014).
-/

namespace Batteries.Random.MersenneTwister

/--
Mersenne Twister configuration.

Letters in parentheses correspond to variable names used by Matsumoto and Nishimura (1998) and
Nishimura (2000).
-/
structure Config where
  /-- Word size (`w`). -/
  wordSize : Nat
  /-- Degree of recurrence (`n`). -/
  stateSize : Nat
  /-- Middle word (`m`). -/
  shiftSize : Fin stateSize
  /-- Twist value (`r`). -/
  maskBits : Fin wordSize
  /-- Coefficients of the twist matrix (`a`). -/
  xorMask : BitVec wordSize
  /-- Tempering shift parameters (`u`, `s`, `t`, `l`). -/
  temperingShifts : Nat × Nat × Nat × Nat
  /-- Tempering mask parameters (`d`, `b`, `c`). -/
  temperingMasks : BitVec wordSize × BitVec wordSize × BitVec wordSize
  /-- Initialization multiplier (`f`). -/
  initMult : BitVec wordSize
  /-- Default initialization seed value. -/
  initSeed : BitVec wordSize

private abbrev Config.uMask (cfg : Config) : BitVec cfg.wordSize :=
  BitVec.allOnes cfg.wordSize <<< cfg.maskBits.val

private abbrev Config.lMask (cfg : Config) : BitVec cfg.wordSize :=
  BitVec.allOnes cfg.wordSize >>> (cfg.wordSize - cfg.maskBits.val)

@[simp] theorem Config.zero_lt_wordSize (cfg : Config) : 0 < cfg.wordSize :=
  Nat.zero_lt_of_lt cfg.maskBits.is_lt

@[simp] theorem Config.zero_lt_stateSize (cfg : Config) : 0 < cfg.stateSize :=
  Nat.zero_lt_of_lt cfg.shiftSize.is_lt

/-- Mersenne Twister State. -/
structure State (cfg : Config) where
  /-- Data for current state. -/
  data : Vector (BitVec cfg.wordSize) cfg.stateSize
  /-- Current data index. -/
  index : Fin cfg.stateSize

/-- Mersenne Twister initialization given an optional seed. -/
@[specialize cfg] protected def Config.init (cfg : MersenneTwister.Config)
    (seed : BitVec cfg.wordSize := cfg.initSeed) : State cfg :=
  ⟨loop seed (.mkEmpty cfg.stateSize) (Nat.zero_le _), 0, cfg.zero_lt_stateSize⟩
where
  /-- Inner loop for Mersenne Twister initalization. -/
  loop (w : BitVec cfg.wordSize) (v : Array (BitVec cfg.wordSize)) (h : v.size ≤ cfg.stateSize) :=
    if heq : v.size = cfg.stateSize then ⟨v, heq⟩ else
      let v := v.push w
      let w := cfg.initMult * (w ^^^ (w >>> cfg.wordSize - 2)) + v.size
      loop w v (by simp only [v, Array.size_push]; omega)

/-- Apply the twisting transformation to the given state. -/
@[specialize cfg] protected def State.twist (state : State cfg) : State cfg :=
  let i := state.index
  let i' : Fin cfg.stateSize :=
    if h : i.val+1 < cfg.stateSize then ⟨i.val+1, h⟩ else ⟨0, cfg.zero_lt_stateSize⟩
  let y := state.data[i] &&& cfg.uMask ||| state.data[i'] &&& cfg.lMask
  let x := state.data[i+cfg.shiftSize] ^^^ bif y[0] then y >>> 1 ^^^ cfg.xorMask else y >>> 1
  ⟨state.data.set i x, i'⟩

/-- Update the state by a number of generation steps (default 1). -/
-- TODO: optimize to `O(log(steps))` using the minimal polynomial
protected def State.update (state : State cfg) : (steps : Nat := 1) → State cfg
  | 0 => state
  | steps+1 => state.twist.update steps

/-- Mersenne Twister iteration. -/
@[specialize cfg] protected def State.next (state : State cfg) : BitVec cfg.wordSize × State cfg :=
  let i := state.index
  let s := state.twist
  (temper s.data[i], s)
where
  /-- Tempering step for Mersenne Twister. -/
  @[inline] temper (x : BitVec cfg.wordSize) :=
    match cfg.temperingShifts, cfg.temperingMasks with
    | (u, s, t, l), (d, b, c) =>
      let x := x ^^^ x >>> u &&& d
      let x := x ^^^ x <<< s &&& b
      let x := x ^^^ x <<< t &&& c
      x ^^^ x >>> l

instance (cfg) : Stream (State cfg) (BitVec cfg.wordSize) where
  next? s := s.next

/-- 32 bit Mersenne Twister (MT19937) configuration. -/
def mt19937 : Config where
  wordSize := 32
  stateSize := 624
  shiftSize := 397
  maskBits := 31
  xorMask := 0x9908b0df
  temperingShifts := (11, 7, 15, 18)
  temperingMasks := (0xffffffff, 0x9d2c5680, 0xefc60000)
  initMult := 1812433253
  initSeed := 4357

/-- 64 bit Mersenne Twister (MT19937-64) configuration. -/
def mt19937_64 : Config where
  wordSize := 64
  stateSize := 312
  shiftSize := 156
  maskBits := 31
  xorMask := 0xb5026f5aa96619e9
  temperingShifts := (29, 17, 37, 43)
  temperingMasks := (0x5555555555555555, 0x71d67fffeda60000, 0xfff7eee000000000)
  initMult := 6364136223846793005
  initSeed := 19650218
