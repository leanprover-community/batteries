/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2. license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace FloatArray

/--
Unsafe optimized implementation of `mapM`.

This function is unsafe because it relies on the implementation limit that the size of an array is
always less than `USize.size`.
-/
@[inline]
unsafe def mapMUnsafe [Monad m] (a : FloatArray) (f : Float → m Float) : m FloatArray :=
  loop a 0 a.usize
where
  /-- Inner loop for `mapMUnsafe`. -/
  @[specialize]
  loop (a : FloatArray) (k s : USize) := do
    if k < s then
      let x := a.uget k lcProof
      let y ← f x
      let a := a.uset k y lcProof
      loop a (k+1) s
    else pure a

/-- `mapM f a` applies the monadic function `f` to each element of the array. -/
@[implemented_by mapMUnsafe]
def mapM [Monad m] (a : FloatArray) (f : Float → m Float) : m FloatArray := do
  let mut r := a
  for i in [0:r.size] do
    r := r.set! i (← f r[i]!)
  return r

/-- `map f a` applies the function `f` to each element of the array. -/
@[inline]
def map (a : FloatArray) (f : Float → Float) : FloatArray :=
  mapM (m:=Id) a f
