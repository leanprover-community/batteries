/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-! # Additional definitions on `ForInStep` -/

/--
This is similar to a monadic `bind` operator, except that the two type parameters have to be
the same, which prevents putting a monad instance on `ForInStepT m α := m (ForInStep α)`.
-/
@[inline] protected def ForInStep.bind [Monad m]
    (a : ForInStep α) (f : α → m (ForInStep α)) : m (ForInStep α) :=
  match a with
  | .done a => return .done a
  | .yield a => f a

@[inherit_doc ForInStep.bind] protected abbrev ForInStep.bindM [Monad m]
    (a : m (ForInStep α)) (f : α → m (ForInStep α)) : m (ForInStep α) := a >>= (·.bind f)

/--
Get the value out of a `ForInStep`.
This is usually done at the end of a `forIn` loop to scope the early exit to the loop body.
-/
@[inline] def ForInStep.run : ForInStep α → α
  | .done a
  | .yield a => a

/-- Applies function `f` to each element of a list to accumulate a `ForInStep` value. -/
def ForInStep.bindList [Monad m]
      (f : α → β → m (ForInStep β)) : List α → ForInStep β → m (ForInStep β)
  | [], s => pure s
  | a::l, s => s.bind fun b => f a b >>= (·.bindList f l)
