/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace List

/--
Version of `List.zipWith` that continues to the end of both lists, passing `none` to one argument
once the shorter list has run out.
-/
-- TODO We should add a tail-recursive version as we do for other `zip` functions above.
def zipWithAll (f : Option α → Option β → γ) : List α → List β → List γ
  | [], bs => bs.map fun b => f none (some b)
  | a :: as, [] => (a :: as).map fun a => f (some a) none
  | a :: as, b :: bs => f a b :: zipWithAll f as bs

@[simp] theorem zipWithAll_nil_right :
    zipWithAll f as [] = as.map fun a => f (some a) none := by
  cases as <;> rfl

@[simp] theorem zipWithAll_nil_left :
    zipWithAll f [] bs = bs.map fun b => f none (some b) := by
  rw [zipWithAll]

@[simp] theorem zipWithAll_cons_cons :
    zipWithAll f (a :: as) (b :: bs) = f (some a) (some b) :: zipWithAll f as bs := rfl
