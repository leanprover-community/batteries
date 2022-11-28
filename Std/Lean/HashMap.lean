/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.HashSet

/-!
# Additional API for `HashSet`

-/

namespace Lean.HashSet

/-- Insert many elements into a HashSet. -/
def insertMany [BEq α] [Hashable α] [ForIn Id ρ α] (s : HashSet α) (as : ρ) : HashSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

end Lean.HashSet
