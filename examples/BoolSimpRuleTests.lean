import Std

section dprop
variable (u v : Prop) [Decidable u] [Decidable v]


end dprop

-- ## Prop Equality tests

section prop
variable (x y : Prop)

section
variable (c : x = y)
example : x = y := by simp [c]
example : x ↔ y := by simp [c]
end

section
variable (c : x ↔ y)
example : x = y := by simp [c]
example : x ↔ y := by simp [c]
end

end prop

-- ## Bool Equality

section bool
variable (x y : Bool)

section
variable (c : x = y)
example : x = y := by simp only [c]
example : x ↔ y := by simp only [c]
example : x == y := by simp [c]
example : x == y := by simp only [c, beq_self_eq_true]
end

section
variable (c : x ↔ y)
example : x = y := by simp only [c]
example : x = y := by simp_all
example : x = y := by simp_all [propext c]
example : x = y := by cases x <;> cases y <;> simp_all
example : x ↔ y := by simp only [c]
example : x = y := by simp only [c]
example : x = y := by simp_all
example : x = y := by simp_all [propext c]
example : x = y := by cases x <;> cases y <;> simp_all
example : x == y := by simp [c]
example : x == y := by simp_all
example : x == y := by simp only [c, beq_self_eq_true]
end

section
variable (c : x == y)
example : x = y := by simp [c]
example : x = y := by simp_all
example : x ↔ y := by simp [c]
example : x ↔ y := by simp_all
example : x == y := by simp [c]
end

end bool

section dprop
variable (x y : Prop) [Decidable x] [Decidable y]

section
variable (c : x = y)
example : x = y := by simp only [c]
example : x ↔ y := by simp only [c]
example : x == y := by simp [c]
example : x == y := by simp only [c, beq_self_eq_true]
end

section
variable (c : x ↔ y)
example : x = y := by simp only [c]
example : x = y := by simp_all
example : x = y := by simp_all [propext c]
example : x = y := by cases decide x <;> cases decide y <;> simp_all
example : x ↔ y := by simp only [c]
example : x = y := by simp only [c]
example : x = y := by simp_all
example : x = y := by simp_all [propext c]
example : x = y := by cases decide x <;> cases decide y <;> simp_all
example : x == y := by simp [c]
example : x == y := by simp_all
example : x == y := by simp only [c, beq_self_eq_true]
end

section
variable (c : x == y)
example : x = y := by simp [c]
example : x = y := by simp_all
example : x ↔ y := by simp [c]
example : x ↔ y := by simp_all
example : x == y := by simp [c]
end

end dprop

-- ## Getting implications from definitions

section prop
variable (x y : Prop)

section
variable (c : x = y)
example : x → y := c.mp
example : y → x := c.mpr
end

section
variable (c : x ↔ y)
example : x → y := c.mp
example : y → x := c.mpr
end

end prop

section bool
variable (x y : Bool)

section
variable (c : x = y)
example : x → y := c.mp
example : y → x := c.mpr
end

section
variable (c : x ↔ y)
example : x → y := c.mp
example : y → x := c.mpr
end

section
variable (c : x == y)
example : x → y := c.mp
example : y → x := c.mpr
end

end bool

section dprop
variable (x y : Prop) [Decidable x] [Decidable y]

section
variable (c : x = y)
example : x → y := c.mp
example : y → x := c.mpr
end

section
variable (c : x ↔ y)
example : x → y := c.mp
example : y → x := c.mpr
end

section
variable (c : x == y)
example : x → y := c.mp
example : y → x := c.mpr
end

end dprop

-- # Inequality tests

-- ## Prop tests

section prop
variable (x y : Prop)

section
variable (c : x ≠ y)
example : x ≠ y := by simp [c]
example : ¬(x = y) := by simp [c]
end

section
variable (c : ¬(x = y))
example : x ≠ y := by simp [c]
example : ¬(x = y) := by simp [c]
end

end prop

-- ## Bool tests

section bool
variable (x y : Bool)

section
variable (c : x ≠ y)
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : ¬(x = y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : ¬(x = y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : ¬(x = y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : ¬(x = y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : xor x y)
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end
end bool

-- ## Decidable Prop tests

section dprop
variable (x y : Prop) [Decidable x] [Decidable y]

section
variable (c : x ≠ y)
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : ¬(x = y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : x != y)
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : ¬(x == y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : !(x == y))
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end

section
variable (c : xor x y)
example : x ≠ y     := by simp [c]
example : ¬(x = y)  := by simp [c]
example : x != y    := by simp [c]
example : ¬(x == y) := by simp [c]
example : !(x == y) := by simp [c]
example : xor x y   := by simp [c]
end
end dprop

-- # Not tests

section bool
variable (x : Bool)

section
variable (c : ¬x)
example : ¬x := by simp [c]
example : !x := by simp [c]
end

section
variable (c : !x)
example : ¬x := by simp [c]
example : !x := by simp [c]
end
end bool

section dprop
variable (x : Prop) [Decidable x]

section
variable (c : ¬x)
example : ¬x := by simp [c]
example : !x := by simp [c]
end

section
variable (c : !x)
example : ¬x := by simp [c]
example : !x := by simp [c]
end
end dprop

-- # And tests

section prop
variable (x y : Prop)

section
variable (c : x ∧ y)
example : x ∧ y := by simp [c]
example : x := by simp [c]
example : y := by simp [c]
end

end prop

section bool
variable (x y : Bool)

section
variable (c : x ∧ y)
example : x ∧ y := by simp [c]
example : x := by simp [c]
example : y := by simp [c]
example : x && y := by simp [c]
end

section
variable (c : x && y)
example : x ∧ y := by simp [c]
example : x ∧ y := by simp_all
example : x := by simp_all
example : y := by simp_all
example : x && y := by simp [c]
end
end bool

section dprop
variable (x y : Prop) [Decidable x] [Decidable y]

section
variable (c : x ∧ y)
example : x ∧ y := by simp [c]
-- Tests simp reduces conjunction lemmas
example : x := by simp [c]
example : y := by simp [c]
example : x && y := by simp [c]
example : x ∨ y := by simp [c]
example : x || y := by simp [c]
end

section
variable (c : x && y)
-- Simp does not reduce x && y
example : x ∧ y := by simp [c]
example : x ∧ y := by simp_all
example : x := by simp [c]
example : y := by simp [c]
example : x && y := by simp [c]
end
end dprop

-- # Or tests

section
variable (x y : Prop)

section
variable (c : x ∨ y)
example : x ∨ y := by simp [c]
end

end

section bool
variable (x y : Bool)

section
variable (c : x ∨ y)
example : x ∨ y := by simp [c]
example : x || y := by simp [c]
end

section
variable (c : x || y)
example : x ∨ y := by simp [c]
example : x ∨ y := by simp_all
example : x || y := by simp [c]
end

end bool

section dprop
variable (x y : Prop) [Decidable x] [Decidable y]

section
variable (c : x ∨ y)
example : x ∨ y := by simp [c]
example : x || y := by simp [c]
end

section
variable (c : x || y)
example : x ∨ y := by simp [c]
example : x ∨ y := by simp_all
example : x || y := by simp [c]
end
end dprop

-- # TODO: Tests with other types involving LawfulBEq

-- ## Preliminaries

-- Define a type with a BEq instance

inductive DecType where
| prim : DecType
| proper : DecType
deriving DecidableEq

inductive LawType where
| roger : LawType
| rober : LawType
deriving BEq

instance : LawfulBEq LawType where
  rfl := by
    intro a
    cases a <;> rfl
  eq_of_beq := by
    intro a b eq
    -- N.B. It'd be ideal if contradiction was not needed
    cases a <;> cases b <;> simp_all <;> contradiction

-- A type without a lawful equality
inductive OutlawType where
| foo : OutlawType
| bar : OutlawType

instance : BEq OutlawType where
  beq _ _ := false
