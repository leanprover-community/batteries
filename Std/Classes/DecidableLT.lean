/--
Asserts that the "less-than" relation on `α` is decidable, that is, `a < b` is decidable for all
`a b : α`. See `Decidable`.

It is generally not necessary to create instances of this class directly, because Lean will create
one whenever a `DecidableRel` instance exists for the `LT` instance in question.
-/
class DecidableLT (α : Type u) extends LT α where
  /-- Decide whether `x` is less than `y`. -/
  decLT : (x y : α) → Decidable (LT.lt x y)

instance [DecidableLT α] {x y : α} : Decidable (x < y) := DecidableLT.decLT _ _

instance [inst : LT α] [DecidableRel (@LT.lt α inst)] : DecidableLT α where
  decLT := inferInstance
