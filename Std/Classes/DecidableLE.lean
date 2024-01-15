/--
Asserts that the "less-than-or-equal" relation on `α` is decidable, that is, `a ≤ b` is decidable
for all `a b : α`. See `Decidable`.

It is generally not necessary to create instances of this class directly, because Lean will create
one whenever a `DecidableRel` instance exists for the `LE` instance in question.
-/
class DecidableLE (α : Type u) extends LE α where
  /-- Decide whether `x` is less than or equal to `y`. -/
  decLE : (x y : α) → Decidable (LE.le x y)

instance [DecidableLE α] {x y : α} : Decidable (x ≤ y) := DecidableLE.decLE _ _

instance [inst : LE α] [DecidableRel (@LE.le α inst)] : DecidableLE α where
  decLE := inferInstance
