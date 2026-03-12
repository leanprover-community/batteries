import Batteries.Tactic.Lint

/-! Tests that linters skip auto-generated declarations from coinductive predicates. -/

/-- A coinductive stream predicate for testing. -/
coinductive MyStream (α : Type) : Prop where
  | cons : α → MyStream α → MyStream α

mutual
  /-- Coinductive half of a mutual block for testing. -/
  coinductive tick : Prop where
  | mk : ¬tock → tick

  /-- Inductive half of a mutual block for testing. -/
  inductive tock : Prop where
  | mk : ¬tick → tock
end

#guard_msgs in
#lint- only defLemma

#guard_msgs in
#lint- only docBlame
