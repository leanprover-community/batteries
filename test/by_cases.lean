import Std.Tactic.ByCases
import Std.Tactic.GuardMsgs

example : True := by
  if 1 + 1 = 2 then _ else ?_
  case pos => trivial
  fail_if_success case neg => contradiction
  · contradiction

example (p : Prop) : True := by
  if p then ?foo else trivial
  case foo => trivial

theorem foo1 (p q : Prop) [Decidable p] [Decidable q] : p ∧ q ∨ ¬p ∨ ¬q := by
  by_cases hp : p
  · if hq : q then ?foo else _
    case foo =>
      exact .inl <| .intro hp hq
    case pos.neg =>
      exact .inr <| .inr hq
  · by_cases q
    case neg.pos =>
      exact .inr <| .inl hp
    case neg.neg =>
      exact .inr <| .inr (by assumption)

/--
info: 'foo1' does not depend on any axioms
-/
#guard_msgs in #print axioms foo1

theorem foo2 (p q : Prop) [Decidable p] [Decidable q] : p ∧ q ∨ ¬p ∨ ¬q := by
  if hp : p then _ else ?_
  · by_cases hq : q
    case pos.pos =>
      exact .inl <| .intro hp hq
    case pos.neg =>
      exact .inr <| .inr hq
  · if q then _ else _
    case pos =>
      exact .inr <| .inl hp
    case neg =>
      exact .inr <| .inr (by assumption)

/--
info: 'foo2' does not depend on any axioms
-/
#guard_msgs in #print axioms foo2
