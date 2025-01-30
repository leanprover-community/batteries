import Batteries.Tactic.Basic

private def nonDecid (P : Prop) (x : P) : P := by
  by_contra h
  guard_hyp h : ¬P
  guard_target = False
  exact h x

private def decid (P : Prop) [Decidable P] (x : P) : P := by
  by_contra h
  guard_hyp h : ¬P
  guard_target = False
  exact h x

example (P : Prop) [Decidable P] : nonDecid P = decid P := by
  delta nonDecid decid
  guard_target =
    (fun x : P => Classical.byContradiction fun h => h x) =
    (fun x : P => Decidable.byContradiction fun h => h x)
  rfl

example (P : Prop) : P → P := by
  by_contra
  guard_hyp ‹_› : ¬(P → P)
  exact ‹¬(P → P)› id
