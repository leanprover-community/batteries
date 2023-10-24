import Std.Tactic.TryThis

section width
-- here we test that the width of try this suggestions is not too big

-- simulate a long and complicated term
def longdef (a b : Nat) (h h h h h h h h h h h h h h h h h
    h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h
    h h h h h h h h h h h h h h h h h h h h h h h
    h h h h h h h h h h h h h h h h h h h h h : a = b) :
  2 * a = 2 * b := by rw [h]

namespace Std.Tactic.TryThis
open Lean Elab Tactic

set_option hygiene false in
elab "test" : tactic => do
  addSuggestion (← getRef) (←
  `(tactic| exact longdef a b h h h h h h h h h h h h h h
      h h h h h h h h h h h h h h h h h h h h h h
      h h h h h h h h h h h h h h h h h h h h h h
      h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h))

end Std.Tactic.TryThis

-- ideally we would have a #guard_widgets or #guard_infos too, but instead we can simply check by
-- hand that the widget suggestion (not the message) fits into 100 columns
theorem asda (a b : Nat) (h : a = b) : 2 * a = 2 * b := by
  test
--exact
--  longdef a b h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h
--    h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h
--    h h h h h
  have : 2 * a = 2 * b := by
    test
--  exact
--    longdef a b h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h
--      h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h h
--      h h h h h h h
    sorry
  sorry
