/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

-- Note: this will be replaced by `_root_.map_inj_right_of_nonempty` in nightly-2025-02-07
theorem _root_.LawfulFunctor.map_inj_right_of_nonempty [Functor f] [LawfulFunctor f] [Nonempty α]
    {g : α → β} (h : ∀ {x y : α}, g x = g y → x = y) {x y : f α} :
    g <$> x = g <$> y ↔ x = y := by
  constructor
  · open Classical in
    let g' a := if h : ∃ b, g b = a then h.choose else Classical.ofNonempty
    have g'g a : g' (g a) = a := by
      simp only [exists_apply_eq_apply, ↓reduceDIte, g']
      exact h (_ : ∃ b, g b = g a).choose_spec
    intro h'
    simpa only [Functor.map_map, g'g, id_map'] using congrArg (g' <$> ·) h'
  · intro h'
    rw [h']

-- Note: this will be replaced by `_root_.map_inj_right` in nightly-2025-02-07
theorem _root_.LawfulMonad.map_inj_right [Monad m] [LawfulMonad m]
    {f : α → β} (h : ∀ {x y : α}, f x = f y → x = y) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  by_cases hempty : Nonempty α
  · exact LawfulFunctor.map_inj_right_of_nonempty h
  · constructor
    · intro h'
      have (z : m α) : z = (do let a ← z; let b ← pure (f a); x) := by
        conv => lhs; rw [← bind_pure z]
        congr; funext a
        exact (hempty ⟨a⟩).elim
      rw [this x, this y]
      rw [← bind_assoc, ← map_eq_pure_bind, h', map_eq_pure_bind, bind_assoc]
    · intro h'
      rw [h']
