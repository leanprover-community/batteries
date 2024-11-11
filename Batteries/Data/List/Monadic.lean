/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Classes.SatisfiesM

/-!
# Results about monadic operations on `List`, in terms of `SatisfiesM`.

-/

namespace List

theorem SatisfiesM_foldlM [Monad m] [LawfulMonad m] {f : β → α → m β} (h₀ : motive b)
    (h₁ : ∀ (b) (_ : motive b) (a : α) (_ : a ∈ l), SatisfiesM motive (f b a)) :
    SatisfiesM motive (List.foldlM f b l) := by
  have g b hb a am := Classical.indefiniteDescription _ (h₁ b hb a am)
  clear h₁
  induction l generalizing b with
  | nil => exact SatisfiesM.pure h₀
  | cons hd tl ih =>
    simp only [foldlM_cons]
    apply SatisfiesM.bind_pre
    let ⟨q, qh⟩ := g b h₀ hd (List.mem_cons_self hd tl)
    exact ⟨(fun ⟨b, bh⟩ => ⟨b, ih bh (fun b bh a am => g b bh a (mem_cons_of_mem hd am))⟩) <$> q,
      by simpa using qh⟩

end List
